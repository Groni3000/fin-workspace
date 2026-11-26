//! Runs async code on a thread of its own and talks to it from synchronous code.
//!
//! [`spawn`] starts a thread with a single-threaded tokio runtime and runs a task on it. The task
//! sends events to the synchronous side and receives requests from it; both channels are
//! unbounded, so neither side ever waits for the other.

use std::future::Future;
use std::sync::mpsc::{self, RecvError, RecvTimeoutError};
use std::thread::JoinHandle;
use std::time::Duration;

use tokio::sync::{mpsc as tokio_mpsc, oneshot};

/// The synchronous side of a running task.
///
/// Dropping it cancels the task (at its next `.await`) and joins the thread. If the task
/// panicked, the panic is resumed on the dropping thread, unless that one is already panicking.
pub struct Bridge<E, Q> {
    events: mpsc::Receiver<E>,
    requests: tokio_mpsc::UnboundedSender<Q>,
    cancel: Option<oneshot::Sender<()>>,
    thread: Option<JoinHandle<()>>,
}

/// Starts `task` on a new thread named `bridge`. The task gets the sending end for events and
/// the receiving end for requests.
pub fn spawn<E, Q, F, Fut>(task: F) -> std::io::Result<Bridge<E, Q>>
where
    E: Send + 'static,
    Q: Send + 'static,
    F: FnOnce(mpsc::Sender<E>, tokio_mpsc::UnboundedReceiver<Q>) -> Fut + Send + 'static,
    Fut: Future<Output = ()>,
{
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    let (events_tx, events) = mpsc::channel();
    let (requests, requests_rx) = tokio_mpsc::unbounded_channel();
    let (cancel, cancelled) = oneshot::channel();
    let thread = std::thread::Builder::new()
        .name("bridge".to_string())
        .spawn(move || {
            runtime.block_on(async move {
                tokio::select! {
                    () = task(events_tx, requests_rx) => {}
                    // Fires when the `Bridge` drops the sender.
                    _ = cancelled => {}
                }
            });
        })?;
    Ok(Bridge {
        events,
        requests,
        cancel: Some(cancel),
        thread: Some(thread),
    })
}

impl<E, Q> Bridge<E, Q> {
    /// Hands `request` to the task. Gives it back if the task has ended.
    pub fn send(&self, request: Q) -> Result<(), Q> {
        self.requests.send(request).map_err(|e| e.0)
    }

    /// Waits for the next event. Events the task sent before it ended are still delivered; after
    /// them, an error.
    pub fn recv(&self) -> Result<E, RecvError> {
        self.events.recv()
    }

    /// Like [`Bridge::recv`], giving up after `timeout`.
    pub fn recv_timeout(&self, timeout: Duration) -> Result<E, RecvTimeoutError> {
        self.events.recv_timeout(timeout)
    }

    /// Cancels the task and joins the thread, returning the task's panic if it had one.
    pub fn finish(mut self) -> std::thread::Result<()> {
        self.stop()
    }

    fn stop(&mut self) -> std::thread::Result<()> {
        drop(self.cancel.take());
        match self.thread.take() {
            Some(thread) => thread.join(),
            None => Ok(()),
        }
    }
}

impl<E, Q> Drop for Bridge<E, Q> {
    fn drop(&mut self) {
        if let Err(panic) = self.stop()
            && !std::thread::panicking()
        {
            std::panic::resume_unwind(panic);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Events = mpsc::Sender<()>;
    type Requests = tokio_mpsc::UnboundedReceiver<()>;

    /// Never sends, never ends. Holds the sender, so the channel stays open.
    async fn quiet(events: Events, _: Requests) {
        let _events = events;
        std::future::pending::<()>().await
    }

    /// Holds the sender until it panics, so `recv` returns only once the panic has happened.
    async fn boom(events: Events, _: Requests) {
        let _events = events;
        panic!("boom")
    }

    #[test]
    fn requests_come_back_as_events_in_order() {
        let bridge = spawn(|events: mpsc::Sender<u32>, mut requests| async move {
            while let Some(n) = requests.recv().await {
                events.send(n * 10).unwrap();
            }
        })
        .unwrap();
        for n in [1_u32, 2, 3] {
            bridge.send(n).unwrap();
        }
        let got: Vec<u32> = (0..3).map(|_| bridge.recv().unwrap()).collect();
        assert_eq!(got, [10, 20, 30]);
        bridge.finish().unwrap();
    }

    #[test]
    fn the_task_runs_on_the_bridge_thread() {
        let bridge = spawn(|events: mpsc::Sender<Option<String>>, _: tokio_mpsc::UnboundedReceiver<()>| async move {
            events
                .send(std::thread::current().name().map(str::to_string))
                .unwrap();
        })
        .unwrap();
        assert_eq!(bridge.recv().unwrap().as_deref(), Some("bridge"));
    }

    #[test]
    fn recv_timeout_gives_up_while_the_task_is_quiet() {
        let bridge = spawn(quiet).unwrap();
        assert_eq!(
            bridge.recv_timeout(Duration::from_millis(20)),
            Err(RecvTimeoutError::Timeout)
        );
    }

    /// The task never looks at its requests, so only cancelling it can end the thread.
    #[test]
    fn finishing_cancels_a_task_that_never_ends() {
        let bridge = spawn(quiet).unwrap();
        bridge.finish().unwrap();
    }

    #[test]
    fn events_sent_before_the_task_ended_are_delivered() {
        let bridge = spawn(
            |events: mpsc::Sender<u32>, _: tokio_mpsc::UnboundedReceiver<()>| async move {
                events.send(1).unwrap();
                events.send(2).unwrap();
            },
        )
        .unwrap();
        assert_eq!(bridge.recv(), Ok(1));
        assert_eq!(bridge.recv(), Ok(2));
        assert_eq!(bridge.recv(), Err(RecvError));
        assert_eq!(bridge.send(()), Err(()), "the task has ended");
    }

    #[test]
    fn a_panic_in_the_task_reaches_the_synchronous_side() {
        let bridge = spawn(boom).unwrap();
        assert_eq!(bridge.recv(), Err(RecvError));
        let panic = bridge.finish().unwrap_err();
        assert_eq!(panic.downcast_ref::<&str>(), Some(&"boom"));
    }

    #[test]
    #[should_panic(expected = "boom")]
    fn dropping_resumes_the_tasks_panic() {
        let bridge = spawn(boom).unwrap();
        assert_eq!(bridge.recv(), Err(RecvError));
        drop(bridge);
    }
}
