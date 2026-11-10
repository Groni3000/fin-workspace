# engine

The runtime around a strategy: events, the queue that orders them, and the
executors that turn requests into acks and fills. Built on
[`mdata`](../mdata) (market-data records) and [`oms`](../oms) (orders, fills, and the
order protocol: `ExecEvent`, `Request`, `RejectReason`, `RequestSink`).

| Module | What's in it |
|---|---|
| `event` | `Event`, `Kind` (market data, an executor's `ExecEvent`, or a feed error), `EventSource`, and `Scheduled`/`Scheduler` for events due in the future |
| `executor` | the `Executor` trait: whatever fills, cancels and rejects orders, simulated or live |
| `merge` | the one rule for merging feed records with scheduled events: `scheduled_first` and `NextRecord` |
| `sim` | backtest-only pieces: `SimQueue`, `MarketExecutor`, `MarketStopLimitExecutor` |
| `telemetry` | `SimClock`, which stamps log lines with simulated time, and `init`/`init_json` to install a logger with it |
| `utils` | helpers for strategies, such as `dt_trigger::DateTimeTrigger` |

## The idea

Everything that happens is an `Event`: market data, an ack, a fill, a reject.
An `EventSource` hands them out in time order and, as a `RequestSink`, accepts
`Request`s (send an order, cancel one). The caller reacts to each event and submits requests;
it never knows whether a simulator or a venue is on the other side.

In a backtest that source is a `SimQueue`. It merges a market-data stream
with what a simulated executor schedules: a scheduled event wins a tie with
market data, and equal-time scheduled events go out in the order they were
scheduled. The executor sees every event before the caller does, so it can
fill against each bar.

## Examples

Each example is a folder under [`examples/`](./examples) with its own README:

| Example | What it shows |
|---|---|
| [`market_order`](./examples/market_order) | the smallest complete backtest: a market order acked, then filled at the next bar's open |

```bash
cargo run -p engine --example market_order
```

Each example asserts its own output and is run by `cargo test`, so a behaviour
change breaks the build. The output shown in an example's README is not checked
automatically: keep it in sync with the `expected` list in its `main.rs`.
