//! There are two different kinds of records: scheduled and not.
//!
//! Scheduled examples: backtest executor events (Ack, Fill, ...), timer expiration (not yet ready).
//!
//! Not scheduled examples: market data, real gateway executor events (Ack, Fill, ...).
//!
//! And we have one pipe - event queue. So we need to merge them somehow.
//! The obvious way - by timestamp. But what if they happened at the same time?
//!
//! We decided to emit scheduled first. Why?
//!
//! The reasoning is simple. Backtest is deterministic so every executor event is scheduled
//! and we want to react to executor events (Acks, Fills) as fast as possible.
//! And for live gateways the mere fact that we want to follow backtest as close as
//! possible forces us to use the same merging logic.

/// Describes the next record of a feed whose timestamps aren't known in advance.
/// The most obvious example - market data feed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NextRecord {
    /// Timestamp of the next record.
    At(i64),
    /// There may be one, but it has not been read yet.
    /// - The feed is still alive, yet no data arrived.
    /// - Nothing scheduled may go out because next record may have
    ///   timestamp < last known scheduled event timestamp and we will panic.
    Unknown,
    /// The feed has ended; whatever is scheduled is all that is left.
    End,
}

/// A tie goes to the scheduled event: an ack or fill reaches the strategy before the
/// record that comes at the same time.
pub fn scheduled_first(scheduled: Option<i64>, record: NextRecord) -> bool {
    match (scheduled, record) {
        (None, _) | (_, NextRecord::Unknown) => false,
        (Some(scheduled), NextRecord::At(record)) => scheduled <= record,
        (Some(_), NextRecord::End) => true,
    }
}

#[cfg(test)]
mod tests {
    use super::{NextRecord, scheduled_first};

    #[test]
    fn a_scheduled_event_goes_out_no_later_than_the_record_after_it() {
        assert!(scheduled_first(Some(5), NextRecord::At(6)));
        assert!(scheduled_first(Some(5), NextRecord::At(5)), "ties too");
        assert!(!scheduled_first(Some(5), NextRecord::At(4)));
    }

    /// The live-replay bug: an unread channel was taken for an empty one.
    #[test]
    fn nothing_scheduled_goes_out_while_the_next_record_is_unknown() {
        assert!(!scheduled_first(Some(5), NextRecord::Unknown));
    }

    #[test]
    fn the_end_of_the_feed_releases_what_is_left() {
        assert!(scheduled_first(Some(5), NextRecord::End));
        assert!(!scheduled_first(None, NextRecord::End));
        assert!(!scheduled_first(None, NextRecord::At(5)));
    }
}
