use std::fmt;

use super::{Event, Kind};

/// A record that can't be cloned, so the only way to get it back is to move it out.
#[derive(Debug, PartialEq)]
struct Record(String);

/// A feed error with its own type, so the test can tell it from a rebuilt copy.
#[derive(Debug)]
struct FeedFailure(&'static str);

impl fmt::Display for FeedFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "feed failure: {}", self.0)
    }
}

impl std::error::Error for FeedFailure {}

#[test]
fn market_data_moves_out_without_a_clone() {
    let event = Event::new(5, Kind::MarketData(Record("spy bar".to_string())));

    let kind = event.into_kind();

    let Kind::MarketData(record) = kind else {
        panic!("expected market data, got {kind:?}");
    };
    assert_eq!(record, Record("spy bar".to_string()));
}

/// A boxed error can't be copied, so moving out error helps to not rebuild it.
#[test]
fn a_feed_error_moves_out_as_the_same_error() {
    let event = Event::<Record>::new(5, Kind::FeedError(Box::new(FeedFailure("socket closed"))));

    let kind = event.into_kind();

    let Kind::FeedError(err) = kind else {
        panic!("expected a feed error, got {kind:?}");
    };
    let original = err
        .downcast_ref::<FeedFailure>()
        .expect("the original error type, not a copy");
    assert_eq!(original.0, "socket closed");
}
