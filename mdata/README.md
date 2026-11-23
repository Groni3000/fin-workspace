# mdata

Market-data record traits, on top of [`instrid`](../instrid) and
[`tradeprim`](../tradeprim).

Every data source has its own record format: vendor CSV, a Kafka JSON topic,
an aggregated bar. Code that *consumes* market data (a strategy, a simulated
executor, an aggregator) shouldn't care which one. `mdata` splits a record
into small capability traits, and consumers ask only for the ones they need:

| Trait | What the record can tell you |
|---|---|
| `HasTimestamp` | when it happened in UTC |
| `HasLastPrice` | a single price (`HasTimestamp` + `last_price`) |
| `Candle` | open / high / low / close / volume (extends `HasLastPrice`) |
| `HasInstrument` | which `Instrument` it belongs to |
| `HasSymbol` | a raw venue/vendor symbol not yet resolved to an `Instrument` |

`MarketData` is a fallible stream of such records. It's blanket-implemented
for any `Iterator<Item = Result<R, E>>`, so a reader only has to be an
iterator.

`Ohlcv` is a plain candle implementing `HasTimestamp`, `HasLastPrice` (its close) and
`Candle`, for examples, tests and other hand-written data. It checks nothing (a `low` above
the `high` is stored as given). For a real data source, write your own record type and
implement the traits: what to check when a record is built is up to that type.

Most formats name the instrument once (in the file name or the topic), not on
every row. `Tagged<R>` pairs a record with its instrument, which makes it
`HasInstrument` while carrying over everything the inner record already has.

## Example

```rust
use chrono::{DateTime, Utc};
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use mdata::{HasInstrument, HasLastPrice, HasTimestamp, Tagged};
use tradeprim::{currency::Currency, price::Price};

/// A vendor format: knows its time and price, not its instrument.
#[derive(Debug)]
struct Trade {
    ts: DateTime<Utc>,
    px: Price,
}

impl HasTimestamp for Trade {
    fn timestamp(&self) -> DateTime<Utc> {
        self.ts
    }
}

impl HasLastPrice for Trade {
    fn last_price(&self) -> Price {
        self.px
    }
}

/// A consumer that works with any format providing these capabilities.
fn describe<R: HasLastPrice + HasInstrument>(r: &R) -> String {
    format!("{} @ {}", r.instrument(), r.last_price())
}

let spy = Instrument::Stock(Stock::new(
    Asset::new("SPY", AssetClass::Equity).unwrap(),
    Asset::new("USD", AssetClass::Currency).unwrap(),
    Mic::arcx(),
    Currency::usd(),
));
let trade = Trade {
    ts: DateTime::from_timestamp_nanos(0),
    px: Price::from_str_unchecked("512.25"),
};

let tagged = Tagged::new(spy, trade);
assert_eq!(tagged.instrument(), spy);
assert_eq!(tagged.last_price(), Price::from_str_unchecked("512.25"));
assert_eq!(describe(&tagged), "Stock:Equity|SPY/Currency|USD@ARCX(USD) @ 512.25");
```
