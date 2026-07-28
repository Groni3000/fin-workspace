# instrid

Strongly-typed financial-instrument identification for Rust.

## What it solves

Every trading system has to answer "what are we trading?" before it can price,
route, risk-check, report, or backtest anything. The answer comes at two
granularities, and most type systems blur them into one:

- **Entity-level identity** — "this is AAPL, an equity". Useful for grouping
  exposure across venues, computing P&L by ticker, or building reference data
  keyed by issuer.
- **Venue-level identity** — "this is AAPL on NASDAQ Global Select (`XNGS`)".
  Required for execution, market-data subscriptions, regulatory reporting,
  and disambiguating dual-listed names.

`instrid` keeps both visible in the type system:

- [`Asset`] - represents the entity: (`name + AssetClass`)
- [`TradedInstrument`] - represents what we buy/sell (`base: Asset`), what is used to
  quote base (`price_quotation: Asset`), where it is traded (`mic: Mic`) and what it
  settles in (`settlement_currency: Currency`).
- [`Stock`, `FuturesContract`, `OptionContract`] - concrete implementations of each trading instrument type.
- [`Instrument`] - enum of concrete implementations
  (useful for gathering all instrument types together).

Each element is kind of... Fat. `Stock`, the smallest, is 216 bytes.
`OptionContract`, the largest is 232 bytes. Add 8 bytes for tag in `Instrument`
and you'll get 240 bytes size. The main villain is MIC code - it holds all ISO information.

Despite that, this library has exactly one heap allocation
at the first call to the MIC registry. Every value
in this library lives on the stack and is `Copy`.

That's the core product. No live prices, no orders, no connection state — just
identity, with enough structure to compose into bigger things.

The one layer built on top is the optional [`spec`](#specifications-from-quote-to-money)
module: it attaches per-instrument trading arithmetic (tick sizes → point value →
currency notional) so a raw quote can be turned into settlement-currency money.

## Quick start

```rust
use instrid::prelude::*;
use std::str::FromStr;
use tradeprim::currency::Currency;
use tradeprim::prelude::Price;

// `Asset::new` returns a `Result` (the name length is validated);
// unwrapped here for brevity.
let spy = Stock::new(
    Asset::new("SPY", AssetClass::Equity).unwrap(),
    Asset::new("USD", AssetClass::Currency).unwrap(),
    Mic::arcx(),                   // NYSE Arca — where SPY actually lists
    Currency::usd(),               // settlement currency
);

let cl_dec25 = FuturesContract::new(
    Asset::new("CL", AssetClass::Commodity).unwrap(),
    Asset::new("USD", AssetClass::Currency).unwrap(),
    Mic::xnym(),                   // NYMEX
    Currency::usd(),
    2025,
    Tenor::December,
    None,                          // unknown/unspecified day-of-month
).unwrap();

let aapl_call = OptionContract::new(
    Asset::new("AAPL", AssetClass::Equity).unwrap(),
    Asset::new("USD", AssetClass::Currency).unwrap(),
    Mic::xnas(),
    Currency::usd(),
    2025, Tenor::December, 19,     // exact expiry (required for options)
    OptionKind::Call,
    ExerciseStyle::American,
    Price::from_str("200.00").unwrap(),
).unwrap();

// A little bit verbose, but it's not like we print instruments all the time
// and it holds all essential information. `Stock` and `FuturesContract` append
// the settlement currency as `(USD)`; `OptionContract` does not.
println!("{spy}");                 // Stock:Equity|SPY/Currency|USD@ARCX(USD)
println!("{cl_dec25}");            // Futures:Commodity|CL/Currency|USD@XNYM(USD) 2025-12
println!("{aapl_call}");           // Option:Equity|AAPL/Currency|USD@XNAS 2025-12-19 American::Call#200
```

## Specifications: from quote to money

Identity tells you _what_ you traded; a `Specification` (in the [`spec`] module) tells you what a price
_means in money_.

The pipeline is two multiplications:

```text
Quantity   ×  Price           ->  QuoteNotional     (quote space, may not be money)
PointValue ×  QuoteNotional   ->  CurrencyNotional  (settlement money, currency-tagged)
```

`QuoteNotional` is a value that represents price quotation, it is _not_ always money:
a T-bond quote is in points, a grain quote is in cents.
`PointValue` it into currency, and `CurrencyNotional` is the only currency-tagged money type.

A `Specification` carries three things and derives the third from the first two:

```ignore
pub struct Specification {
    tick_size_price: Price,                 // smallest price increment, in quote units
    tick_size_currency: (Price, Currency),  // money that one price-tick is worth, in currency major units
    point_value: PointValue,                // derived: tick_size_currency / tick_size_price
}
```

The `Spec` trait exposes them plus `currency_notional(QuoteNotional) -> CurrencyNotional`:

```rust
use instrid::spec::{PointValue, Spec, Specification};
use tradeprim::currency::Currency;
use tradeprim::price::Price;
use tradeprim::quote_notional::QuoteNotional;

// ZB T-bond: quoted in points, tick = 1/32 = 0.03125, and one tick is worth $31.25.
let zb = Specification::new(
    Price::from_str_unchecked("0.03125"),
    (Price::from_str_unchecked("31.25"), Currency::usd()),
).unwrap();

// point_value = 31.25 / 0.03125 = 1000
assert_eq!(zb.point_value().value(), 1000 * PointValue::SCALE);

// 552.8125 points of quote notional -> $552,812.5 of settlement money.
let money = zb.currency_notional(QuoteNotional::from_str_unchecked("552.8125"));
println!("{money}"); // 552_812.5 (USD)
```

`Specification::new` returns `None` if `tick_size_price` is outside `(0, Price::ONE]`
or the derived point value is out of range. The `Default` spec is a plain US share:
`0.01` tick, `0.01` per tick, point value `1`.

### The units trap

`point_value` is derived by dividing two numbers, and **the division can't check
your units** — that's on you. The classic mistake is copy-pasting an exchange's
listed tick straight into `tick_size_price`:

- CME lists **ZW** (wheat) with a tick of `0.0025`. But ZW is _quoted in cents_, and
  `0.0025` is the _dollar_ (major-form) value of that tick. In quote (cent) units the
  tick is `0.25` — a quarter of a cent. Use `0.25`, not `0.0025`.
- With `(0.25, (12.5, USD))` you get `point_value = 12.5 / 0.25 = 50`. With the
  copy-pasted `0.0025` you'd get `5000`.

For example, here are some specs I used for testing:

| Instrument            | `tick_size_price` | `tick_size_currency` | `point_value` |
| --------------------- | ----------------- | -------------------- | ------------- |
| US share (`Default`)  | `0.01`            | `(0.01, USD)`        | `1`           |
| ZW wheat (5k bu)      | `0.25`            | `(12.5, USD)`        | `50`          |
| RB gasoline (42k gal) | `0.0001`          | `(4.2, USD)`         | `42_000`      |
| ZB T-bond             | `0.03125`         | `(31.25, USD)`       | `1_000`       |
| 6J JPY future         | `0.0000005`       | `(6.25, USD)`        | `12_500_000`  |

The rule: **fill a spec once, verify by hand, and reuse it.** Don't derive tick sizes
at runtime or, at least, make sure it is correct.

## Dependencies

This library is built on top of `tradeprim`, the primitives crate.

We use:

- default
  - `tradeprim` for the `Currency` settlement tag and the fixed-point `Price`
    type (option strikes, spec tick sizes).
- features
  - `serde`:
    - `serde`
    - `tradeprim/serde`

## MICs

This is a very interesting topic.

MIC - Market Identifier Code. It uniquely identifies a venue - a place where trading occurs.
It has a special standardized registry: ISO 10383. You can check it out in the assets folder.

This registry has ~3_000 entries.

Due to the library intent: every value on the stack, `Copy`, - I tried to use code generation
using `build.rs`. I generated a giant match expression.

But there was a problem with rust-analyzer. Every time I tried to implement trait for `Mic`,
my rust-analyzer hung up for a minute or more. That's not acceptable.

I tried `phf` - perfect hash map. The lag was shorter, but still long enough to make me mad.

So, instead of having this whole registry at compile time with all types, it was embedded
as pure static bytes. The registry is constructed once (that exact one heap allocation)
during first MIC lookup. All subsequent lookups are pure hashmap lookups.

But that's not all. It would be nice to have some LSP support for the most common MICs.
So, unconditionally, we codegen some of them as associated const constructors.
The docstring for each construction will tell you MIC's name and whether it's
an operating or segment MIC.
If a segment, it also shows the operating parent.

```rust
# use instrid::prelude::Mic;
// What comments says
let nasdaq: Mic  = Mic::xnas();   // NASDAQ - ALL MARKETS (XNAS, operating).
let bats:   Mic  = Mic::bats();   // CBOE BZX U.S. EQUITIES EXCHANGE (BATS, segment of XCBO).
```

Usage of MIC the whole registry is performed via enabling the `mic-full` feature
and using `mic_by_code` function:

```rust
use instrid::mic::mic_by_code;

assert!(mic_by_code("XNAS").is_some());
assert!(mic_by_code("ZZZZ").is_none());      // unknown
assert!(mic_by_code("XNA").is_none());       // wrong length
```

## Serialization

Enable the `serde` feature for `Serialize` / `Deserialize` on every public
identity type:

```toml
[dependencies]
instrid = { version = "*", features = ["serde"] }
```

Wire formats are chosen for human-readability and exact roundtripping:

- `Mic` → 4-letter code string (`"XNAS"`), deserialized via the registry.
- `Tenor` → `u8` (1–12), via `From<Tenor> for u8` + `TryFrom<u8> for Tenor`.
- `Price` strikes → string (`"200"`), via `tradeprim`'s fixed-point formatting.
- `OptionKind`, `ExerciseStyle`, `AssetClass` → variant name strings.
- `Instrument` → internally tagged: `{"type": "Stock", "base": ..., ...}`.

Every type that implements `Deserialize` is `DeserializeOwned` — no borrowed
fields, the bytes can come from a `Vec<u8>` and be dropped immediately.

```rust
# use instrid::prelude::*;
# use tradeprim::prelude::{Currency, Price};
let opt = OptionContract::new(
    Asset::new("AAPL", AssetClass::Equity).unwrap(),
    Asset::new("USD", AssetClass::Currency).unwrap(),
    Mic::xnas(),
    Currency::usd(),
    2025,
    Tenor::December,
    19,
    OptionKind::Call,
    ExerciseStyle::American,
    Price::from_str_unchecked("200"),
).unwrap();

let json = serde_json::to_string(&opt).unwrap();
let back: OptionContract = serde_json::from_str(&json).unwrap();
assert_eq!(opt, back);
```

Every type has a (little bit bloated) `Display` impl.

## Use cases

**Base crate** - it is essential crate and probably every crate will be built
on top of this crate. I have a strong opinion: "You can't trade if you can't
uniquely identify a trading instrument". For example, there is already implemented
crate `futchain` - a crate that allows to comfortably work with futures contracts:
move forward (advance) or backward (retreat) in the futures contracts chain.

**Grouping operations.** You can check implementation of grouping operations in
examples using naive (yet not that bad) `Fill` struct.
You can groupby by base asset or quote asset or by venue.
Such a simple library gives you granular control over
identification and thus different flavors of grouping by.

The `examples/typed_groupby.rs` example goes further after I "finished" developing primitives.
`Instrument` is `Hash`, it keys a `HashMap<Instrument, Specification>` registry, converts each
fill through `currency_notional` (remember `Spec` trait?), and groups signed cashflow — and realized PnL
for flat positions — by settlement currency, base asset, and asset class. See
`examples/typed_groupby_output.md` for sample output.

**Composing FIX / venue-specific symbols in a downstream crate.**
Each venue has its own quirks for the `Symbol(55)` tag. Unity uses
`EQ.SPY.ARCX` — Asset class + ticker + MIC, which is exactly the data
`instrid` already encodes. A small adapter crate translates:

```ignore
// pseudocode, in a separate `instrid-adapters` crate
fn unity_symbol(s: &Stock) -> String {
    format!("{}.{}.{}",
        asset_class_prefix(s.base().class()),    // "EQ"
        s.base().name(),                         // "SPY"
        s.mic())                                 // "ARCX"
}
```

Other venues need different shapes; each adapter is a thin function over the
same `instrid` types.

**Backtests.** You have 3 options to use:

- `Instrument` - enum. Match expressions everywhere. Useful when your strategy
  trades several types of instruments.
- Direct types - usually if your strategy trade one particular instrument.
- Anything that implements `TradedInstrument` trait.

Maybe it's gonna be useful to make some trait that exposes `Instrument`.
So, if we build adapters crate that uses composition - we can leverage that
in our trading algorithms... But I'm not sure yet how adapters should look like.

## Limitation: you bring the data

`instrid` has the _types_ but no reference-data catalogue. To call
`Stock::new(Asset::new("SPY", AssetClass::Equity), ..., Mic::arcx())`, you
have to _know_ that SPY is an equity and lists on NYSE Arca. There is no
`Stock::from_ticker("SPY")` and there won't be — that's a reference-data
problem, solved by Bloomberg/Refinitiv/OpenFIGI feeds or by your own internal
DB, neither of which belongs in a types crate.

The practical pattern: bootstrap an internal DB the first time you encounter
each instrument, persisted somehow (sqlite, CSV, whatever fits). With the
`serde` feature, every identity type roundtrips through JSON (or any other
serde format) out of the box — see [Serialization](#serialization). `Display`
is still the human-readable form; serde is the machine-readable one.

## License

Licensed under either of MIT ([LICENSE-MIT](../LICENSE-MIT)) or Apache-2.0
([LICENSE-APACHE](../LICENSE-APACHE)) at your option.
