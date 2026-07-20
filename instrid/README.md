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

Each element is kind of... Fat. `Stock`, the smallest, is 192 bytes. 
`OptionContract`, the largest is 216 bytes. Add 8 bytes for tag in `Instrument`
and you'll get 224 bytes size. The main villain is MIC code - it holds all ISO information.

Despite that, this library has exactly one heap allocation
at the first call to the MIC registry. Every value 
in this library lives on the stack and is `Copy`.

That's the whole product. No prices, no orders, no connection state. Just
identity, with enough structure to compose into bigger things.

## Quick start

```rust
use instrid::prelude::*;

let spy = Stock::new(
    Asset::new("SPY", AssetClass::Equity),
    Asset::new("USD", AssetClass::Currency),
    Mic::arcx(),                   // NYSE Arca — where SPY actually lists
);

let cl_dec25 = FuturesContract::new(
    Asset::new("CL", AssetClass::Commodity),
    Asset::new("USD", AssetClass::Currency),
    Mic::xnym(),                   // NYMEX
    2025,
    Tenor::December,
    None,                          // unknown/unspecified day-of-month
);

let aapl_call = OptionContract::new(
    Asset::new("AAPL", AssetClass::Equity),
    Asset::new("USD", AssetClass::Currency),
    Mic::xnas(),
    2025, Tenor::December, 19,     // exact expiry (required for options)
    OptionKind::Call,
    ExerciseStyle::American,
    dec!(200.00),
);

// A little bit verbose, but it's not like we print instruments all the time
// and it holds all essential information.
println!("{spy}");                 // Stock:(Equity)SPY/(Currency)USD@ARCX
println!("{cl_dec25}");            // Futures:(Commodity)CL/(Currency)USD@XNYM 2025-12
println!("{aapl_call}");           // Option:(Equity)AAPL/(Currency)USD@XNAS 2025-12-19 American::Call#200
```

## Dependencies
This library is trying to be dependency-free by default, but...

We use:
- default
  - `rust_decimal` for options strike price.
- features
  - `serde`:
    - `serde`
    - `rust_decimal/serde`
    
Unfortunately, if not strike price, this library would be dependency-free by default.

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
- `Decimal` strikes → string (`"200.00"`), preserving scale.
- `OptionKind`, `ExerciseStyle`, `AssetClass` → variant name strings.
- `Instrument` → internally tagged: `{"type": "Stock", "base": ..., ...}`.

Every type that implements `Deserialize` is `DeserializeOwned` — no borrowed
fields, the bytes can come from a `Vec<u8>` and be dropped immediately.

```rust
let opt = OptionContract::new(/* ... */);
let json = serde_json::to_string(&opt)?;
let back: OptionContract = serde_json::from_str(&json)?;
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
examples using naive `Fill` struct. 
You can groupby by base asset or quote asset or by venue. 
Such a simple library gives you granular control over 
identification and thus different flavors of grouping by.

**Composing FIX / venue-specific symbols in a downstream crate.**
Each venue has its own quirks for the `Symbol(55)` tag. Unity uses
`EQ.SPY.ARCX` — Asset class + ticker + MIC, which is exactly the data
`instrid` already encodes. A small adapter crate translates:

```rust
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

`instrid` has the *types* but no reference-data catalogue. To call
`Stock::new(Asset::new("SPY", AssetClass::Equity), ..., Mic::arcx())`, you
have to *know* that SPY is an equity and lists on NYSE Arca. There is no
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
