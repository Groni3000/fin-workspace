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

- [`Asset`] carries the entity (`name + AssetClass`).
- [`TradedInstrument`] carries the venue-level identity: `(base: Asset, quote:
  Asset, mic: Mic)` plus the contract kind (stock, futures, …). Two trades on
  the same `TradedInstrument` are arbitrage-free against each other; two trades
  sharing only an `Asset` may not be.

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

println!("{spy}");                 // Stock:(Equity)SPY/(Currency)USD@ARCX
println!("{cl_dec25}");            // Futures:(Commodity)CL/(Currency)USD@XNYM 2025-12
println!("{aapl_call}");           // Option:(Equity)AAPL/(Currency)USD@XNAS 2025-12-19 American::Call#200
```

`OptionContract` uses [`rust_decimal::Decimal`] for the strike to avoid
floating-point precision issues. Unlike `FuturesContract`, the expiry day is
**required**: weeklies, EOM, and 0DTE options can share a `(year, month)`
with different strikes/kinds at different dates, so the day is part of identity.

## MICs

The ISO 10383 Market Identifier Code registry (~2800 venues) is parsed at
build time via `build.rs`. Two access patterns are exposed:

**Common MICs as named constructors** — always compiled in (~30 entries),
discoverable via LSP autocomplete, doc-strings include the venue's full name
and whether it's an operating or segment MIC:

```rust
let nasdaq: Mic  = Mic::xnas();   // operating MIC
let bats:   Mic  = Mic::bats();   // segment of XCBO
```

**Lookup by string** — for codes you only have at runtime (parsing a trade feed,
a config file, a FIX message):

```rust
use instrid::mic::mic_by_code;

assert!(mic_by_code("XNAS").is_some());
assert!(mic_by_code("ZZZZ").is_none());      // unknown
assert!(mic_by_code("XNA").is_none());       // wrong length
```

By default `mic_by_code` covers only the curated ~30. Enable the `mic-full`
feature to include the full registry:

```toml
[dependencies]
instrid = { version = "*", features = ["mic-full"] }
```

This trades ~2s of compile time for venue coverage you can't get otherwise.

## Types

| Type | What it represents |
|---|---|
| `Asset` | Tradable or settle-able entity: `(name, AssetClass)` |
| `AssetClass` | Equity, Commodity, Currency, FixedIncome, RealEstate, Index |
| `Mic` | ISO 10383 venue identifier + registry metadata |
| `Tenor` | Calendar month (Jan–Dec) for contract expiries |
| `Stock`, `FuturesContract`, `OptionContract` | Concrete `TradedInstrument` implementors |
| `OptionKind` | `Call` / `Put` |
| `ExerciseStyle` | `European` / `American` / `Bermudan` |
| `Instrument` | Enum over the concrete kinds, also implements `TradedInstrument` |
| `TradedInstrument` | Trait: `base() -> &Asset`, `quote() -> &Asset`, `mic() -> &Mic` |

Every type has a `Display` impl. `Mic`, `MicType`, `MicStatus`,
`MarketCategoryCode`, `Date`, and `Tenor` also implement `FromStr` so registry
data round-trips through strings.

## Use cases

**Grouping fills.** `HashMap<Asset, Position>` aggregates exposure across
venues; `HashMap<Mic, ...>` slices by venue; `HashMap<Instrument, ...>` keeps
both. Pick the granularity the question demands.

**Composing FIX / venue-specific symbols in a downstream crate.** Each venue
has its own quirks for the `Symbol(55)` tag. Exante uses
`EQ.SPY.ARCX` — Asset class + ticker + MIC, which is exactly the data
`instrid` already encodes. A small adapter crate translates:

```rust
// pseudocode, in a separate `instrid-adapters` crate
fn exante_symbol(s: &Stock) -> String {
    format!("{}.{}.{}",
        asset_class_prefix(s.base().category()),   // "EQ"
        s.base().name(),                            // "SPY"
        s.mic())                                    // "ARCX"
}
```

Other venues need different shapes; each adapter is a thin function over the
same `instrid` types.

**Listed-tenor generators (future work in a separate crate).** Most venues
publish only a subset of calendar months for any given product (e.g. CL trades
all 12, ES trades the four quarterly cycle months plus serials). A separate
crate could carry a `ListedTenors` table per product and generate the next
`FuturesContract` from "current date" without `instrid` itself having to know
about it. `instrid` provides the building blocks; iteration logic lives where
the venue-specific data does.

**Backtests.** A backtester typically holds `Vec<(Timestamp, Instrument,
Side, Qty, Price)>`. `Instrument` here is the venue-precise identity; the
`Asset`-level group-by happens at the analysis layer. Because `instrid`'s
types are plain data (no allocations beyond the `Mic` metadata strings,
which are `&'static str`), millions of records fit cheaply.

## Limitation: you bring the data

`instrid` has the *types* but no reference-data catalogue. To call
`Stock::new(Asset::new("SPY", AssetClass::Equity), ..., Mic::arcx())`, you
have to *know* that SPY is an equity and lists on NYSE Arca. There is no
`Stock::from_ticker("SPY")` and there won't be — that's a reference-data
problem, solved by Bloomberg/Refinitiv/OpenFIGI feeds or by your own internal
DB, neither of which belongs in a types crate.

The practical pattern: bootstrap an internal DB the first time you encounter
each instrument, persisted somehow (sqlite, CSV, whatever fits). The
`Display` output is a reasonable serialization key — it's stable and unique
per `TradedInstrument` — but `instrid` doesn't yet provide `FromStr` for the
composite instrument types, so today you'd need to define your own
(de)serialization. That's likely to land as the project matures.

## Why not just use strings?

Because then every consumer reinvents parsing, every comparison is
string-equality with all the edge cases that implies, and every grouping
question (by ticker? by venue? by both?) requires regex. `instrid` makes
the layers structural so the type system enforces the distinction the
business actually cares about.
