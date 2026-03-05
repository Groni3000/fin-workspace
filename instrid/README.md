# instrid

Financial instrument identification types for Rust.

## Why

Every trading system needs to answer a basic question: **what are we trading?**
Before you can price, route, or backtest anything, you need a way to name
instruments that is compact, unambiguous, and cheap to pass around.

`instrid` provides exactly that — small, stack-allocated value types that
identify financial instruments. No heap allocations, no runtime overhead,
no dependencies. Just plain data that tells you what something *is*, not
what to *do* with it.

## Design principles

**Identification, not behavior.** These types carry identity — base asset,
exchange, contract month — but no market data, no pricing logic, no connection
state. A `Future` knows it's `CL/USD@NYMEX#2025-JUN`, but it doesn't know the
current price or how to place an order. Business logic belongs in downstream
crates (like `fin-futures`).

**Value semantics everywhere.** All types are `Copy + Clone`. They live on the
stack, fit in registers, and can be passed by value without worrying about
ownership. An `Asset` is 9 bytes. An `Instrument` is 27 bytes. You can embed
them in structs, use them as map keys, or store millions of them in a `Vec`
without a single allocation per item.

**Parse what you display.** Every type round-trips through `Display` and
`FromStr`. If you can print it, you can parse it back. This makes logging,
serialization, and debugging straightforward — the string representation *is*
the canonical format.

## Types

### Primitives

`Asset` and `Exchange` store 1-8 uppercase ASCII characters in a fixed `[u8; 8]`
buffer. No heap `String`, no lifetimes.

```rust
use instrid::asset::Asset;
use instrid::exchange::Exchange;

// Compile-time constants
const BTC: Asset = Asset::BTC;
const CME: Exchange = Exchange::CME;

// Runtime parsing
let eth: Asset = "ETH".parse().unwrap();
```

Built-in constants: `Asset::{BTC, ETH, USD, EUR, GBP, JPY, USDT}`,
`Exchange::{CME, CBOT, NYMEX, NASDAQ, NYSE, BINANCE}`.

### Tenor

An enum representing contract months (January through December). Ordinal values
1-12, with `Ord` derived so months sort in calendar order.

```rust
use instrid::tenor::Tenor;

let month = Tenor::March;
assert_eq!(month.ordinal(), 3);
assert_eq!(month.max_days(), 31);
assert_eq!(format!("{month}"), "MAR");
```

### Instrument

The fundamental building block — a `(base, quote, exchange)` triple.
All composite types embed this.

```rust
use instrid::instrument::Instrument;

let inst: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
assert_eq!(format!("{inst}"), "BTC/USDT@BINANCE");
```

### Stock

A thin wrapper around `Instrument`. Exists so your type system distinguishes
a stock from a raw instrument when it matters.

### Future

An instrument with a contract date (year, month, optional day) and optional
multiplier:

```rust
use instrid::future::Future;

let cl: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
let es: Future = "ES/USD@CME#2025-SEP-15*50".parse().unwrap();

// Futures are ordered by expiration date
assert!(cl < es);
```

Format: `BASE/QUOTE@EXCHANGE#YYYY-MMM[-DD][*MULT]`

### OptionContract

A future extended with option type (call/put) and strike price:

```rust
use instrid::option_contract::OptionContract;

let opt: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
```

Format: `BASE/QUOTE@EXCHANGE#YYYY-MMM[-DD][*MULT]:CALL|PUT$STRIKE`

Named `OptionContract` (not `Option`) to avoid collision with `std::option::Option`.

### TradeInstrument trait

All instrument types implement `TradeInstrument`, providing uniform access
to `base()`, `quote()`, and `exchange()`. Use it when you need to write code
that works across instrument types.

## Eq, Hash, and Ord

| Type | `Eq + Hash` | `Ord` | Why |
|------|:-----------:|:-----:|-----|
| `Asset`, `Exchange`, `Tenor` | Yes | Yes | Pure integer/enum data |
| `Instrument`, `Stock` | Yes | - | Composed of `Eq` types |
| `Future`, `OptionContract` | No | No | Contain `f64` (multiplier, strike) |

`Future` and `OptionContract` implement `PartialEq` and `PartialOrd` (by
expiration date). They cannot implement `Eq`/`Hash` because `f64` does not.

## Validation

- **Multiplier** must be positive and finite
- **Strike** must be non-negative and finite
- **Day** is validated against the month (e.g., Feb maxes at 29, Apr at 30)
- **Asset/Exchange** codes must be 1-8 uppercase ASCII characters
