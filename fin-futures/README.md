# fin-futures

Futures contract rolling and offset arithmetic. Built on top of
[`instrid`](../instrid) identification types.

## Why

`instrid` answers "what is this contract?" — `fin-futures` answers "what
contract comes next?"

When you're backtesting a strategy on crude oil futures, you need to roll from
CL JUN 2025 to CL JUL 2025. When you're building a term structure, you need
the next 8 quarterly contracts from a starting point. These operations require
knowing which months a product actually lists — ES lists quarterly (Mar, Jun,
Sep, Dec), CL lists every month, ZS lists a custom set.

`fin-futures` provides two types to handle this:

- `ListingSchedule` — which months exist for a product
- `ContractOffset` — how far to jump, in years and/or listed tenors

## ListingSchedule

Defines which contract months are listed for a given product. Tenors are
always stored sorted and deduplicated.

```rust
use fin_futures::schedule::ListingSchedule;
use instrid::tenor::Tenor;

// Built-in presets
let quarterly = ListingSchedule::quarterly(); // Mar, Jun, Sep, Dec
let monthly = ListingSchedule::monthly();     // All 12 months

// Custom schedule (e.g., ZS soybeans: Jan, Mar, May, Jul, Aug, Sep, Nov)
let zs = ListingSchedule::new(&[
    Tenor::January, Tenor::March, Tenor::May, Tenor::July,
    Tenor::August, Tenor::September, Tenor::November,
]);

// Navigation
let (next, rolled) = quarterly.next_tenor(Tenor::December);
assert_eq!(next, Tenor::March);
assert!(rolled); // wrapped into the next year

let (prev, rolled) = quarterly.prev_tenor(Tenor::March);
assert_eq!(prev, Tenor::December);
assert!(rolled); // wrapped into the previous year
```

**What it models:** The set of tenor months a product uses — its annual
listing cycle. This is layer 1 of contract availability: *which months exist
at all*. It does not model layer 2 — *which specific contracts are tradeable
right now* — because that depends on the current date, exchange-specific listing
windows, and contract termination rules. Layer 1 is sufficient for rolling and
backtesting; layer 2 is a live trading concern.

## ContractOffset

An offset with two independent components: `years` and `listed_tenors`.
This separation makes common operations expressive:

```rust
use fin_futures::offset::ContractOffset;
use fin_futures::schedule::ListingSchedule;
use instrid::future::Future;
use instrid::tenor::Tenor;

let schedule = ListingSchedule::quarterly();
let es: Future = "ES/USD@CME#2025-JUN".parse().unwrap();

// Roll to the next quarterly contract
let next = ContractOffset::tenors(1).apply(&es, &schedule);
assert_eq!(next.month, Tenor::September);
assert_eq!(next.year, 2025);

// Jump to the same month next year
let next_year = ContractOffset::years(1).apply(&es, &schedule);
assert_eq!(next_year.month, Tenor::June);
assert_eq!(next_year.year, 2026);

// Combine: 1 year and 2 tenors forward
let combined = ContractOffset::new(1, 2).apply(&es, &schedule);
assert_eq!(combined.month, Tenor::December);
assert_eq!(combined.year, 2026);

// Roll backward
let prev = ContractOffset::tenors(-1).apply(&es, &schedule);
assert_eq!(prev.month, Tenor::March);
assert_eq!(prev.year, 2025);
```

### Offset arithmetic

Offsets support `Add`, `Sub`, and `Neg`, so you can compose them:

```rust
use fin_futures::offset::ContractOffset;

let a = ContractOffset::years(1);
let b = ContractOffset::tenors(2);
let combined = a + b; // { years: 1, listed_tenors: 2 }
let negated = -combined; // { years: -1, listed_tenors: -2 }
```

### Works with options too

`apply_option` does the same thing for `OptionContract`, preserving the
strike price and option type:

```rust
use fin_futures::offset::ContractOffset;
use fin_futures::schedule::ListingSchedule;
use instrid::option_contract::OptionContract;
use instrid::tenor::Tenor;

let schedule = ListingSchedule::quarterly();
let opt: OptionContract = "ES/USD@CME#2025-JUN:CALL$4500".parse().unwrap();

let next = ContractOffset::tenors(1).apply_option(&opt, &schedule);
assert_eq!(next.month, Tenor::September);
assert_eq!(next.strike, 4500.0);
```

## Why the schedule is external

You might wonder why `Future` doesn't store its schedule internally, which
would allow `future + offset` syntax. There are a few reasons:

1. **`instrid` is identification-only.** A `Future` identifies a contract. It
   shouldn't carry business context like which other months are listed — that's
   product-level data, not contract-level data.
2. **`Copy` semantics.** `Future` is `Copy` (27 bytes on the stack). Embedding
   a `Vec<Tenor>` or a schedule reference would break `Copy` and require
   lifetimes or `Arc`, adding complexity for marginal ergonomic gain.
3. **Explicitness.** `offset.apply(&future, &schedule)` makes the dependency
   on the schedule visible at every call site. No hidden state, no surprises
   about which schedule a future is using.
