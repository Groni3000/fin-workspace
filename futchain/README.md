# futchain

Futures contract chain navigation and end-of-trading date calculation, on top
of [`instrid`](../instrid).

## What it solves

A futures product (ES, GC, CL, NG, …) is not one instrument — it's a *chain*
of contracts, each listed against a tenor in a fixed cycle (quarterly for ES,
monthly for CL, etc.). Two pieces of logic show up in every backtest, every
roll engine, every "what's the front month today?" query:

1. **Chain navigation** — given a contract, what's the next one? The previous?
   Five contracts forward? The cycle wraps the year boundary, and the year
   itself can over/underflow if you walk far enough.
2. **End-of-trading date** — when does a given contract stop being the right
   thing to hold? Each product has its own rule, written against the
   contract-month calendar (e.g. *third Friday*, *last business day of the
   prior month minus 3*).

`futchain` keeps those two concerns separate and composable. The chain knows
*nothing* about dates; the rule knows *nothing* about the cycle. You glue
them together in a `while` loop.

## Quick start

```rust
use chrono::{NaiveDate, Weekday};
use futchain::{
    EndOfTrading, FutChain, ListedTenors,
    eot::{DateOffset, NthInMonth, NthWeekdayOfCurrentMonth},
};
use instrid::prelude::{Asset, AssetClass, FuturesContract, Mic, Tenor};

// ES: quarterly cycle, terminates 3rd Friday of contract month, -1 BDay defensive.
let listing = ListedTenors::quarterly();
let rule = NthWeekdayOfCurrentMonth {
    n: NthInMonth::Third,
    weekday: Weekday::Fri,
    offset: DateOffset::BusinessDays(-1),
};

let start = FuturesContract::new(
    Asset::new("ES", AssetClass::Index),
    Asset::new("USD", AssetClass::Currency),
    Mic::xcme(),
    2024, Tenor::December, None,
);

let today = NaiveDate::from_ymd_opt(2026, 5, 13).unwrap();
let mut chain = FutChain::new(start, &listing).unwrap();

while rule.calculate(chain.contract()) < today {
    chain.advance();
}
// chain.contract() is now today's active ES contract.
```

See `examples/find_active_contract.rs` and `examples/historical_roll_schedule.rs`
for full runnable demos.

## Concepts

### `ListedTenors`

A non-empty, duplicate-free, chronologically-sorted set of `Tenor`s — the
cycle the product is listed against. Constructors:

- `ListedTenors::new(Vec<Tenor>)` — arbitrary cycle, validated.
- `ListedTenors::quarterly()` — Mar, Jun, Sep, Dec.
- `ListedTenors::monthly()` — all twelve months.

### `FutChain<'a>`

A cursor over a contract, parameterised by a borrowed `&'a ListedTenors`. The
cursor is a `FuturesContract`; navigation moves it through the cycle.

- `advance` / `retreat` — single step. Wraps the year automatically.
- `advance_by(n)` / `retreat_by(n)` — `n` steps. Simple loop today; the API
  permits a one-shot modular replacement if profiling ever asks for it.
- Year arithmetic is checked: `u16` over/underflow at the chain ends panics
  with a clear message instead of silently wrapping.
- Navigation clears `day`, since the day-of-month of one contract carries no
  information about the next.

### `EndOfTrading`

A trait with a single method:

```rust
fn calculate(&self, contract: &FuturesContract) -> NaiveDate;
```

Implementors hold the *rule parameters* (e.g. "third Friday, offset −1 BDay");
the contract supplies `(year, tenor)`. One rule instance applies to every
contract in a chain, so reuse is free.

### `DateOffset`

```rust
pub enum DateOffset {
    Days(i32),
    BusinessDays(i32),
}
```

Applied after the rule's primary date. Most venue rules want a small defensive
shift — `BusinessDays(-1)` is the common choice to avoid the actual
termination day, where regular trading hours may not apply. Bake spec-defined
offsets in too: 6E's "2 BDay prior to the 3rd Wednesday" with the defensive
shift becomes `BusinessDays(-3)`.

Business-day arithmetic skips weekends only. There is no holiday calendar;
the defensive offset typically absorbs holiday edge cases for rolling
purposes, but this is a deliberate scope limit, not an oversight.

### `NthInMonth`

```rust
pub enum NthInMonth { First, Second, Third, Fourth, Last }
```

`Last` is distinct from `Fourth` — some months contain five of a given
weekday.

## Available rules

| Rule | Used by (examples) |
|---|---|
| `NthWeekdayOfCurrentMonth { n, weekday, offset }` | ES, NQ, FDAX, NKD (3rd Fri); BTC, ETH, MET (last Fri); 6E, 6B, 6A, 6C (3rd Wed −2 BDay) |
| `LastNthBDayOfPrevMonth { n, offset }` | GC, HG, ZS, RB, HO, SI, SB, ZW (`n = 1`); NG (`n = 3`) |

Both rules are `#[derive(Debug, Clone, Copy)]`. More rules are planned for
the products whose specs the current two don't cover (`LastNthBDayOfMonth`
for ZB, calendar-day rules for VX, etc.).

`LastNthBDayOfPrevMonth.n` is a `NonZeroU8` — `n = 0` would silently mean
"first day of the contract month" and produce nonsense. For literal values:

```rust
LastNthBDayOfPrevMonth::from_u8(3, DateOffset::BusinessDays(-1))
```

`from_u8` panics on `0` at runtime, or fails at compile time in a `const`
context. For runtime input, build a `NonZeroU8` upstream and call `new`.

## Scope

In scope:

- Chain navigation under a fixed listing cycle.
- Stateless EOT rules that take a `FuturesContract` and return a `NaiveDate`.
- Weekends-only business-day arithmetic.

Out of scope (intentionally):

- Holiday calendars. Defensive offsets handle most cases; full calendars are
  a separate problem.
- Listing schedule changes mid-history. `ListedTenors` is one fixed cycle.
- Prices, market data, orders.
- Specs for every product on every venue. The crate gives you the *rules*;
  catalogues belong in a downstream layer.

## License

Licensed under either of MIT ([LICENSE-MIT](../LICENSE-MIT)) or Apache-2.0
([LICENSE-APACHE](../LICENSE-APACHE)) at your option.
