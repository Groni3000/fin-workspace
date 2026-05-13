# fin-workspace

A small Rust workspace for the boring-but-load-bearing parts of building
trading systems: identifying instruments, and navigating the contracts
behind a futures product.

The crates are deliberately narrow. Each one owns one concept, exposes
strongly-typed primitives for it, and composes with the others without
forcing a particular framework on the caller.

## Crates

### [`instrid`](./instrid) — strongly-typed instrument identity

Distinguishes *entity-level* identity (`AAPL`, an equity) from *venue-level*
identity (`AAPL @ XNGS`). `Asset`, `Mic`, `TradedInstrument`, and concrete
kinds (`Stock`, `FuturesContract`, `OptionContract`). No prices, no orders —
just identity with enough structure to compose into bigger things.

### [`futchain`](./futchain) — futures chain navigation + end-of-trading rules

A `FutChain` cursor walks a `FuturesContract` through a `ListedTenors` cycle
(quarterly, monthly, or arbitrary). An `EndOfTrading` trait turns
`(year, tenor)` into a calendar `NaiveDate` via per-product rules
(*third Friday*, *last business day of prior month*, etc.). Chain and rule
are independent — glue them together with a `while` loop.

## Layout

```
fin-workspace/
├── Cargo.toml          # workspace root
├── instrid/            # instrument identity
└── futchain/           # chains + EOT rules
```

## Working in the workspace

```bash
cargo test                          # all crates
cargo test -p futchain              # one crate
cargo run -p futchain --example find_active_contract
cargo run -p futchain --example historical_roll_schedule
```

## Design principles

- **One concept per crate.** `instrid` is identity; `futchain` is the chain
  and its calendar rules. They depend in one direction.
- **Strongly-typed inputs over stringly-typed ones.** `Tenor::March`, not
  `"H"`. `NonZeroU8`, not `u8` with a runtime check buried somewhere.
- **Stateless rules.** An `EndOfTrading` impl holds parameters, not state.
  One instance applies to every contract in a chain.
- **Defensive arithmetic at the seams.** Year over/underflow on chain
  navigation panics with a clear message instead of silently wrapping `u16`.
- **Narrow scope, on purpose.** No holiday calendar in `futchain`. No order
  routing in `instrid`. These are downstream concerns; keeping them out
  keeps the primitives reusable.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](./LICENSE-APACHE) or
  <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](./LICENSE-MIT) or
  <https://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual-licensed as above, without any additional terms or
conditions.
