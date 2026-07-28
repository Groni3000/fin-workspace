# fin-workspace

A small Rust workspace for the boring-but-load-bearing parts of building
trading systems: identifying instruments, and navigating the contracts
behind a futures product.

The crates are deliberately narrow. Each one owns one concept, exposes
strongly-typed primitives for it, and composes with the others without
forcing a particular framework on the caller.

## Crates
### [`tradeprim`](./tradeprim) — primitive types for trading

Price, Quantity, Notional, ... - those basic types implemented here.
Currently work in progress.

### [`instrid`](./instrid) — strongly-typed instrument identity

Distinguishes *entity-level* identity (`AAPL`, an equity) from *venue-level*
identity (`AAPL @ XNGS`). `Asset`, `Mic`, `Tenor`, `TradedInstrument`, the
`Instrument` enum, and concrete kinds (`Stock`, `FuturesContract`,
`OptionContract`). No prices, no orders — just identity with enough structure
to compose into bigger things.

`Mic` is 4 bytes (just the code); the full ISO 10383 record lives in a separate
`MicIso`, looked up on demand. `Instrument` is 72 bytes and `Copy`.

Features:
- `mic-full` — embeds the full ISO 10383 MIC registry (~2840 entries) as a
  packed binary blob, lazily parsed into a lookup map on first `mic_by_code`
  call. Off by default; the 33 curated `Mic::xnas()`-style constants are
  always available, and lookup works either way — the feature only widens
  which codes are known.
- `serde` — `Serialize`/`Deserialize` for every public identity type, with
  compile-time `DeserializeOwned` checks (no borrowed fields). Contracts
  deserialize through their validating constructors, so an impossible date
  like `2025-02-31` is rejected rather than rebuilt field-by-field.

### [`futchain`](./futchain) — futures chain navigation + end-of-trading rules

A `FutChain` cursor walks a `FuturesContract` through a `ListedTenors` cycle
(quarterly, monthly, or arbitrary). An `EndOfTrading` trait turns
`(year, tenor)` into a calendar `NaiveDate` via per-product rules
(*third Friday*, *last business day of prior month*, etc.). Chain and rule
are independent — glue them together with a `while` loop.


### [`oms`](./oms) — order management system

This crate will be a thin communication-layer between Strategy and Executor.


## Working in the workspace

```bash
cargo test --workspace --all-features   # everything, including README doctests
cargo test -p futchain                  # one crate
cargo run -p futchain --example find_active_contract
cargo run -p futchain --example historical_roll_schedule
cargo run -p instrid --example typed_groupby
```

Only a Rust toolchain is required. The Kafka experiments in `lab` are behind
the `kafka` feature, since `rdkafka` builds librdkafka from C source and needs
`cmake` plus a C toolchain:

```bash
cargo run -p lab --features kafka --bin kafka_check
```

Each crate's README is included as its crate-level docs and its examples run as
doctests, so they cannot drift from the code without turning the build red.

## Design principles

- **Easy to grasp.** each crate is relatively small.
- **Strongly-typed inputs over stringly-typed ones.** `Tenor::March`, not
  `3` or `"H"`; `Mic::xnas()`, not `"XNAS"`.
- **Balance between performance and assumptions.** There may be
some assumptions about data (struct invariants) to make code more efficient.
- **Invalid states rejected at construction.** Validating constructors return
`Result`; `*_unchecked` variants exist where the caller can prove the invariant.

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
