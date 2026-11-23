# fin-workspace

Rust crates for writing and backtesting trading strategies: trading primitives, instrument
identity, futures chains, market data, an order management system and an event-driven engine.
Backtests and replays only for now; live trading isn't there yet.

## Start here

```bash
cargo test --workspace                        # every crate except lab's Kafka bins
cargo run -p engine --example market_order    # the whole pipeline in one file
cargo run -p engine --example simulated_stop  # a stop the strategy manages itself
```

Read [`engine/examples/market_order`](./engine/examples/market_order) first. To write a
strategy, implement `engine::strategy::Traded` and pass it to `engine::event_loop::run` with a
queue (`engine::sim::SimQueue` for a backtest), an `oms::manager::Oms`, an
`oms::portfolio::Portfolio` and an `oms::rms::Rms`.

## How it works

Two worlds. **External**: the market-data feed and the executor (a simulator or a venue).
**Internal**: the strategy, the OMS and the portfolio. They meet at one pipe, the
`EventSource`: everything external comes in through it as events, in time order (market data,
acks, fills, rejects), and the internal world talks back only with requests into it (send an
order, cancel one).

A strategy never sends orders. It only states its desired state (`oms::desired::Desired`): the
position it wants per instrument. The OMS is what sends orders, by one formula per instrument:

```text
order = desired position − (position + market orders in flight)
```

The RMS can clamp the desired position or block an order. For each event, `event_loop::run`
hands an executor's event to the OMS (fills update the portfolio), shows the event to the
strategy, then lets the OMS reconcile.

## Crates

| Crate | What's in it |
|---|---|
| [`tradeprim`](./tradeprim) | `Price`, `Quantity`, `Position`, `Side`, `Currency` (ISO 4217), `Volume`, notionals; fixed-point decimals |
| [`instrid`](./instrid) | instrument identity: `Asset`, `Mic`, `Tenor`, `Instrument` (`Stock`, `FuturesContract`, `OptionContract`), and `Specification` (tick size, point value, quantity limits); features `mic-full`, `serde` |
| [`futchain`](./futchain) | `FutChain` walks a contract through its listed months; `EndOfTrading` rules give the last trading date |
| [`mdata`](./mdata) | market-data record traits (`HasTimestamp`, `Candle`, …), `MarketData`, `Ohlcv`, `Tagged`; `aggregation`; `formats` (FRD; the chain reader is behind `frd-chain`) |
| [`oms`](./oms) | orders and fills, the executor protocol (`Request`, `ExecEvent`), `Oms`, `Portfolio`, `Rms`, `Desired` |
| [`engine`](./engine) | events and `EventSource`, `event_loop::run`, the `Traded` trait, `SimQueue` and simulated executors, `telemetry` (execution and diagnostics logs) |
| [`indicators`](./indicators) | streaming SMA, EWMA, RSI, TR, ATR that match pandas |
| [`lab`](./lab) | experiments, not held to the same bar: `strat_1`, bins, Kafka formats |

## Working in the workspace

```bash
cargo test --workspace --exclude lab --all-features   # what CI runs, README doctests included
cargo test -p futchain                                # one crate
cargo run -p futchain --example find_active_contract
cargo run -p futchain --example historical_roll_schedule
cargo run -p instrid --example typed_groupby
```

Only a Rust toolchain is needed, except for lab's `kafka` feature: `rdkafka` builds librdkafka
from C source, so it also needs `cmake` and a C toolchain.

Each crate's README is its crate-level docs, and its examples run as doctests.

## Design principles

- **Easy to grasp.** Each crate is small and owns one concept.
- **Strongly-typed inputs over stringly-typed ones.** `Tenor::March`, not `3` or `"H"`;
  `Mic::xnas()`, not `"XNAS"`.
- **Invalid states rejected at construction.** Validating constructors return `Result`;
  `*_unchecked` variants exist where the caller can prove the invariant.
- **Performance over generality where it's safe.** Some types assume invariants about the data
  to stay fast.

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
