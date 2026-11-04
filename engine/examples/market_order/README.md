# market_order

The smallest complete backtest: two one-minute bars, one market order. It does not include a full pipeline of a real backtest/live trading, so **do not** use this example as a bootstrap for your strategies!

```bash
cargo run -p engine --example market_order
```

## What it shows

- **A market-data stream is just an iterator.** `Vec<Result<Tagged<Bar>, io::Error>>`
  is enough. `Bar` implements only what the simulator needs (`Timestamped`,
  `RelevantPrice`, `Candle`), and `Tagged` attaches the instrument.
- **The loop.** `while let Some(event) = queue.next_event()` hands out every
  event in time order. The caller reacts and calls `queue.submit(...)`.
- **The simulated venue answers on its own schedule.** `MarketExecutor` acks
  after its ack latency, and fills at the *open* of the first bar after the
  order is working, plus its fill latency.

## Expected output

```text
1970-01-01 00:01:00 UTC  bar open=100 close=101
1970-01-01 00:01:00.001 UTC  ack (our order)
1970-01-01 00:02:00 UTC  bar open=102 close=103
1970-01-01 00:02:00.005 UTC  fill Buy 1 @ 102 (our order)
```

The order goes out on the first bar and is acked 1 ms later. It fills on the
second bar at that bar's open (102, not its close of 103), 5 ms after the bar.
