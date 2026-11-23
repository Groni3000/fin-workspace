# market_order

A complete backtest on eleven one-minute candles: a strategy enters long, adds, exits, goes
short and exits again, all with market orders. It uses the same pipeline as a real strategy
(strategy, OMS, RMS, portfolio, `event_loop::run`), so it's a fair starting point for your
own.

**Backtests and replays only.** Live, the market-data feed is sometimes behind the market:
while it replays history at start, and whenever it falls behind later. Orders made then go to
a simulator, and when the feed catches up something has to decide what to do about the
positions the simulator opened, which the venue never saw. `event_loop::run` doesn't handle
that yet.

```bash
cargo run -p engine --example market_order
```

## What it shows

- **A market-data stream is just an iterator.** `Vec<Result<Tagged<Ohlcv>, io::Error>>`
  is enough. `Ohlcv` is `mdata`'s plain candle, and `Tagged` attaches the instrument.
- **A strategy says what it wants to hold; it doesn't send orders.** `Scripted` implements
  `Traded`: after each candle it sets its desired position from the script in `CANDLES`. The OMS
  sends a market order for the difference between that and what's held or already working.
- **No change, no order.** When the wanted position is the same as after the previous candle,
  the OMS sends nothing: the execution log has no `send` line after those candles. That holds
  while the order is still working (candle 2) and once it's filled (candle 3).
- **One loop drives everything.** `event_loop::run` hands each event to the OMS, then to
  the strategy, then lets the OMS reconcile. It returns the OMS and the portfolio at the
  end, so the final position comes from what was really filled.
- **The simulated venue answers on its own schedule.** `MarketExecutor` acks 200 ms after
  the order (about 50 ms to decide, about 150 ms of network round trip), and fills at the
  *open* of the next candle, 200 ms after that candle.
- **Logs.** `telemetry::init` writes the order lifecycle (send, ack, fill), as JSON, to
  `market_order.exec.<Sunday>.log`, and everything else to `market_order.diag.<Sunday>.log`,
  in `engine-example-market_order` under the system temp directory. Every line carries the
  simulated time, not the wall clock. After the run the example prints the execution log:
  the strategy only sees what comes back (acks, fills), while the log also has what the OMS
  sent.

  `<temp>` is the system temp folder: `/tmp` on Linux, `%TEMP%` on Windows (usually
  `C:\Users\<name>\AppData\Local\Temp`). Each run deletes the folder first, so it only ever
  holds the last run's logs, a couple of kilobytes. Delete it whenever you like.

## The cost of one-minute candles

The strategy decides on a candle's close, and the order is acked 200 ms later, but it fills
only at the next candle's open, a minute later. The simulator has no prices between candles,
so it can't fill any earlier.

The smaller the candles, the smaller that cost. With latencies like these, one-second candles
are a pretty good approximation for a semi-liquid or somewhat stale market: the next candle's
open is then only a second after the decision.

`MarketExecutor` also has no slippage: it fills exactly at the open. A more advanced executor
should model slippage that changes with the market rather than a fixed amount. That makes a
backtest more accurate, especially on one-second candles, where the fill price is otherwise
close to right already.

## Expected output

```text
logs in <temp>/engine-example-market_order
1970-01-01T00:01:00Z  candle open=100 close=101, want 1
1970-01-01T00:01:00.2Z  ack
1970-01-01T00:02:00Z  candle open=102 close=103, want 1
1970-01-01T00:02:00.2Z  fill Buy 1 @ 102
1970-01-01T00:03:00Z  candle open=103 close=102, want 1
1970-01-01T00:04:00Z  candle open=102 close=104, want 2
1970-01-01T00:04:00.2Z  ack
1970-01-01T00:05:00Z  candle open=105 close=106, want 2
1970-01-01T00:05:00.2Z  fill Buy 1 @ 105
1970-01-01T00:06:00Z  candle open=106 close=104, want 0
1970-01-01T00:06:00.2Z  ack
1970-01-01T00:07:00Z  candle open=103 close=102, want 0
1970-01-01T00:07:00.2Z  fill Sell 2 @ 103
1970-01-01T00:08:00Z  candle open=102 close=100, want -1
1970-01-01T00:08:00.2Z  ack
1970-01-01T00:09:00Z  candle open=99 close=98, want -1
1970-01-01T00:09:00.2Z  fill Sell 1 @ 99
1970-01-01T00:10:00Z  candle open=98 close=99, want 0
1970-01-01T00:10:00.2Z  ack
1970-01-01T00:11:00Z  candle open=100 close=100, want 0
1970-01-01T00:11:00.2Z  fill Buy 1 @ 100
final position: 0

execution log:
1970-01-01T00:01:00Z  send market order Buy 1
1970-01-01T00:01:00.2Z  ack Buy 1
1970-01-01T00:02:00.2Z  fill Buy 1 @ 102
1970-01-01T00:04:00Z  send market order Buy 1
1970-01-01T00:04:00.2Z  ack Buy 1
1970-01-01T00:05:00.2Z  fill Buy 1 @ 105
1970-01-01T00:06:00Z  send market order Sell 2
1970-01-01T00:06:00.2Z  ack Sell 2
1970-01-01T00:07:00.2Z  fill Sell 2 @ 103
1970-01-01T00:08:00Z  send market order Sell 1
1970-01-01T00:08:00.2Z  ack Sell 1
1970-01-01T00:09:00.2Z  fill Sell 1 @ 99
1970-01-01T00:10:00Z  send market order Buy 1
1970-01-01T00:10:00.2Z  ack Buy 1
1970-01-01T00:11:00.2Z  fill Buy 1 @ 100
```

The first part is what the strategy sees; the second is the execution log.

- Candles 1–3: long 1, bought at candle 2's open (102). Candles 2 and 3 want the same, so
  nothing is sent.
- Candles 4–5: long 2. One more is bought at candle 5's open (105), not two: the OMS sends
  only the difference (`send market order Buy 1`).
- Candles 6–7: flat. Both are sold in one order at candle 7's open (103).
- Candles 8–9: short 1, sold at candle 9's open (99).
- Candles 10–11: flat again, bought back at candle 11's open (100).
