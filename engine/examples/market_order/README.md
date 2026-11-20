# market_order

A complete backtest on eleven one-minute bars: a strategy enters long, adds, exits, goes
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

- **A market-data stream is just an iterator.** `Vec<Result<Tagged<Bar>, io::Error>>`
  is enough. `Bar` implements only what the simulator needs (`Timestamped`,
  `RelevantPrice`, `Candle`), and `Tagged` attaches the instrument.
- **A strategy says what it wants to hold; it doesn't send orders.** `Scripted` implements
  `Traded`: after each bar it sets its desired position from the script in `BARS`. The OMS
  sends a market order for the difference between that and what's held or already working.
- **No change, no order.** When the wanted position is the same as after the previous bar,
  the OMS sends nothing: the execution log has no `send` line after those bars. That holds
  while the order is still working (bar 2) and once it's filled (bar 3).
- **One loop drives everything.** `event_loop::run` hands each event to the OMS, then to
  the strategy, then lets the OMS reconcile. It returns the OMS and the portfolio at the
  end, so the final position comes from what was really filled.
- **The simulated venue answers on its own schedule.** `MarketExecutor` acks 200 ms after
  the order (about 50 ms to decide, about 150 ms of network round trip), and fills at the
  *open* of the next bar, 200 ms after that bar.
- **Logs.** `telemetry::init` writes the order lifecycle (send, ack, fill), as JSON, to
  `market_order.exec.<Sunday>.log`, and everything else to `market_order.diag.<Sunday>.log`,
  in `engine-example-market_order` under the system temp directory. Every line carries the
  simulated time, not the wall clock. After the run the example prints the execution log:
  the strategy only sees what comes back (acks, fills), while the log also has what the OMS
  sent.

  `<temp>` is the system temp folder: `/tmp` on Linux, `%TEMP%` on Windows (usually
  `C:\Users\<name>\AppData\Local\Temp`). Each run deletes the folder first, so it only ever
  holds the last run's logs, a couple of kilobytes. Delete it whenever you like.

## The cost of one-minute bars

The strategy decides on a bar's close, and the order is acked 200 ms later, but it fills only
at the next bar's open, a minute later. The simulator has no prices between bars, so it can't
fill any earlier.

The smaller the bars, the smaller that cost. With latencies like these, one-second bars are a
pretty good approximation for a semi-liquid or somewhat stale market: the next bar's open is
then only a second after the decision.

`MarketExecutor` also has no slippage: it fills exactly at the open. A more advanced executor
should model slippage that changes with the market rather than a fixed amount. That makes a
backtest more accurate, especially on one-second bars, where the fill price is otherwise
close to right already.

## Expected output

```text
logs in <temp>/engine-example-market_order
1970-01-01 00:01:00 UTC  bar open=100 close=101, want 1
1970-01-01 00:01:00.200 UTC  ack
1970-01-01 00:02:00 UTC  bar open=102 close=103, want 1
1970-01-01 00:02:00.200 UTC  fill Buy 1 @ 102
1970-01-01 00:03:00 UTC  bar open=103 close=102, want 1
1970-01-01 00:04:00 UTC  bar open=102 close=104, want 2
1970-01-01 00:04:00.200 UTC  ack
1970-01-01 00:05:00 UTC  bar open=105 close=106, want 2
1970-01-01 00:05:00.200 UTC  fill Buy 1 @ 105
1970-01-01 00:06:00 UTC  bar open=106 close=104, want 0
1970-01-01 00:06:00.200 UTC  ack
1970-01-01 00:07:00 UTC  bar open=103 close=102, want 0
1970-01-01 00:07:00.200 UTC  fill Sell 2 @ 103
1970-01-01 00:08:00 UTC  bar open=102 close=100, want -1
1970-01-01 00:08:00.200 UTC  ack
1970-01-01 00:09:00 UTC  bar open=99 close=98, want -1
1970-01-01 00:09:00.200 UTC  fill Sell 1 @ 99
1970-01-01 00:10:00 UTC  bar open=98 close=99, want 0
1970-01-01 00:10:00.200 UTC  ack
1970-01-01 00:11:00 UTC  bar open=100 close=100, want 0
1970-01-01 00:11:00.200 UTC  fill Buy 1 @ 100
final position: 0

execution log:
1970-01-01 00:01:00 UTC  send market order Buy 1
1970-01-01 00:01:00.200 UTC  ack Buy 1
1970-01-01 00:02:00.200 UTC  fill Buy 1 @ 102
1970-01-01 00:04:00 UTC  send market order Buy 1
1970-01-01 00:04:00.200 UTC  ack Buy 1
1970-01-01 00:05:00.200 UTC  fill Buy 1 @ 105
1970-01-01 00:06:00 UTC  send market order Sell 2
1970-01-01 00:06:00.200 UTC  ack Sell 2
1970-01-01 00:07:00.200 UTC  fill Sell 2 @ 103
1970-01-01 00:08:00 UTC  send market order Sell 1
1970-01-01 00:08:00.200 UTC  ack Sell 1
1970-01-01 00:09:00.200 UTC  fill Sell 1 @ 99
1970-01-01 00:10:00 UTC  send market order Buy 1
1970-01-01 00:10:00.200 UTC  ack Buy 1
1970-01-01 00:11:00.200 UTC  fill Buy 1 @ 100
```

The first part is what the strategy sees; the second is the execution log.

- Bars 1–3: long 1, bought at bar 2's open (102). Bars 2 and 3 want the same, so nothing is
  sent.
- Bars 4–5: long 2. One more is bought at bar 5's open (105), not two: the OMS sends only the
  difference (`send market order Buy 1`).
- Bars 6–7: flat. Both are sold in one order at bar 7's open (103).
- Bars 8–9: short 1, sold at bar 9's open (99).
- Bars 10–11: flat again, bought back at bar 11's open (100).
