# simulated_stop

A natural continuation of [`market_order`](../market_order), focused on simulating a stop.
The strategy enters long 1 at market and keeps the stop itself, 2 below its entry fill. Once
a candle's low reaches the stop, it wants to be flat, and the OMS sends a market sell.

Backtests and replays only, like `market_order`.

```bash
cargo run -p engine --example simulated_stop
```

## Why not a stop order

Stop, limit and stop-limit orders behave differently at every venue, especially when you
cancel or modify them: some need only the order id, others want the side, the quantity, the
time in force, and so on. At Interactive Brokers, stops on futures triggered only during the
stock market's regular trading hours: our FIX session had a default "regular hours only"
setting that overrode the order's own flag. It took an escalation for their FIX engineers to
disable that default, so that the outside-regular-hours tag (6205) on each order decides.

And the rules keep changing. For December 6, 2026, Interactive Brokers announced that the
pre-market for US stocks would open at 9 PM ET instead of 4 AM, and that its overnight venue
would be discontinued: orders still flagged for it are rejected from that date. Every flag a
strategy sets on an order is one more thing to keep up with.

To stay out of all that, we recommend market orders only, with the strategy simulating the
other order types. Start with the simple method. If you want, implement it again later with
real order types and compare what the simplicity costs. Maybe the results are even better.
It's better to calculate and compare than to guess.

## The cost of a simulated stop

The strategy learns that the stop was reached only when the candle is complete, so it exits
at the next candle's open, not at the stop price: here at 98 instead of 99. Smaller candles
make the difference smaller.

The stop is measured from the entry fill (101), not from the candle the decision was made on.

## Expected output

```text
logs in <temp>/engine-example-simulated_stop
1970-01-01T00:01:00Z  candle 100/101/99/100, want 1
1970-01-01T00:01:00.2Z  ack
1970-01-01T00:02:00Z  candle 101/102/100/101
1970-01-01T00:02:00.2Z  fill Buy 1 @ 101, stop at 99
1970-01-01T00:03:00Z  candle 100/101/99.5/100
1970-01-01T00:04:00Z  candle 100/100/99/99.5, stop hit, want 0
1970-01-01T00:04:00.2Z  ack
1970-01-01T00:05:00Z  candle 98/99/97/98
1970-01-01T00:05:00.2Z  fill Sell 1 @ 98
1970-01-01T00:06:00Z  candle 98/99/97/98
final position: 0

execution log:
1970-01-01T00:01:00Z  send market order Buy 1
1970-01-01T00:01:00.2Z  ack Buy 1
1970-01-01T00:02:00.2Z  fill Buy 1 @ 101
1970-01-01T00:04:00Z  send market order Sell 1
1970-01-01T00:04:00.2Z  ack Sell 1
1970-01-01T00:05:00.2Z  fill Sell 1 @ 98
```

Candles are open/high/low/close. `<temp>` is the system temp folder, as in `market_order`.

- Candle 3's low (99.5) comes close to the stop but stays above it: nothing is sent.
- Candle 4's low touches 99: the stop is reached, even though the candle closes above it
  (99.5). The strategy wants flat, and the sell fills at candle 5's open (98).
