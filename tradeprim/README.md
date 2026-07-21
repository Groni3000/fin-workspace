# tradeprim

Trade primitives (`tradeprim`).
This crate focuses on:

- Base type/model concepts for everything else: P&L calculation, Fills... - everything that may be needed for
  backtests/real trading.

Basic types conversions:

`Quantity * Price` -> `QuoteNotional`

`PointValue * QuoteNotional` -> `CurrencyNotional`

To explain the idea we will start from a little bit more complex example and
finish with the simple one.

Examples:

1. ZB - U.S. Treasury Bond Futures.

   Contract Unit - Face value at maturity of $100,000

   Price Quotation - Points and fractions of points with par on the basis of 100 points

   Minimum Price Fluctuation - 1/32 of one point (0.03125) = $31.25

Therefore:

Let `quantity = 5 (contract)`, `price = 110'18 (points / contract) = 110.5625 (points / contract)`.

`quote_notional = quantity * price = (contract) * (points / contract) = points`

`quote_notional = 5 * 110.5625 = 552.8125 (points)`

`tick_size = (1/32, 31.25) = (one point per contract, $ per contract)`

`point_value = tick_size.1 * 1 / tick_size.0`

`point_value = ($ / contract) * 1 / (point / contract)`

`point_value = $ / point`

`point_value = 31.25 * 1 / (1 / 32) = 31.25 * 32 = 1_000 ($ / point)`

`currency_notional = point_value * quote_notional = ($ / point) * (point) = $`

`currency_notional = 1_000 * 552.8125 = 552_812.5 ($)`

We see a clear types conversions up to a `CurrencyNotional`.

2. SPY - State Street SPDR S&P 500 ETF Trust.
   Contract unit - 1 share.

   Price Quotation - U.S. dollars and cents per share.

   Minimum Price Fluctuation - 1 cent per share (0.01) = $0.01

Therefore:

Let `quantity = 5 (share)`, `price = 745.65 ($ / share)` ($ means "U.S. dollars and cents").

`quote_notional = quantity * price = (share) * ($ / share) = $`

`quote_notional = 5 * 745.65 = 3_728.25 ($)`

`tick_size = (0.01, 0.01) = ($ per share, $ per share)`

`point_value = tick_size.1 * 1 / tick_size.0`

`point_value = ($ / share) / ($ / share) = scalar`

`point_value = 0.01 * 1 / (0.01) = 1 (scalar)`

`currency_notional = point_value * quote_notional = scalar * ($) = $`

`currency_notional = 1 * 3_728.25 = 3_728.25 ($)`

So, we see how even a complex example of futures contracts maps to this type system 1 to 1.
The idea is to use `quote_notional` for internal math and convert to `currency_notional` for
humans.

## Price concept

- `i64` under the hood.
- Fixed `9` digits precision.
- Max integer part is 1e6, max fractional part (precision) scale is 1e9.
- Max representable value is: `1_000_000.999_999_999`.
- Has conversion from `f64` to `Price`.
  Overprecise `f64` values are rounded to `Price` precision because
  it's not possible to handle `f64` precision loss at some values closer to
  max digits capacity.
- Has **canonical** (`-1.32` for example) conversion from `&str` to `Price`.
  Can reject overprecise `str`/out of range values/wrong format.

## Quantity concept

- Represents quantity of `instrid::TradedInstrument` - **it is very important**, look `QuoteNotional`
  for more concrete info.
- Copy-paste of `Price`, changing underlying `i64 -> u64`.
- Max representable value is: `5_000_000.999_999_999`.
- Has conversion from `f64` to `Quantity`.
  But. At such scale and big max value it has precision loss at extreme values.
- Has **canonical** (`1.32` for example) conversion from `&str` to `Quantity`.
  Can reject overprecise `str`/out of range values/wrong format.

## QuoteNotional concept

- Represents Notional in quote. It isn't always money. For such example: look ZB example above.
- Similar to other types, `i128` and fixed precision to `9` digits.
- Max representable value is: `5_000_006_000_000.993_999_998`.
- **DOESN'T** have conversion from `f64` to `QuoteNotional`.
  That is because f64 has ~15-16 significant digits, while this type
  requires more.
- Has **canonical** (`-1.32` for example) conversion from `&str` to `QuoteNotional`.
  Can reject overprecise `str`/out of range values/wrong format.
