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

Let's see one more example:

3. RB - RBOB Gasoline Futures.

   Contract Unit - 42,000 gallons

   Price Quotation - U.S. dollars and cents per gallon

   Minimum Price Fluctuation - 0.0001 per gallon = $4.20

Therefore:

Let `quantity = 5 (contract)`, `price = 3.2062 ($ / gallon)`.

`quote_notional = quantity * price = (contract) * ($ / gallon)`

`quote_notional = 5 * 3.2062 = 16.031 (contract * $ / gallon)`

`tick_size = (0.0001, 4.20) = ($ per gallon, $ per contract)`

`point_value = tick_size.1 * 1 / tick_size.0`

`point_value = ($ / contract) * 1 / ($ / gallon)`

`point_value = gallon / contract`

`point_value = 4.20 * (1 / 0.0001) = 4.2 * 10_000 = 42_000 (gallon / contract)`

`currency_notional = point_value * quote_notional = (gallon / contract) * (contract * $ / gallon)`

`currency_notional = $`

`currency_notional = 42_000 * 16.031 = 673_302 ($)`

To be honest, this conversions and type system deserves to be
written using `std::marker::PhantomData`, but I've already chosen
"runtime compatibility", though I must admit that developing this new
type system would be interesting and so much fun.

Ok, one more:

4. ZW - Chicago SRW Wheat Futures.

   Contract Unit - 5,000 bushels

   Price Quotation - U.S. cents per bushel

   Minimum Price Fluctuation - 1/4 of one cent (0.0025) per bushel = $12.50

Therefore:

Let `quantity = 5 (contract)`, `price = 696'4 ($cents / bushel) = 696 + 4/8 ($cents / bushel) = 696.5 ($cents / bushel)`.

`quote_notional = quantity * price = (contract) * ($cents / bushel)`

`quote_notional = 5 * 696.5 = 3_482.5 (contract * $cents / bushel)`

`tick_size = (0.0025, 12.5) = ($ per bushel, $ per contract)`

`point_value = tick_size.1 * 1 / tick_size.0`

`point_value = ($ / contract) * 1 / ($ / bushel)`

`point_value = bushel / contract`

`point_value = 12.5 * (1 / 0.0025) = 12.5 * 400 = 5_000 (bushel / contract)`

`currency_notional = point_value * quote_notional = (bushel / contract) * (contract * $cents / bushel)`

`currency_notional = $cents`

`currency_notional = 5_000 * 3_482.5 = 17_412_500 ($cents) = 174_125.0 ($)`

The last part is the problem - you don't know that you need to multiply by 100 to get major form of the currency.
So, when we write specification, we need to manually do it once.

`tick_size = (0.25, 12.5) = (cent / bushel, $ / contract)`

`point_value = ($ / contract) / (cent / bushel)  = ($ * bushel) / (cent * contract)`

`point_value = 12.5 * (1 / 0.25) = 12.5 * 4 = 50 ($ * bushel) / (cent * contract)`

`currency_notional = ($ * bushel) / (cent * contract) * (contract * cent / bushel)`

`currency_notional = $`

`currency_notional = 50 * 3_482.5 = 174_125.0 ($)`

## Currency concept

- Parsed from ISO 4217
- Only currently used currencies.
- Usually we use derived `CurrencyTag` (`.into`) that holds only `alphabetic_code` and precision.
  `CurrencyTag` basically a subset of `Currency`.
- `CurrencyTag` is used when we use `CurrencyNotional` (definition below).

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

## CurrencyNotional concept

- Basically, the same idea as QuoteNotional, but tagged with a real currency.
- min/max values are `-i128::MAX, i128::MAX` in a raw int representation.
  Note `-i128::MAX != i128::MIN`: `i128::MIN` is excluded so that negation is
  always a true negation, never an identity mapping.
- Addition comes in two forms:
  - `checked_add` -> `Result<Self, CnAddError>`, reporting `CurrencyMismatch`
    or `Overflow`. Use this anywhere the operands come from outside the process
    (broker reports, config) — a mismatched currency is a data problem, not a
    programmer error, and the layer above should decide whether to halt.
  - `Add` (`+`) delegates to `checked_add` and panics on either failure.
    Convenient when both operands are already known to share a currency.
- Used via the `Specification` of an instrument.
- Very limited in ways to get this type: either Spec or deliberately `::new`.
  At least for now I think this is a very delicate type and allowing to get it
  in a lot of different ways may hurt more than help. Though... Strategy's state
  will require ser/de so... It's probably unavoidable? At least formatters will do the work
  not the user of this library.
