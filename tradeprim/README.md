# tradeprim

Trade primitives (`tradeprim`).
This crate focuses on:

- Base type/model concepts for everything else: P&L calculation, Fills... - everything that may be needed for
  backtests/real trading.
- The general idea of calculation over `Amount<Asset>`. That way math is simple, conversion
  is what's complex.

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

- Represents Notional in quote. For example:
  - SPY/USD -> QuoteNotional is in $. And you can simply think of it as
    a simple notional value, money.
  - `RB/($ per gallon)` -> QuoteNotional is in `(n_contracts * ($ per gallon))`.
    Example: price 3.1 which is quoted in `($ / gallon)`. If you multiply
    by quantity (let it be 5 contracts), you **won't** get `15.5 ($)` of notional
    value. You will get `5 (contract) * 3.1 ($ / gallon)`.
    **That** is `QuoteNotional`. You can't treat it like money.
    In order to get money value, you need to multiply it by `point_value`
    per specification. In this case it is 42_000 (gallons / contract).
    Let's do this:

    `5 (contract) * 3.1 ($ / gallon) * 42_000 (gallon / contract) =`

    `= {notice how "contract" and "gallon" cancel out} =`

    `= 5 * 3.1 ($) * 42_000 = 651_000 ($)`

    **This** is `CurrencyNotional` in money as we all used to.

  - There are more examples like this: "cents per bushel" or some bond futures are traded in
    "% per par" etc.

- Similar to other types, `i128` and fixed precision to `18` digits.
- Max representable value is: `999 trillions`.
- **DOESN'T** have conversion from `f64` to `QuoteNotional`.
  That is because f64 has ~15-16 significant digits, while this type
  requires more.
- Has **canonical** (`-1.32` for example) conversion from `&str` to `QuoteNotional`.
  Can reject overprecise `str`/out of range values/wrong format.
