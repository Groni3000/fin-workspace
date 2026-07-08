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
- Max integer part is 1e6, max mantissa (precision) scale is 1e9.
- Max representable value is: `1_000_000.999_999_999`.
- Has conversion from `f64` to `Price`. 
Overprecise `f64` values are rounded to `Price` precision because
it's not possible to handle `f64` precision loss at some values closer to
max digits capacity.
- Has **canonical** (`-1.32` for example) conversion from `&str` to `Price`. 
Can reject overprecise `str`/out of range values/wrong format.
