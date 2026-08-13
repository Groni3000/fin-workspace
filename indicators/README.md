# indicators

A port of my python(pandas)+rust indicators library with python part stripped.

Usually, we use python + pandas to draft strategies backtests using vectorized approach.
It's fast, relatively reliable (if you leverage python type system and pandas stubs minimizing pd.DataFrame usage)
and easy to use.

But when you have a stream of prices and you need to calculate some indicator - it feels off.

New price -> convert to pd.Series -> pd.concat([old buffer, converted price]) -> recalculate?

Emmm... That feels highly inefficient and just wrong. Therefore we anyway have to create an indicator
for a "streaming" mode with some buffer and manual computation.

And here's the kicker: you may miss some of pandas behavior and your backtest may drift away from a real execution.
It may be very tricky. Especially with indicators, whose state depends on the whole history
instead of a fixed window (like default `.ewm`).

So, knowing that I'm gonna build indicators from scratch replicating pandas behavior for a "streaming" mode,
why won't I leverage rust + PyO3? But for this project python part is not needed. That's why I stripped it.

## Design

The project is designed around two types of structs: `Parameters`, `Indicator`.
Probably it was not a really good idea to name them literally like that) Maybe, later, I'll change naming.

That design is dictated by using configs:

- `config.parameters` - put parameters in a config.
- `strategy_state.indicator` - put indicator instance in a strategy state.
- `[strategy_state.indicator.parameter]` - optionally, but very handy to have access to parameters
  even when you have access to indicator only.

Indicators only have `pub fn update(...)` to update inner state.

This design allowed to leverage "stacked" indicators. For example, if indicator A uses indicator B, you can
use inner indicator parameters as a parameter for outer indicator parameters and use B.update inside A.
Yet it made parameters instantiation very bloated...

## Examples

```rust
use indicators::{RSI, SMA};

let mut rsi = RSI::Indicator::new(&RSI::Parameters::new(SMA::Parameters::new(3).expect("period must be correct")));
// prices: 100.0, 102.0, 101.0, 103.0, 104.0
// expected output: f64::NAN, f64::NAN, f64::NAN, 80, 75
let mut rsi_value = rsi.update(100.0);
assert!(rsi_value.is_nan());
rsi_value = rsi.update(102.0);
assert!(rsi_value.is_nan());
rsi_value = rsi.update(101.0);
assert!(rsi_value.is_nan());
rsi_value = rsi.update(103.0);
assert!(!rsi_value.is_nan());
assert!(rsi_value == 80.0);
rsi_value = rsi.update(104.0);
assert!(!rsi_value.is_nan());
assert!(rsi_value == 75.0);
```

## Some useful commands

```bash
# Run doc tests
cargo test -p indicators --doc
# Run all other tests
cargo test -p indicators --all-targets
```
