# tradeprim

Trade primitives (`tradeprim`) - experimental crate, on top of [`instrid`](../instrid).
This crate focuses on:
  - Base concepts for P&L calculation, Fills... - everything that may be needed for
backtests/real trading.
  - The general idea of calculation over `Amount<Asset>`. That way math is simple, conversion
is what's complex.


Conversion between assets (USD ↔ EUR, points ↔ USD via point-value) is hard. 
We will **probably** provide some generic version of 
conversion between assets `Convert<From, To>`, but it's not gonna be our main focus. Moreover
generic version is kind of *"enough"* if you already have some kind of 
conversion rates system plugged in your trading program.
