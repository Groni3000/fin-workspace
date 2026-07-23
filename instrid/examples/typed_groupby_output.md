Sample output of `cargo run --example typed_groupby` (keys sorted, so it reproduces run-to-run).

For illustration only.

```
signed cashflow by currency
───────────────────────────
  Currency|CHF: -4_800.8 (CHF)
  Currency|EUR: -76_468.75 (EUR)
  Currency|USD: 88_086.59 (USD)

signed cashflow by base
───────────────────────
  Commodity|XAU:
        Currency|CHF: -4_800.8 (CHF)
        Currency|EUR: 31.25 (EUR)
        Currency|USD: 105.2 (USD)
  Crypto|BTC:
        Currency|USD: 550 (USD)
  Currency|JPY:
        Currency|USD: 85_943.75 (USD)
  Equity|AAPL:
        Currency|USD: 0.14 (USD)
  Index|ES:
        Currency|USD: 1_487.5 (USD)
  Index|FDX:
        Currency|EUR: -76_500 (EUR)

fills by asset class
────────────────────
  Commodity: 8 fills
  Crypto   : 2 fills
  Currency : 2 fills
  Equity   : 4 fills
  Index    : 6 fills

signed cashflow by asset class
──────────────────────────────
  (Commodity, Currency|CHF): -4_800.8 (CHF)
  (Commodity, Currency|EUR): 31.25 (EUR)
  (Commodity, Currency|USD): 105.2 (USD)
  (Crypto, Currency|USD)   : 550 (USD)
  (Currency, Currency|USD) : 85_943.75 (USD)
  (Equity, Currency|USD)   : 0.14 (USD)
  (Index, Currency|EUR)    : -76_500 (EUR)
  (Index, Currency|USD)    : 1_487.5 (USD)

realized pnl per instrument (flat positions only, no FIFO/LIFO matcher yet)
───────────────────────────────────────────────────────────────────────────
  Futures:Index|ES/Currency|USD@XCME(USD) 2026-06 : 1_487.5 (USD)
  Futures:Index|FDX/Currency|EUR@XEUR(EUR) 2026-06: -76_500 (EUR)
  Stock:Commodity|XAU/Currency|EUR@XLBM(EUR)      : 31.25 (EUR)
  Stock:Commodity|XAU/Currency|USD@XLBM(USD)      : 105.2 (USD)
  Stock:Crypto|BTC/Currency|USD@IEXG(USD)         : 550 (USD)
  Stock:Equity|AAPL/Currency|USD@XLON(USD)        : 0.1 (USD)
  Stock:Equity|AAPL/Currency|USD@XNAS(USD)        : 0.04 (USD)
```
