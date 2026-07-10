# Lab

A place where I experiment, trying to figure out what do I need to build next.

## Entities

- **Strategy** - owns `(desired_position, desired_orders)` per symbol. `desired_position` -
  is **current, unconditional** desire. `desired_orders` - mostly
  stop/limit/stop-limit orders that the strategy want to be working.

  **BE CAREFUL** - this all is desired, not actual. For actual, you need to read
  state from other concepts below (`OMS`, `Porfolio`)

- **Portfolio** - owns strategies, account information, positions, fills.
  Emits orders to `RMS`, `OMS`.
  Due to the fact it owns strategies, it can net some orders potentially lowering costs.

  **THE ONLY SOURCE OF TRUTH OF CURRENT EXPOSURE AND FILLED ORDERS**

- **RMS** - reads order(s) that are meant to be sent, open orders,
  portfolio info (margin), risk rules. Allows or discards orders (with notification)
  based on these rules.

- **OMS** - tracks order lifecycle. 1 order type per `(strategy, instrument)` in order
  to eliminate spam orders risk. All filled orders are sent to `Portfolio`.

  **THE ONLY SOURCE OF TRUTH OF CURRENT WORKING ORDERS**

- **Executor** - receives orders from `OMS` and executes them, sends trades reports back
  to `OMS`.

- **Reconciler** - reads desired position (`Strategy`), reads actual position (`Portfolio`),
  reads desired orders (`Strategy`), reads open orders (`OMS`), and reconciles.

## Small description of concept idea

- **Data stream** - the idea is to treat every data source as a stream of data.
  Need to figure out how to do that. Probably `Iterator<Item=Result<MarketData, FeedError>>`
  (`MarketData::Tick/Bar/BookUpdate`) trait. Also it would be great to implement this trait
  on multiple sources at once, so we can consume and use the most relevant data
  (probably we need to introduce some kind of data-driven `Clock`?). But that's... Later.

- **Instrument specification** - I need to know such things as:
  min, max, step for both quantity and price.
  Also I need to know to which precision I need to round price.
  Quite a bummer tbh. Filling this shit out is error prone and boring...

- **Executor** (or **BrokerAdapter**?) - orders are filled here. Emits execution reports.

  In backtests it fills orders based on some strategy.
  Examples of such `FillStrategy`:
  - **naive** - everything fills.
  - **probabilistic** - fills based on some probability distribution, therefore partial fills,
    slippage.
  - **look-ahead probabilistic** - takes some small frequency data and trying to
    figure out the probability distribution based on traded volume and dominant traded side
    and execute accordingly, probably too complex for me xD.
  - **order book** - (though order book data feed needed).
  - ... You can imagine a lot of strategies here. But for now,
    let's start with the first two. First one just to get used to traits, second one to
    have something +- realistic.

- **OMS** - order management system.
  - **order state machine** - (PendingNew→New→…→Filled/Rejected, IN_DOUBT).
  - **position** - derived only from fills.
  - **freeze-on-silence** - **per-symbol in-flight mutex**
  - **reconciliation** - against the executor, **throttles** / **kill switch**.

- ... Yet to be added
