# Lab

A place where I experiment, trying to figure out what do I need to build next.

## Entities

- **Strategy** - owns `(desired_position, desired_orders)` per symbol. `desired_position` -
  is **current, unconditional** desire. `desired_orders` - mostly
  stop/limit/stop-limit orders that the strategy want to be working.

  **BE CAREFUL** - this all is desired, not actual. For actual, you need to read
  state from other concepts below (`OMS`, `Portfolio`).

- **Portfolio** - read-only accounting truth: account information, positions, fills,
  realized/unrealized PnL. **Mutated ONLY by applying fills** (fed from `OMS`).
  Does **not** own strategies and does **not** emit orders - it is fills-in / reads-out.

  **THE ONLY SOURCE OF TRUTH OF CURRENT EXPOSURE AND FILLED ORDERS**

- **ExecutionLoop** - the gap worker. Reads desired state from every `Strategy`,
  reads actual position (`Portfolio`) and open orders (`OMS`), computes
  `gap = target - actual - working` per instrument, and emits proposed orders to `RMS`.

  (Netting desires across strategies is possible here, but **deferred** - it drags in
  fill-attribution: when a netted order fills, which strategy owns the PnL? Skip for now.)

- **RMS** - reads order(s) that are meant to be sent, open orders,
  portfolio info (margin), risk rules. Allows or discards orders (with notification)
  based on these rules.

- **OMS** - tracks order lifecycle. **Only 1 _unacknowledged command_ per `instrument`**
  at a time. That means if I sent something and don't know yet what happened to it, I
  don't send the next command for an instrument until the previous one is acknowledged
  and in a known state or I re-query it.

  Point is: if it goes silent, the only thing I definitely know is its `client_order_id` ->
  I ask about it, never blindly resend (that's the spam trap). All subsequent commands
  for that instrument are blocked until I get a response and understand what state it's in.

  When we receive the response, we update the order status to known (for example, we received
  order status = New) and treat it as a working order. Next order command now can be sent.

  Fills go to `Portfolio`.

  **THE ONLY SOURCE OF TRUTH OF CURRENT WORKING ORDERS**

- **Executor** - receives orders from `OMS` and executes them, sends execution reports
  back to `OMS`. (Backtest fill behaviour lives here)

- **Reconciler** - drift detection, **not** the gap loop. Compares _local believed_ state
  (`Portfolio` positions, `OMS` working orders) against the _broker's reported_ state
  (via `Executor`). On divergence beyond tolerance: halt and alert. Never auto-resolve
  on data you suspect is bad.

## My thoughts about current tasks.

- **Data stream** - the idea is to treat every data source as a stream of data.
  Need to figure out how to do that. Probably `Iterator<Item=Result<MarketData, FeedError>>`
  (`MarketData::Tick/Bar/BookUpdate`) trait. Also it would be great to implement this trait
  on multiple sources at once, so we can consume and use the most relevant data
  (probably we need to introduce some kind of data-driven `Clock`?). But that's... Later.

- **Instrument specification** - I need to know such things as:
  min, max, step for both quantity and price.
  Also I need to know to which precision I need to round price.
  Quite a bummer tbh. Filling this shit out is error prone and boring...
