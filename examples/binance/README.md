# binance-example

Copy `profiles.example.toml` to `profiles.toml`, fill it in, and check a profile with
`cargo run -p binance-example --bin ping -- testnet`.

## Threads

```text
  main thread: synchronous                        bridge thread: tokio, single-threaded
  (the same code as a backtest)                   (the SDK's tasks take turns on it)
┌──────────────────────────────────────┐        ┌──────────────────────────────────────┐
│ engine::event_loop::run              │        │ market data (WebSocket) ─────────┐   │
│                                      │ events │ user data (WebSocket) ───────────┤   │
│ queue.next_event() ◄─────────────────┼────────┼── MarketData, Exec(Ack/Fill/…) ──┘   │
│   ├─ oms.on_exec(exec, &mut pf)      │        │                                      │
│   ├─ strategy.on_event(&event, &pf)  │        │                                      │
│   └─ oms.reconcile(desired, …)       │requests│                                      │
│        └─ queue.submit(req) ─────────┼────────┼──► executor                          │
│           returns at once:           │        │      match req {                     │
│           no network here            │        │        market order → SDK call       │
│                                      │        │        cancel       → SDK call       │
│                                      │        │      }                               │
│                                      │        │      ack / reject → events           │
└──────────────────────────────────────┘        └──────────────────────────────────────┘

  both channels are unbounded: events over std::sync::mpsc, requests over tokio::sync::mpsc
```

- The main thread runs the same `run` loop as a backtest. `submit` only puts the request in a
  channel; the OMS never waits on the network.
- The bridge thread basically runs a market data and Executor - everything that talks to Binance. 
- The cost of one thread: a task that computes for long without waiting (parsing the 18 MB
  exchange info, say) holds up the others meanwhile.
- Unbounded channels: a main thread that falls behind is caught by measuring lag instead.
