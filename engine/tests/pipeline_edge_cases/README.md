# pipeline_edge_cases

The whole pipeline (strategy, OMS, RMS, `event_loop::run`) in the cases that may not be obvious: a change of mind while an order is working, long to short in one step, and so on. Each
test pins one trace: the events the strategy saw and the requests the OMS sent, in order,
plus the final position.

```bash
cargo test -p engine --test pipeline_edge_cases
```

## Layout

```
pipeline_edge_cases/
├── main.rs              declares the modules below
├── common.rs            works with any executor
├── <executor_1>.rs      the setup for executor 1
├── <executor_1>/        its cases, one file each
│   ├── <case_1>.rs
│   ├── <case_2>.rs
│   └── ...
├── <executor_2>.rs      the setup for executor 2
├── <executor_2>/
│   ├── <case_1>.rs
│   └── ...
└── ...
```

So the idea is simple: pin every non-obvious behavior of pipeline
(mainly `Oms`/`Executor`).

#### Why one folder per executor

What the pipeline does depends on the executor underneath. `MarketExecutor` fills a whole
order at the next candle's open; another executor may fill partially, at a different price,
or reject what this one accepts. The same scenario then gives a different trace, with its
own edge cases, so each executor gets its own folder.
