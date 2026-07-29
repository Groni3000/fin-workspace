One-time per boot (samply's only prereq)

```zsh
sudo sysctl kernel.perf_event_paranoid=1
```

Symbols come from the `profiling` profile.

```Cargo.toml
[profile.profiling]
inherits = "release"
debug = 1
```

Build with `--profile profiling` and the binary lands in `target/profiling/`:

```zsh
cargo build --profile profiling -p lab --bin file_reader
samply record ./target/profiling/file_reader
```
