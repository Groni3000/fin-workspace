One-time per boot (samply's only prereq)

```zsh
sudo sysctl kernel.perf_event_paranoid=1
```

Make sure release has symbols (add to Cargo.toml first if not already):

```Cargo.toml
[profile.release]

debug = true
```

```zsh
cargo build --release -p lab --bin file_reader
samply record ./target/release/file_reader
```
