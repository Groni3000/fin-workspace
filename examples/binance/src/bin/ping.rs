//! Ping check

use std::time::{Instant, SystemTime, UNIX_EPOCH};

use binance_example::Env;
use binance_sdk::config::ConfigurationRestApi;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let env: Env = std::env::args()
        .nth(1)
        .ok_or("usage: ping <testnet|demo|live>")?
        .parse()?;
    let client = env.rest(ConfigurationRestApi::builder().build()?);

    let started = Instant::now();
    client.ping().await?.data().await?;
    println!("{env:?}: ping {} ms", started.elapsed().as_millis());

    let sent = SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis() as i64;
    let server = client
        .time()
        .await?
        .data()
        .await?
        .server_time
        .ok_or("no serverTime")?;
    let received = SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis() as i64;
    let ours = (sent + received) / 2;
    println!(
        "server time {server} ms, ours {ours} ms, offset {} ms",
        server - ours
    );
    Ok(())
}
