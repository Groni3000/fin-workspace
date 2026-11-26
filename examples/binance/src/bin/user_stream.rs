//! The account's own events (orders, balances) as Binance sends them:
//! `cargo run -p binance-example --bin user_stream -- <profile>`.
//!
//! Subscribes through the WebSocket API with a signed request, then prints every message raw,
//! with the time it arrived, until Ctrl-C.

use std::path::Path;
use std::process::ExitCode;

use binance_example::orders::BoxError;
use binance_example::profile::Profile;
use binance_sdk::models::WebsocketEvent;
use binance_sdk::spot::websocket_api::UserDataStreamSubscribeSignatureParams;
use jiff::Timestamp;
use tokio::sync::mpsc;

const PROFILES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/profiles.toml");

#[tokio::main]
async fn main() -> ExitCode {
    match run().await {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

async fn run() -> Result<(), BoxError> {
    let name = std::env::args()
        .nth(1)
        .ok_or("usage: user_stream <profile>")?;
    let profile = Profile::load(Path::new(PROFILES), &name)?;
    let api = profile.env.ws_api(profile.ws_api_builder().build()?);
    println!("{name} ({:?})", profile.env);

    let connection = api.connect().await?;
    let (events, mut received) = mpsc::unbounded_channel();
    connection.subscribe_on_ws_events(move |event| {
        // Stamped here: the printing task may run later.
        let _ = events.send((Timestamp::now(), event));
    });
    let (reply, _stream) = connection
        .user_data_stream_subscribe_signature(UserDataStreamSubscribeSignatureParams::default())
        .await?;
    println!("subscribed: {:?}", reply.data()?);

    while let Some((at, event)) = received.recv().await {
        let at = at.strftime("%H:%M:%S%.3f");
        match event {
            WebsocketEvent::Message(raw) => println!("{at} {raw}"),
            other => println!("{at} [{other:?}]"),
        }
    }
    Ok(())
}
