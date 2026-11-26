//! Market orders by hand, and the account they change.

use std::time::{Duration, Instant};

use binance_sdk::errors::ConnectorError;
use binance_sdk::models::ConfigBuildError;
use binance_sdk::spot::rest_api::{
    AccountCommissionParams, GetAccountParams, GetOpenOrdersParams, GetOrderParams,
    GetOrderResponse, NewOrderNewOrderRespTypeEnum, NewOrderParams, NewOrderResponse,
    NewOrderSideEnum, NewOrderTypeEnum, RestApi,
};
use rust_decimal::Decimal;
use uuid::Uuid;

use crate::profile::Profile;

pub type BoxError = Box<dyn std::error::Error + Send + Sync>;

/// How long [`wait_filled`] waits.
const FILL_WAIT: Duration = Duration::from_secs(30);
const FILL_POLL: Duration = Duration::from_millis(200);

/// A REST client for placing orders.
///
/// The SDK's default 1 s timeout is about what a fresh connection takes, and a timed-out order
/// may still have been placed. No retries: the SDK can resend an order that went through.
pub fn trading_client(profile: &Profile) -> Result<RestApi, ConfigBuildError> {
    let config = profile.rest_builder().timeout(10_000).retries(0).build()?;
    Ok(profile.env.rest(config))
}

/// Places a market order for `quantity`, sent unrounded, with a UUID v7 as its client id (the
/// kind an `oms::OrderId` holds). Returns Binance's full answer and how long it took.
pub async fn place_market(
    client: &RestApi,
    symbol: &str,
    side: NewOrderSideEnum,
    quantity: Decimal,
) -> Result<(NewOrderResponse, Duration), BoxError> {
    let params = NewOrderParams::builder(symbol.to_string(), side, NewOrderTypeEnum::Market)
        .quantity(quantity)
        .new_client_order_id(Uuid::now_v7().to_string())
        .new_order_resp_type(NewOrderNewOrderRespTypeEnum::Full)
        .build()?;
    let started = Instant::now();
    let sent = client.new_order(params).await;
    let took = started.elapsed();
    match sent {
        Ok(response) => Ok((response.data().await?, took)),
        Err(e) => {
            // The message alone drops Binance's error code; the executor will need it.
            let detail = match e.downcast_ref::<ConnectorError>() {
                Some(ConnectorError::BadRequestError { code, body, .. }) => format!(
                    "\ncode {code:?}, body {}",
                    body.as_ref()
                        .map_or("none".to_string(), ToString::to_string)
                ),
                _ => String::new(),
            };
            Err(format!("rejected after {} ms: {e:#}{detail}", took.as_millis()).into())
        }
    }
}

/// Asks Binance about the order until it is filled. Errors if it ends otherwise (expired,
/// canceled, rejected) or is still open after 30 s.
pub async fn wait_filled(
    client: &RestApi,
    symbol: &str,
    client_id: &str,
) -> Result<GetOrderResponse, BoxError> {
    let started = Instant::now();
    loop {
        let params = GetOrderParams::builder(symbol.to_string())
            .orig_client_order_id(client_id.to_string())
            .build()?;
        let order = client.get_order(params).await?.data().await?;
        match order.status.as_deref() {
            Some("FILLED") => return Ok(order),
            Some("NEW" | "PARTIALLY_FILLED" | "PENDING_NEW") if started.elapsed() < FILL_WAIT => {
                tokio::time::sleep(FILL_POLL).await;
            }
            status => {
                return Err(format!(
                    "order {client_id} is {status:?} after {} ms",
                    started.elapsed().as_millis()
                )
                .into());
            }
        }
    }
}

/// Prints whether the account can trade, its commission rates, its non-zero balances and its
/// open orders.
pub async fn print_account(client: &RestApi) -> Result<(), BoxError> {
    let params = GetAccountParams::builder()
        .omit_zero_balances(true)
        .build()?;
    let account = client.get_account(params).await?.data().await?;
    println!(
        "account type {}, can trade {}, permissions {}",
        show(&account.account_type),
        show(&account.can_trade),
        account.permissions.unwrap_or_default().join(", ")
    );
    if let Some(rates) = account.commission_rates {
        println!(
            "commission: maker {}, taker {}, buyer {}, seller {}",
            show(&rates.maker),
            show(&rates.taker),
            show(&rates.buyer),
            show(&rates.seller)
        );
    }
    let mut balances = account.balances.unwrap_or_default();
    balances.sort_by(|a, b| a.asset.cmp(&b.asset));
    println!(
        "{} non-zero balances (asset, free, locked):",
        balances.len()
    );
    for b in &balances {
        println!(
            "  {:<12} {:>24} {:>24}",
            show(&b.asset),
            show(&b.free),
            show(&b.locked)
        );
    }

    let orders = client
        .get_open_orders(GetOpenOrdersParams::builder().build()?)
        .await?
        .data()
        .await?;
    println!("{} open orders:", orders.len());
    for o in &orders {
        println!(
            "  {} {} {} {} of {} done, price {}, {}, client id {}",
            show(&o.symbol),
            show(&o.side),
            show(&o.r#type),
            show(&o.executed_qty),
            show(&o.orig_qty),
            show(&o.price),
            show(&o.status),
            show(&o.client_order_id)
        );
    }
    Ok(())
}

/// Prints the commission on `symbol` and whether paying it with BNB is on.
pub async fn print_commission(client: &RestApi, symbol: &str) -> Result<(), BoxError> {
    let params = AccountCommissionParams::builder(symbol.to_string()).build()?;
    let commission = client.account_commission(params).await?.data().await?;
    if let Some(c) = commission.standard_commission {
        println!(
            "{symbol} commission: maker {}, taker {}",
            show(&c.maker),
            show(&c.taker)
        );
    }
    if let Some(d) = commission.discount {
        println!(
            "fee discount: on for the account {}, for {symbol} {}, paid in {}, fee x{}",
            show(&d.enabled_for_account),
            show(&d.enabled_for_symbol),
            show(&d.discount_asset),
            show(&d.discount)
        );
    }
    Ok(())
}

/// A field Binance may leave out, as `?` when it did.
pub fn show<T: ToString>(field: &Option<T>) -> String {
    field.as_ref().map_or_else(|| "?".to_string(), T::to_string)
}
