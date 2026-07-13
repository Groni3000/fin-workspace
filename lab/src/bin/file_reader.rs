use lab::FrdCandle;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::time::Instant;
use tradeprim::price::Price;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let quotes = File::open("lab/data/files/futures/frd/RB_Z25_1min.txt")?;
    // let mut reader = BufReader::with_capacity(64 * 1024, quotes);
    let mut reader = BufReader::new(quotes);

    // Compare buffer size performance implications
    let start = Instant::now();

    let mut line = String::new();
    let mut counter = 0;
    let each_n = 20_000;
    loop {
        match reader.read_line(&mut line) {
            Ok(n) => {
                if n == 0 {
                    break;
                }
            }
            Err(err) => println!("{:?}", err),
        }

        // let candle = FrdCandle::from_frd_csv_line(&line).unwrap();
        let candle = FrdCandle::from_frd_csv_line_unchecked(&line).unwrap();
        counter += 1;
        if counter % each_n == 0 {
            println!("Processed {} lines", counter);
            println!("Last processed: {}", line);
            println!("Last candle: {:?}", candle);
            println!(
                "Last close: {}",
                (candle.close().value() as f64 / Price::SCALE as f64)
            );
        }

        line.clear();
    }

    let duration = start.elapsed();
    println!("Time elapsed: {:?}", duration);
    println!("Processed {} lines", counter);

    Ok(())
}
