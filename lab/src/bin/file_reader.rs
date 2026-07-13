use lab::FrdCandle;
use std::fs::{self, File};
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::time::Instant;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let dir = Path::new("lab/data/files/futures/frd");

    // Collect only the .txt data files
    // sorted for a deterministic run order.
    let mut files: Vec<_> = fs::read_dir(dir)?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "txt"))
        .collect();
    files.sort();

    println!("Found {} data files in {}", files.len(), dir.display());

    let start = Instant::now();
    let mut total_lines: u64 = 0;

    // Reused buffer for each record.
    let mut line = String::new();
    for path in &files {
        let mut reader = BufReader::new(File::open(path)?);

        let file_start = Instant::now();
        let mut lines: u64 = 0;
        let mut last: Option<FrdCandle> = None;

        loop {
            line.clear();
            let n = reader.read_line(&mut line)?;
            if n == 0 {
                break;
            }

            let candle =
                FrdCandle::from_frd_csv_line_unchecked(&line).map_err(|e| e.to_string())?;
            lines += 1;
            last = Some(candle);
        }

        total_lines += lines;
        println!(
            "{:<20} {:>8} lines in {:>10?}  last: {:?}",
            path.file_name().unwrap().to_string_lossy(),
            lines,
            file_start.elapsed(),
            last.map(|c| c.timestamp()),
        );
    }

    let duration = start.elapsed();
    println!("---");
    println!(
        "Parsed {} lines across {} files in {:?}",
        total_lines,
        files.len(),
        duration
    );

    Ok(())
}
