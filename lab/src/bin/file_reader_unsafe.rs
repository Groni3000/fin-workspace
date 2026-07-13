use lab::{FrdCandle, OffsetCache};
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
    let mut line_bytes = Vec::new();
    // One offset cache across all files: a date change (even backwards, when a
    // new contract file starts) just triggers a recompute, which is correct.
    let mut tz_cache = OffsetCache::new();
    for path in &files {
        let mut reader = BufReader::new(File::open(path)?);

        let file_start = Instant::now();
        let mut lines: u64 = 0;
        let mut last: Option<FrdCandle> = None;

        loop {
            line_bytes.clear();
            let n = reader.read_until(b'\n', &mut line_bytes)?;
            if n == 0 {
                break;
            }

            let candle = FrdCandle::from_frd_csv_line_unchecked(&line_bytes, &mut tz_cache)
                .map_err(|e| e.to_string())?;
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
