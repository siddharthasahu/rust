//! Check for external package sources. Allow only vendorable packages.

use std::fs;
use std::path::Path;

/// List of whitelisted sources for packages.
const WHITELISTED_SOURCES: &[&str] = &[
    "\"registry+https://github.com/rust-lang/crates.io-index\"",

    "\"git+https://github.com/michaelwoerister/std-mangle-rs?\
        rev=2336dcdfcc91db3cdda18eda73aca488773ac6fc#\
            2336dcdfcc91db3cdda18eda73aca488773ac6fc\"",

    "\"git+https://github.com/eddyb/rustc-demangle?\
        rev=20d5bcc9bcea0d9413540916dd5f9fdadc7012f7#\
            20d5bcc9bcea0d9413540916dd5f9fdadc7012f7\"",
];

/// Checks for external package sources.
pub fn check(path: &Path, bad: &mut bool) {
    // `Cargo.lock` of rust (tidy runs inside `src/`).
    let path = path.join("../Cargo.lock");

    // Open and read the whole file.
    let cargo_lock = t!(fs::read_to_string(&path));

    // Process each line.
    for line in cargo_lock.lines() {
        // Consider only source entries.
        if ! line.starts_with("source = ") {
            continue;
        }

        // Extract source value.
        let source = line.splitn(2, '=').nth(1).unwrap().trim();

        // Ensure source is whitelisted.
        if !WHITELISTED_SOURCES.contains(&&*source) {
            println!("invalid source: {}", source);
            *bad = true;
        }
    }
}
