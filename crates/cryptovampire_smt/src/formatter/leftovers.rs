use std::io::{self, Read};

use super::format_term;
use crate::formatter::parser::parse_program;

/// Formats an SMT-LIB string.
///
/// # Arguments
///
/// * `input` - A string slice that holds the SMT-LIB content.
///
/// # Returns
///
/// A `Result` containing the formatted string or an error message.
pub fn format_smtlib(input: &str) -> Result<String, String> {
    let terms = parse_program(input)?;
    let mut result = String::new();
    for term in terms {
        result.push_str(&format_term(&term, 0));
        result.push('\n');
    }
    Ok(result)
}

#[allow(dead_code)]
fn main() {
    let mut input = String::new();
    if io::stdin().read_to_string(&mut input).is_err() {
        eprintln!("Failed to read from stdin");
        return;
    }

    match format_smtlib(&input) {
        Ok(formatted) => print!("{formatted}"),
        Err(e) => {
            eprintln!("{e}");
            print!("{input}"); // Print original on error
            std::process::exit(1);
        }
    }
}
