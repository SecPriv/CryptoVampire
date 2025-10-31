use std::path::PathBuf;

use clap::{Parser, command};
use steel_derive::Steel;

/// A computationnally sound automated cryptographic protocol verifier based on the CCSA.
#[derive(Parser, Debug, Clone, Steel)]
#[command(author, version, about)]
pub struct Config {
}