//! Nonce freshness

declare_trace!($"nonce_fresh");

/// Re-exports the `FreshNonce` struct, which represents a rule for handling fresh nonces.
pub use deduce_fresh::FreshNonce;
/// Provides rules for deducing fresh nonces.
mod deduce_fresh;

/// Re-exports the `Nonce` struct, used for searching for nonces.
pub use searcher::Nonce;
/// Provides functionalities for searching for nonces.
mod searcher;

/// Re-exports the `mk_no_guessing_smt` function, which generates SMT formulas for no-guessing assumptions.
pub use smt_no_guessing::mk_no_guessing_smt;
/// Provides SMT-related functionalities for no-guessing assumptions.
mod smt_no_guessing;

#[cfg(test)]
mod test;
