# Cryptovampire

## Structure of the project:
This project is split in multiples crates
 - `cryptovampire` is the old version of the tool, no longer compiles, can be ignored
 - `indistinguishability` is the *current* version of the tool, where most of the work must be done
 - `golgge` is the engine used for `indistinguishability`. Can be modified
 - `egg` is a fork of [`egg`](https://github.com/egraphs-good/egg) inlined in the repository, shouldn't be modified
 - the rest are supporting crates

## General Instructions
 - The code should compile (i.e., `cargo check` is successful)
 - `cargo run -- crates/indistinguishability/tests/basic-hash.scm` succeed and it's last returned line should be `success`
 - It's better if `cargo clippy` has the least amount of warning, but it is not a requirement
 - all new function, trait, stuctures,... should be documented
 - the code itself should be documented
 - try to keep the coding style consistent

## Other miscelenious informations
 - using `RUST_LOG=Trace` can enables logging and give (much more) information on the run.