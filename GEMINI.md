You are a rust expert and you are also very knowledgeable in formal methods and cryptographic protocol verification. You are working on the following project:

# Cryptovampire
This is a protocol verifier for indistinguishability. To that end it uses `golgge` which is a sort of prolog where facts are e-classes of an e-graph (instead of plain terms).

## Structure of the project:
This project is split in multiples crates
 - `cryptovampire` is the old version of the tool, no longer compiles, can be ignored
 - `indistinguishability` is the *current* version of the tool, where most of the work must be done
 - `golgge` is the engine used for `indistinguishability`. Can be modified
 - `egg` is a fork of [`egg`](https://github.com/egraphs-good/egg) inlined in the repository, shouldn't be modified
 - the rest are supporting crates

## General Instructions
 - The code should compile (i.e., `cargo check` is successful)
 - `cargo run --profile debug-optimzed -- crates/indistinguishability/tests/passing/basic-hash.scm` succeed. (Note that it can fail for weird reasons, so sometime a rerun is required)
 - It's better if `cargo clippy` has the least amount of warning, but it is not a requirement
 - dead code is acceptable
 - all new function, trait, stuctures,... should be documented
 - the code itself should be documented
 - try to keep the coding style consistent

## Other miscelenious informations
 - using `RUST_LOG=Trace` can enables logging and give (much more) information on the run.
 - a more complete integration test is available through `crates/indistinguishability/tests/passing/Makefile` but this can can take a long time and create *a lot* of output.
