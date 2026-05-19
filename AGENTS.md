You are a Rust expert knowledgeable in formal methods and cryptographic protocol verification.

# Cryptovampire

A protocol verifier for computational indistinguishability that turns protocol specifications into SMT files for theorem provers (Vampire, Z3, CVC5). It uses `golgge`, a Prolog-like engine where facts are e-classes of an e-graph.

See [README.md](README.md) for detailed usage and installation instructions.

## Project Structure

Workspace crates:
- **`indistinguishability`** — Current tool version (main development focus)
- **`golgge`** — E-graph based reasoning engine (can be modified)
- **`egg`** — Fork of [`egg`](https://github.com/egraphs-good/egg) (do not modify)
- **`cryptovampire`** — Legacy version (does not compile, ignore)
- **Supporting crates**: `utils`, `logic_formula`, `cryptovampire_macros`, `cryptovampire_smt`, `quarck`

## Development Guidelines

### Code Quality
- Code must compile: `cargo check` must succeed
- Minimize `cargo clippy` warnings (not strictly required)
- Document all new functions, traits, structs, and modules
- Maintain consistent coding style
- Dead code is acceptable during development

### Testing
Verify changes with integration tests:
- **Quick test** (seconds): `cargo run --profile debug-optimized -- crates/indistinguishability/tests/passing/basic-hash.scm`
- **Comprehensive test** (~15 minutes): `make` in `crates/indistinguishability/tests/passing/`

Note: Tests may occasionally fail for non-deterministic reasons; a rerun may help.

## Useful Commands

```bash
# Check compilation
cargo check

# Run quick integration test
cargo run --profile debug-optimized -- crates/indistinguishability/tests/passing/basic-hash.scm

# Enable verbose logging
RUST_LOG=trace cargo run --profile debug-optimized -- <args>

# Run comprehensive test suite
cd crates/indistinguishability/tests/passing && make
```

## Additional Information

- **Logging**: Set `RUST_LOG=trace` for detailed execution logs
- **Profiles**: Use `--profile debug-optimized` for development (optimized but with debug symbols)
- **SMT Solvers**: Requires Vampire, Z3, or CVC5 for full functionality
- **Test Files**: See `crates/indistinguishability/tests/passing/` for example protocol specifications
