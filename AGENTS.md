You are a Rust expert knowledgeable in formal methods and cryptographic protocol verification.

# Cryptovampire

This repository contains **two** tools (don't confuse them):

- **`cryptovampire2`** — *current* tool (main development focus): a protocol verifier for **computational indistinguishability**. Runs Scheme (`.scm`) input on the `steel` interpreter, using the `golgge` e-graph engine, and turns protocol specs into SMT files for Vampire/Z3/CVC5. Binary: `cryptovampire2`. See `examples/cryptovampire2/`.
- **`cryptovampire`** — the *older* trace-property verifier (`.ptcl` input; the `--exec-pred`, `--pairwise-find-fa`, add-rewrite and `-1`/`-2` model work lives here). It **compiles and works** on `master` (build: `cargo build --release -p cryptovampire`); the binary is `cryptovampire`. See `examples/cryptovampire/`.

See [README.md](README.md) for detailed usage and installation.

## Getting up to speed (read this first)

[`agents/cryptovampire.md`](agents/cryptovampire.md) is a distilled agent knowledge base: how each binary works, the CLI, the `.ptcl`/`.scm` DSLs, how the SMT output (protocoles, `; fa pairs`, `; uf-cma`, …) is shaped, solver practice, known traps/fixes, and the current state of the example corpus. It distinguishes v1 `cryptovampire` from v2 `cryptovampire2` throughout. Read it before doing protocol-verification work in this repo.

## Project Structure

Workspace crates:
- **`cryptovampire2`** — Current tool version (main development focus; scheme/`steel`)
- **`golgge`** — E-graph based reasoning engine (used by `cryptovampire2`; can be modified)
- **`egg`** — Fork of [`egg`](https://github.com/egraphs-good/egg) (do not modify)
- **`cryptovampire`** — Older `.ptcl` tool (trace properties). Builds & runs on `master` (`cargo build --release -p cryptovampire`); most of the recent find/lemma work lives here
- **Supporting crates**: `utils`, `logic_formula`, `cryptovampire_macros`, `cryptovampire_smt`, `quarck`

## Development Guidelines

### Code Quality
- Code must compile: `cargo check` must succeed
- Minimize `cargo clippy` warnings (not strictly required)
- Document all new functions, traits, structs, and modules
- Maintain consistent coding style
- Dead code is acceptable during development

### Testing
Verify changes with the corpus harnesses (the old `crates/cryptovampire2/tests/passing/` path no longer exists — tests moved to the `examples/*` Makefiles):
- **v2 (.scm)**: `make` in `examples/cryptovampire2/`
- **v1 (.ptcl)**: `make` in `examples/cryptovampire/` (content-aware flag dispatch; flaky-but-correct, has 2-attempt retries)

Note: Tests may occasionally fail for non-deterministic reasons; a rerun may help.

## Useful Commands

```bash
# Check compilation
cargo check

# v2 (.scm) corpus harness
cd examples/cryptovampire2 && make

# v1 (.ptcl) corpus harness (needs Vampire/Z3/CVC5 on PATH)
cd examples/cryptovampire && make

# Enable verbose logging
RUST_LOG=trace cargo run --profile debug-optimized -- <args>
```

## Additional Information

- **Logging**: Set `RUST_LOG=trace` for detailed execution logs
- **Profiles**: Use `--profile debug-optimized` for development (optimized but with debug symbols) — but `debug_assertions` stay on, so any internal error hard-panics; **judge provability only with `--release`**
- **SMT Solvers**: Requires Vampire, Z3, or CVC5 for full functionality
- **Test Files**: v1 models at `examples/cryptovampire/*.ptcl`; v2 at `examples/cryptovampire2/*.scm`

## Scheme programing
Use `delimiter-validator` to debug parenthising problems in  scheme.
See `delimiter-validator -h` for the exact parameters to use.

When calling `delimiter-validator -t "scheme" -v -f <file>` it re-outputs the file with `xx: yy->zz: <the line>` where `xx` is the line number, `yy` is how deeply nested the parenthesing is at the begining of the line, and `zz` is the same for the end of the line. 
