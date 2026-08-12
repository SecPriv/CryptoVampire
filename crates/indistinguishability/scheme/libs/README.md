# Scheme libraries

This folder contains many of the builtin libraries here is ease interacting with the bindings.

Unfortunatly, `steel` does not seems to support documentation for things like macros or re-export, hence why the `help` function returns nothing on them. Documentation for such things is inlined in the files.

## Documentation

- Functions carry their docs in `@doc` blocks, so `(help name)` works for all
  the callable functions of these libraries.
- Macros and plain values (sorts, structs) cannot hold `help` docs; their
  documentation lives in the `syntax-docs` / `types-docs` registries in
  `doc.scm`, next to the `cv-help` helper used by the `@doc` blocks.
- `../docgen.scm` assembles `docs/scheme-api.md` from both sources.  Regenerate
  from the repository root with:

  ```sh
  cargo run --release -- crates/indistinguishability/scheme/docgen.scm
  ```
