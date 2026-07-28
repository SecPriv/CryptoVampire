# CryptoVampire

**NB**: This repository is currently being refactored for CCS2026. Documentation is notably mangled between the multiple versions of Cryptovampire.

## Cryptovampire for indistinguishability

This is the new `cryptovampire`. Its code base is the [`indistinguishability`](./crates/indistinguishability) crate.
Currently it produces `indistinguishability` binaries.

### Installation / Building
#### `cargo`
```bash
$ cargo build --release
```

You will find the binary in `/tmp/ccsa/build/dir/release/indistinguishability`.

debug builds are significantly slower and also force tracing on.

#### `nix`
```bash
$ nix build
```

You will find the binary in `./result/bin/indistinguishability`.

### Usage
In general running `indistinguishability --help` brings out all the options.

`indistinguishability` runs a scheme interpreter (via [`steel`](https://github.com/mattwparas/steel)) and expects to be manipulated through there. Protocols are defined in scheme and options can be overwritten there as well. This also means that `indistinguishability`'s input files are fully fledged scheme programs.

```
indistinguishability <file> <args>
```
executes `<file>` omitting that argument will make the tool listen from stdin.

The `-i` option starts an interactive shell. Notably the `help` command returns some documentation for the rust bindings. Unfortunately, it is unclear how to activate this for our own scheme wrappers.


## Cryptovampire for Trace properties

**NB**: The tool *should* be in a working state. But changes to downstream crates for the CCS submission may have broken things in a non-obvious way. If any issues arise they will be fixed shortly.

[CryptoVampire](https://eprint.iacr.org/2024/534) is an automated, computationally sound protocol verifier. It turns a protocol specification into an `smt` file to be proven by some other FOL theorem prover.

It can run standalone (see [Usage](#usage)) or through [`squirrel`](https://squirrel-prover.github.io/) (see [Squirrel](#squirrel)).

### Installation

#### `cargo`
CryptoVampire is a plain `rust` project, so it can be installed via [`cargo`](https://doc.rust-lang.org/cargo/getting-started/installation.html).

```bash
$ cargo install --git https://github.com/SecPriv/CryptoVampire -p cryptovampire
```
You can use the same command to update.

#### [`nix`](https://nixos.org/)
This repository is a `nix` [`flake`](https://nixos.wiki/wiki/flakes), therefore:

```bash
# get a shell with cryptovampire
$ nix shell github:SecPriv/CryptoVampire#cryptovampire
```

#### From source

##### `cargo`
Then, as with all `rust` projects, you can compile or run it using cargo:

```bash
# compile
cargo build --release -p cryptovampire

# run
cargo run --release -p cryptovampire -- <args>
```

**NB: Windows and `squirrel` users:**
For this project, cargo will write to `/tmp/ccsa/build/dir`, thus the executable will be built in `/tmp/ccsa/build/dir/release/cryptovampire` (resp. `/tmp/ccsa/build/dir/debug/cryptovampire`) when the `--release` flag was given (resp. was *not* given) to `cargo`. You can override the location of the build directory using the `--target-dir <dir>` flag to cargo.

**NB: `release` vs `debug`**
Compiling with `debug` makes the program very eager to crash instead of trying to recover. Especially when reading `vampire`'s output this can lead to crashes that are recovered from in `--release` mode.

##### `nix`

This project is set up to work with `nix` as well.

###### `nix develop`

`nix develop` brings you into a shell with all the tools available (`cargo`, `vampire`, `z3`, `cvc5`, ...). Note that we couldn't get the modified version of vampire to compile using `nix`; therefore, to use it, you will have to build it yourself from [`vampire`'s repository](https://github.com/vprover/vampire/tree/ccsa).

##### `nix build .#cryptovampire`

Works as expected.

### Usage

**Usability is known to be somewhat poor at the moment.**

To use `cryptovampire` effectively, you will need SMT solvers like (in order of preference) [`vampire`](https://github.com/vprover/vampire), [`z3`](https://github.com/Z3Prover/z3), `cvc5`, or any other [`smtlib 2.6`](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) compliant first-order theorem prover.

`cryptovampire` can run on its own with `vampire`, `z3` and it can learn some information about the runs done with `vampire` (see [`auto`](#auto)).

#### Command line
To get the specifics of the command line interface, run:
```bash
$ cryptovampire --help
```

By default, `cryptovampire` runs in [`auto`](#auto) mode with all the solvers it can find in the path, taking a file from the standard input and outputting to the standard output. It may write temporary files wherever the operating system tells it to.

Use the `auto` command to run in [auto](#auto) mode; run `cryptovampire auto --help` for more information and see the section [auto](#auto).

To export to an `smt` file (or possibly many `smt` files), use the `to-file` command. See the [to-file](#to-file) section and run `cryptovampire to-file --help` for more information.

##### `auto`
To get the specifics of the command line interface, run:
```bash
$ cryptovampire auto --help
```

In this mode, `cryptovampire` attempts to prove everything without user intervention by calling the solvers on its own with (somewhat) optimized files.

- `--timeout`: sets the timeout for all the solvers (default 1s)
- `--num-of-retry`: `cryptovampire` can learn how to apply the cryptography from runs performed by `vampire`. This parameter sets how many times it tries (default `5`).
- `--lemmas`: with this flag, `cryptovampire` will attempt to prove the `lemma` formula of the input file and subsequently use it for the final proof. If any of the lemmas fail, `cryptovampire` fails. When this option is not activated, `cryptovampire` still uses the lemmas as hints to apply cryptographic axioms.

**NB**:
- `cryptovampire` fails if a solver terminates for an unexplainable reason (e.g., a syntax error). This can cause problems when using older versions of the solver that do not yet support some of their own extensions to the `smt` format. This is notably the case with older versions of `vampire`.

##### `to-file`
To get the specifics of the command line interface, run:
```bash
$ cryptovampire to-file --help
```

Renders one (or many when activating the lemmas) `smt` file. Without the `-o` flag, it outputs to the standard output, letting the user pipe the result into the solver of their choice.

**NB**:
- To get a fully `smtlib`-compliant file, use the `--cvc5` option. Otherwise, the tool will aim for files readable by the latest released `vampire` and `z3`. Other options make the tool aim for specific versions of `vampire`.

#### `squirrel`
**NB**: mostly broken currently. (`squirrel` considers a `cryptovampire` success as a failure)

It is possible to run `cryptovampire` from the [`squirrel`](https://squirrel-prover.github.io/) proof assistant. It will then use the [`auto`](#auto) mode with default parameters.

To use it, you need to compile `squirrel` using the `cryptovampire` branch (available [here](https://github.com/puyral/squirrel-prover)) and have the `cryptovampire` executable either available on your `PATH` or pointed to by the environment variable `CRYPTOVAMPIRE_EXECUTABLE`.

You will then get access to the `cryptovampire` tactic. You can also add the optional parameters `nt` and `t` to control `--num-of-retry` and `--timeout`, respectively.

**NB**:
- The solvers need to be available in the path.
- It can *only* work on local goals.
- Like the `smt` tactic, it doesn't look in the environment for lemmas already proven or admitted axioms. You will need to use the `use` tactic to explicitly make them available to `cryptovampire`.
- The macros `exec` and `frame` are not supported (yet). The `att` function isn't either.
- `cryptovampire` casts everything to either `index` or `message`, therefore weirder uses of those sorts will lead to failures.
- It does support biprocesses and will try to check both sides of the biprocess.
- Unlike `smt`, it can use cryptography.
- It doesn't support higher-order functions; it will fail if it encounters any.
- for testing purposes, setting `SQUIRREL_CRYPTOVAMPIRE_FORCE_QUANTUM` to anything declares the tactic as quantum sound.

Please report any error that isn't `"ran out of tries"`.

#### Files
You can see example files in the [tests](./tests/) directory (all those ending in `.ptcl`). In particular the files in [test/nix](./tests/nix/), are tested by the CI/CD, so they should :tm: be fully working.

Infix functions don't really exist (yet); therefore, the parser uses parentheses to fake them (e.g., you need to use `(a = b)` instead of just `a = b`).

The tool will try to point out any mistakes while reporting where they come from as best as it can.

**NB**:
- Parsing relies on [`pest`](https://pest.rs/) (for better or worse). You can find the grammar in [grammar.pest](./cryptovampire/grammar.pest).
