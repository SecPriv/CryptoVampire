# CryptoVampire

CryptoVampire is an automated computationally sound protocol verifier. It turns a protocol specification into an `smt` file to be proven by some other FOL theorem prover

## Compiling

### `cargo`

As for all `rust` projects you can compile or run them using cargo:

```bash
# compile
cargo build

# run
cargo run -- <args>
```

Note that `cargo` is configured to write to `"/tmp/ccsa/build/dir"`. To overwrite this behavior, you can use the `--target-dir <`dir>` argument to cargo.

### `nix`

This project is set up to work with `nix` as well.

#### `nix develop`

`nix develop` brings you in a shell with all the tools available (`cargo`, `vampire`, `z3`, `cvc5`, ...). Note that we couldn't get the modified version of vampire to compile using `nix`, therefore, to use it, you will have to build it yourself from [`vampire`'s repository](https://github.com/vprover/vampire/tree/ccsa).

#### `nix build` & `nix run`

Work as expected.

## Usage

**Usability is known to be somewhat poor at the moment**

To get all the options use `cryptovampire --help`:
```
$ cryptovampire --help
Usage: cryptovampire [OPTIONS] [FILE]

Arguments:
  [FILE]
          

Options:
  -o, --output-location <FILE|DIR>
          output location
          
          This should be a file unless `lemmas` is set
          
          [default: /dev/stdout]

  -l, --lemmas
          uses the lemmas
          
          It will generate multiples files lemma_0: output_location/0.smt ... lemma_n: output_location/n.smt query: output_location/n+1.smt
          
          The order of the lemma is determined based on their order in the file. The files are generated such that lemma_0 to n are assertion in lemma_n+1's file. Same for the query

      --eval-rewrite
          use rewrite in evaluate
          
          NB: not in the smt standard

      --crypto-rewrite
          use rewrite in crypto axioms
          
          NB: not in the smt standard

      --vampire-subterm
          use vampire's special subterm
          
          NB: not in the smt standard, requires modified vampire

      --assert-theory
          use vampire's 'assert-theory'
          
          NB: not in the smt standard, requires vampire

  -s, --skolemnise
          skolemnise before passing to sat solver

  -p, --preprocessing
          preprocess subterm of input do as much preprocessing as possible

      --legacy-evaluate
          add (|x1| == |x1'|)/\.../\(|xn| == |xn'|) => |f(x1,...,xn)| == |f(x1',...,xn')| axioms

      --no-bitstring
          remove the bitstring functions, evaluation must then be handeled by somthing else

      --cvc5
          use `(assert (not ...))` instead of `(assert-not ...)` for the query and no `assert-ground` either

      --assert-ground
          *deprecated* use vampire's `assert-ground`. Requires modified vampire

  -n, --no-symbolic
          deactivate subterm and optimises evaluates
          
          NB: the program will crash it subterms are required somewhere

  -a, --auto-retry
          Use vampire cryptovampire's builtin runner
          
          This opens (and activates by default) the ability to automatically learn about a given vampire run. This is incompatible with lemmas. *NB*: This deactivates AVATAR

      --vampire-location <VAMPIRE_LOCATION>
          Location of the `vampire` executable
          
          [default: vampire]

      --num-of-retry <NUM_OF_RETRY>
          Upper bound of how many tries on the vampire runner
          
          0 for an infinite number of tries
          
          [default: 5]

      --vampire-exec-time <VAMPIRE_EXEC_TIME>
          Vampire execution time
          
          [default: 1]

      --vampire-smt-debug <VAMPIRE_SMT_DEBUG>
          A folder to put temporary smt files

      --ignore-lemmas
          Deactivate the lemmas.
          
          CryptoVampire will ignore the lemmas as a whole and work as if there weren't any. This is used for testing purposes.

  -h, --help
          Print help (see a summary with '-h')

  -V, --version
          Print version

```

**Notes**
 - To get a fully `smtlib` compliant file, use the `--cvc5` option. Otherwise, the tool will aim for files readable by the latest released `vampire` and `z3`. Other options make the tool aim for specific versions of `vampire`.
 - experimentally `-pn` works the best. `-p` is almost always required to prove a protocol.

### Example
You can find an example in the [test](./test/) directory

```bash
cryptovampire test/basic-hash-1.ptcl -pn | vampire --input_syntax smtlib2
```

Note that the input language is far from perfect. One of its most notable problems is the poor support of infix operators. Thus to use infix operators (e.g., `=` or `&`) please make extensive use of parenthesis. (e.g., use `(a = b)` instead of `a = b`)

The tool will try to point out any mistakes while reporting where they come from as best as it can.

Parsing relies on [`pest`](https://pest.rs/). You can find the grammar in [grammar.pest](./cryptovampire/grammar.pest).

# Structure of the Tool

The tool is split into 3 crates:
 - **[`cryptovampire-lib`](./cryptovampire-lib/)**: This is the core of the tool.
 - **[`cryptovampire`](./cryptovampire/)**: This handles command-line arguments and parsing. This can be compiled into a binary and is the user-facing part of cryptovampire.
 - **[`utils`](./utils/)**: Various utility functions that are not specific to `cryptovampire` but where made during its development.
