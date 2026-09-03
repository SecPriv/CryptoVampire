# Cryptovampire — agent know-how

Working notes distilled from hands-on work on this repo (master, around commits
`514ba734` / `c6c31723`). The purpose of this file is to get a fresh agent up to
speed fast: what the tools are, how they work, how the SMT output is shaped, the
CLI, the `.ptcl`/`.scm` languages, solver practice, known traps, and the current
state of the example corpus.

> **Grounding caveat**: this repo is a moving target (README says documentation
> "is notably mangled between the multiple versions of Cryptovampire"). Treat
> every claim here as a *starting point* — confirm with the commands given
> (`cargo build`, `--help`, a `to-file` + `grep` on the emitted SMT) before
> relying on it. Facts marked "verified" were checked on master at the commits
> above.

---

## 0. There are TWO tools in this repo. Do not confuse them.

| | **v1 `cryptovampire`** | **v2 `cryptovampire2`** |
|---|---|---|
| Purpose | trace-property / protocol equality verifier (the "old" tool, eprint 2024/534 lineage) | computational indistinguishability verifier (the NEW CCS2026 refactor, this is the main focus per AGENTS.md) |
| Input | `.ptcl` files (a custom FOL-ish DSL, `examples/cryptovampire/*.ptcl`) | `.scm` files (full Scheme programs run on the `steel` interpreter, `examples/cryptovampire2/*.scm`) |
| Binary | `cryptovampire` (build: `cargo build --release -p cryptovampire`) | `cryptovampire2` (workspace default-member; `cargo build --release`) |
| Engine | custom parser -> SMT for Vampire/Z3/CVC5 | `golgge` (e-graph "Prolog-like" reasoner) on top of the `egg` fork |
| Status | compiles and works on master (verified); old AGENTS.md claim "does not compile" is **stale** | main development; scheme API documented via docgen/mdBook |

If your task is about `.ptcl` files, `examples/cryptovampire/`, `--pairwise-find-fa`,
`--exec-pred`, or `Makefile` flag dispatch → that's **v1**. If it's about `.scm`,
`steel`, `golgge`, or `cryptovampire2` binary → that's **v2**.

---

## 1. Workspace layout

```
Cargo.toml            default-members = ["crates/cryptovampire2"]   (so a plain cargo build builds v2)
crates/
  cryptovampire/      V1 tool (the .ptcl verifier)   <-- v1 CLI lives here
  cryptovampire2/     V2 tool (scheme, steel)        <-- main dev focus
  golgge/             e-graph reasoning engine (v2)  (may be modified)
  egg/                fork of egraphs-good/egg (do NOT modify)
  quarck/             CowArc etc. helpers
  logic_formula/  cryptovampire_macros/  cryptovampire_smt/  utils/   supporting
examples/
  cryptovampire/      v1 .ptcl corpus + Makefile (the harness)
  cryptovampire2/     v2 .scm corpus + Makefile
docs/                 mdBook + scheme-api (v2 docs; generated scheme-api.md is gitignored)
docker/ experimental/  build / failing|trace|indistinguishability|stateful experiments
```

---

## 2. The v1 tool (`.ptcl`) in detail

### 2.1 What it is

A computationally-sound protocol verifier. You write a protocol (steps,
message building, `find`s, crypto assumptions) as `.ptcl`; the tool turns it
into an SMT problem (FOL, quantified) for Vampire/Z3/CVC5. "Computationally
sound" because the crypto primitives get *axioms* (`euf-cma`, `nonce`, hash
collision-freeness, etc.) rather than being treated as uninterpreted.

Reading flow of a `.ptcl`: `type` · `fun`/`let`-macros · `step`s ·
`assert-crypto` · `lemma`s · `query`. The **query** is the property to prove
(e.g. "reader's output == idealized output"); **lemmas** are user-provided
helper statements that, with `-l`, become separate proof obligations which are
*assumed* when proving the query.

### 2.2 CLI (v1, `crates/cryptovampire/src/cli.rs`)

Global flags (before the subcommand):

| flag | meaning |
|---|---|
| `--pairwise-find-fa` | **experimental, trusted**: emit the pairwise "find-such-that ⇒ FA" axiom. Quadratic in the number of `try find`s. This is what makes find-based add-rewrite proofs possible (mimics squirrel's `fa` tactic). |
| `--exec-pred` | declare a named `exec_pred : Step -> Bool` symbol **and its definitional axiom** derived from the protocol's own steps (⟺ "happens"). Needed whenever `.ptcl` mentions `exec_pred(...)`. |
| `--eval-rewrite` / `--crypto-rewrite` / `--vampire-subterm` / `--skolemnise` / `--no-preprocessing` | variant encodings (not all SMT-standard) |
| `--find-exhaustiveness`-ish family | experimental find axioms |
| `--disallow-shadowing` | forbid variable shadowing (off by default; v1 lets variables shadow any symbol) |

Subcommands:
- `auto` (**default**): run the solvers in a portfolio and retry, "learn from
  each run". Args (after the subcommand): `-l/--lemmas`, `-n/--num-of-retry`
  (default 5 tries; 0 = infinite), `-t/--timeout` (default **1 s**), `--solver-file-debug DIR`,
  `--ignore-lemmas`, `--vampire-location`/`--z3-location`/`--cvc5-location`,
  `--disable-vampire`/`--disable-z3`/`--disable-cvc5`.
- `to-file`: only build the SMT files, don't run solvers. Args: `-o FILE|DIR`,
  `-l` (emit the per-protocole files into a DIR), `--cvc5` (query as
  `(assert (not ...))` instead of `(assert-not ...)`).

Working invocation for find-based proofs (verified):
```
cryptovampire examples/cryptovampire/mw-add-rewrite-2.ptcl \
  --exec-pred --pairwise-find-fa auto -l -t 15 -n 2
```
Global flags go **before** `auto`; subcommand args (`-l -t -n ...`) go after.

**Profiles matter.** `--profile debug-optimized` is fast but keeps
`debug_assertions` → any internal error/assert **hard-panics** (rc 101), which
has misled debugging before. **Judge provability only with `--release`.**

### 2.3 The `.ptcl` DSL (quick dictionary)

- `type index;` — protocol indices (sessions, rows).
- `fun f(Message,Message):Message` — uninterpreted functions.
- `let name!(a,b) = <expr>` — macros; evaluated/lowered at parse time.
- `step s(i:index) { guard } { output }` — an honest protocol step producing a message.
- `try find (i:index, j:index) such that { cond } then { out } else { ko }` —
  adversarial decryption/find construct.
- `lemma forall (…) {( guard => (body) )}` — helper to prove.
- `query forall (…) {( … == … )}` — the property.
- `assert forall (…) { … }` — model-level axioms (e.g. `sel1of2/sel2of2`).
- `assert-crypto euf-cma hash verify;` / `assert-crypto nonce;` — crypto axiom selection.
- `cond!(...)` — frequently renders to vacuous `{true}`; `msg!(s i)` — the message emitted by step `s` at index `i`.
- `s_lt` vs `lt` — strict orderings; in some models the find condition must be
  spelled with `s_lt` (mirroring how the tool lowers `fdst!`) rather than `lt`.
- **`exec_pred`** — only defined when `--exec-pred` is passed; otherwise it is
  an *uninterpreted* atom (a proof using it without the flag is unsound).
- **one-index vs two-index**: `-1` models declare `key(i)`, `id(i)` (one session
  index); `-2` models declare `key(i,j)`, `id(i,j)` (session + row). This single
  difference has big proof consequences (§5).

### 2.4 SMT generation & the protocoles

With `-l` and **L lemmas**, the tool generates **L+1 protocoles**:
`0.smt .. (L-1).smt` each proves one lemma (in file order), and `L.smt` is the
**query with all lemmas asserted**. (Hence 1 lemma ⇒ 2 files `0/1.smt`;
2 lemmas ⇒ 3 files `0/1/2.smt`.) `to-file -l -o DIR` writes them.

Sections inside each `.smt` (grep `^; `):
```
; ordering   ... step/≤/lt axioms
; evaluate   ...
; fa pairs   ... the pairwise-find-fa bridge  (only with --pairwise-find-fa)
; crypto     ... generic crypto axioms
; uf-cma     ... many-one/many-to-many reduction axioms   (with assert-crypto euf-cma)
; nonce      ... uniqueness axioms
; user asserts ... the lemmas (and model asserts)
; query      ... the negated property (assert (not ...))
```
- The **fa-pairs** section is where the find-bridge lives. Its two clauses (for
  a reader decrypt vs an idealized find) look like:
  - backward: `(=> honest (verify ...))` where `honest` is the find's
    search condition as a conjunction (e.g. 6 conjuncts: `input(tag)==nr`,
    two `sel*of2` matches, `exec_pred(reader2)`, two `s_lt` orderings).
  - forward: `(=> (verify ...) (exists ((t index)) honest))`.
  `exec_pred` inside `honest` is *itself a conjunct*.
- **Query wrapper** (verified on `to-file` output): the negated query is emitted
  as standard `(assert (not ...))` — `to-file` never emits Vampire's non-standard
  `assert-not`. (The `--cvc5` flag on `to-file` only disables the deprecated
  `assert-ground`.) Debug artifacts from `auto --solver-file-debug DIR` get
  per-solver filenames (e.g. `cryptovampire-vampire*.smt`); any wrapper
  differences are semantically equivalent.
- **Diagnostics that worked**: the number of `(exists` blocks and the number of
  asserts in `; uf-cma` are sensitive to model shape. E.g. a bloated one-index
  encoding had 69 `(exists` vs 10 for two-index in protocol-2, and 59 uf-cma
  asserts vs 3 — a reliable fingerprint for "the encoding exploded" vs "clean".

### 2.5 Solver practice

- Portfolio (auto) tries vampire, z3, cvc5 and "learns". cvc5 and vampire
  (portfolio mode) typically outperform z3 on these problems.
- **Timeouts**: `-t 10`..`-t 20` is plenty for problems that go through; 40 s is
  "way too much". Use the tool's `-t` (vampire) rather than wrapping with the
  `timeout` binary. When looping over raw SMT files externally: cvc5 `--tlimit`,
  z3 `-T`, vampire `-t` (not the `timeout` shell command).
- **Flakiness**: results are occasionally non-deterministic; rerun (the repo
  README says exactly this). The v1 Makefile retries twice for this reason.

### 2.6 Known traps (all hit & solved in real sessions)

1. **Parser silently dropping args** (FIXED in `514ba734`): `signature.args()
   .zip(provided)` truncates to the shorter list, so an application with *more*
   args than declared (e.g. `id(i,t)` against a one-index `id(i)`) silently
   became `id(i)` and produced a *false* `∀`-lemma. It is now a hard, located
   error: `too many arguments: got N, M extra argument(s) would be dropped
   (declared arity is [..])`. Symptom to look for: a lemma that is
   unprovable *and* has a bound variable never occurring in the body.
2. **`PestLocation` rendering bug** (FIXED in `514ba734`): the location stored
   only `span.as_str()` while `start/end` are offsets into the whole input, so
   any `pest::Span`-kind error printed `!!! FAILED TO BUILD SPAN !!!`. Fix:
   store `span.get_input()`. Use `ASTLocation::render_with` / `bail_at!` for
   located errors; also, `--exec-pred`/lemma-inactivity parse warnings were
   threaded this way.
3. **debug-optimized panics** — build with `--release` before judging proofs.
4. **one-index forward hardness** — see §5.
5. **Parenthesis debugging**: use the external `delimiter-validator
   -t scheme -v -f <file>` to see per-line nesting depth (`xx: yy->zz: line`).

### 2.7 The v1 corpus & harness (`examples/cryptovampire/`)

Families: `basic-hash`, `ddh`-family, `euf_key_secrecy`, `canauth`, `feldhofer`
& `feldhofer-ind`, `hash-lock`, `mw`, `lak-tag` — plus the **add-rewrite**
models (`mw-add-rewrite-*`, `lak-tag-add-rewrite-*`) that prove the
reader's real output equals its idealized `fdst2!` output.

- `-2` models = **two-index**; these prove fast (1 try at ~15 s) with
  `--exec-pred --pairwise-find-fa auto -l`.
- `-1` models = **one-index**; *correct* (arity-clean, fa-faithful two-lemma
  bridge) but the fa-*forward* `c1 => ∃t.honest` requires witness
  reconstruction the solvers do not close at 10–30 s (tested: `-t 30 -n 3`
  fails 3/3). They are **skipped** by the Makefile; use `-2` for the fast path.
- `ddh-*-2-1`, `ddh-*-s-2-1/2` use `exec_pred` *in the query* → they **require
  `--exec-pred`** or the proof is vacuous/unsound.
- `feldhofer-ind-*` use `exec_pred` + needs `--pairwise-find-fa`.

The `Makefile` dispatches flags **content-aware**, not by name pattern alone:
`grep -q "exec_pred("` ⇒ `--exec-pred`; `grep -q "^lemma"` ⇒ `-l`;
add-rewrite / feldhofer-ind glob ⇒ `--pairwise-find-fa`. Default timeouts
`PLAIN_TIMEOUT=15`, `PAIRWISE_TIMEOUT=20` (override with `TIMEOUT=...`), 2
attempts, `*-add-rewrite-1.ptcl` skipped. It is considered **flaky-but-correct**
(the user plans a better dispatch later). Some models (e.g. `mw-2-ra`) are
intrinsically flaky — README-sanctioned rerun.

### 2.8 How to work a proof problem (pattern that worked)

1. Build release: `cargo build --release -p cryptovampire`.
2. `to-file -l -o DIR` the model; inspect `grep '^; '` sections and the
   `(exists`/assert counts to see whether the encoding exploded.
3. To understand a hypothetical bridge/lemma: compare the `; fa pairs` clauses
   with the `; user asserts` lemmas *in the same file*, α-renaming `iX<n>`→`V`,
   stripping `evaluate_cond`/`evaluate_msg` wrappers, and `and`-flattening into
   sorted conjunct sets. Only trust cvc5/Z3/Vampire *verdicts* after confirming
   the shapes match.
4. Prove with `auto -l -t <10..20> -n 2+`; use `RUST_LOG=trace` for tool-internals.

---

## 3. v2 (`cryptovampire2`) — the current tool (distinct!)

- Runs a **Scheme interpreter (`steel`)**; `.scm` inputs are full Scheme programs;
  `cryptovampire2 <file> [args]`, `-i` interactive, `help` lists Rust bindings +
  scheme wrappers (`@doc` blocks).
- Reasoning engine is **`golgge`** (e-graph based, "facts are e-classes of an
  e-graph", Prolog-ish rules) on the **`egg`** fork; `quarck` is CowArc helpers.
- `default-members` — `cargo build --release` / `nix build` produce
  `cryptovampire2`; `nix build .#doc` builds docs.
- Docs: `Makefile` `html` target → `docs/scheme-api.md` + mdBook `out/book`;
  docgen at `crates/cryptovampire2/scheme/docgen.scm`.
- **Tests**: the harness is `examples/cryptovampire2/Makefile` (runs the `.scm`
  corpus, results CSV to `results/`). Note: AGENTS.md/README still reference
  `crates/cryptovampire2/tests/passing/` — that path **no longer exists** and
  the integration test file is commented out; don't go looking for it.
- Quick smoke test: `cargo run --profile debug-optimized --
  examples/cryptovampire2/basic-hash.scm`-style (but judge on release).

---

## 4. Repo hygiene & conventions (for the agent doing the work)

- **Commit discipline**: the user says commit only when asked; commits carry the
  co-author trailer
  `Co-authored-by: <Model Name> (<Company>, <Provider>) <ai-assistant@pi>` (check
  the model identity each session). Keep working tree changes small and reviewable.
- **Worktrees**: only the main repo `/home/simon/cryptovampire` should exist;
  delete throwaway worktrees to keep the model tidy (all branches/commits stay
  in the object store).
- **Remote sync**: there is a host sync via `/mnt/host/cryptovampire`
  (origin/remote provide the pull source used to advance `master`).
- Logging: `RUST_LOG=trace` for verbosity. `Makefile` in `examples/cryptovampire`
  owns the v1 corpus; `delimiter-validator` for parens.
- Preference notes from real sessions: user iterates on timeouts (10–20 s enough);
  labels careful claims vs data points; flags wrong inferences; likes
  content-based (not name-based) dispatch; dislikes long solver waits.
