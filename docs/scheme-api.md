# CryptoVampire Scheme API

Reference of the `cryptovampire/*` scheme libraries.
Generated from the `help` doc tables and the `syntax-docs`/`types-docs`
registries in `cryptovampire/doc`.

Regenerate with:

```sh
cargo run --release -- crates/indistinguishability/scheme/docgen.scm
```

## Sorts & types

### Nonce

A fresh nonce: an unpredictable value used once, typically as a key or seed.
A function returning a `Nonce` gets wrapped (`wrap-nonce`) so it can be called in terms.

### Bool

The boolean sort.  Formula combinators such as `cand`, `cor`, `eq`, `lt` build `Bool` formulas.

### Bitstring

Raw bitstrings, the sort of messages.  Most cryptographic operations (hashing, encryption, xor, exponentiation) map bitstrings to bitstrings.

### Message

Alias of `Bitstring`: messages sent on the wire are bitstrings.

### Time

Times, used to order steps (`lt`, `leq`, `pred`, ...).  The `Step` of a step is the time at which it happens.

### Protocol

A protocol (a participant).  Declared with `declare-protocol`; steps and memory cells are instantiated per protocol.

### Step

Alias of `Time`.  A step is identified by the time at which it happens.

### Index

An index, used to range over repetitions (protocol runs, list elements, ...).  Binds fresh in `bind`, `exists`, `publish`, step declarations, ...

### Any

The top/unknown sort, used when a term's sort is not (yet) fixed.

### Condition

Alias of `Bool`: the sort of step run-conditions.

### step

A step *instance*: one run of a step inside one protocol.Fields: `protocol`, `condition`, `message`, `assignements`.  Pass a list of them to `declare-step`.

### tuple

Synonym of `ctuple`: builds a tuple term from the given terms.

## cryptovampire/stdlib

### Functions

#### partial


**Usage:** `(partial f . args)`

Returns a function that applies `f` to the given `args` followed by the arguments of the call.
*Example:*
```scheme
    (define add1 (partial + 1))
    (add1 2) ;; => 3
    ```

## cryptovampire/function

### Functions

#### nonce?


**Usage:** `(nonce? f)`

Is `f` a `Nonce`?  Accepts either a `Sort`, or a function whose output sort is `Nonce`.

#### get-function


**Usage:** `(get-function f)`

Returns the underlying `Function` of a lifted function (as produced by `lift-function`/`register-function`), of a `Formula`, or of a `Function`.
Most `cryptovampire/*` functions accept such a value wherever a function is expected.

#### get-input-sorts


**Usage:** `(get-input-sorts f)`

Returns the list of input `Sort`s of the function `f`.

#### get-output-sort


**Usage:** `(get-output-sort f)`

Returns the output `Sort` of the function `f`.

#### wrap-nonce


**Usage:** `(wrap-nonce f)`

This wraps a function (lifted or not) outputing a `Nonce` inside the `nonce` constructor and lifts the result.
*Example:*
```scheme
    (get-output-sort _mk) ;; Nonce
    (define mk (wrap-nonce _mk))
    (mk i j p) ;; return `(nonce (_mk i j p))`
    ```

#### unwrap-nonce


**Usage:** `(unwrap-nonce f)`

Inverse of `wrap-nonce`: returns the lifted function that produces the raw (unmarked) nonce.
*Example:*
```scheme
    ((unwrap-nonce k1) i) ;; the bare term behind (mk i ...)
    ```

#### lift-function


**Usage:** `(lift-function f)`

Turns the `Function` `f` into a callable scheme value:
- a nullary function becomes the constant formula `(f)`
- otherwise a function that maps formula arguments to the application `(f a ...)`
Argument values passed to the resulting function go through `convert-to-formula`.

This is a major point of magic in the cryptovampire API. It lets the user use 'functions' as scheme functions (i.e., without macros) while still being able to use them as identifier to configure the various aspects of cryptovampire.
See `get-function` to retrive the cryptovampire `Function` object from a lifted function.

#### register-function


**Usage:** `(register-function fun)`

Lifts `fun` (via `lift-function`) and records it so the underlying `Function` can later be recovered with `get-function`.
Returns the lifted callable, or the constant formula for nullary functions.

#### declare-function


**Usage:** `(declare-function pbl fun)`

Declares `fun` into the problem `pbl`, registering it so it can be used by name.  Returns the registered (lifted) function.

#### mk-function


**Usage:** `(mk-function name cryptos args)`

Builds a fresh `Function` named `name`.
`cryptos` is the list of crypto modules the function depends on.  `args` is the input sorts followed by the *output* sort, e.g. `(mk-function "h" (list prf) (list Bitstring Bitstring Bitstring))`.
Prefer the `define-function` macro over this low-level entry point.

#### arity


**Usage:** `(arity f)`

Number of input sorts of `f` (or of the `Signature` `f`).

#### mk-alias-rw


**Usage:** `(mk-alias-rw sorts rw)`

Builds an alias rewrite: `sorts` are the bound sorts, `rw` is a term builder returning `(list args... result)`.  Backs the `alias-rw`/`define-alias` macros.

#### convert-to-formula


**Usage:** `(convert-to-formula arg)`

Coerces `arg` into a formula.
- a `Formula` is returned as-is
- a `Variable` becomes the corresponding variable formula
- a boolean becomes the constant `true`/`false`
- anything else raises an error.

### Syntax rules

#### define-function

Defines and binds a function named `name` in the problem `pbl`.
The crypto modules it uses come first (in a list, optional); then the
argument sorts; then `->` and the output sort.  A bare sort declares a
nullary constant; a nonce output is wrapped so the result can be called
directly.  The bound identifier is a lifted callable/formula value.

**Usage:**
```scheme
(define-function mhash pbl (prf) (Bitstring Bitstring) -> Bitstring)
(define-function ok pbl Bitstring)              ; nullary constant
(define-function k1 pbl (Index) -> Nonce)       ; nonce -> wrapped
```

#### define-alias

Declares a function that is defined by rewriting into previously declared
functions (often per-protocol, or with `wrap-nonce`).  Each clause is a
`[ (alias-rw ...) ... ]` rewrite.

**Usage:**
```scheme
(define-alias _mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> ((unwrap-nonce k1) i))
    ([ (i Index) (j Index) ] (i j p2) -> ((unwrap-nonce k2) i j)) ])
(define mk (wrap-nonce _mk))
```

#### alias-rw

Builds one rewrite used by `define-alias`, binding the given ids to fresh
variables of the given sorts.

**Usage:**
```scheme
(alias-rw ((i Index) (j Index)) ((unwrap-nonce k1) i) -> ...)
```

## cryptovampire/formula

### Functions

#### mexists


**Usage:** `(mexists (list Sort ...) builder)`

Builds an `exists` formula over one fresh variable per sort in `sorts`.
`builder` is applied to the fresh variables and must return the formula to quantify (`body` of the `exists` macro).  Prefer the `exists` macro.

#### mforall


**Usage:** `(mforall (list Sort ...) builder)`

Builds a `forall` formula over one fresh variable per sort in `sorts`.
`builder` is applied to the fresh variables and must return the formula to quantify.  Prefer the `forall` macro.

#### mfindst


**Usage:** `(mfindst (list Sort ...) cond-builder formula-builder result)`

Builds a `find such that` formula over one fresh variable per sort in `sorts`.
`cond-builder` and `formula-builder` are applied to the fresh variables; `result` is a plain term.  Prefer the `findst` macro.

#### cand


**Usage:** `(cand . args)`

Symbolic `and` of the given boolean formulas.

#### cor


**Usage:** `(cor . args)`

Symbolic `or` of the given boolean formulas.

#### ctuple


**Usage:** `(ctuple . args)`

Builds a tuple term from the given terms.  `tuple` is a synonym.

This also auto-nests arguments. Therefore it accpepts more than 2 arguments

#### subst


**Usage:** `(subst a b f)`

Returns `f` with every occurrence of term `a` replaced by `b`.

**NB**: the logic is very simple. Notably variables are not taken into account for unification or capture avoidance. Correctness is therefore the caller's responsibility.

### Syntax rules

#### exists

Binds fresh existential variables of the given sorts and builds an `exists` formula over `body`.

**Usage:**
```scheme
(exists ((i Index) (j Index)) body)
```

#### forall

Binds fresh universal variables of the given sorts and builds a `forall` formula over `body`.

**Usage:**
```scheme
(forall ((i Index)) body)
```

#### findst

Builds a `find such-that` formula: binds the given vars, evaluates `cond` and `formula` over them, returns `result`.

**Usage:**
```scheme
(findst ((i Index)) cond formula result)
```

## cryptovampire/protocol

### Functions

#### declare-step


**Usage:** `(declare-step pbl name sorts . contents)`

Declares a step named `name` taking inputs of `sorts`, with one `step` struct per protocol.
Returns the registered (lifted) step function; call it with fresh input terms to build the step term, e.g. `(tag i j)`.

#### declare-same-step


**Usage:** `(declare-same-step pbl name ptcls sorts msg mcond assignements)`

Declares the step `name` for every protocol in `ptcls`, sharing the message `msg` and condition `mcond` functions `(lambda (p args...) ...)`.

#### declare-memory-cell


**Usage:** `(declare-memory-cell pbl name params init)`

Declares a memory cell `name` with one value per index combination in `params` (and per protocol).
`init` returns the initial value: `(lambda (protocol . vars) value)`.  Returns the registered cell function.

#### empty-assignements


**Usage:** `(empty-assignements . _)`

A step that assigns nothing: use as the `assignements` field of a `step` when the step updates no memory cell.

### Syntax rules

#### store-cell

Declares an update of a memory cell, to be used inside the `assignements`
function of a `step` (which returns a list of them).

**Usage:**
```scheme
(list (store-cell s := mempty))                                  ; plain cell
(list (store-cell ((_) kT i) := (H (cells kT i) (key i))))       ; indexed cell
```

## cryptovampire/solver

### Functions

#### add-golgge-rule


**Usage:** ` (add-golgge-rule pbl rule) `

Adds a prolog/golgge `rule` (built with `prolog`) to the search space of `pbl`.

#### add-smt-axiom


**Usage:** ` (add-smt-axiom pbl formula) `

Adds `formula` as an SMT axiom available to the solvers of `pbl`.
*Example:*
```scheme
    (add-smt-axiom pbl (mnot (eq tag1 tag2)))
    ```

#### add-rewrite


**Usage:** ` (add-rewrite pbl rw) `

Adds a rewrite rule `rw` (built with `rw.new`) to the term rewriting of `pbl`.
*Example:*
```scheme
 (add-rewrite pbl (rw.new "lemma" (list i t j p) lhs rhs)) 
```

#### run


**Usage:** ` (run pbl p1 p2) `

Runs the indistinguishability check between protocols `p1` and `p2` in `pbl`. Returns `#t` on success.

#### mk-problem


**Usage:** ` (mk-problem tag) `

Creates a fresh problem object ; the `tag` is only a name.  Pass the result to all `declare-*` functions.
*Example:*
```scheme
    (define pbl (mk-problem 'x))
    ```

#### declare-protocol


**Usage:** ` (declare-protocol pbl) `

Declares a fresh protocol in `pbl`. Returns a protocol value ; use one per protocol/participant.
*Example:*
```scheme
    (define p1 (declare-protocol pbl))
    ```

### Syntax rules

#### bind

Binds each id to a fresh variable of the given sort, then evaluates `body`.
Used for context-wide lemmas/rewrites over fresh variables.

**Usage:**
```scheme
(bind ((i Index) (j Index) (p Protocol))
  (add-rewrite pbl (rw.new "lemma" (list i j p) lhs rhs)))
```

#### prolog

Builds a prolog-style golgge rule `name` with body `from` and additional goals `to ...`; add it with `add-golgge-rule`.

**Usage:**
```scheme
(prolog "r" (from) :- (goal-1) (goal-2))
```

#### add-constrain

Adds a constraint between steps, binding the given ids to fresh `Index` variables.

**Usage:**
```scheme
(add-constrain pbl (i j) (lt (tag i) (r j)))
```

#### publish

Declares `term` (over the fresh vars of the given sorts) to be public knowledge.

**Usage:**
```scheme
(publish pbl ((i Index)) (mexp g (a i)))
```

## cryptovampire/cryptography

### Functions

#### declare-cryptography


**Usage:** ` (declare-cryptography pbl) `

Declares a fresh cryptographic module in `pbl` ; returns the crypto value to pass to `initialize-as-*`.
Use one per cryptographic family used in the problem.
*Example:*
```scheme
    (define prf (declare-cryptography pbl))
    ```
Such object is used by cryptovampire to track the builtin axioms/rules to add, and how to instanciate them

#### register-fresh-nonce


**Usage:** ` (register-fresh-nonce crypto vars f) `

Registers the term `f` (over the variables `vars`) as a user-provided fresh nonce for `crypto`.
Useful so rules such as PRF, ENC-KP or DDH unify to this nonce instead of spawning a fresh one.

#### initialize-as


**Usage:** ` (initialize-as crypto kind . funs) `

Initializes `crypto` as an instance of `kind`, with `funs` as its building functions.
`kind` is one of `prf`, `ddh`, `aenc`, `senc` or `xor`. Prefer the dedicated `initialize-as-prf` & co. wrappers.

#### initialize-as-prf


**Usage:** ` (initialize-as-prf crypto . funs) `

Enables *pseudo-random-function* axioms and rules on `crypto` for the given `funs`.

#### initialize-as-ddh


**Usage:** ` (initialize-as-ddh crypto . funs) `

Enables *decisional Diffie-Hellman* axioms and rules on `crypto` for the given `funs`.

#### initialize-as-aenc


**Usage:** ` (initialize-as-aenc crypto . funs) `

Enables *asymmetric encryption* axioms and rules (IND-CCA and ENC-KP) on `crypto` for the given `funs`.

#### initialize-as-senc


**Usage:** ` (initialize-as-senc crypto . funs) `

Enables *symmetric encryption* axioms and rules (IND-CCA) on `crypto` for the given `funs`.

#### initialize-as-xor


**Usage:** ` (initialize-as-xor crypto . funs) `

Enables *xor* axioms and rules on `crypto` for the given `funs`.

## cryptovampire/signature

### Syntax rules

#### signature

A concise way to build a `Signature`: `(inputs ...) -> output`.  A bare sort is a nullary signature.

**Usage:**
```scheme
(signature (Index Index) -> Nonce)
(signature Nonce)   ; same as (signature () -> Nonce)
```
