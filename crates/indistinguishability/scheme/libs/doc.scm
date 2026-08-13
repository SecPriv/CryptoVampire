(provide cv-help syntax-docs types-docs
  register-syntax-doc! register-type-doc!)

(@doc "\
  Helpers used to build `@doc` docstrings for the `cryptovampire/*` libraries.

  `cv-help` renders a small markdown block: a bold `title`, a `Usage:` line
  with the snippet in backticks, then the free-form body `paras`.  It is meant
  to be called as the *documentation* expression of the `@doc` macro:

  ```scheme
  (@doc (cv-help \"my-fn\" \"(my-fn a b)\" \"Adds a and b.\") (define (my-fn a b) (+ a b)))
  ```

  **TITLE**  -- function name (string)
  **USAGE**  -- a scheme call snippet (string)
  **PARAS**  -- body paragraphs (strings); use ```scheme fenced blocks for examples

  This also help defeat the overzealous auto-formating.
  "
  (define (cv-help title usage . paras)
    (string-join
      (append (list (string-append "**`" title "`**") ""
          (string-append "**Usage:** `" usage "`") "")
        paras)
      "\n")))

;; ---------------------------------------------------------------------------
;; Registries of documentation that cannot live in the `help` doc table (it only
;; stores closures): the `syntax-docs` dictionary for syntax-rules macros and
;; the `types-docs` dictionary for plain values (sorts & aliases).  They are
;; consumed by `crates/indistinguishability/scheme/docgen.scm`.
;; ---------------------------------------------------------------------------

(define syntax-docs (hash))
(define types-docs (hash))

(define (register-syntax-doc! name . doc)
  (set! syntax-docs (hash-insert syntax-docs name (string-join doc "\n"))))

(define (register-type-doc! name . doc)
  (set! types-docs (hash-insert types-docs name (string-join doc "\n"))))

;; ---------------- syntax rules (macros) ----------------


(register-syntax-doc! 'forall
  "Binds fresh universal variables of the given sorts and builds a `forall` formula over `body`.\n\n**Usage:**\n```scheme\n(forall ((i Index)) body)\n```")

(register-syntax-doc! 'findst
  "Builds a `find such-that` formula: binds the given vars, evaluates `cond` and `formula` over them, returns `result`.\n\n**Usage:**\n```scheme\n(findst ((i Index)) cond formula result)\n```")

(register-syntax-doc! 'store-cell
  (string-append
    "Declares an update of a memory cell, to be used inside the `assignements`\n"
    "function of a `step` (which returns a list of them).\n"
    "\n**Usage:**\n```scheme\n"
    "(list (store-cell s := mempty))                                  ; plain cell\n"
    "(list (store-cell ((_) kT i) := (H (cells kT i) (key i))))       ; indexed cell\n"
    "```"))

(register-syntax-doc! 'bind
  (string-append
    "Binds each id to a fresh variable of the given sort, then evaluates `body`.\n"
    "Used for context-wide lemmas/rewrites over fresh variables.\n"
    "\n**Usage:**\n```scheme\n"
    "(bind ((i Index) (j Index) (p Protocol))\n"
    "  (add-rewrite pbl (rw.new \"lemma\" (list i j p) lhs rhs)))\n"
    "```"))

(register-syntax-doc! 'prolog
  "Builds a prolog-style golgge rule `name` with body `from` and additional goals `to ...`; add it with `add-golgge-rule`.\n\n**Usage:**\n```scheme\n(prolog \"r\" (from) :- (goal-1) (goal-2))\n```")

(register-syntax-doc! 'add-constrain
  "Adds a constraint between steps, binding the given ids to fresh `Index` variables.\n\n**Usage:**\n```scheme\n(add-constrain pbl (i j) (lt (tag i) (r j)))\n```")

(register-syntax-doc! 'publish
  "Declares `term` (over the fresh vars of the given sorts) to be public knowledge.\n\n**Usage:**\n```scheme\n(publish pbl ((i Index)) (mexp g (a i)))\n```")

(register-syntax-doc! 'signature
  "A concise way to build a `Signature`: `(inputs ...) -> output`.  A bare sort is a nullary signature.\n\n**Usage:**\n```scheme\n(signature (Index Index) -> Nonce)\n(signature Nonce)   ; same as (signature () -> Nonce)\n```")

;; ---------------- types & values ----------------

(register-type-doc! 'Nonce
  "A fresh nonce: an unpredictable value used once, typically as a key or seed.\nA function returning a `Nonce` gets wrapped (`wrap-nonce`) so it can be called in terms.")

(register-type-doc! 'Bool
  "The boolean sort.  Formula combinators such as `cand`, `cor`, `eq`, `lt` build `Bool` formulas.")

(register-type-doc! 'Bitstring
  "Raw bitstrings, the sort of messages.  Most cryptographic operations (hashing, encryption, xor, exponentiation) map bitstrings to bitstrings.")

(register-type-doc! 'Message
  "Alias of `Bitstring`: messages sent on the wire are bitstrings.")

(register-type-doc! 'Time
  "Times, used to order steps (`lt`, `leq`, `pred`, ...).  The `Step` of a step is the time at which it happens.")

(register-type-doc! 'Protocol
  "A protocol (a participant).  Declared with `declare-protocol`; steps and memory cells are instantiated per protocol.")

(register-type-doc! 'Step
  "Alias of `Time`.  A step is identified by the time at which it happens.")

(register-type-doc! 'Index
  "An index, used to range over repetitions (protocol runs, list elements, ...).  Binds fresh in `bind`, `exists`, `publish`, step declarations, ...")

(register-type-doc! 'Any
  "The top/unknown sort, used when a term's sort is not (yet) fixed.")

(register-type-doc! 'Condition
  "Alias of `Bool`: the sort of step run-conditions.")

(register-type-doc! 'step
  (string-append
    "A step *instance*: one run of a step inside one protocol."
    "Fields: `protocol`, `condition`, `message`, `assignements`.  Pass a list of them to `declare-step`."))

(register-type-doc! 'tuple
  "Synonym of `ctuple`: builds a tuple term from the given terms.")
