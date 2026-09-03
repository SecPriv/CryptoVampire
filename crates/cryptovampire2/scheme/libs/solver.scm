(provide
  bind prolog
  add-golgge-rule add-smt-axiom add-rewrite
  add-constrain publish
  run mk-problem declare-protocol
  solver-doc)
(require-builtin cryptovampire/ll/variable as var->)
(require-builtin cryptovampire/ll/formula as f->)
(require-builtin cryptovampire/ll/pbl as pbl->)
(require-builtin cryptovampire/ll/rule as rule->)
(require-builtin cryptovampire/ll/configuration as conf->)
(require-builtin cryptovampire/ll/rewrite as rw->)
(require-builtin cryptovampire/ll/report as report->)
(require-builtin cryptovampire/ll as base->)
(require "cryptovampire/function")
(require "cryptovampire/sort")
(require "cryptovampire/doc")

;; Documentation table for the `cryptovampire/solver` library (macro docs,
;; next to their definitions).  See `cryptovampire/doc` for the mechanism.
(define solver-doc (make-doc-table))
(define (register-syntax-doc! name . doc)
  (set! solver-doc (apply doc-add! solver-doc name doc)))
(define (register-type-doc! name . doc)
  (set! solver-doc (apply doc-add! solver-doc name doc)))

;; ---------------------------------------------------------------------------
;; bind
;;
;; Binds each id to a fresh variable of the given sort, then evaluates body.
;; Used to state context-wide lemmas/rewrites over fresh variables.
;; ---------------------------------------------------------------------------

(register-syntax-doc! 'bind
  "Binds each id to a fresh variable of the given sort, then evaluates `body`."
  "Used for context-wide lemmas/rewrites over fresh variables."
  ""
  "**Usage:**"
  "```scheme"
  "(bind ((i Index) (j Index) (p Protocol))"
  "  (add-rewrite pbl (rw.new \"lemma\" (list i j p) lhs rhs)))"
  "```")

(define-syntax bind
  (syntax-rules ()
    [ (_ ((ids sorts) ...) arg)
      (let [ (ids (var->fresh-with-sort sorts)) ...] arg) ]))

;; ---------------------------------------------------------------------------
;; prolog
;;
;; Builds a prolog-style golgge rule `name` with body `from` and additional
;; goals `to ...`, e.g. `(prolog "r" (from) :- (goal-1) (goal-2))`.
;; Add the result to the problem with `add-golgge-rule`.
;; ---------------------------------------------------------------------------

(register-syntax-doc! 'prolog
  "Builds a prolog-style golgge rule `name` with body `from` and additional goals `to ...`; add it with `add-golgge-rule`."
  ""
  "**Usage:**"
  "```scheme"
  "(prolog \"r\" (from) :- (goal-1) (goal-2))"
  "```")

(define-syntax prolog
  (syntax-rules (:-)
    [ (_ name from)
      (rule->new-prolog name from '()) ]
    [ (_ name from :- to ...)
      (rule->new-prolog name
        from (list to ...)) ]))

(@doc (cv-help "add-golgge-rule" " (add-golgge-rule pbl rule) "
    "Adds a prolog/golgge `rule` (built with `prolog`) to the search space of `pbl`.")
  (define (add-golgge-rule pbl rule) (pbl->add-rule pbl rule)))

(@doc (cv-help "add-smt-axiom" " (add-smt-axiom pbl formula) "
    "Adds `formula` as an SMT axiom available to the solvers of `pbl`."
    "*Example:*"
    "```scheme"
    "(add-smt-axiom pbl (mnot (eq tag1 tag2)))"
    "```")
  (define (add-smt-axiom pbl formula) (pbl->add-smt-axiom pbl formula)))

(@doc (cv-help "add-rewrite" " (add-rewrite pbl rw) "
    "Adds a rewrite rule `rw` (built with `rw.new`) to the term rewriting of `pbl`."
    "*Example:*"
    "```scheme"
    "(add-rewrite pbl (rw.new \"lemma\" (list i t j p) lhs rhs)) "
    "```")
  (define (add-rewrite pbl rw) (pbl->add-rewrite pbl rw)))

(@doc (cv-help "run" " (run pbl p1 p2) "
    "Runs the indistinguishability check between protocols `p1` and `p2` in `pbl`. Returns `#t` on success.")
  (define (run pbl p1 p2)
    (pbl->run pbl (get-function p1) (get-function p2))))

(@doc (cv-help "mk-problem" " (mk-problem tag) "
    "Creates a fresh problem object ; the `tag` is only a name.  Pass the result to all `declare-*` functions."
    "*Example:*"
    "```scheme"
    "(define pbl (mk-problem 'x))"
    "```")
  (define (mk-problem _) (pbl->empty base->cli-config)))

;; ---------------------------------------------------------------------------
;; add-constrain
;;
;; Adds a constraint between steps, binding the given ids to fresh `Index`
;; variables: `(add-constrain pbl (i j) (lt (tag i) (r j)))`.
;; ---------------------------------------------------------------------------

(register-syntax-doc! 'add-constrain
  "Adds a constraint between steps, binding the given ids to fresh `Index` variables."
  ""
  "**Usage:**"
  "```scheme"
  "(add-constrain pbl (i j) (lt (tag i) (r j)))"
  "```")

(define-syntax add-constrain
  (syntax-rules ()
    [ (_ pbl (vars ...) constrain)
      (let [ (vars (f->var (var->fresh-with-sort Index))) ...]
        (pbl->add-constrain pbl constrain)) ]))

;; ---------------------------------------------------------------------------
;; publish
;;
;; Declares `term` (over the fresh vars of the given sorts) to be public
;; knowledge: `(publish pbl ((i Index)) (mexp g (a i)))`.
;; ---------------------------------------------------------------------------

(register-syntax-doc! 'publish
  "Declares `term` (over the fresh vars of the given sorts) to be public knowledge."
  ""
  "**Usage:**"
  "```scheme"
  "(publish pbl ((i Index)) (mexp g (a i)))"
  "```")

(define-syntax publish
  (syntax-rules ()
    [ (_ pbl ((vars sorts) ...) term)
      (let [ (vars (var->fresh-with-sort sorts)) ...]
        (pbl->publish pbl (list vars ...) term)) ]))

(@doc (cv-help "declare-protocol" " (declare-protocol pbl) "
    "Declares a fresh protocol in `pbl`. Returns a protocol value ; use one per protocol/participant."
    "*Example:*"
    "```scheme"
    "(define p1 (declare-protocol pbl))"
    "```")
  (define (declare-protocol pbl)
    (register-function (pbl->declare-protocol pbl))))
