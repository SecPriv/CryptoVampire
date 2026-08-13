(provide
  Function? Formula? Sort? Signature? Variable?)


(require-builtin cryptovampire/ll/variable as var->)
(require-builtin cryptovampire/ll/formula as f->)
(require-builtin cryptovampire/ll/function as fun->)
(require-builtin cryptovampire/ll/sort as sort->)
(require-builtin cryptovampire/ll/signature as sig->)

;; ---------------------------------------------------------------------------
;; Type predicates over the core objects of the logic: variables, formulas,
;; functions, sorts and signatures.
;;
;;   (Variable?  x)  -- is `x` a variable?
;;   (Formula?   x)  -- is `x` a formula/term?
;;   (Function?  x)  -- is `x` a function object?
;;   (Sort?      x)  -- is `x` a sort (e.g. `Nonce`, `Bitstring`, ...)?
;;   (Signature? x)  -- is `x` a signature (`(inputs ...) -> output`)?
;;
;; They are plain native predicates, so they have no `help` documentation, but
;; they are exactly the ones used throughout the `cryptovampire/*` libraries
;; (e.g. `convert-to-formula`, `declare-step`).
;; ---------------------------------------------------------------------------

(define Variable? var->Variable?)
(define Function? fun->Function?)
(define Formula? f->Formula?)
(define Sort? sort->Sort?)
(define Signature? sig->Signature?)
