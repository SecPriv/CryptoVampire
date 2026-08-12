(provide
  nonce?
  get-function
  get-input-sorts
  get-output-sort
  wrap-nonce
  unwrap-nonce
  lift-function
  register-function
  declare-function
  mk-function
  arity
  define-alias
  alias-rw
  define-function
  mk-alias-rw
  convert-to-formula)
(require-builtin cryptovampire/ll/function as fun->)
(require-builtin cryptovampire/ll/builtin-functions as funs->)
(require-builtin cryptovampire/ll/variable as var->)
(require-builtin cryptovampire/ll/formula as f->)
(require-builtin cryptovampire/ll/sort as sort->)
(require-builtin cryptovampire/ll/signature as sig->)
(require-builtin cryptovampire/ll/pbl as pbl->)
(require-builtin cryptovampire/ll/alias as alias->)
(require "cryptovampire/type")
(require "cryptovampire/sort")
(require "cryptovampire/signature")
(require "cryptovampire/doc")
(require-builtin steel/hash)

(define functions-map (hash))

(define (insert-function p f)
  (set! functions-map
    (hash-insert functions-map p f)))

;; ---------------------------------------------------------------------------
;; Lifting: builtin symbols are turned into callable scheme functions.
;; ---------------------------------------------------------------------------

(@doc (cv-help "convert-to-formula" "(convert-to-formula arg)"
    "Coerces `arg` into a formula."
    "- a `Formula` is returned as-is"
    "- a `Variable` becomes the corresponding variable formula"
    "- a boolean becomes the constant `true`/`false`"
    "- anything else raises an error.")
  (define (convert-to-formula arg)
    (cond
      [ (Formula? arg) arg]
      [ (Variable? arg) (f->var arg) ]
      [ (boolean? arg) (if arg (f->app funs->mtrue '()) (f->app funs->mfalse '())) ]
      [else (begin
          (displayln arg)
          (error "not a formula")) ])))

(define get-head 'head)
(define (requests-head? args) (equal? (first args) get-head))

(@doc (cv-help "get-function" "(get-function f)"
    "Returns the underlying `Function` of a lifted function (as produced by `lift-function`/`register-function`), of a `Formula`, or of a `Function`."
    "Most `cryptovampire/*` functions accept such a value wherever a function is expected.")
  (define (get-function funf)
    (cond
      [ (Formula? funf) (hash-ref functions-map funf) ]
      [ (Function? funf) funf]
      [else (funf get-head) ])))


(define (sarity f) (length (sig->inputs f)))
(define (get-signature f) (fun->signature (get-function f)))

(@doc (cv-help "get-input-sorts" "(get-input-sorts f)"
    "Returns the list of input `Sort`s of the function `f`.")
  (define (get-input-sorts f) (sig->inputs (get-signature f))))

(@doc (cv-help "get-output-sort" "(get-output-sort f)"
    "Returns the output `Sort` of the function `f`.")
  (define (get-output-sort f) (sig->output (get-signature f))))

(@doc (cv-help "nonce?" "(nonce? f)"
    "Is `f` a `Nonce`?  Accepts either a `Sort`, or a function whose output sort is `Nonce`.")
  (define (nonce? f)
    (if (Sort? f) (Nonce? f) (Nonce? (get-output-sort f)))))

(@doc (cv-help "lift-function" "(lift-function f)"
    "Turns the `Function` `f` into a callable scheme value:"
    "- a nullary function becomes the constant formula `(f)`"
    "- otherwise a function that maps formula arguments to the application `(f a ...)`"
    "Argument values passed to the resulting function go through `convert-to-formula`."
    "\nThis is a major point of magic in the cryptovampire API. It lets the user use 'functions' as scheme functions (i.e., without macros) while still being able to use them as identifier to configure the various aspects of cryptovampire."
    "See `get-function` to retrive the cryptovampire `Function` object from a lifted function.")
  (define (lift-function f)
    (if (= (sarity (fun->signature f)) 0)
      (f->app f '())
      (lambda args
        (if (requests-head? args) f
          (f->app f (map convert-to-formula args)))))))

(@doc (cv-help "register-function" "(register-function fun)"
    "Lifts `fun` (via `lift-function`) and records it so the underlying `Function` can later be recovered with `get-function`."
    "Returns the lifted callable, or the constant formula for nullary functions.")
  (define (register-function fun)
    (let
      [ (f (lift-function fun)) ]
      (if (f->Formula? f)
        (begin
          (insert-function f fun)
          f)
        f))))

(define (mnonce n) (f->app funs->mnonce (list n)))

(@doc (cv-help "wrap-nonce" "(wrap-nonce f)"
    "This wraps a function (lifted or not) outputing a `Nonce` inside the `nonce` constructor and lifts the result."
    "*Example:*"
    "```scheme
    (get-output-sort _mk) ;; Nonce
    (define mk (wrap-nonce _mk))
    (mk i j p) ;; return `(nonce (_mk i j p))`
    ```")
  (define (wrap-nonce nonce)
    (let ((f (get-function nonce)))
      (if (f->Formula? nonce)
        (begin
          (insert-function (mnonce nonce) f)
          (mnonce nonce))
        (lambda args
          (if (requests-head? args) f
            (mnonce (apply nonce args))))))))

(@doc (cv-help "unwrap-nonce" "(unwrap-nonce f)"
    "Inverse of `wrap-nonce`: returns the lifted function that produces the raw (unmarked) nonce."
    "*Example:*"
    "```scheme
    ((unwrap-nonce k1) i) ;; the bare term behind (mk i ...)
    ```")
  (define (unwrap-nonce nonce)
    (lift-function (get-function nonce))))

(@doc (cv-help "arity" "(arity f)"
    "Number of input sorts of `f` (or of the `Signature` `f`).")
  (define (arity f)
    (if (Signature? f)
      (sarity f)
      (sarity (get-signature f)))))

(@doc (cv-help "mk-function" "(mk-function name cryptos args)"
    "Builds a fresh `Function` named `name`."
    "`cryptos` is the list of crypto modules the function depends on.  `args` is the input sorts followed by the *output* sort, e.g. `(mk-function \"h\" (list prf) (list Bitstring Bitstring Bitstring))`."
    "Prefer the `define-function` macro over this low-level entry point.")
  (define (mk-function name cryptos args)
    (if (< (length args) 1)
      (error "mk-fun: expected at least one sort argument")
      (let* ((outsort (last args))
          (in-sorts (take args (- (length args) 1))))
        ; body of the function
        (if (equal? outsort Nonce)
          (fun->mk-nonce name (sig->new in-sorts outsort))
          (fun->mk-function name
            (sig->new in-sorts outsort) cryptos))))))

(@doc (cv-help "declare-function" "(declare-function pbl fun)"
    "Declares `fun` into the problem `pbl`, registering it so it can be used by name.  Returns the registered (lifted) function.")
  (define (declare-function pbl fun)
    (register-function (pbl->declare-function pbl fun))))


;; decalres a function, and wraps a nonce if needed
(define (pre-define-function name pbl cryptos args ret)
  (let* [
      (allArgs (push-back args ret))
      (f (declare-function pbl (mk-function name cryptos allArgs))) ]
    (if (Nonce? ret) (wrap-nonce f) f)))

;; ---------------------------------------------------------------------------
;; define-function
;;
;; Declares and binds a function with the given name.  The crypto modules it
;; uses come first (optional, in a list); then the argument sorts; then `->`
;; and the output sort.  For nullary constants, a bare sort suffices.
;;
;; *Examples:*
;; ```scheme
;; (define-function mhash pbl (prf) (Bitstring Bitstring) -> Bitstring)
;; (define-function ok pbl Bitstring)              ; nullary constant
;; (define-function k1 pbl (Index) -> Nonce)       ; nonce -> wrapped
;; ```
;;
;; Note that the resulting scheme identifier is a lifted callable/formula, so
;; it can be passed around as a value.
;; ---------------------------------------------------------------------------

(define-syntax define-function
  (syntax-rules (->)
    [ (_ name pbl (crypto ...) (args ...) -> sort)
      (define name
        (pre-define-function (symbol->string 'name) pbl (list crypto ...) (list args ...) sort)) ]
    [ (_ name pbl (args ...) -> sort)
      (define-function name pbl () (args ...) -> sort) ]
    [ (_ name pbl sort)
      (define-function name pbl () () -> sort) ]
    [ (_ name pbl (crypto ...) sort)
      (define-function name pbl (crypto ...) () -> sort) ]))


(@doc (cv-help "mk-alias-rw" "(mk-alias-rw sorts rw)"
    "Builds an alias rewrite: `sorts` are the bound sorts, `rw` is a term builder returning `(list args... result)`.  Backs the `alias-rw`/`define-alias` macros.")
  (define (mk-alias-rw sorts rw)
    (let*
      [ (vars (map var->fresh-with-sort sorts))
        (vars-app (map f->var vars))
        (rwl (apply rw vars-app)) ]
      (if (< (length rwl) 1)
        (error "mk-fun: expected at least one sort argument")
        (let* ((res (last rwl))
            (args (take rwl (- (length rwl) 1))))
          (alias->new-rewrite vars args res))))))

;; ---------------------------------------------------------------------------
;; alias-rw
;;
;; Builds one rewrite used by `define-alias`: `(alias-rw ((i Index) (j Index)) ((unwrap-nonce k1) i) -> ...)`.
;; Binds the given ids to fresh variables of the given sorts.
;; ---------------------------------------------------------------------------

(define-syntax alias-rw
  (syntax-rules (->)
    [ (_ ((ids sorts) ...) (args ...) -> res)
      (mk-alias-rw
        (list sorts ...)
        (lambda (ids ...)
          (list args ... res))) ]))

;; ---------------------------------------------------------------------------
;; define-alias
;;
;; Declares a function that is defined by rewriting into previously declared
;; functions (often per-protocol, or for `wrap-nonce`).  Each rewrite is a
;; `[ (alias-rw ...) ... ]` clause.
;;
;; *Example:* (from the tests)
;; ```scheme
;; (define-alias _mk pbl (Index Index Protocol) Nonce
;;   [ ([ (i Index) (j Index) ] (i j p1) -> ((unwrap-nonce k1) i))
;;     ([ (i Index) (j Index) ] (i j p2) -> ((unwrap-nonce k2) i j)) ])
;; (define mk (wrap-nonce _mk))
;; ```
;; ---------------------------------------------------------------------------

(define-syntax define-alias
  (syntax-rules (->)
    [ (_ name pbl (inputs ...) output ((((ids sorts) ...) (args ...) -> res) ...))
      (define name (declare-function pbl
          (fun->mk-alias
            (symbol->string 'name)
            (sig->new (list inputs ...) output)
            (list
              (mk-alias-rw (list sorts ...) (lambda (ids ...) (list args ... res)))
              ...)))) ]))
