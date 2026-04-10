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
  mk-alias-rw)
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
(require-builtin steel/hash)

(define functions-map (hash))

(define (insert-function p f)
  (set! functions-map
    (hash-insert functions-map p f)))


(define (convert-to-formula arg)
  (cond
    [ (Variable? arg) (f->var arg) ]
    [ (boolean? arg) (if arg (f->app funs->mtrue '()) (f->app funs->mfalse '())) ]
    [else arg]))

(define get-head 'head)
(define (requests-head? args) (equal? (first args) get-head))

(define (get-function funf)
  (cond
    [ (Formula? funf) (hash-ref functions-map funf) ]
    [ (Function? funf) funf]
    [else (funf get-head) ]))


(define (sarity f) (length (sig->inputs f)))
(define (get-signature f) (fun->signature (get-function f)))
(define (get-input-sorts f) (sig->inputs (get-signature f)))
(define (get-output-sort f) (sig->output (get-signature f)))
(define (nonce? f)
  (if (Sort? f) (Nonce? f) (Nonce? (get-output-sort f))))

(define (lift-function f)
  (if (= (sarity (fun->signature f)) 0)
    (f->app f '())
    (lambda args
      (if (requests-head? args) f
        (f->app f (map convert-to-formula args))))))

(define (register-function fun)
  (let
    [ (f (lift-function fun)) ]
    (if (f->Formula? f)
      (begin
        (insert-function f fun)
        f)
      f)))

(define (mnonce n) (f->app funs->mnonce (list n)))

(define (wrap-nonce nonce)
  (let ((f (get-function nonce)))
    (if (f->Formula? nonce)
      (begin
        (insert-function (mnonce nonce) f)
        (mnonce nonce))
      (lambda args
        (if (requests-head? args) f
          (mnonce (apply nonce args)))))))

(define (unwrap-nonce nonce)
  (lift-function (get-function nonce)))

(define (arity f)
  (if (Signature? f)
    (sarity f)
    (sarity (get-signature f))))

(define (mk-function name cryptos args)
  (if (< (length args) 1)
    (error "mk-fun: expected at least one sort argument")
    (let* ((outsort (last args))
        (in-sorts (take args (- (length args) 1))))
      ; body of the function
      (if (equal? outsort Nonce)
        (fun->mk-nonce name (sig->new in-sorts outsort))
        (fun->mk-function name
          (sig->new in-sorts outsort) cryptos)))))

(define (declare-function pbl fun)
  (register-function (pbl->declare-function pbl fun)))


;; decalres a function, and wraps a nonce if needed
(define (pre-define-function name pbl cryptos args ret)
  (let* [
    (allArgs (push-back args ret))
    (f (declare-function pbl (mk-function name cryptos allArgs))) ]
    (if (Nonce? ret) (wrap-nonce f) f)))


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


(define (mk-alias-rw sorts rw)
  (let*
    [ (vars (map var->fresh-with-sort sorts))
    (vars-app (map f->var vars))
    (rwl (apply rw vars-app)) ]
    (if (< (length rwl) 1)
      (error "mk-fun: expected at least one sort argument")
      (let* ((res (last rwl))
          (args (take rwl (- (length rwl) 1))))
        (alias->new-rewrite vars args res)))))

(define-syntax alias-rw
  (syntax-rules (->)
    [ (_ ((ids sorts) ...) (args ...) -> res)
    (mk-alias-rw
      (list sorts ...)
      (lambda (ids ...)
        (list args ... res))) ]))

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
