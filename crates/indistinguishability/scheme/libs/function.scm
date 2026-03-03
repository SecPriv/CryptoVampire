(provide
  nonce?
  get-function
  wrap-nonce
  register-function
  declare-function
  mk-function
  arity)
(require-builtin cryptovampire/ll/function as fun->)
(require-builtin cryptovampire/ll/builtin-functions as funs->)
(require-builtin cryptovampire/ll/variable as var->)
(require-builtin cryptovampire/ll/formula as f->)
(require-builtin cryptovampire/ll/sort as sort->)
(require-builtin cryptovampire/ll/signature as sig->)
(require-builtin cryptovampire/ll/pbl as pbl->)
(require "cryptovampire/type") 
(require "cryptovampire/sort") 
(require-builtin steel/hash)

(define functions-map (hash))

(define (insert-function p f)
  (set! functions-map
    (hash-insert functions-map p f)))

(define (nonce? f) 
  (if (Sort? f) (Nonce? f)  (Nonce? (fun->get-sort f)))))


(define (convert-to-formula arg)
  (if (Variable? arg) (f->var arg)
    (if (boolean? arg) (if arg (f->app funs->mtrue '()) (f->app funs->mfalse '()))
      arg)))

(define get-head 'head)
(define get-unnonce 'unnonce)
(define (requests-head? args) (equal? (first args) get-head))
(define (requests-unnonce? args) (equal? (first args) get-unnonce))

(define (get-function funf)
  (if (Formula? funf)
    (hash-ref functions-map funf)
    (if (Function? funf) funf (funf get-head))))


(define (sarity f) (length (sig->inputs (fun->signature f))))

(define (lift-fun f)
  (if (= (sarity f) 0)
    (f->app f '())
    (lambda args
      (if (requests-head? args) f
        (f->app f (map convert-to-formula args))))))

(define (register-function fun)
  (let
    [ (f (lift-fun fun)) ]
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

(define (arity f)
  (if (Signature? f)
    (sarity f)
    (sarity (fun->signature (get-function f)))))

(define (mk-function name cryptos . args)
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


; (define (define-function' name pbl cryptos args) 
; (let [(f (declare-function pbl (mk-function name pbl cryptos args)))]
; (

; )

; )
;  )


(define-syntax define-function
  (syntax-rules (->)
    [ (_ name pbl (crypto ...) (args ...) -> sort)
    (define name 
      (let [ (f (mk-fun (symbol->string 'name) (list crypto ...) args ... sort)) ] (if (equal? sort cv-Nonce)
          (wrap-nonce f)
           f)
        )) ]
    [ (_ name pbl (args ...) -> sort)
    (define-function name pbl () (args ...) -> sort) ]
    [ (_ name pbl sort)
    (define-function name pbl () () -> sort) ]
    [ (_ name pbl (crypto ...) sort)
    (define-function name pbl (crypto ...) () -> sort) ]))