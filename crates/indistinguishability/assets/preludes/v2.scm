(provide
  declare-function
  declare-step
  declare-protocol
  declare-cryptography
  initialize-as-prf
  initialize-as-aenc
  initialize-as-senc
  initialize-as-xor
  initialize-as-ddh
  set-init-step
  run
  get-function
  register-function
  wrap-nonce
  mk-fun
  mk-alias
  mk-alias-rw
  mk-problem
  Nonce?
  step
  step-protocol
  ;; macros
  bind exists forall findst
  mfindst
  prolog signature
  alias-rw
  define-alias
  define-function
  add-constrain
  publish
  lift-fun
  cand cor tuple eql <>
  ;  @@@EXPORTS@@@
  )
(require-builtin cryptovampire as cv-)
(require-builtin steel/hash)

(define functions-map (hash))

(define (insert-function p f)
  (set! functions-map
    (hash-insert functions-map p f)))

(define (Nonce? f) (equal? cv-Nonce (cv-get-sort f)))

(define (convert-to-formula arg)
  (if (cv-Variable? arg) (cv-mk-varf arg)
    (if (boolean? arg) (if arg (cv-mk-appf cv-__pre_mtrue '()) (cv-mk-appf cv-__pre_mfalse '()))
      arg)))

(define get-head 'head)

(define (get-function funf)
  (if (cv-Formula? funf)
    (hash-ref functions-map funf)
    (if (cv-Function? funf) funf (funf get-head))))

(define (requests-head args) (equal? (first args) get-head))

(define (lift-fun f)
  (if (= (cv-arity f) 0)
    (cv-mk-appf f '())
    (lambda args
      (if (requests-head args) f
        (cv-mk-appf f (map convert-to-formula args))))))

(define (register-function fun)
  (let
    [ (f (lift-fun fun)) ]
    (if (cv-Formula? f)
      (begin
        (insert-function f fun)
        f)
      f)))

(define (wrap-nonce nonce)
  (let ((f (get-function nonce)))
    (if (cv-Formula? nonce)
      (begin
        (insert-function (mnonce nonce) f)
        (mnonce nonce))
      (lambda args
        (if (requests-head args) f
          (mnonce (apply nonce args)))))))



; @@@DEFINITIONS@@@

(define S λS)
(define O λO)

;; This is some ChatGPT magic ^^''
(define (mexists sorts arg)
  (let loop ((ss sorts) (vars '()))
    (if (null? ss)
      ;; once all vars generated
      (let ((rev-vars (reverse vars)))
        (cv-mk-binderf cv-existsf rev-vars (list (apply arg rev-vars))))
      ;; otherwise, generate next var and recur
      (let* ((s (car ss))
          (v (cv-mk-fresh-var-w-sort s)))
        (loop (cdr ss) (cons v vars))))))

(define (mforall sorts arg)
  (let loop ((ss sorts) (vars '()))
    (if (null? ss)
      ;; once all vars generated
      (let ((rev-vars (reverse vars)))
        (cv-mk-binderf cv-forallf rev-vars (list (apply arg rev-vars))))
      ;; otherwise, generate next var and recur
      (let* ((s (car ss))
          (v (cv-mk-fresh-var-w-sort s)))
        (loop (cdr ss) (cons v vars))))))

(define (mfindst sorts arg1 arg2 arg3)
  (let*
    [ (vars (map cv-mk-fresh-var-w-sort sorts))
    (varsf (map cv-mk-varf vars))
    (c (apply arg1 varsf))
    (l (apply arg2 varsf)) ]
    (cv-mk-binderf cv-findstf vars (list c l arg3))))

(define-syntax exists
  (syntax-rules ()
    [ (_ ((ids sorts) ...) arg)
    (mexists (list sorts ...) (lambda (ids ...) arg)) ]))
(define-syntax forall
  (syntax-rules ()
    [ (_ ((ids sorts) ...) arg)
    (mforall (list sorts ...) (lambda (ids ...) arg)) ]))
(define-syntax findst
  (syntax-rules ()
    [ (_ ((ids sorts) ...) arg1 arg2 arg3)
    (mfindst (list sorts ...)
      (lambda (ids ...) arg1)
      (lambda (ids ...) arg2)
      arg3) ]))


(struct step (protocol condition message))

(define (declare-step pbl name sorts . content)
  (let*
    [ (step (cv-declare-step pbl name sorts))
    (stepf (register-function step)) ]
    (begin
      (for-each (lambda (c)
          (let*
            [ (ptclf (step-protocol c))
            (msgf (step-message c))
            (condf (step-condition c))
            (ptcl (get-function ptclf))
            (variables
              (map cv-mk-varf (cv-get-step-variables pbl step ptcl)))
            (in (macro_input (apply stepf variables) ptclf)) ]
            (begin
              (cv-set-step-message pbl step ptcl
                (apply msgf (cons in variables)))
              (cv-set-step-condition pbl step ptcl
                (apply condf (cons in variables))))))
        content)
      stepf)))

(define (set-init-step pbl . content)
  (let [ (s (get-function init)) ]
    (begin
      (for-each (lambda (c)
          (let [ (condf (step-message c)) (ptcl (step-protocol c)) ]
            (cv-set-step-message pbl s (get-function ptcl)
              condf)))))))

(define (mk-fun name cryptos . args)
  (if (< (length args) 1)
    (error "mk-fun: expected at least one sort argument")
    (let* ((outsort (last args))
        (in-sorts (take args (- (length args) 1))))
      ; body of the function
      (if (equal? outsort cv-Nonce)
        (cv-mk-nonce name (cv-mk-signature in-sorts outsort))
        (cv-mk-fun name
          (cv-mk-signature in-sorts outsort) cryptos)))))

(define-syntax prolog
  (syntax-rules (:-)
    [ (_ name from)
    (mk-prolog name from '()) ]
    [ (_ name from :- to ...)
    (mk-prolog name
      from (list to ...)) ]))

(define-syntax bind
  (syntax-rules ()
    [ (_ ((ids sorts) ...) arg)
    (let [ (ids (cv-mk-fresh-var-w-sort sorts)) ...] arg) ]))

(define-syntax signature
  (syntax-rules (->)
    [ (_ () -> sort) (cv-mk-signature '() sort) ]
    [ (_ (sorts ...) -> sort) (cv-mk-signature (list sorts ...) sort) ]
    [ (_ sort) (cv-mk-signature '() sort) ]))

(define mk-alias cv-mk-alias)

(define (mk-alias-rw sorts rw)
  (let*
    [ (vars (map cv-mk-fresh-var-w-sort sorts))
    (vars-app (map cv-mk-varf vars))
    (rwl (apply rw vars-app)) ]
    (if (< (length rwl) 1)
      (error "mk-fun: expected at least one sort argument")
      (let* ((res (last rwl))
          (args (take rwl (- (length rwl) 1))))
        (cv-mk-alias-rwf vars args res)))))

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
        (mk-alias
          (symbol->string 'name)
          (signature (inputs ...) -> output)
          (list
            (alias-rw ((ids sorts) ...) (args ...) -> res)
            ...)))) ]))



(define (initialize-as-prf prf fhash)
  (cv-initialize-as-prf prf (get-function fhash)))

(define (initialize-as-aenc aenc enc dec pk)
  (cv-initialize-as-aenc aenc
    (get-function enc) (get-function dec) (get-function pk)))

(define (initialize-as-senc senc enc dec)
  (cv-initialize-as-senc senc
    (get-function enc) (get-function dec)))

(define (initialize-as-xor xor-crypt xor)
  (cv-initialize-as-xor xor-crypt
    (get-function xor)))

(define (initialize-as-ddh ddh g exp)
  (cv-initialize-as-ddh ddh
    (get-function g) (get-function exp)))

(define (run pbl p1 p2)
  (cv-run pbl (get-function p1) (get-function p2)))

(define (declare-protocol pbl)
  (register-function (cv-declare-protocol pbl)))

(define (declare-function pbl fun)
  (let [ (f (cv-declare-function pbl fun)) ]
    (register-function f)))

(define (mk-problem _) (cv-empty-problem cv-cli-config))
(define declare-cryptography cv-declare-cryptography)


(define-syntax define-function
  (syntax-rules (->)
    [ (_ name pbl (crypto ...) (args ...) -> sort)
    (define name (declare-function pbl
        (mk-fun (symbol->string 'name) (list crypto ...) args ... sort))) ]
    [ (_ name pbl (args ...) -> sort)
    (define-function name pbl () (args ...) -> sort) ]
    [ (_ name pbl sort)
    (define-function name pbl () () -> sort) ]
    [ (_ name pbl (crypto ...) sort)
    (define-function name pbl (crypto ...) () -> sort) ]))

(define-syntax add-constrain
  (syntax-rules ()
    [ (_ pbl (vars ...) constrain)
    (let [ (vars (cv-mk-varf (cv-mk-fresh-var-w-sort cv-Index))) ...]
      (cv-add-constrain pbl constrain)) ]))

(define-syntax publish
  (syntax-rules ()
    [ (_ pbl ((vars sorts) ...) term)
    (let [ (vars (cv-mk-fresh-var-w-sort sorts)) ...]
      (cv-publish pbl (list vars ...) term)) ]))

(define (cand . args) (cv-cand args))
(define (cor . args) (cv-cor args))
(define (tuple . args) (cv-tuple args))
(define (eql a b) (eq (bitstring-length a) (bitstring-length b)))
(define <> incompatible)
