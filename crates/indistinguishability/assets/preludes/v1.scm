(require-builtin cryptovampire)

(define (Nonce? f) (equal? Nonce (get-sort f)))

(define (convert-to-formula arg)
  (if (Variable? arg) (mk-varf arg) 
  (if (boolean? arg) (if arg (mk-appf __pre_mtrue '()) (mk-appf __pre_mfalse '()))
  arg)))

(define (lift-fun fun-name)
  (if (= (arity fun-name) 0)
    (mk-appf fun-name '())
    (lambda args 
      (if (= (length args) (arity fun-name))
        (mk-appf fun-name (map convert-to-formula args))
        (begin
          (displayln (function-name fun-name))
          (error "Wrong arity")
        ))
      )))



; @@@DEFINITIONS@@@

(define S λS)
(define O λO)

;; This is some ChatGPT magic ^^''
(define (mexists sorts arg)
  (let loop ((ss sorts) (vars '()))
    (if (null? ss)
        ;; once all vars generated
        (let ((rev-vars (reverse vars)))
          (mk-binderf existsf rev-vars (list (apply arg rev-vars))))
        ;; otherwise, generate next var and recur
        (let* ((s (car ss))
               (v (mk-fresh-var-w-sort s)))
          (loop (cdr ss) (cons v vars))))))

(define (mforall sorts arg)
  (let loop ((ss sorts) (vars '()))
    (if (null? ss)
        ;; once all vars generated
        (let ((rev-vars (reverse vars)))
          (mk-binderf forallf rev-vars (list (apply arg rev-vars))))
        ;; otherwise, generate next var and recur
        (let* ((s (car ss))
               (v (mk-fresh-var-w-sort s)))
          (loop (cdr ss) (cons v vars))))))

(define (mfindst sorts arg1 arg2 arg3)
  (let loop ((ss sorts) (vars '()))
    (if (null? ss)
        (let ((rev-vars (reverse vars)))
          (mk-binderf findstf rev-vars 
            (list 
              (apply arg1 rev-vars)
              (apply arg2 rev-vars) 
              arg3)))
        (let* ((s (car ss))
               (v (mk-fresh-var-w-sort s)))
          (loop (cdr ss) (cons v vars))))))

(define-syntax bind
  (syntax-rules ()
  [(_ ((ids sorts) ...) arg) (let [(ids (mk-fresh-var-w-sort sorts)) ...] arg)]))

(define-syntax exists
  (syntax-rules () 
  [(_ ((ids sorts) ...) arg)
    (mexists (list sorts ...) (lambda (ids ...) arg))]))
(define-syntax forall
  (syntax-rules () 
  [(_ ((ids sorts) ...) arg)
    (mforall (list sorts ...) (lambda (ids ...) arg))]))
(define-syntax findst
  (syntax-rules () 
  [(_ ((ids sorts) ...) arg1 arg2 arg3)
    (mforall (list sorts ...) (lambda (ids ...) arg1) (lambda (ids ...) arg2) arg3)]))

(define (set-message pbl step ptcl msg) 
  (let* [(vars (map mk-varf (get-step-variables pbl step ptcl)))
          (in (macro_input (mk-appf step vars) (mk-appf ptcl '())))]
  (set-step-message pbl step ptcl (apply msg (cons in vars)))))
(define (set-condition pbl step ptcl condition) 
  (let* [(vars (map mk-varf (get-step-variables pbl step ptcl)))
          (in (macro_input (mk-appf step vars) (mk-appf ptcl '())))]
  (set-step-condition pbl step ptcl (apply condition (cons in vars)))))

(define-syntax signature
  (syntax-rules (->)
  [(_ () -> sort) (mk-signature '() sort)]
  [(_ (sorts ...) -> sort) (mk-signature (list sorts ...) sort)]
  [(_ sort) (mk-signature '() sort)]
  ))

(define-syntax prolog
  (syntax-rules (:-)
  [(_ name from) 
    (mk-prolog name from '())]
  [(_ name from :- to ...) 
    (mk-prolog name 
      from (list to ...  ))]
))