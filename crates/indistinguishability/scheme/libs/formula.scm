(provide 
  cand cor ctuple tuple
  exists forall findst
  mexists mforall mfindst
  subst)
(require "cryptovampire/function") 
(require-builtin cryptovampire/ll/builtin-functions as funs->)
(require-builtin cryptovampire/ll/variable as var->)
(require-builtin cryptovampire/ll/formula as f->)
(require-builtin cryptovampire/ll/signature as sig->)


;; This is some ChatGPT magic ^^''
(define (mexists sorts arg)
  (let loop ((ss sorts) (vars '()))
    (if (null? ss)
      ;; once all vars generated
      (let ((rev-vars (reverse vars)))
        (f->binder f->binder->exists rev-vars (list (apply arg rev-vars))))
      ;; otherwise, generate next var and recur
      (let* ((s (car ss))
          (v (var->fresh-with-sort s)))
        (loop (cdr ss) (cons v vars))))))

(define (mforall sorts arg)
  (let loop ((ss sorts) (vars '()))
    (if (null? ss)
      ;; once all vars generated
      (let ((rev-vars (reverse vars)))
        (f->binder f->binder->forall rev-vars (list (apply arg rev-vars))))
      ;; otherwise, generate next var and recur
      (let* ((s (car ss))
          (v (var->fresh-with-sort s)))
        (loop (cdr ss) (cons v vars))))))

(define (mfindst sorts arg1 arg2 arg3)
  (let*
    [ (vars (map var->fresh-with-sort sorts))
    (varsf (map f->var vars))
    (c (apply arg1 varsf))
    (l (apply arg2 varsf)) ]
    (f->binder f->binder->findst vars (list c l arg3))))

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

(define (cand . args) (f->cand args))
(define (cor . args) (f->cor args))
(define (ctuple . args) (f->ctuple args))
(define tuple ctuple)

(define (subst a b f)
  (cond
    [(equal? f a) b]
    [(f->var? f) f]
    [(f->app? f)
     (let ((parts (f->destruct f)))
       (f->app (car parts) (map (lambda (arg) (subst a b arg)) (cadr parts))))]
    [(f->binder? f)
     (let ((parts (f->destruct f)))
       (f->binder (car parts) (cadr parts)
                  (map (lambda (arg) (subst a b arg)) (caddr parts))))]
    [else f]))