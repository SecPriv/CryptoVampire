(provide
  cand cor ctuple tuple
  exists forall findst
  mexists mforall mfindst
  subst
  formula-doc)
(require "cryptovampire/function")
(require "cryptovampire/doc")
(require-builtin cryptovampire/ll/builtin-functions as funs->)
(require-builtin cryptovampire/ll/variable as var->)
(require-builtin cryptovampire/ll/formula as f->)
(require-builtin cryptovampire/ll/signature as sig->)

;; Documentation table for the `cryptovampire/formula` library (macro & value
;; docs, next to their definitions).  See `cryptovampire/doc` for the mechanism.
(define formula-doc (make-doc-table))
(define (register-syntax-doc! name . doc)
  (set! formula-doc (apply doc-add! formula-doc name doc)))
(define (register-type-doc! name . doc)
  (set! formula-doc (apply doc-add! formula-doc name doc)))


;; ---------------------------------------------------------------------------
;; Quantifiers.
;;
;; `exists` / `forall` / `findst` are the convenient macros:
;; ```scheme
;; (exists ((i Index) (j Index)) body)
;; (forall ((i Index)) body)
;; (findst ((i Index)) cond formula result)
;; ```
;; They bind fresh (existential/universal) variables of the given sorts and
;; build the corresponding quantified formula.  The `m*` functions below are
;; their functional counterparts, exposed mainly for the macros.
;; ---------------------------------------------------------------------------


(register-syntax-doc! 'exists
  "Binds fresh existential variables of the given sorts and builds an `exists` formula over `body`."
  ""
  "**Usage:**"
  "```scheme"
  "(exists ((i Index) (j Index)) body)"
  "```")

(define-syntax exists
  (syntax-rules ()
    [ (_ ((ids sorts) ...) arg)
      (mexists (list sorts ...) (lambda (ids ...) arg)) ]))
(define-syntax forall
  (syntax-rules ()
    [ (_ ((ids sorts) ...) arg)
      (mforall (list sorts ...) (lambda (ids ...) arg)) ]))

(register-syntax-doc! 'forall
  "Binds fresh universal variables of the given sorts and builds a `forall` formula over `body`."
  ""
  "**Usage:**"
  "```scheme"
  "(forall ((i Index)) body)"
  "```")

(define-syntax findst
  (syntax-rules ()
    [ (_ ((ids sorts) ...) arg1 arg2 arg3)
      (mfindst (list sorts ...)
        (lambda (ids ...) arg1)
        (lambda (ids ...) arg2)
        arg3) ]))

(register-syntax-doc! 'findst
  "Builds a `find such-that` formula: binds the given vars, evaluates `cond` and `formula` over them, returns `result`."
  ""
  "**Usage:**"
  "```scheme"
  "(findst ((i Index)) cond formula result)"
  "```")


;; This is some ChatGPT magic ^^''
(@doc (cv-help "mexists" "(mexists (list Sort ...) builder)"
    "Builds an `exists` formula over one fresh variable per sort in `sorts`."
    "`builder` is applied to the fresh variables and must return the formula to quantify (`body` of the `exists` macro).  Prefer the `exists` macro.")
  (define (mexists sorts arg)
    (let loop ((ss sorts) (vars '()))
      (if (null? ss)
        ;; once all vars generated
        (let ((rev-vars (reverse vars)))
          (f->binder f->binder->exists rev-vars (list (apply arg rev-vars))))
        ;; otherwise, generate next var and recur
        (let* ((s (car ss))
            (v (var->fresh-with-sort s)))
          (loop (cdr ss) (cons v vars)))))))

(@doc (cv-help "mforall" "(mforall (list Sort ...) builder)"
    "Builds a `forall` formula over one fresh variable per sort in `sorts`."
    "`builder` is applied to the fresh variables and must return the formula to quantify.  Prefer the `forall` macro.")
  (define (mforall sorts arg)
    (let loop ((ss sorts) (vars '()))
      (if (null? ss)
        ;; once all vars generated
        (let ((rev-vars (reverse vars)))
          (f->binder f->binder->forall rev-vars (list (apply arg rev-vars))))
        ;; otherwise, generate next var and recur
        (let* ((s (car ss))
            (v (var->fresh-with-sort s)))
          (loop (cdr ss) (cons v vars)))))))

(@doc (cv-help "mfindst" "(mfindst (list Sort ...) cond-builder formula-builder result)"
    "Builds a `find such that` formula over one fresh variable per sort in `sorts`."
    "`cond-builder` and `formula-builder` are applied to the fresh variables; `result` is a plain term.  Prefer the `findst` macro.")
  (define (mfindst sorts arg1 arg2 arg3)
    (let*
      [ (vars (map var->fresh-with-sort sorts))
        (varsf (map f->var vars))
        (c (apply arg1 varsf))
        (l (apply arg2 varsf)) ]
      (f->binder f->binder->findst vars (list c l arg3)))))


(@doc (cv-help "cand" "(cand . args)"
    "Symbolic `and` of the given boolean formulas.")
  (define (cand . args) (f->cand args)))

(@doc (cv-help "cor" "(cor . args)"
    "Symbolic `or` of the given boolean formulas.")
  (define (cor . args) (f->cor args)))

(@doc (cv-help "ctuple" "(ctuple . args)"
    "Builds a tuple term from the given terms.  `tuple` is a synonym."
    "\nThis also auto-nests arguments. Therefore it accpepts more than 2 arguments")
  (define (ctuple . args) (f->ctuple args)))

(define tuple ctuple)

(register-type-doc! 'tuple
  "Synonym of `ctuple`: builds a tuple term from the given terms."
  ""
  "**Usage:**"
  "```scheme"
  "(tuple a b c)"
  "```")

(@doc (cv-help "subst" "(subst a b f)"
    "Returns `f` with every occurrence of term `a` replaced by `b`."
    "\n**NB**: the logic is very simple. Notably variables are not taken into account for unification or capture avoidance. Correctness is therefore the caller's responsibility.")
  (define (subst a b f)
    (cond
      [ (equal? f a) b]
      [ (f->var? f) f]
      [ (f->app? f)
        (let ((parts (f->destruct f)))
          (f->app (car parts) (map (lambda (arg) (subst a b arg)) (cadr parts)))) ]
      [ (f->binder? f)
        (let ((parts (f->destruct f)))
          (f->binder (car parts) (cadr parts)
            (map (lambda (arg) (subst a b arg)) (caddr parts)))) ]
      [else f])))
