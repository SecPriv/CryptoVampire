(provide
  step
  step-protocol
  declare-step declare-same-step
  declare-memory-cell
  store-cell
  empty-assignements)
(require-builtin cryptovampire/ll/pbl as pbl->)
(require-builtin cryptovampire/ll/step as step->)
(require-builtin cryptovampire/ll/formula as f->)
(require-builtin cryptovampire/ll/builtin-functions as funs->)
(require-builtin cryptovampire/ll/variable as var->)
(require (prefix-in fun. "cryptovampire/function"))
(require "cryptovampire/stdlib")
(require "cryptovampire/builtin-functions")
(require (prefix-in t-> "cryptovampire/type"))


(struct step (protocol condition message assignements))
(struct assignement (cell single-assignement))

(define empty-assignements (lambda _ '()))

(define __inner-get-function fun.get-function)
(define __inner-get-input-sorts fun.get-input-sorts)
(define __inner-mk-single-assignment step->mk-single-assignment)
(define __inner-fresh-with-sort var->fresh-with-sort)
(define __inner-convert-to-formula fun.convert-to-formula)

(define (ensure-var f) (cond
    [ (t->Variable? f) f]
    [ (f->var? f) (car (f->destruct f)) ]
    [else (error "should be a variable") ]))


(define-syntax store-cell
  (syntax-rules (:=)
    [
      (_ ((vars ...) cell cargs ...) := value)
      (let* [
          (cell-sorts (__inner-get-input-sorts cell))
          (cell-fresh-vars (map __inner-fresh-with-sort cell-sorts))
          (args-vars (map ensure-var ((lambda (vars ...) (list cargs ...)) cell-fresh-vars)))
          (valuef (__inner-convert-to-formula (apply (lambda (vars ...) value) cell-fresh-vars)))
        ]
      (assignement (__inner-get-function cell) (__inner-mk-single-assignment args-vars cell-fresh-vars valuef)))
  ]
[
  (_ cell := value)
  (assignement (__inner-get-function cell) (__inner-mk-single-assignment '() '() value))
]))

;; if an arguement remain after the argument to the step, it will be taken for the time
(define (mk-cell-macro time ptcl cell . args)
  (let*
    [
      (cell-arity (fun.arity cell))
      (cell-args (take args cell-arity))
      (remaining-args (drop args cell-arity))
      (ftime
        (if (empty? remaining-args)
          time
          (car remaining-args)))
      (fcell (if (t->Formula? cell) cell (apply cell cell-args)))
    ]
  (macro_memory_cell fcell ftime ptcl)))


(define (declare-step pbl name sorts . content)
  (let* [
      (step (step->declare-step pbl name sorts))
      (stepf (fun.register-function step)) ]
    (begin
      (map (lambda (c)
          (let* [
              (ptclf (step-protocol c))
              (msgf (step-message c))
              (condf (step-condition c))
              (assignements (step-assignements c))
              (ptcl (fun.get-function ptclf))
              (variables
                (map f->var (step->get-vars pbl step ptcl)))
              (applied-step (if (t->Formula? stepf) stepf (apply stepf variables)))
              (in (macro_input applied-step ptclf))
              (cells (partial mk-cell-macro (pred applied-step) ptclf))
              (args (append (cons in variables) (list cells)))
            ]
          (begin
            (step->set-msg pbl step ptcl
              (apply msgf args))
            (step->set-cond pbl step ptcl
              (apply condf args))
            (for-each (lambda (assignement)
                (step->insert-assignement pbl step ptcl (assignement-cell assignement)
                  (assignement-single-assignement assignement)))
              (apply assignements args)))))
      content)
    stepf)))

(define (declare-same-step pbl name ptcls sorts msg mcond assignements)
  (let* [
      (declare (partial declare-step pbl name sorts))
      (content (map (lambda (p) (step p (partial msg p) (partial mcond p) assignements)) ptcls)) ]
    (apply declare content)))

;; Memory cell helpers
(define (declare-memory-cell pbl name params init)
  (let* [
      (params (map var->fresh-with-sort params))
      (initv (map (lambda (p) (apply init (cons p params))) (pbl->get-all-protocols pbl)))
      (cell (pbl->declare-memory-cell pbl name params initv))
      (cellf (fun.register-function cell)) ]
    cellf))
