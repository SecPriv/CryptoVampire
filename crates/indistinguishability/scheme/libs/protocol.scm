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


;; ---------------------------------------------------------------------------
;; step
;;
;; A struct describing one *instance* of a step, i.e. a run of the step inside
;; one protocol.  Fields:
;;   protocol      -- the protocol value (as returned by `declare-protocol`)
;;   condition     -- a function `(lambda (p in args ...) formula)` returning the
;;                    condition under which the step runs
;;   message       -- a function `(lambda (p in args ...) term)` returning the
;;                    message produced by the step
;;   assignements  -- a function `(lambda (in cells ...) (list (store-cell ...) ...))`
;;                    (or `empty-assignements`) updating memory cells
;; Pass a list of these to `declare-step` (one per protocol).
;; ---------------------------------------------------------------------------

(struct step (protocol condition message assignements))
(struct assignement (cell single-assignement))

(@doc (cv-help "empty-assignements" "(empty-assignements . _)"
  "A step that assigns nothing: use as the `assignements` field of a `step` when the step updates no memory cell.")
 (define empty-assignements (lambda _ '())))

(define __inner-get-function fun.get-function)
(define __inner-get-input-sorts fun.get-input-sorts)
(define __inner-mk-single-assignment step->mk-single-assignment)
(define __inner-fresh-with-sort var->fresh-with-sort)
(define __inner-convert-to-formula fun.convert-to-formula)

(define (ensure-var f) (cond
    [ (t->Variable? f) f]
    [ (f->var? f) (car (f->destruct f)) ]
    [else (error "should be a variable") ]))


;; ---------------------------------------------------------------------------
;; store-cell
;;
;; Declares an update of a memory cell, to be used inside the `assignements`
;; function of a `step`:
;; ```scheme
;; (list (store-cell s := mempty))                      ; cell without index
;; (list (store-cell ((_) kT i) := (H (cells kT i) (key i))))  ; indexed cell
;; ```
;; The left-hand side is the cell (with index variables); the right-hand side
;; is the new value term.
;; ---------------------------------------------------------------------------

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


;; ---------------------------------------------------------------------------
;; declare-step
;;
;; Declares a step `name` in `pbl`, taking inputs of the given `sorts` (e.g.
;; `(list Index Index)`) plus the implicit input we receive and the current
;; time.  `content` is a `step` struct per protocol, describing how the step
;; behaves in each of them.
;;
;; *Example:* (from the tests)
;; ```scheme
;; (define rf (declare-step pbl "rf" (list Index)
;;   (step p1 (lambda _ mtrue)
;;         (lambda (p in i . _) (mnot (exists ((j Index)) ...)))
;;         empty-assignements)
;;   (step p2 (lambda _ mtrue) (lambda (p in i . _) ko) empty-assignements)))
;; ```
;;
;; The step functions receive `(p in custom-args...)` where `in` is the input
;; message and `custom-args` are fresh terms for the declared input sorts.
;; ---------------------------------------------------------------------------

(@doc (cv-help "declare-step" "(declare-step pbl name sorts . contents)"
  "Declares a step named `name` taking inputs of `sorts`, with one `step` struct per protocol."
  "Returns the registered (lifted) step function; call it with fresh input terms to build the step term, e.g. `(tag i j)`.")
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
    stepf))))

;; ---------------------------------------------------------------------------
;; declare-same-step
;;
;; A shorthand for `declare-step` when the same step is implemented in several
;; protocols at once: `ptcls` is the list of protocols, and the message /
;; condition are given once as functions over a protocol argument.
;;
;; *Example:* (from the tests)
;; ```scheme
;; (define tag (declare-same-step pbl "tag" ptcls (list Index Index)
;;   (lambda _ mtrue)
;;   (lambda (p in i j . _) (tuple (n i j) (mhash (n i j) (mk i j p))))
;;   empty-assignements))
;; ```
;; ---------------------------------------------------------------------------

(@doc (cv-help "declare-same-step" "(declare-same-step pbl name ptcls sorts msg mcond assignements)"
  "Declares the step `name` for every protocol in `ptcls`, sharing the message `msg` and condition `mcond` functions `(lambda (p args...) ...)`.")
 (define (declare-same-step pbl name ptcls sorts msg mcond assignements)
  (let* [
      (declare (partial declare-step pbl name sorts))
      (content (map (lambda (p) (step p (partial msg p) (partial mcond p) assignements)) ptcls)) ]
    (apply declare content))))

;; ---------------------------------------------------------------------------
;; declare-memory-cell
;;
;; Declares a stateful memory cell with index parameters `params` and an initial
;; value function `init` taking `(protocol . vars)` and returning the initial
;; value term of the cell in that protocol.
;;
;; *Example:* (from the tests)
;; ```scheme
;; (define s (declare-memory-cell pbl "s" '() (lambda (p) empty)))
;; (define kT (declare-memory-cell pbl "kT" (list Index) (lambda (_ i) (seed i))))
;; ```
;; Read the current value with `(cells <cell> ...)` inside step assignements,
;; and update with `store-cell`.
;; ---------------------------------------------------------------------------

(@doc (cv-help "declare-memory-cell" "(declare-memory-cell pbl name params init)"
  "Declares a memory cell `name` with one value per index combination in `params` (and per protocol)."
  "`init` returns the initial value: `(lambda (protocol . vars) value)`.  Returns the registered cell function.")
 (define (declare-memory-cell pbl name params init)
  (let* [
      (params (map var->fresh-with-sort params))
      (initv (map (lambda (p) (apply init (cons p params))) (pbl->get-all-protocols pbl)))
      (cell (pbl->declare-memory-cell pbl name params initv))
      (cellf (fun.register-function cell)) ]
    cellf)))
