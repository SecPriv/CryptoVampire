(provide
  step
  step-protocol
  declare-step declare-same-step
  set-init-step)
(require-builtin cryptovampire/ll/pbl as pbl->)
(require-builtin cryptovampire/ll/step as step->)
(require-builtin cryptovampire/ll/formula as f->)
(require "cryptovampire/function")
(require "cryptovampire/stdlib")
(require "cryptovampire/builtin-functions")


(struct step (protocol condition message))

(define (declare-step pbl name sorts . content)
  (let* [
    (step (step->declare-step pbl name sorts))
    (stepf (register-function step)) ]
    (begin
      (for-each (lambda (c)
          (let* [
            (ptclf (step-protocol c))
            (msgf (step-message c))
            (condf (step-condition c))
            (ptcl (get-function ptclf))
            (variables
              (map f->var (step->get-vars pbl step ptcl)))
            (applied-step (if (empty? variables) stepf (apply stepf variables)))
            (in (macro_input applied-step ptclf)) ]
            (begin
              (step->set-msg pbl step ptcl
                (apply msgf (cons in variables)))
              (step->set-cond pbl step ptcl
                (apply condf (cons in variables))))))
        content)
      stepf)))

(define (declare-same-step pbl name ptcls sorts msg mcond)
  (let* [
    (declare (partial declare-step pbl name sorts))
    (content (map (lambda (p) (step p (partial msg p) (partial mcond p))) ptcls)) ]
    (apply declare content)))

(define (set-init-step pbl . content)
  (let [ (s (get-function init)) ]
    (begin
      (for-each (lambda (c)
          (let [ (condf (step-message c)) (ptcl (step-protocol c)) ]
            (step->set-msg pbl s (get-function ptcl)
              condf)))))))
