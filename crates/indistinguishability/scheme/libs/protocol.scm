(provide
  step
  step-protocol
  declare-step
  set-init-step)
(require-builtin cryptovampire/ll/pbl as pbl->)
(require-builtin cryptovampire/ll/step as step->)
(require-builtin cryptovampire/ll/formula as f->)
(require "cryptovampire/function")
(require "cryptovampire/builtin-functions")


(struct step (protocol condition message))

(define (declare-step pbl name sorts . content)
  (let*
    [ (step (step->declare-step pbl name sorts))
    (stepf (register-function step)) ]
    (begin
      (for-each (lambda (c)
          (let*
            [ (ptclf (step-protocol c))
            (msgf (step-message c))
            (condf (step-condition c))
            (ptcl (get-function ptclf))
            (variables
              (map f->var (step->get-vars pbl step ptcl)))
            (in (macro_input (apply stepf variables) ptclf)) ]
            (begin
              (step->set-msg pbl step ptcl
                (apply msgf (cons in variables)))
              (step->set-cond pbl step ptcl
                (apply condf (cons in variables))))))
        content)
      stepf)))

(define (set-init-step pbl . content)
  (let [ (s (get-function init)) ]
    (begin
      (for-each (lambda (c)
          (let [ (condf (step-message c)) (ptcl (step-protocol c)) ]
            (step->set-msg pbl s (get-function ptcl)
              condf)))))))
