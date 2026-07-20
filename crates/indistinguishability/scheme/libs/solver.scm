(provide
  bind prolog
  add-golgge-rule add-smt-axiom add-rewrite
  add-constrain publish
  run mk-problem declare-protocol)
(require-builtin cryptovampire/ll/variable as var->)
(require-builtin cryptovampire/ll/formula as f->)
(require-builtin cryptovampire/ll/pbl as pbl->)
(require-builtin cryptovampire/ll/rule as rule->)
(require-builtin cryptovampire/ll/configuration as conf->)
(require-builtin cryptovampire/ll/rewrite as rw->)
(require-builtin cryptovampire/ll/report as report->)
(require-builtin cryptovampire/ll as base->)
(require "cryptovampire/function")
(require "cryptovampire/sort")

(define-syntax bind
  (syntax-rules ()
    [ (_ ((ids sorts) ...) arg)
      (let [ (ids (var->fresh-with-sort sorts)) ...] arg) ]))

(define-syntax prolog
  (syntax-rules (:-)
    [ (_ name from)
      (rule->new-prolog name from '()) ]
    [ (_ name from :- to ...)
      (rule->new-prolog name
        from (list to ...)) ]))

(define add-golgge-rule pbl->add-rule)
(define add-smt-axiom pbl->add-smt-axiom)
(define add-rewrite pbl->add-rewrite)

(define (run pbl p1 p2)
  (pbl->run pbl (get-function p1) (get-function p2)))
(define (mk-problem _) (pbl->empty base->cli-config))

(define-syntax add-constrain
  (syntax-rules ()
    [ (_ pbl (vars ...) constrain)
      (let [ (vars (f->var (var->fresh-with-sort Index))) ...]
        (pbl->add-constrain pbl constrain)) ]))

(define-syntax publish
  (syntax-rules ()
    [ (_ pbl ((vars sorts) ...) term)
      (let [ (vars (var->fresh-with-sort sorts)) ...]
        (pbl->publish pbl (list vars ...) term)) ]))

(define (declare-protocol pbl)
  (register-function (pbl->declare-protocol pbl)))
