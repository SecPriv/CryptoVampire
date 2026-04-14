(require "../save-results.scm")
(require "cryptovampire/function")
(require "cryptovampire/builtin-functions")
(require "cryptovampire/cryptography")
(require "cryptovampire/protocol")
(require "cryptovampire/solver")
(require "cryptovampire/sort")
(require "cryptovampire/formula")
(require "cryptovampire/signature")
(require-builtin cryptovampire/ll/pbl as pbl.)
(require-builtin cryptovampire/ll/configuration as config.)
(require-builtin cryptovampire/ll as b.)
(require-builtin cryptovampire/ll/report as report.)
(require-builtin cryptovampire/ll/builtin-functions as builtin.)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define prf (declare-cryptography pbl))

(define-function H pbl (prf) (Bitstring) -> Bitstring)
(define-function key pbl (Index) -> Nonce)
(define-function seed pbl (Index) -> Nonce)

(define kT (declare-memory-cell pbl "kT" (list Index) (lambda (i) (seed i))))

(define tag
  (declare-step pbl "tag" (list Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i cells . _) (H (cells kT)))
      (lambda (in i cells . _) (list (store-cell (kT i) := (H (cells kT))))))
    (step p2
      (lambda _ mtrue)
      (lambda (in i cells . _) (H (cells kT)))
      (lambda (in i cells . _) (list (store-cell (kT i) := (H (cells kT))))))))

(initialize-as-prf prf H)

(config.set_smt_timeout pbl (b.mult->duration scale-timeout (b.string->duration "150ms")))
(config.set_fa_limit pbl 1)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed toy-state-equiv"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "toy-state-equiv" pbl)
