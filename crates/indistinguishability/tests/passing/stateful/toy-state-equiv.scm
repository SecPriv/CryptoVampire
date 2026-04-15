(require "../../save-results.scm")
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

(define-function H pbl (prf) (Bitstring Bitstring) -> Bitstring)
(define-function key pbl (Index) -> Nonce)
(define-function n pbl (Index Index) -> Nonce)
(define-function seed pbl (Index) -> Nonce)

(define kT (declare-memory-cell pbl "kT" (list Index) (lambda (_ i) (seed i))))

(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i _ cells . _) (H (cells kT i) (key i)))
      (lambda (in i _ cells . _) (list (store-cell ((_) kT i) := (H (cells kT i) (key i))))))
    (step p2
      (lambda _ mtrue)
      (lambda (in i j cells . _) (n i j))
      (lambda (in i _ cells . _) (list (store-cell ((_) kT i) := (H (cells kT i) (key i))))))))

(initialize-as-prf prf H)

(pbl.add-smt-axiom pbl
  (forall ((t1 Time) (i Index) (i2 Index) (j Index))
    (=> (and (happens (tag i j)) (lt t1 (tag i j)))
      (not (eq (macro_memory_cell (kT i) (tag i j) p1) (macro_memory_cell (kT i2) t1 p1))))))

(config.set_smt_timeout pbl (b.mult->duration scale-timeout (b.string->duration "1s")))
(config.set_fa_limit pbl 1)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed toy-state-equiv"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "toy-state-equiv" pbl)
