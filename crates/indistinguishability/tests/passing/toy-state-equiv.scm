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
(require-builtin cryptovampire/ll/rewrite as rw.)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define prf (declare-cryptography pbl))

(define-function hkey pbl (prf) (Bitstring) -> Bitstring)
(define-function ok pbl Bitstring)
(define-function ko pbl Bitstring)
(define-function key pbl (Index) -> Nonce)
(define-function seed pbl (Index) -> Nonce)
(define-function n pbl (Index Index) -> Nonce)

(define kT (declare-memory-cell pbl "kT" (list Index) (lambda (i) (seed i))))

(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i j cells . _)
        (let ((old-val (cells kT)))
          (tuple (hkey old-val) (hkey old-val (key i)))))
      (lambda (in i j cells . _)
        (list (store-cell (kT i) := (hkey (cells kT) (key i))))))
    (step p2
      (lambda _ mtrue)
      (lambda (in i j cells . _)
        (let ((old-val (cells kT)))
          (tuple (hkey old-val) (n i j))))
      (lambda (in i j cells . _)
        (list (store-cell (kT i) := (hkey (cells kT) (key i))))))))

(initialize-as-prf prf hkey)

(bind ((i Index) (j Index) (t Time) (p Protocol))
  (let ((in (macro_input t p)))
    (add-rewrite pbl (rw.new "stateInequality" (list i j t p)
        (eq in (hkey (macro_memory_cell kT t p) (key i)))
        (exists ((j Index))
          (cand
            (eq in (sel1of2 (macro_msg (tag i j) p)))
            (lt (tag i j) t)))))))

(add-smt-axiom pbl (forall ((i Index) (j Index) (p Protocol))
  (not (eq (key i) (n i j)))))

(config.set_smt_timeout pbl (b.mult->duration scale-timeout (b.string->duration "2s")))
(config.set_fa_limit pbl 2)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed toy-state-equiv"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "toy-state-equiv" pbl)
