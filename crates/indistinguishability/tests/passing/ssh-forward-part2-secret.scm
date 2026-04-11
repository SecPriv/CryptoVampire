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
(define ptcls (list p1 p2))

(define ddh (declare-cryptography pbl))
(define-function g pbl (ddh) Bitstring)
(define-function mexp pbl (ddh) (Bitstring Bitstring) -> Bitstring)
(initialize-as-ddh ddh g mexp)

(define-function a1 pbl Nonce)
(define-function b1 pbl Nonce)
(define-function c11 pbl Nonce)

(register-fresh-nonce ddh '() c11)

(define empty-cond (lambda _ mtrue))

(define SDIS1 (declare-same-step pbl "SDIS1" ptcls '()
    empty-cond
    (lambda (p in . _) (mexp g b1))
    empty-assignements))

(define SDIS2 (declare-step pbl "SDIS2" '()
    (step p1 (lambda (in . _) (eq in (mexp g a1)))
      (lambda (in . _) (mexp (mexp g a1) b1))
      empty-assignements)
    (step p2 (lambda (in . _) (eq in (mexp g a1)))
      (lambda (in . _) (mexp g c11))
      empty-assignements)))

(add-constrain pbl () (lt SDIS1 SDIS2))

(publish pbl () (mexp g a1))
(publish pbl () (mexp g b1))

(define default-timeout (b.string->duration "300ms"))
(config.set_smt_timeout pbl (b.mult->duration scale-timeout default-timeout))


(if (run pbl p1 p2)
  (displayln "success")
  (error "failed ssh-forward-part2-secret"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "ssh-forward-part2-secret" pbl)
