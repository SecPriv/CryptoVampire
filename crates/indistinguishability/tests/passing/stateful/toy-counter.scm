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

(define-function h pbl (prf) (Bitstring Bitstring) -> Bitstring)
(define-function secret pbl Nonce)
(define-function key pbl Nonce)
(define-function myZero pbl Bitstring)
(define-function mySucc pbl (Bitstring) -> Bitstring)

(define d (declare-memory-cell pbl "d" '() (lambda _ myZero)))

(define A (declare-step pbl "A" '()
    (step p1
      (lambda _ mtrue)
      (lambda (in . cells) (h (tuple (car cells) secret) key))
      (lambda (_ . cells) (list (store-cell d := (mySucc (car cells))))))))

(define B (declare-step pbl "B" '()
    (step p1
      (lambda (p in . cells)
        (eq in (h (tuple (car cells) secret) key)))
      (lambda (p in . cells)
        (if (eq p p1) secret myZero))
      (lambda (p in . cells) (list (store-cell d := (mySucc (car cells))))))))

(initialize-as-prf prf h)

(pbl.add-smt-axiom pbl (forall ((n Bitstring))
  (not (eq n (mySucc n)))))

(config.set_smt_timeout pbl (b.mult->duration scale-timeout (b.string->duration "150ms")))
(config.set_fa_limit pbl 1)

(displayln "toy-counter setup complete")
