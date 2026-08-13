(require "./scripts/save-results.scm")
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
(define-function k11 pbl Nonce)

(register-fresh-nonce ddh '() k11)

(define empty-cond (lambda _ mtrue))

(define P1 (declare-same-step pbl "P1" ptcls '()
    empty-cond
    (lambda (p in . _) (mexp g a1))
    empty-assignements))

(define P2 (declare-step pbl "P2" '()
    (step p1 (lambda (in . _) (eq in (mexp g b1)))
      (lambda (in . _) (mexp (mexp g a1) b1))
      empty-assignements)
    (step p2 (lambda (in . _) (eq in (mexp g b1)))
      (lambda (in . _) (mexp g k11))
      empty-assignements)))

(define S1 (declare-same-step pbl "S1" ptcls '()
    empty-cond
    (lambda (p in . _) (mexp g b1))
    empty-assignements))

(define S2 (declare-step pbl "S2" '()
    (step p1 (lambda (in . _) (eq in (mexp g a1)))
      (lambda (in . _) (mexp (mexp g a1) b1))
      empty-assignements)
    (step p2 (lambda (in . _) (eq in (mexp g a1)))
      (lambda (in . _) (mexp g k11))
      empty-assignements)))

(add-constrain pbl () (lt P1 P2))
(add-constrain pbl () (lt S1 S2))

(publish pbl () (mexp g a1))
(publish pbl () (mexp g b1))

(define mehhh (declare-step pbl "meh" '()
    (step p1 empty-cond (lambda _ (mexp (mexp g a1) b1)) empty-assignements)
    (step p2 empty-cond (lambda _ (mexp g k11)) empty-assignements)
  ))
(add-constrain pbl () (lt mehhh S1))
(add-constrain pbl () (lt mehhh P1))
(add-rewrite pbl (rw.new "l1" '() (mexp (mexp g a1) b1) (unfold_msg mehhh p1) ))
(add-rewrite pbl (rw.new "l2" '() (mexp g k11) (unfold_msg mehhh p2) ))

(register-fresh-nonce ddh '() k11)

;; configuration
(config.set_guided_nonce_search pbl #t)

(run-and-save "ssh-forward-part1-secret" pbl p1 p2 "150ms")