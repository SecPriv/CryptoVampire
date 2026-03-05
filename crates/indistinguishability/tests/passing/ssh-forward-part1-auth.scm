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

(define-function ok pbl Bitstring)
(define-function ko pbl Bitstring)
(define-function forwarded pbl Bitstring)

(define ddh (declare-cryptography pbl))
(define-function g pbl (ddh) Bitstring)
(define-function mexp pbl (ddh) (Bitstring Bitstring) -> Bitstring)
(initialize-as-ddh ddh g mexp)

(define prf (declare-cryptography pbl))
(define-function h pbl (prf) (Bitstring Bitstring) -> Bitstring)
(initialize-as-prf prf h)

(define euf-cma (declare-cryptography pbl))
(define-function sign pbl (euf-cma) (Bitstring Bitstring) -> Bitstring)
(define-function checksign pbl (euf-cma) (Bitstring Bitstring Bitstring) -> Bool)
(define-function vk pbl (euf-cma) (Bitstring) -> Bitstring)

(define senc (declare-cryptography pbl))
(define-function enc pbl (senc) (Bitstring Bitstring Bitstring) -> Bitstring)
(define-function dec pbl (senc) (Bitstring Bitstring) -> Bitstring)
(initialize-as-senc senc enc dec)

;; honest nonces
(define-function a1 pbl Nonce)
(define-function b1 pbl Nonce)
(define-function k11 pbl Nonce)
(define-function hKey pbl Nonce)
(define-function skP pbl Nonce)
(define-function skS pbl Nonce)
(define-function rP pbl Nonce)

;; attacker nonces
(define-function a pbl (Index) -> Nonce)
(define-function b pbl (Index) -> Nonce)

(publish pbl ((i Index)) (mexp g (a i)))
(publish pbl ((i Index)) (mexp g (b i)))
; (publish pbl () (mexp g a1))
; (publish pbl () (mexp g b1))
(publish pbl () hKey)

; (publish pbl () skP)
; (publish pbl () rP)
; (publish pbl () skS)

;; Protocol P
(define P1 (declare-same-step pbl "P1" ptcls '()
    (lambda _ mtrue)
    (lambda (p in) (mexp g a1))))

(define (gB p) (macro_input P2 p))

(define P2 (declare-same-step pbl "P2" ptcls '()
    (lambda _ mtrue)
    (lambda (p in) ok)))

(define P3 (declare-same-step pbl "P3" ptcls '()
    (lambda (p in)
      (let [ (sidP (h (tuple (tuple (mexp g a1) (gB p)) (mexp (gB p) a1)) hKey))
        (pkS_in (sel1of2 in))
        (sigS (sel2of2 in)) ]
        (cand (eq pkS_in (vk skS))
          (checksign sidP sigS pkS_in))))
    (lambda (p in)
      (let [ (sidP (h (tuple (tuple (mexp g a1) (gB p)) (mexp (gB p) a1)) hKey)) ]
        (enc (sign sidP skP) rP (mexp (gB p) a1))))))

(define P4_ok (declare-same-step pbl "P4_ok" ptcls '()
    (lambda (p in) (cor (eq (gB p) (mexp g b1))
        (exists ((i Index)) (eq (gB p) (mexp g (b i))))))
    (lambda _ ok)))

(define P4_fail (declare-step pbl "P4_fail" '()
    (step p1
      (lambda (in) (mnot (cor (eq (gB p1) (mexp g b1))
            (exists ((i Index)) (eq (gB p1) (mexp g (b i)))))))
      (lambda _ ok))
    (step p2
      (lambda (in) (mnot (cor (eq (gB p2) (mexp g b1))
            (exists ((i Index)) (eq (gB p2) (mexp g (b i)))))))
      (lambda _ ko))))

(add-constrain pbl () (lt P1 P2))
(add-constrain pbl () (lt P2 P3))
(add-constrain pbl () (lt P3 P4_ok))
(add-constrain pbl () (lt P3 P4_fail))
(add-constrain pbl () (<> P4_ok P4_fail))

;; Protocol S
(define S1 (declare-same-step pbl "S1" ptcls '()
    (lambda _ mtrue)
    (lambda (p in) (mexp g b1))))

(define (gP p) (macro_input S1 p))

(define S2 (declare-same-step pbl "S2" ptcls '()
    (lambda _ mtrue)
    (lambda (p in)
      (let [ (sidS (h (tuple (tuple (gP p) (mexp g b1)) (mexp (gP p) b1)) hKey)) ]
        (tuple (vk skS) (sign sidS skS))))))

(define S3 (declare-same-step pbl "S3" ptcls '()
    (lambda (p in)
      (let [ (sidS (h (tuple (tuple (gP p) (mexp g b1)) (mexp (gP p) b1)) hKey)) ]
        (checksign sidS (dec in (mexp (gP p) b1)) (vk skP))))
    (lambda _ ok)))

(define S4_ok (declare-same-step pbl "S4_ok" ptcls '()
    (lambda (p in) (cor (eq (gP p) (mexp g a1))
        (exists ((i Index)) (eq (gP p) (mexp g (a i))))))
    (lambda _ ok)))

(define S4_fail (declare-step pbl "S4_fail" '()
    (step p1
      (lambda (in) (mnot (cor (eq (gP p1) (mexp g a1))
            (exists ((i Index)) (eq (gP p1) (mexp g (a i)))))))
      (lambda _ ok))
    (step p2
      (lambda (in) (mnot (cor (eq (gP p2) (mexp g a1))
            (exists ((i Index)) (eq (gP p2) (mexp g (a i)))))))
      (lambda _ ko))))

(add-constrain pbl () (lt S1 S2))
(add-constrain pbl () (lt S2 S3))
(add-constrain pbl () (lt S3 S4_ok))
(add-constrain pbl () (lt S3 S4_fail))
(add-constrain pbl () (<> S4_ok S4_fail))

(bind ((p Protocol))
  (add-rewrite pbl (rw.new "lemma-P" (list p)
      (cand (macro_exec P4_fail p) (macro_cond P4_fail p))
      mfalse)))

(bind ((p Protocol))
  (add-rewrite pbl (rw.new "lemma-S" (list p)
      (cand (macro_exec S4_fail p) (macro_cond S4_fail p))
      mfalse)))

(config.set_vampire_timeout pbl (b.string->duration "300ms"))
(config.set_guided_nonce_search pbl #t)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed ssh-forward-part1-auth"))
; #t

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "ssh-forward-part1-auth" pbl)
