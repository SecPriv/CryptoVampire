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
(define-function mfail pbl Bitstring)
(define-function forwarded pbl Bitstring)
(define-function reqsign pbl Bitstring)
(define-function anssign pbl Bitstring)

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

;; nonces
(define-function ake11 pbl Nonce)
(define-function bke11 pbl Nonce)
(define-function k11 pbl Nonce)
(define-function a1 pbl Nonce)
(define-function b1 pbl Nonce)
(define-function hKey pbl Nonce)
(define-function skP pbl Nonce)
(define-function skS pbl Nonce)
(define-function r pbl Nonce)
(define-function r2 pbl (Index) -> Nonce)
(define-function r3 pbl Nonce)
(define-function r4 pbl Nonce)

;; attacker nonces
(define-function a pbl (Index) -> Nonce)
(define-function b pbl (Index) -> Nonce)
(define-function ake1 pbl (Index) -> Nonce)
(define-function bke1 pbl (Index) -> Nonce)

; (publish pbl () (mexp g a1))
; (publish pbl () (mexp g b1))
; (publish pbl () (mexp g ake11))
; (publish pbl () (mexp g bke11))
; (publish pbl ((i Index)) (mexp g (a i)))
; (publish pbl ((i Index)) (mexp g (b i)))
; (publish pbl ((i Index)) (mexp g (ake1 i)))
; (publish pbl ((i Index)) (mexp g (bke1 i)))
; (publish pbl () (vk skP))
; (publish pbl () (vk skS))
(publish pbl () hKey)
(publish pbl () forwarded)
(publish pbl () reqsign)
(publish pbl () anssign)

;; Simplified P1FA
(define P1FA1 (declare-same-step pbl "P1FA1" ptcls '()
    (lambda _ mtrue)
    (lambda (p in . _) ok)
    empty-assignements))

(define (gB_P1FA p) (macro_input P1FA1 p))

(define P1FA2 (declare-same-step pbl "P1FA2" ptcls '()
    (lambda (p in . _)
      (let [ (sidPaF (h (tuple (tuple (mexp g ake11) (gB_P1FA p)) k11) hKey))
        (pkSaF (sel1of2 in))
        (sigS (sel2of2 in)) ]
        (cand (eq pkSaF (vk skS))
          (checksign sidPaF sigS pkSaF))))
    (lambda (p in . _)
      (let [ (sidPaF (h (tuple (tuple (mexp g ake11) (gB_P1FA p)) k11) hKey)) ]
        (enc (sign sidPaF skP) r k11)))
    empty-assignements))

(define FA (declare-same-step pbl "FA" ptcls (list Index)
    (lambda (p in i . _)
      (let [ (x (dec in k11)) ]
        (cand (mnot (eq x mfail))
          (eq (sel1of2 x) reqsign))))
    (lambda (p in i . _)
      (let [ (x (dec in k11)) ]
        (enc (tuple anssign (sign (tuple forwarded (sel2of2 x)) skP)) (r2 i) k11)))
    empty-assignements))

;; Simplified PDIS
(define PDIS1 (declare-same-step pbl "PDIS1" ptcls '()
    (lambda _ mtrue)
    (lambda (p in . _) (mexp g bke11))
    empty-assignements))

(define (gP0_PDIS p) (macro_input PDIS1 p))

(define PDIS2 (declare-same-step pbl "PDIS2" ptcls '()
    (lambda _ mtrue)
    (lambda (p in . _)
      (let [ (sidS0a (h (tuple (tuple (gP0_PDIS p) (mexp g bke11)) k11) hKey)) ]
        (tuple (tuple (vk skS) (mexp g bke11)) (sign sidS0a skS))))
    empty-assignements))

(define PDIS3 (declare-same-step pbl "PDIS3" ptcls '()
    (lambda (p in . _)
      (let [ (sidS0a (h (tuple (tuple (gP0_PDIS p) (mexp g bke11)) k11) hKey)) ]
        (checksign sidS0a (dec in (mexp (gP0_PDIS p) bke11)) (vk skP))))
    (lambda _ ok)
    empty-assignements))

(define PDIS4 (declare-same-step pbl "PDIS4" ptcls '()
    (lambda _ mtrue)
    (lambda (p in . _) (mexp g a1))
    empty-assignements))

(define (gB_PDIS p) (macro_input PDIS5 p))

(define PDIS5 (declare-same-step pbl "PDIS5" ptcls '()
    (lambda _ mtrue)
    (lambda (p in . _) ok)
    empty-assignements))

(define PDIS6 (declare-same-step pbl "PDIS6" ptcls '()
    (lambda (p in . _)
      (let [ (sidPa (h (tuple (tuple (mexp g a1) (gB_PDIS p)) (mexp (gB_PDIS p) a1)) hKey))
        (pkSa (sel1of2 in))
        (sigS (sel2of2 in)) ]
        (cand (eq pkSa (vk skS))
          (checksign sidPa sigS pkSa))))
    (lambda (p in . _)
      (let [ (sidPa (h (tuple (tuple (mexp g a1) (gB_PDIS p)) (mexp (gB_PDIS p) a1)) hKey)) ]
        (enc (tuple reqsign sidPa) r3 k11)))
    empty-assignements))

;; PDIS Fail branch
(define Pfail (declare-step pbl "Pfail" '()
    (step p1
      (lambda (in . _) (mnot (cor (eq (gB_PDIS p1) (mexp g b1))
            (exists ((i Index)) (eq (gB_PDIS p1) (mexp g (b i)))))))
      (lambda _ ok)
      empty-assignements)
    (step p2
      (lambda (in . _) (mnot (cor (eq (gB_PDIS p2) (mexp g b1))
            (exists ((i Index)) (eq (gB_PDIS p2) (mexp g (b i)))))))
      (lambda _ ko)
      empty-assignements)))

;; Simplified SDIS
(define SDIS1 (declare-same-step pbl "SDIS1" ptcls '()
    (lambda _ mtrue)
    (lambda (p in . _) (mexp g b1))
    empty-assignements))

(define (gP_SDIS p) (macro_input SDIS1 p))

(define SDIS2 (declare-same-step pbl "SDIS2" ptcls '()
    (lambda _ mtrue)
    (lambda (p in . _)
      (let [ (sidSa (h (tuple (tuple (gP_SDIS p) (mexp g b1)) (mexp (gP_SDIS p) b1)) hKey)) ]
        (tuple (tuple (vk skS) (mexp g b1)) (sign sidSa skS))))
    empty-assignements))

(define SDIS3 (declare-same-step pbl "SDIS3" ptcls '()
    (lambda (p in . _)
      (let [ (sidSa (h (tuple (tuple (gP_SDIS p) (mexp g b1)) (mexp (gP_SDIS p) b1)) hKey))
        (x4 (dec in (mexp (gP_SDIS p) b1))) ]
        (checksign (tuple forwarded sidSa) x4 (vk skP))))
    (lambda _ ok)
    empty-assignements))

(define Sfail (declare-step pbl "Sfail" '()
    (step p1
      (lambda (in . _) (mnot (cor (eq (gP_SDIS p1) (mexp g a1))
            (exists ((i Index)) (eq (gP_SDIS p1) (mexp g (a i)))))))
      (lambda _ ok)
      empty-assignements)
    (step p2
      (lambda (in . _) (mnot (cor (eq (gP_SDIS p2) (mexp g a1))
            (exists ((i Index)) (eq (gP_SDIS p2) (mexp g (a i)))))))
      (lambda _ ko)
      empty-assignements)))

(add-constrain pbl () (lt P1FA1 P1FA2))
(add-constrain pbl (i) (lt P1FA2 (FA i)))

(add-constrain pbl () (lt PDIS1 PDIS2))
(add-constrain pbl () (lt PDIS2 PDIS3))
(add-constrain pbl () (lt PDIS3 PDIS4))
(add-constrain pbl () (lt PDIS4 PDIS5))
(add-constrain pbl () (lt PDIS5 PDIS6))
(add-constrain pbl () (lt PDIS6 Pfail))

(add-constrain pbl () (lt SDIS1 SDIS2))
(add-constrain pbl () (lt SDIS2 SDIS3))
(add-constrain pbl () (lt SDIS3 Sfail))

(bind ((p Protocol))
  (add-rewrite pbl (rw.new "lemma-P" (list p)
      (cand (macro_exec Pfail p) (macro_cond Pfail p))
      mfalse)))

(bind ((p Protocol))
  (add-rewrite pbl (rw.new "lemma-S" (list p)
      (cand (macro_exec Sfail p) (macro_cond Sfail p))
      mfalse)))

(define default-timeout (b.string->duration "300ms"))
(config.set_smt_timeout pbl (b.mult->duration scale-timeout default-timeout))
(config.set_guided_nonce_search pbl #t)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed ssh-forward-part2-auth"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "ssh-forward-part2-auth" pbl)
