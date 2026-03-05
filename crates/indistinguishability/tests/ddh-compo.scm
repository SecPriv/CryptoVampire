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


(define-function ko pbl Bitstring)
(define-function ok pbl Bitstring)

;; we don't need to know anything about signature for indistinguishability as
;; this comes form the lemmas
(define euf-cma (declare-cryptography pbl));; we never instanciate this cryptography
(define-function sign pbl (euf-cma) (Bitstring Bitstring) -> Bitstring)
(define-function checksign pbl (euf-cma) (Bitstring Bitstring Bitstring) -> Bool)
(define-function vk pbl (euf-cma) (Bitstring) -> Bitstring)

(define ddh (declare-cryptography pbl))
(define-function g pbl (ddh) Bitstring)
(define-function mexp pbl (ddh) (Bitstring Bitstring) -> Bitstring)

(define prf (declare-cryptography pbl))
(define-function h pbl (prf) (Bitstring Bitstring) -> Bitstring)

;; honnests nonces
(define-function a1 pbl Nonce);; DH share of P
(define-function b1 pbl Nonce);; DH share of S
(define-function k11 pbl Nonce);; ideal key derived between P and S <- might remove
;; attacker nonces
(define-function a pbl (Index) -> Nonce)
(define-function b pbl (Index) -> Nonce)
;; keys
(define-function skP pbl Nonce)
(define-function skS pbl Nonce)

(define empty-cond (lambda _ mtrue))

;; same for e^a and e^b
(publish pbl ((i Index)) (mexp g (a i)))
(publish pbl ((i Index)) (mexp g (b i)))
(publish pbl () (mexp g a1))
(publish pbl () (mexp g b1))

(define ptcls (list p1 p2))

(define P1 (declare-same-step pbl "P1" ptcls '()
    empty-cond
    (lambda (p in) (tuple (vk skP) (mexp g a1)))))

(define P2 (declare-same-step pbl "P2" ptcls '()
    (lambda (p in)
      (let [ (gs (sel2of2 (sel1of2 in))) (vks (sel1of2 (sel1of2 in))) ]
        (checksign (tuple (mexp g a1) gs (vk skP)) (sel2of2 in) vks)))
    (lambda (p in)
      (let [ (gs (sel2of2 (sel1of2 in))) (vks (sel1of2 (sel1of2 in))) ]
        (sign (tuple gs (mexp g a1) vks) skP)))))
(define (inP2 p) (macro_input P2 p))
(define (vks p) (sel1of2 (sel1of2 (inP2 p))))

(define P3 (declare-same-step pbl "P3" ptcls '()
    (lambda (p in) (cand
        (eq (vks p) (vk skP))
        (eq (sel2of2 (sel1of2 (inP2 p))) (mexp g b1))))
    (lambda _ ok)))

(define P4 (declare-same-step pbl "P4" ptcls (list Index)
    (lambda (p in i) (cand
        (eq (vks p) (vk skP))
        (mnot (eq (sel2of2 (sel1of2 (inP2 p))) (mexp g b1)))
        (eq (sel2of2 (sel1of2 (inP2 p))) (mexp g (b i)))))
    (lambda _ ok)))

(define P5
  (declare-step pbl "P5" '()
    (step p1
      (lambda (in) (cand
          (eq (vks p1) (vk skP))
          (mnot (eq (sel2of2 (sel1of2 (inP2 p1))) (mexp g b1)))
          (mnot (exists ((i Index))
              (eq (sel2of2 (sel1of2 (inP2 p1))) (mexp g (b i)))))))
      (lambda _ ok))
    (step p2
      (lambda (in) (cand
          (eq (vks p2) (vk skP))
          (mnot (eq (sel2of2 (sel1of2 (inP2 p2))) (mexp g b1)))
          (mnot (exists ((i Index))
              (eq (sel2of2 (sel1of2 (inP2 p2))) (mexp g (b i)))))))
      (lambda _ ko))))

(add-constrain pbl () (lt P1 P2))
(add-constrain pbl () (lt P2 P3))
(add-constrain pbl (i) (lt P2 (P4 i)))
(add-constrain pbl () (lt P2 P5))
(add-constrain pbl (i) (<> P3 (P4 i)))
(add-constrain pbl (i) (<> P5 (P4 i)))
(add-constrain pbl () (<> P5 P3))


(define S1 (declare-same-step pbl "S1" ptcls '()
    empty-cond
    (lambda (p in)
      (let [ (gp (sel2of2 in)) (vkp (sel1of2 in)) ]
        (tuple
          (vk skS)
          (mexp g b1)
          (sign (tuple gp (mexp g b1) vkp) skS))))))
(define (S1in p) (macro_input S1 p))
(define (vkS p) (sel1of2 (S1in p)))
(define (gpS p) (sel2of2 (S1in p)))

(bind ((i Index))
  (begin
    (add-rewrite pbl (rw.new "Schall1-gb-1" '()
        (mexp g b1) (sel1of2 (sel2of2 (macro_msg S1 p1)))))
    (add-rewrite pbl (rw.new "Schall1-gb-2" '()
        (mexp g b1) (sel1of2 (sel2of2 (macro_msg S1 p2)))))))



(define S2 (declare-same-step pbl "S2" ptcls '()
    (lambda (p in)
      (checksign (tuple (mexp g b1) (gpS p) (vk skS)) in (vkS p)))
    (lambda _ ok)))
(define (S2in p) (macro_input S2 p))


(define S3 (declare-same-step pbl "S3" ptcls '()
    (lambda (p in)
      (cand
        (eq (vkS p) (vk skP))
        (eq (gpS p) (mexp g a1))))
    (lambda _ ok)))

(define S4 (declare-same-step pbl "S4" ptcls (list Index)
    (lambda (p in i)
      (cand
        (eq (vkS p) (vk skP))
        (mnot (eq (gpS p) (mexp g a1)))
        (eq (gpS p) (mexp g (a i)))))
    (lambda _ ok)))


(define S5
  (declare-step pbl "Schall3fail" '()
    (step p1
      (lambda (c)
        (and
          (eq (vkS p2) (vk skP))
          (mnot (eq (gpS p1) (mexp g a1)))
          (mnot (exists ((i Index)) (eq (gpS p1) (mexp g (a i)))))))
      (lambda _ ok))
    (step p2
      (lambda (c)
        (and
          (eq (vkS p2) (vk skP))
          (mnot (eq (gpS p2) (mexp g a1)))
          (mnot (exists ((i Index)) (eq (gpS p2) (mexp g (a i)))))))
      (lambda _ ko))))

;; ordering constrains
(add-constrain pbl () (lt S1 S2))
(add-constrain pbl () (lt S2 S3))
(add-constrain pbl (i) (lt S2 (S4 i)))
(add-constrain pbl () (lt S2 S5))
(add-constrain pbl (i) (<> S3 (S4 i)))
(add-constrain pbl (i) (<> S5 (S4 i)))
(add-constrain pbl () (<> S5 S3))

;; lemma (given by the crypto)
(bind ((p Protocol))
  (add-rewrite pbl (rw.new "lemma-S" (list p)
      (cand (macro_exec S5 p) (macro_cond S5 p))
      mfalse)))
(bind ((p Protocol))
  (add-rewrite pbl (rw.new "lemma-P" (list p)
      (cand (macro_exec P5 p) (macro_cond P5 p))
      mfalse)))

(initialize-as-ddh ddh g mexp)

; tell the ddh rules to make use of `k i j`
; This is mnot the case default for efficiency reasons
(register-fresh-nonce ddh '() k11)

; enable looking for extra things to publish
(config.set_guided_nonce_search pbl #t)

;; configuration
; (cv-set-trace pbl #t)
(config.set_node_limit pbl 100000)
(config.set_vampire_timeout pbl (b.string->duration "300ms"))
; (cv-set-fa-limit pbl 0)
; (cv-set-keep-smt-files pbl #t)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed ddh-S"))

(displayln (report.print-report (pbl.get-report pbl)))
; (save-results "ddh-S" pbl)

