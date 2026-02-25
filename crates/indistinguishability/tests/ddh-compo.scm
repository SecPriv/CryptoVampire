(require "cryptovampire/v2")
(require "./save-results.scm")
(require-builtin cryptovampire as cv-)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))


(define-function ko pbl Bitstring)
(define-function ok pbl Bitstring)

;; we don't need to know anything about signature for indistinguishability as
;; this comes form the lemmas
(define euf-cma (declare-cryptography pbl)) ;; we never instanciate this cryptography
(define-function sign pbl (euf-cma) (Bitstring Bitstring) -> Bitstring)
(define-function checksign pbl (euf-cma) (Bitstring Bitstring Bitstring) -> Bool)
(define-function vk pbl (euf-cma) (Bitstring) -> Bitstring)

(define ddh (declare-cryptography pbl))
(define-function g pbl (ddh) Bitstring)
(define-function mexp pbl (ddh) (Bitstring Bitstring) -> Bitstring)

(define prf (declare-cryptography pbl))
(define-function h pbl (prf) (Bitstring Bitstring) -> Bitstring)

;; honnests nonces
(define-function a1 pbl Nonce) ;; DH share of P
(define-function b1 pbl Nonce) ;; DH share of S
(define-function k11 pbl Nonce) ;; ideal key derived between P and S <- might remove
;; attacker nonces
(define-function a pbl (Index) -> Nonce)
(define-function b pbl (Index) -> Nonce)
;; keys
(define-function skP pbl  Nonce)
(define-function skS pbl  Nonce)

(define empty-cond (lambda _ mtrue))

;; same for e^a and e^b
(publish pbl ((i Index)) (mexp g (a i)))
(publish pbl ((i Index)) (mexp g (b i)))
(publish pbl ((i Index)) (mexp g a1))
(publish pbl ((i Index)) (mexp g b1))

(define P1
  (declare-step pbl "P1" '()
    (step p1 empty-cond
      (lambda (in)
        (tuple (vk skP) (mexp g a1))))
    (step p2 empty-cond
      (lambda (in)
        (tuple (vk skP) (mexp g a1))))))

(define P2
  (declare-step pbl "P2" '()
    (step p1
      (lambda (in)
        (let [ (gs (sel2of2 (sel1of2 in))) (vks (sel1of2 (sel1of2 in))) ]
            (checksign (tuple (mexp g (a i)) gs (vk skP)) (sel2of2 in) vks)))
      (lambda (in)
        (let [ (gs (sel2of2 (sel1of2 in))) (vks (sel1of2 (sel1of2 in))) ]
          (sign (tuple gs (mexp g (a i)) vks) skP))))
    (step p2
      (lambda (in)
        (let [ (gs (sel2of2 (sel1of2 in))) (vks (sel1of2 (sel1of2 in))) ]
            (checksign (tuple (mexp g (a i)) gs (vk skP)) (sel2of2 in) vks)
            ))
      (lambda (in)
        (let [ (gs (sel2of2 (sel1of2 in))) (vks (sel1of2 (sel1of2 in))) ]
          (sign (tuple gs (mexp g (a i)) vks) skP))))))
(define (inP2 p) (macro_input P2 p))
(define (vks p) (sel1of2 (sel1of2 (inP2 p))))

(define P3
  (declare-step pbl "P3" '()
    (step p1
      (lambda (in) (
        (and (eq (vks p1) (vk skP)) (sel2of2 (sel1of2 (inP2 p1))))
      ))
      (lambda (in) ok)
    )
    (step p1
      (lambda (in) (
        (and (eq (vks p1) (vk skP)) (eq (sel2of2 (sel1of2 (inP2 p1))) (mexp g b1)))
      ))
      (lambda (in) ok)
    )
  )
)

(define P4
  (declare-step pbl "P4" (list Index)
    (step p1
      (lambda (in i) (
        (and (eq (vks p1) (vk skP)) (not (eq (sel2of2 (sel1of2 (inP2 p1))) (mexp g b1))) (not (eq (sel2of2 (sel1of2 (inP2 p1))) (mexp g (b i)))))
      ))
      (lambda _ ok)
    )
    (step p1
      (lambda (in i) (
        (and (eq (vks p1) (vk skP)) (not (eq (sel2of2 (sel1of2 (inP2 p1))) (mexp g b1))) (not (eq (sel2of2 (sel1of2 (inP2 p1))) (mexp g (b i)))))
      ))
      (lambda _ ok)
    )
  )
)


(define Schall1
  (declare-step pbl "Schall1" (list Index)
    (step p1
      (lambda (in j)
        (let [ (gp (sel2of2 in)) (vkp (sel1of2 in)) ]
          (eq vkp (vk skP))))
      (lambda (in j)
        (let [ (gp (sel2of2 in)) (vkp (sel1of2 in)) ]
          (tuple
            (vk skS)
            (mexp g (b j))
            (sign (tuple gp (mexp g (b j)) vkp) skS)))))
    (step p2
      (lambda (in j)
        (let [ (gp (sel2of2 in)) (vkp (sel1of2 in)) ]
          (eq vkp (vk skP))))
      (lambda (in j)
        (let [ (gp (sel2of2 in)) (vkp (sel1of2 in)) ]
          (tuple
            (vk skS)
            (mexp g (b j))
            (sign (tuple gp (mexp g (b j)) vkp) skS)))))))
(define (S1in j p) (macro_input (Schall1 j) p))
(bind ((i Index))
  (begin
    (cv-add-rewrite pbl (cv-mk-rewrite "Schall1-gb-1" (list i)
        (mexp g (b i)) (sel1of2 (sel2of2 (macro_msg (Schall1 i) p1)))))
    (cv-add-rewrite pbl (cv-mk-rewrite "Schall1-gb-2" (list i)
        (mexp g (b i)) (sel1of2 (sel2of2 (macro_msg (Schall1 i) p2)))))))

(define Schall2
  (declare-step pbl "Schall2" (list Index)
    (step p1
      (lambda (in j)
        (let [ (gp (sel2of2 (S1in j p1))) (vkp (sel1of2 (S1in j p1))) ]
          (checksign (tuple (mexp g (b j)) gp (vk skS)) in vkp)))
      (lambda _ ok))
    (step p2
      (lambda (in j)
        (let [ (gp (sel2of2 (S1in j p2))) (vkp (sel1of2 (S1in j p2))) ]
          (checksign (tuple (mexp g (b j)) gp (vk skS)) in vkp)))
      (lambda _ ok))))
(define (S2in j p) (macro_input (Schall2 j) p))

(define Schall3
  (declare-step pbl "Schall3" (list Index Index)
    (step p1
      (lambda (challenge i j)
        (let [ (gp (sel2of2 (S1in j p1))) (vkp (sel1of2 (S1in j p1))) ]
          (eq gp (mexp g (a i)))))
      (lambda (challenge i j)
        (mexp (mexp g (a i)) (b j))))
    (step p2
      (lambda (challenge i j)
        (let [ (gp (sel2of2 (S1in j p2))) (vkp (sel1of2 (S1in j p2))) ]
          (eq gp (mexp g (a i)))))
      (lambda (challenge i j)
        (mexp g (k i j))))))

(define Schall3fail
  (declare-step pbl "Schall3fail" (list Index)
    (step p1
      (lambda (challenge j)
        (let [ (gp (sel2of2 (S1in j p1))) (vkp (sel1of2 (S1in j p1))) ]
          (mnot (exists ((i Index)) (eq gp (mexp g (a i)))))))
      (lambda _ ok))
    (step p2
      (lambda (challenge j)
        (let [ (gp (sel2of2 (S1in j p2))) (vkp (sel1of2 (S1in j p2))) ]
          (mnot (exists ((i Index)) (eq gp (mexp g (a i)))))))
      (lambda _ ko))))

;; ordering constrains
(add-constrain pbl (i) (lt (P1 i) (P2 i)))
(add-constrain pbl (i) (lt (Schall1 i) (Schall2 i)))
(add-constrain pbl (i) (lt (Schall2 i) (Schall3fail i)))
(add-constrain pbl (i j) (lt (Schall2 j) (Schall3 i j)))
(add-constrain pbl (i j) (<> (Schall3fail i) (Schall3 i j)))

;; lemma (given by the crypto)
(bind ((i Index) (j Index) (p Protocol))
  (cv-add-rewrite pbl (cv-mk-rewrite "lemma" (list i j p)
      (and (macro_exec (Schall3fail i) p) (macro_cond (Schall3fail i) p))
      mfalse)))

(initialize-as-ddh ddh g mexp)

; tell the ddh rules to make use of `k i j`
; This is not the case default for efficiency reasons
(bind ((i Index) (j Index))
  (cv-register-fresh-nonce ddh (list i j) (k i j)))

; enable looking for extra things to publish
(cv-set-guided-nonce-search pbl #t)

;; configuration
; (cv-set-trace pbl #t)
(cv-set-node-limit pbl 100000)
(cv-set-vampire-timeout pbl (cv-string->duration "300ms"))
; (cv-set-fa-limit pbl 0)
; (cv-set-keep-smt-files pbl #t)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed ddh-S"))

(displayln (cv-print-report (cv-get-report pbl)))
(save-results "ddh-S" pbl)