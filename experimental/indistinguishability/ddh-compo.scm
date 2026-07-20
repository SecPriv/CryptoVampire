;; This is a 'copy' of squirrel's `signed-ssh-compo`

(require "cryptovampire/v2")
(require "../save-results.scm")
(require-builtin cryptovampire as cv-)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))


(define-function ko pbl Bitstring)
(define-function ok pbl Bitstring)

(define-function sign pbl (Bitstring Bitstring) -> Bitstring)
(define-function checksign pbl (Bitstring Bitstring Bitstring) -> Bool)
(define-function vk pbl (Bitstring) -> Bitstring)

(define ddh (declare-cryptography pbl))
(define-function g pbl (ddh) Bitstring)
(define-function mexp pbl (ddh) (Bitstring Bitstring) -> Bitstring)

(define-function _a pbl (Index) -> Nonce)
(define-function _b pbl (Index) -> Nonce)
(define-function _a1 pbl Nonce)
(define-function _b1 pbl Nonce)
(define-function _k11 pbl Nonce)
(define-function _skP pbl Nonce)
(define-function _skS pbl Nonce)

;; A hash that I don't know what it is used for
(define-function h plb (Bitstring Bitstring) -> Bitstring)

(define a1 (wrap-nonce _a1))
(define b1 (wrap-nonce _b1))
(define k11 (wrap-nonce _k11))
(define skP (wrap-nonce _skP))
(define skS (wrap-nonce _skS))

(define empty-cond (lambda _ mtrue))

(define (declare-same-step name args cond msg)
  (declare-step pbl name args
    (step p1 (curry cond p1) (curry msg p1))
    (step p2 (curry cond p2) (curry msg p2))))

(define P1 (declare-same-step "P1" '()
    empty-cond
    (lambda (p in)
      (tuple (vk skP) (mexp g a1)))))

(define P2 (declare-same-step "P2" '()
    (lambda (p in)
      (let [ (gs (sel2of2 (sel1of2 in))) (vks (sel1of2 (sel1of2 in))) ]
        (checksign (tuple (mexp g a1) gs (vk skP)) (sel2of2 in) vks)))
    (lambda (p in)
      (let [ (gs (sel2of2 (sel1of2 in))) ]
        (sign (tuple gs (mexp g a1) (vk skS)) skP)))))
(add-constrain pbl () (lt P1 P2))
(define (P2in p) (macro_input P2 p))

(define P3 (declare-same-step "P3" '()
    (lambda (p in)

    )
))



(define P3
  (declare-step pbl "P3" (list Index Index)
    (step p1
      (lambda (challenge i j)
        (let [ (gS (sel2of2 (sel1of2 (P2in i p1)))) (vkS (sel1of2 (sel1of2 (P2in i p1)))) ]
          (eq gS (mexp g (b j)))))
      (lambda (challenge i j)
        (mexp (mexp g (a i)) (b j))))
    ; ok
    ; )) ;))
    (step p2
      (lambda (challenge i j)
        (let [ (gS (sel2of2 (sel1of2 (P2in i p2)))) (vkS (sel1of2 (sel1of2 (P2in i p2)))) ]
          (eq gS (mexp g (b j)))))
      (lambda (challenge i j)
        (mexp g (k i j))))))
; ok
; ))))

(define P3fail
  (declare-step pbl "P3fail" (list Index)
    (step p1
      (lambda (challenge i)
        (let [ (gS (sel2of2 (sel1of2 (P2in i p1)))) (vkS (sel1of2 (sel1of2 (P2in i p1)))) ]
          (mnot (exists ((j Index)) (eq gS (mexp g (b j)))))))
      (lambda _ ok))
    (step p2
      (lambda (challenge i)
        (let [ (gS (sel2of2 (sel1of2 (P2in i p2)))) (vkS (sel1of2 (sel1of2 (P2in i p2)))) ]
          (mnot (exists ((j Index)) (eq gS (mexp g (b j)))))))
      (lambda _ ko))))

(add-constrain pbl (i) (lt (P2 i) (P3fail i)))
(add-constrain pbl (i j) (lt (P2 i) (P3 i j)))
(add-constrain pbl (i j) (<> (P3 i j) (P3fail i)))

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
(add-constrain pbl (i) (lt (Schall1 i) (Schall2 i)))

(publish pbl ((i Index)) (mexp g (a i)))
(publish pbl ((i Index)) (mexp g (b i)))

; enable looking for extra things to publish
(cv-set-guided-nonce-search pbl #t)

;; configuration
; (cv-set-trace pbl #t)
(cv-set-vampire-timeout pbl (cv-string->duration "300ms"))
(cv-set-node-limit pbl 100000)
; (cv-set-keep-smt-files pbl #t)

(initialize-as-ddh ddh g mexp)

(bind ((i Index) (p Protocol))
  (cv-add-rewrite pbl (cv-mk-rewrite "lemma" (list i p)
      (and (macro_exec (P3fail i) p) (macro_cond (P3fail i) p))
      mfalse)))

(bind ((i Index) (j Index))
  (cv-register-fresh-nonce ddh (list i j) (k i j)))

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed ddh-P"))

(displayln (cv-print-report (cv-get-report pbl)))
; (save-results "ddh-P" pbl)

