(require "cryptovampire/v2")
(require "../save-results.scm")
(require-builtin cryptovampire as cv-)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define prf (declare-cryptography pbl))

(define-function mhash pbl (prf) (Bitstring Bitstring) -> Bitstring)
(define-function ok pbl Bitstring)
(define-function ko pbl Bitstring)
(define-function k1 pbl (Index) -> Nonce)
(define-function k2 pbl (Index Index) -> Nonce)
(define-function _n pbl (Index Index) -> Nonce)

(define-alias _mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> (k1 i))
  ([ (i Index) (j Index) ] (i j p2) -> (k2 i j)) ])

(define n (wrap-nonce _n))
(define mk (wrap-nonce _mk))


(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i j)
        (tuple (n i j) (mhash (n i j) (mk i j p1)))))
    (step p2
      (lambda _ mtrue)
      (lambda (in i j)
        (tuple (n i j) (mhash (n i j) (mk i j p2)))))))

(define rs
  (declare-step pbl "rs" (list Index Index)
    (step p1
      (lambda (in i j)
        (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p1))))
      (lambda _ ok))
    (step p2
      (lambda (in i j)
        (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p2))))
      (lambda _ ok))))

(define rf
  (declare-step pbl "rf" (list Index)
    (step p1
      (lambda (in i)
        (mnot (exists ((j Index))
            (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p1))))))
      (lambda _ ok))
    (step p2
      (lambda (in i)
        (mnot (exists ((j Index))
            (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p2))))))
      (lambda _ ok))))

(initialize-as-prf prf mhash)

(bind
  ((i Index) (j Index)
    (t Time)
    (p Protocol))
  (let [ (in (macro_input t p)) ]
    (cv-add-rewrite pbl (cv-mk-rewrite "lemma-2" (list i t j p)
        (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p)))
        (exists ((j Index))
          (cand
            (eq (sel1of2 in) (sel1of2 (macro_msg (tag i j) p)))
            (eq (sel2of2 in) (sel2of2 (macro_msg (tag i j) p)))
            (lt (tag i j) t))))))); <- very important

;; configuration
; (cv-set-trace pbl #t)
(cv-set-vampire-timeout pbl (cv-string->duration "2s"))

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed basic-hash"))

(displayln (cv-print-report (cv-get-report pbl)))
(save-results "basic-hash" pbl)