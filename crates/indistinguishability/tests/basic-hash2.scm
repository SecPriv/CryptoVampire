(require "cryptovampire/v2")
(require-builtin cryptovampire as cv-)
; (require-builtin steel/base)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define prf (declare-cryptography pbl))

(define-function mhash pbl (prf) (Bitstring Bitstring) -> Bitstring)
(define-function ok pbl Bitstring)
(define-function ko pbl Bitstring)
(define-function k1 pbl (Index) -> Nonce)
(define-function k2 pbl (Index Index) -> Nonce)
(define-function n pbl (Index Index) -> Nonce)

(define-alias mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> (k1 i))
  ([ (i Index) (j Index) ] (i j p2) -> (k2 i j)) ])




(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i j)
        (mtuple (mnonce (n i j)) (mhash (mnonce (n i j)) (mnonce (mk i j p1))))))
    (step p2
      (lambda _ mtrue)
      (lambda (in i j)
        (mtuple (mnonce (n i j)) (mhash (mnonce (n i j)) (mnonce (mk i j p2))))))))

(define rs
  (declare-step pbl "rs" (list Index Index)
    (step p1
      (lambda (in i j)
        (eq (sel2of2 in) (mhash (sel1of2 in) (mnonce (mk i j p1)))))
      (lambda _ ok))
    (step p2
      (lambda (in i j)
        (eq (sel2of2 in) (mhash (sel1of2 in) (mnonce (mk i j p2)))))
      (lambda _ ok))))

(define rf
  (declare-step pbl "rf" (list Index)
    (step p1
      (lambda (in i)
        (mnot (exists ((j Index))
            (eq (sel2of2 in) (mhash (sel1of2 in) (mnonce (mk i j p1)))))))
      (lambda _ ok))
    (step p2
      (lambda (in i)
        (mnot (exists ((j Index))
            (eq (sel2of2 in) (mhash (sel1of2 in) (mnonce (mk i j p2)))))))
      (lambda _ ok))))

; (displayln (cv-string-of-formula 
;   (cv-mk-appf (get-function mhash) (list ok ok ok))))
; (displayln (cv-to-string-step pbl (get-function p1) (get-function tag)))
; (get-function "f")
(displayln (cv-function-name (get-function mhash)))

(initialize-as-prf prf mhash)

(bind
  ((i Index) (j Index)
    (t Time)
    (p Protocol))
  (let [ (in (macro_input t p)) ]
    (cv-add-rewrite pbl (cv-mk-rewrite "lemma-2" (list i t j p)
        (eq (sel2of2 in) (mhash (sel1of2 in) (mnonce (mk i j p))))
        (exists ((i Index))
          (mand
            (lt (tag i j) t) ; <- very important
            (mand (eq (sel1of2 in) (sel1of2 (macro_input (tag i j) p)))
              (eq (sel2of2 in) (sel2of2 (macro_input (tag i j) p))))))))))


(if (run pbl p1 p2)
  (displayln "success")
  (error "failed"))

