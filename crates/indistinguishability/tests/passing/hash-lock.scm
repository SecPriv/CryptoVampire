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
(define-function _nr pbl (Index) -> Nonce)

(define-alias _mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> (k1 i))
  ([ (i Index) (j Index) ] (i j p2) -> (k2 i j)) ])

(define n (wrap-nonce _n))
(define nr (wrap-nonce _nr))
(define mk (wrap-nonce _mk))


(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i j)
        (tuple (n i j) (mhash (tuple in (n i j)) (mk i j p1)))))
    (step p2
      (lambda _ mtrue)
      (lambda (in i j)
        (tuple (n i j) (mhash (tuple in (n i j)) (mk i j p2)))))))

(define reader1
  (declare-step pbl "reader1" (list Index)
    (step p1 (lambda _ mtrue) (lambda (in i) (nr i)))
    (step p2 (lambda _ mtrue) (lambda (in i) (nr i)))))

(define rs
  (declare-step pbl "reader_success" (list Index Index)
    (step p1
      (lambda (in i j)
        (eq (tuple (nr i) (sel2of2 in)) (mhash (sel1of2 in) (mk i j p1))))
      (lambda _ ok))
    (step p2
      (lambda (in i j)
        (eq (tuple (nr i) (sel2of2 in)) (mhash (sel1of2 in) (mk i j p2))))
      (lambda _ ok))))

(define rf
  (declare-step pbl "reader_fail" (list Index)
    (step p1
      (lambda (in i)
        (mnot (exists ((j Index))
            (eq (tuple (nr i) (sel2of2 in))
              (mhash (sel1of2 in) (mk i j p1))))))
      (lambda _ ko))
    (step p2
      (lambda (in i)
        (mnot (exists ((j Index))
            (eq (tuple (nr i) (sel2of2 in))
              (mhash (sel1of2 in) (mk i j p2))))))
      (lambda _ ko))))

(initialize-as-prf prf mhash)

(bind
  ((i Index) (j Index)
    (t Time)
    (p Protocol))
  (let [ (in (macro_input t p)) (int (lambda (j) (macro_msg (tag i j) p))) ]
    (cv-add-rewrite pbl (cv-mk-rewrite "lemma-2" (list i t j p)
        (eq (tuple (nr i) (sel2of2 in)) (mhash (sel1of2 in) (mk i j p)))
        (exists ((j Index))
          (cand
            (eq (sel1of2 in) (sel1of2 (int j)))
            (eq (sel2of2 in) (sel2of2 (int j)))
            (eq (macro_input (tag i j) p) (macro_msg (reader1 i) p))
            (lt (reader1 i) (tag i j))
            (lt (tag i j) t))))))); <- very important

(add-constrain pbl (i j) (lt (reader1 i) (rs i j)))
(add-constrain pbl (i) (lt (reader1 i) (rf i)))
(add-constrain pbl (i j) (<> (rs i j) (rf i)))

;; configuration
; (cv-set-trace pbl #t)
(cv-set-vampire-timeout pbl (cv-string->duration "10s"))

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed hash-lock"))

(displayln (cv-print-report (cv-get-report pbl)))
(save-results  "hash-lock" pbl)