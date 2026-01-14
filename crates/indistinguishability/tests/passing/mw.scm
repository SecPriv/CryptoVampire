(require "cryptovampire/v2")
(require "../save-results.scm")
(require-builtin cryptovampire as cv-)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define prf (declare-cryptography pbl))
(define mxorc (declare-cryptography pbl))

(define-function mhash pbl (prf) (Bitstring Bitstring) -> Bitstring)
(define-function mxor pbl (mxorc) (Bitstring Bitstring) -> Bitstring)
(define-function ok pbl Bitstring)
(define-function ko pbl Bitstring)
(define-function k1 pbl (Index) -> Nonce)
(define-function k2 pbl (Index Index) -> Nonce)
(define-function _nt pbl (Index Index) -> Nonce)
(define-function _nr pbl (Index) -> Nonce)
(define-function tag1 pbl Bitstring)
(define-function tag2 pbl Bitstring)

(define-function id1 pbl (Index) -> Bitstring)
(define-function id2 pbl (Index Index) -> Bitstring)

(define-alias _mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> (k1 i))
  ([ (i Index) (j Index) ] (i j p2) -> (k2 i j)) ])

(define-alias mid pbl (Index Index Protocol) Bitstring
  [ ([ (i Index) (j Index) ] (i j p1) -> (id1 i))
  ([ (i Index) (j Index) ] (i j p2) -> (id2 i j)) ])

(define mk (wrap-nonce _mk))
(define nt (wrap-nonce _nt))
(define nr (wrap-nonce _nr))

(define empty-cond (lambda _ mtrue))

(define (mk-fdst1 in j p)
  (findst ((i Index) (k Index))
    (eq
      (mxor
        (mid i k p) (sel2of2 in))
      (mhash
        (tuple (tuple (nr j) (sel1of2 in)) tag1)
        (mk i k p)))
    (mxor
      (mid i k p)
      (mhash
        (tuple (tuple (nr j) (sel1of2 in)) tag2)
        (mk i k p)))
    ko))

(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1 empty-cond
      (lambda (in i j)
        (tuple (nt i j)
          (mxor
            (mid i j p1)
            (mhash
              (tuple (tuple in (nt i j)) tag1)
              (mk i j p1))))))
    (step p2 empty-cond
      (lambda (in i j)
        (tuple (nt i j)
          (mxor
            (mid i j p2)
            (mhash
              (tuple (tuple in (nt i j)) tag1)
              (mk i j p2))))))))
; (bind ((j Index) (i Index) (p Protocol))
;   (cv-add-rewrite pbl (cv-mk-rewrite "rebuild mid" (list j i p)
;       (mid i j p)
;       (mxor
;         (mhash (tuple (tuple (macro_input (tag i j) p) (nt i j)) tag1) (mk i j p))
;         (sel2of2 (macro_msg (tag i j) p))))))

(define r1
  (declare-step pbl "r" (list Index)
    (step p1 empty-cond (lambda (_ i) (nr i)))
    (step p2 empty-cond (lambda (_ i) (nr i)))))

(bind ((i Index))
  (begin
    (cv-add-rewrite pbl (cv-mk-rewrite "lemma1" (list i)
        (nr i) (macro_msg (r1 i) p1)))
    (cv-add-rewrite pbl (cv-mk-rewrite "lemma2" (list i)
        (nr i) (macro_msg (r1 i) p2)))))

(define r2
  (declare-step pbl "r2" (list Index)
    (step p1 empty-cond
      (lambda (in j) (mk-fdst1 in j p1)))
    (step p2 empty-cond
      (lambda (in j) (mk-fdst1 in j p2)))))
(add-constrain pbl (i) (lt (r1 i) (r2 i)))

(initialize-as-prf prf mhash)
(initialize-as-xor mxorc mxor)

; hashes have the length of nonces
(bind ((i Index) (j Index) (p Protocol))
  (cv-add-rewrite pbl (cv-mk-rewrite "length id" (list i j p)
      (bitstring-length (mid i j p)) eta)))

(define (mk-fdst2 r p)
  (let [ (in (macro_input (r2 r) p)) ]
    (findst ((i Index) (t Index))
      (cand
        (eq (sel1of2 in) (sel1of2 (macro_msg (tag i t) p)))
        (eq (sel2of2 in) (sel2of2 (macro_msg (tag i t) p)))
        (macro_exec (r2 r) p)
        (lt (r1 r) (tag i t))
        (lt (tag i t) (r2 r))) ; <- very important
      (mxor (mid i t p) (mhash (tuple (tuple (nr r) (sel1of2 in)) tag2) (mk i t p)))
      ko)))

(bind ((j Index) (r Index) (p Protocol))
  (cv-add-rewrite pbl (cv-mk-rewrite "lemma" (list j r p)
      (m_ite (macro_exec (r2 r) p) (mk-fdst1 (macro_input (r2 r) p) j p) mempty)
      (m_ite (macro_exec (r2 r) p) (mk-fdst2 r p) mempty))))


(cv-add-smt-axiom pbl (mnot (eq tag1 tag2)))

;; configuration
; (cv-set-trace pbl #t)
(cv-set-vampire-timeout pbl (cv-string->duration "1.5s"))
(cv-set-node-limit pbl 100000)
(cv-set-prf-limit pbl 1)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed mw"))

(displayln (cv-print-report (cv-get-report pbl)))
(save-results "mw" pbl)