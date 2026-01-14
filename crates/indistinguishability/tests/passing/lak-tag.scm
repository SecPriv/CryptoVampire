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
(define-function _nt pbl (Index Index) -> Nonce)
(define-function _nr pbl (Index) -> Nonce)
(define-function tag1 pbl Bitstring)
(define-function tag2 pbl Bitstring)

(define-alias _mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> (k1 i))
  ([ (i Index) (j Index) ] (i j p2) -> (k2 i j)) ])

(define mk (wrap-nonce _mk))
(define nt (wrap-nonce _nt))
(define nr (wrap-nonce _nr))

; (define tag (declare-step pbl "tag" (list Index Index)))
; (define r (declare-step pbl "r" (list Index)))
; (define r2 (declare-step pbl "r2" (list Index)))

(define empty-cond (lambda _ mtrue))

(define (mk-fdst1 in j p)
  (findst ((i Index) (k Index))
    (eq
      (sel2of2 in)
      (mhash
        (tuple (tuple (nr j) (sel1of2 in)) tag1)
        (mk i k p)))
    (mhash
      (tuple (tuple (nr j) (sel1of2 in)) tag2)
      (mk i k p))
    ko))

(define r2
  (declare-step pbl "r2" (list Index)
    (step p1 empty-cond
      (lambda (in j) (mk-fdst1 in j p1)))
    (step p2 empty-cond
      (lambda (in j) (mk-fdst1 in j p2)))))

(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1 empty-cond
      (lambda (in i j)
        (tuple (nt i j)
          (mhash
            (tuple (tuple in (nt i j)) tag1)
            (mk i j p1)))))
    (step p2 empty-cond
      (lambda (in i j)
        (tuple (nt i j)
          (mhash
            (tuple (tuple in (nt i j)) tag1)
            (mk i j p1)))))))


(define r
  (declare-step pbl "r" (list Index)
    (step p1 empty-cond (lambda (_ i) (nr i)))
    (step p2 empty-cond (lambda (_ i) (nr i)))))

(initialize-as-prf prf mhash)

(define (mk-fdst2 t j p)
  (let [ (in (macro_input t p)) ]
    (findst ((i Index) (k Index))
      (cand
        (eq (sel1of2 in) (sel1of2 (macro_msg (tag i k) p)))
        (eq (sel2of2 in) (sel2of2 (macro_msg (tag i k) p)))
        (macro_exec t p)
        (lt (tag i k) t)) ; <- very important
      (mhash (tuple (tuple (nr j) (sel1of2 in)) tag2) (mk i k p))
      ko)))

(bind ((j Index) (t Time) (p Protocol))
  (cv-add-rewrite pbl (cv-mk-rewrite "lemma" (list t j p)
      (m_ite (macro_exec t p) (mk-fdst1 (macro_input t p) j p) mempty)
      (m_ite (macro_exec t p) (mk-fdst2 t j p) mempty))))


(cv-add-smt-axiom pbl (mnot (eq tag1 tag2)))
(cv-add-smt-axiom pbl (forall [ (j Index) ] (lt (r j) (r2 j))))

;; configuration
; (cv-set-trace pbl #t)
(cv-set-vampire-timeout pbl (cv-string->duration "3s"))
(cv-set-node-limit pbl 100000)
(cv-set-prf-limit pbl 1)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed lak-tag"))


(displayln (cv-print-report (cv-get-report pbl)))
(save-results "lak-tag" pbl)