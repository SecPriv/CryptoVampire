(require "cryptovampire/v2")
(require-builtin cryptovampire as cv-)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define aenc (declare-cryptography pbl))

(define-function enc pbl (aenc) (Bitstring Bitstring Bitstring) -> Bitstring)
(define-function dec pbl (aenc) (Bitstring Bitstring) -> Bitstring)
(define-function pk pbl (aenc) (Bitstring) -> Bitstring)

(define-function a1 pbl Index)
(define-function a2 pbl Index)
(define-function _ka pbl (Index Index) -> Nonce)
(define-function _kb pbl (Index) -> Nonce)
(define-function _nb pbl (Index) -> Nonce)
(define-function _na pbl (Index Index) -> Nonce)
(define-function _ra pbl (Index Index) -> Nonce)
(define-function _rb pbl (Index) -> Nonce)

(define ka (wrap-nonce _ka))
(define kb (wrap-nonce _kb))
(define na (wrap-nonce _na))
(define nb (wrap-nonce _nb))
(define ra (wrap-nonce _ra))
(define rb (wrap-nonce _rb))

(define (pka1 i) (pk (ka a1 i)))
(define (pka2 i) (pk (ka a2 i)))
(define (pkb i) (pk (kb i)))

(define (ltrue . args) mtrue)

(declare-step pbl "publish_a" (list Index Index)
  (step p1 ltrue (lambda (in i j) (pk (ka i j))))
  (step p2 ltrue (lambda (in i j) (pk (ka i j)))))

(declare-step pbl "publish_b" (list Index)
  (step p1 ltrue (lambda (in i) (pkb i)))
  (step p2 ltrue (lambda (in i) (pkb i))))

(define b1
  (declare-step pbl "b1" (list Index)
    (step p1 ltrue (lambda (in i) (nb i)))
    (step p2 ltrue (lambda (in i) (nb i)))))

(define b2
  (declare-step pbl "b2" (list Index)
    (step p1 ltrue (lambda (in i)
        (let [ (in (dec in (kb i))) (dflt (tuple (nb i) (nb i))) ]
          (m_ite
            (eq (sel1of2 in) (pka1 i))
            (m_ite (eql (tuple (sel2of2 in) (nb i)) dflt)
              (enc (tuple (sel2of2 in) (nb i)) (rb i) (pka1 i))
              (enc dflt (rb i) (pka1 i)))
            (enc dflt (rb i) (pka1 i))))))
    (step p2 ltrue (lambda (in i)
        (let [ (in (dec in (kb i))) (dflt (tuple (nb i) (nb i))) ]
          (m_ite
            (eq (sel1of2 in) (pka2 i))
            (m_ite (eql (tuple (sel2of2 in) (nb i)) dflt)
              (enc (tuple (sel2of2 in) (nb i)) (rb i) (pka2 i))
              (enc dflt (rb i) (pka2 i)))
            (enc dflt (rb i) (pka2 i))))))))

(define as (declare-step pbl "as" (list Index Index)
    (step p1 ltrue (lambda (in i j) (enc (tuple in (na i j)) (ra i j) (pkb j))))
    (step p2 ltrue (lambda (in i j) (enc (tuple in (na i j)) (ra i j) (pkb j))))))

(initialize-as-aenc aenc enc dec pk)

; (bind
;   ((i Index) (j Index)
;     (t Time)
;     (p Protocol))
;   (let [ (in (macro_input t p)) ]
;     (cv-add-rewrite pbl (cv-mk-rewrite "lemma-2" (list i t j p)
;         (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p)))
;         (exists ((i Index))
;           (cand
;             (eq (sel1of2 in) (sel1of2 (macro_input (tag i j) p)))
;             (eq (sel2of2 in) (sel2of2 (macro_input (tag i j) p)))
;             (lt (tag i j) t))))))); <- very important

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed"))
