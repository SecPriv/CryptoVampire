(require "cryptovampire/v2")
(require "../save-results.scm")
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

(define (ltrue . args) mtrue)

(define (pka1 i) (pk (ka a1 i)))
(define (pka2 i) (pk (ka a2 i)))
(define (pkb i) (pk (kb i)))

;; put this step first to fail faster
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


(publish pbl ((i Index) (j Index)) (pk (ka i j)))
(publish pbl ((i Index) ) (pkb i))
; (publish pbl ((i Index) ) (nb i))

; (define pa (declare-step pbl "publish_a" (list Index Index)
;     (step p1 ltrue (lambda (in i j) (pk (ka i j))))
;     (step p2 ltrue (lambda (in i j) (pk (ka i j))))))

; (define pb (declare-step pbl "publish_b" (list Index)
;     (step p1 ltrue (lambda (in i) (pkb i)))
;     (step p2 ltrue (lambda (in i) (pkb i)))))

(define b1
  (declare-step pbl "b1" (list Index)
    (step p1 ltrue (lambda (in i) (nb i)))
    (step p2 ltrue (lambda (in i) (nb i)))))


(bind ((i Index) (j Index))
  (begin
    ; (cv-add-rewrite pbl (cv-mk-rewrite "message_pa1" (list i j)
    ;     (pk (ka i j)) (macro_msg (pa i j) p1)))
    ; (cv-add-rewrite pbl (cv-mk-rewrite "message_pa2" (list i j)
    ;     (pk (ka i j)) (macro_msg (pa i j) p2)))
    ; (cv-add-rewrite pbl (cv-mk-rewrite "message_pb1" (list i)
    ;     (pkb i) (macro_msg (pb i) p1)))
    ; (cv-add-rewrite pbl (cv-mk-rewrite "message_pb2" (list i)
    ;     (pkb i) (macro_msg (pb i) p2)))
    (cv-add-rewrite pbl (cv-mk-rewrite "message_b1_1" (list i)
        (nb i) (macro_msg (b1 i) p1)))
    (cv-add-rewrite pbl (cv-mk-rewrite "message_b1_2" (list i)
        (nb i) (macro_msg (b1 i) p2)))))

(define as (declare-step pbl "as" (list Index Index)
    (step p1 ltrue (lambda (in i j) (enc (tuple in (na i j)) (ra i j) (pkb j))))
    (step p2 ltrue (lambda (in i j) (enc (tuple in (na i j)) (ra i j) (pkb j))))))

(initialize-as-aenc aenc enc dec pk)

; (add-constrain pbl (i j k) (lt (pb k) (as i j)))
; (add-constrain pbl (i j k l) (lt (pa k l) (as i j)))
; (add-constrain pbl (i k l) (lt (pa k l) (b1 i)))
; (add-constrain pbl (i k) (lt (pb k) (b1 i)))
; (add-constrain pbl (i) (lt (b1 i) (b2 i)))

;; if flips
(bind
  ((m1 Bitstring) (m2 Bitstring) (c Bool) (r Bitstring) (k Bitstring))
  (begin
    (cv-add-rewrite pbl (cv-mk-rewrite "flip" (list m1 m2 c r k)
        (m_ite c (enc m1 r k) (enc m2 r k))
        (enc (m_ite c m1 m2) r k)))
    (cv-add-rewrite pbl (cv-mk-rewrite "rev" (list m1 m2 c r k)
        (enc (m_ite c m1 m2) r k)
        (m_ite c (enc m1 r k) (enc m2 r k))))
    (cv-add-rewrite pbl (cv-mk-rewrite "flip-zeroes" (list m1 m2 c)
        (m_ite c (zeroes m1) (zeroes m2))
        (zeroes (m_ite c m1 m2))))
    ; (cv-add-rewrite pbl (cv-mk-rewrite "flip-length" (list m1 m2 c)
    ;     (m_ite c (bitstring-length m1) (bitstring-length m2))
    ;     (bitstring-length (m_ite c m1 m2))))
    (cv-add-rewrite pbl (cv-mk-rewrite "flip-length-rev" (list m1 m2 c)
        (bitstring-length (m_ite c m1 m2))
        (m_ite c (bitstring-length m1) (bitstring-length m2))))))

;; configuration
; (cv-set-trace pbl #t)
(cv-set-vampire-timeout pbl (cv-string->duration "300ms"))
(cv-set-node-limit pbl 10000000)
; (cv-set-node-limit pbl 200)
(cv-set-enc-kp-limit pbl 1)
(cv-set-fa-limit pbl 0)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed private auth"))

(displayln (cv-print-report (cv-get-report pbl)))
(save-results "private-auth" pbl)