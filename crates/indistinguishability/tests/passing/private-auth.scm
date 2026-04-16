(require "../save-results.scm")
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

(define aenc (declare-cryptography pbl))

(define-function enc pbl (aenc) (Bitstring Bitstring Bitstring) -> Bitstring)
(define-function dec pbl (aenc) (Bitstring Bitstring) -> Bitstring)
(define-function pk pbl (aenc) (Bitstring) -> Bitstring)

(define-function a1 pbl Index)
(define-function a2 pbl Index)
(define-function ka pbl (Index Index) -> Nonce)
(define-function kb pbl (Index) -> Nonce)
(define-function nb pbl (Index) -> Nonce)
(define-function na pbl (Index Index) -> Nonce)
(define-function ra pbl (Index Index) -> Nonce)
(define-function rb pbl (Index) -> Nonce)

(define (ltrue . args) mtrue)

(define (pka1 i) (pk (ka a1 i)))
(define (pka2 i) (pk (ka a2 i)))
(define (pkb i) (pk (kb i)))

;; put this step first to fail faster
(define b2
  (declare-step pbl "b2" (list Index)
    (step p1 ltrue (lambda (in i . _)
        (let [ (in (dec in (kb i))) (dflt (tuple (nb i) (nb i))) ]
          (m_ite
            (eq (sel1of2 in) (pka1 i))
            (m_ite (eql (tuple (sel2of2 in) (nb i)) dflt)
              (enc (tuple (sel2of2 in) (nb i)) (rb i) (pka1 i))
              (enc dflt (rb i) (pka1 i)))
            (enc dflt (rb i) (pka1 i)))))
      empty-assignements)
    (step p2 ltrue (lambda (in i . _)
        (let [ (in (dec in (kb i))) (dflt (tuple (nb i) (nb i))) ]
          (m_ite
            (eq (sel1of2 in) (pka2 i))
            (m_ite (eql (tuple (sel2of2 in) (nb i)) dflt)
              (enc (tuple (sel2of2 in) (nb i)) (rb i) (pka2 i))
              (enc dflt (rb i) (pka2 i)))
            (enc dflt (rb i) (pka2 i)))))
      empty-assignements)))


(publish pbl ((i Index) (j Index)) (pk (ka i j)))
(publish pbl ((i Index) ) (pkb i))
; (publish pbl ((i Index) ) (nb i))

; (define pa (declare-step pbl "publish_a" (list Index Index)
;     (step p1 ltrue (lambda (in i j . _) (pk (ka i j))) empty-assignements)
;     (step p2 ltrue (lambda (in i j . _) (pk (ka i j))) empty-assignements)))

; (define pb (declare-step pbl "publish_b" (list Index)
;     (step p1 ltrue (lambda (in i . _) (pkb i)) empty-assignements)
;     (step p2 ltrue (lambda (in i . _) (pkb i)) empty-assignements)))

(define b1
  (declare-step pbl "b1" (list Index)
    (step p1 ltrue (lambda (in i . _) (nb i)) empty-assignements)
    (step p2 ltrue (lambda (in i . _) (nb i)) empty-assignements)))


(bind ((i Index) (j Index))
  (begin
    ; (add-rewrite pbl (rw.new "message_pa1" (list i j)
    ;     (pk (ka i j)) (macro_msg (pa i j) p1)))
    ; (add-rewrite pbl (rw.new "message_pa2" (list i j)
    ;     (pk (ka i j)) (macro_msg (pa i j) p2)))
    ; (add-rewrite pbl (rw.new "message_pb1" (list i)
    ;     (pkb i) (macro_msg (pb i) p1)))
    ; (add-rewrite pbl (rw.new "message_pb2" (list i)
    ;     (pkb i) (macro_msg (pb i) p2)))
    (add-rewrite pbl (rw.new "message_b1_1" (list i)
        (nb i) (macro_msg (b1 i) p1)))
    (add-rewrite pbl (rw.new "message_b1_2" (list i)
        (nb i) (macro_msg (b1 i) p2)))))

(define as (declare-step pbl "astep" (list Index Index)
    (step p1 ltrue (lambda (in i j . _) (enc (tuple in (na i j)) (ra i j) (pkb j))) empty-assignements)
    (step p2 ltrue (lambda (in i j . _) (enc (tuple in (na i j)) (ra i j) (pkb j))) empty-assignements)))

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
    (add-rewrite pbl (rw.new "flip" (list m1 m2 c r k)
        (m_ite c (enc m1 r k) (enc m2 r k))
        (enc (m_ite c m1 m2) r k)))
    (add-rewrite pbl (rw.new "rev" (list m1 m2 c r k)
        (enc (m_ite c m1 m2) r k)
        (m_ite c (enc m1 r k) (enc m2 r k))))
    (add-rewrite pbl (rw.new "flip-zeroes" (list m1 m2 c)
        (m_ite c (zeroes m1) (zeroes m2))
        (zeroes (m_ite c m1 m2))))
    ; (add-rewrite pbl (rw.new "flip-length" (list m1 m2 c)
    ;     (m_ite c (bitstring-length m1) (bitstring-length m2))
    ;     (bitstring-length (m_ite c m1 m2))))
    (add-rewrite pbl (rw.new "flip-length-rev" (list m1 m2 c)
        (bitstring-length (m_ite c m1 m2))
        (m_ite c (bitstring-length m1) (bitstring-length m2))))))

;; configuration
; (config.set_trace pbl #t)
(define default-timeout (b.string->duration "150ms"))
(config.set_smt_timeout pbl (b.mult->duration scale-timeout default-timeout))
(config.set_egg_node_limit pbl 10000000)
; (config.set_egg_node_limit pbl 200)
(config.set_enc_kp_limit pbl 1)
(config.set_fa_limit pbl 0)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed private auth"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "private-auth" pbl)