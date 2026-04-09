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

(define senc (declare-cryptography pbl))

(define-function enc pbl (senc) (Bitstring Bitstring Bitstring) -> Bitstring)
(define-function dec pbl (senc) (Bitstring Bitstring) -> Bitstring)

(define-function ok pbl Bitstring)
(define-function ko pbl Bitstring)
(define-function k1 pbl (Index) -> Nonce)
(define-function k2 pbl (Index Index) -> Nonce)
(define-function nt pbl (Index Index) -> Nonce)
(define-function rr pbl (Index) -> Nonce)
(define-function rt pbl (Index Index) -> Nonce)
(define-function nr pbl (Index) -> Nonce)
(define-function tagT pbl Bitstring)
(define-function tagR pbl Bitstring)

(define-alias _mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> ((unwrap-nonce k1) i))
  ([ (i Index) (j Index) ] (i j p2) -> ((unwrap-nonce k2) i j)) ])
(define mk (wrap-nonce _mk))

; (define tag (declare-step pbl "tag" (list Index Index)))
; (define r (declare-step pbl "r" (list Index)))
; (define r2 (declare-step pbl "r2" (list Index)))

(define empty-cond (lambda _ mtrue))

; (publish pbl ((i Index) (j Index)) (nt i j))
; (publish pbl ((i Index)) (nr i))

(define (mk-fdst1 in j p)
  (let* [ (pt (lambda (i j) (dec in (mk i j p))))
    (nt (lambda (i j) (sel2of2 (sel2of2 (pt i j))))) ]
    (findst ((i Index) (k Index))
      (cand
        (eq (sel1of2 (pt i k)) tagT)
        (eq (sel1of2 (sel2of2 (pt i k))) (nr j)))
      (enc
        (tuple tagR (tuple (nr j) (nt i j)))
        (rr j)
        (mk i k p))
      ko)))

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
        (enc
          (tuple tagT (tuple in (nt i j)))
          (rt i j)
          (mk i j p1))))
    (step p2 empty-cond
      (lambda (in i j)
        (enc
          (tuple tagT (tuple in (nt i j)))
          (rt i j)
          (mk i j p2))))))


(define r
  (declare-step pbl "r" (list Index)
    (step p1 empty-cond (lambda (_ i) (nr i)))
    (step p2 empty-cond (lambda (_ i) (nr i)))))

; (define exposes-nt
;   (declare-step pbl "exposts-nt" (list Index Index)
;     (step p1 empty-cond (lambda (_ i j) (nt i j)))
;     (step p2 empty-cond (lambda (_ i j) (nt i j)))))
; (define exposes-nr
;   (declare-step pbl "exposts-nr" (list Index)
;     (step p1 empty-cond (lambda (_ j) (nr j)))
;     (step p2 empty-cond (lambda (_ j) (nr j)))))
; (add-constrain pbl (i j k) (lt (exposes-nt i j) (r k)))
; (add-constrain pbl (i j k l) (lt (exposes-nt i j) (tag k l)))
; (add-constrain pbl (i j k) (lt (exposes-nr i) (r k)))
; (add-constrain pbl (i j k l) (lt (exposes-nr i) (tag k l)))

; (bind ((i Index) (j Index) (p Protocol)) (begin
;     (cv-add-rewrite pbl (cv-mk-rewrite "nt1" (list i j)
;         (nt i j) (macro_msg (exposes-nt i j) p1)))
;     (cv-add-rewrite pbl (cv-mk-rewrite "nt2" (list i j)
;         (nt i j) (macro_msg (exposes-nt i j) p2)))
;     (cv-add-rewrite pbl (cv-mk-rewrite "nr1" (list i)
;         (nr i) (macro_msg (exposes-nr i) p1)))
;     (cv-add-rewrite pbl (cv-mk-rewrite "nr2" (list i)
;         (nr i) (macro_msg (exposes-nr i) p2)))
;     (cv-add-rewrite pbl (cv-mk-rewrite "nt_exec" (list i j p)
;         (macro_exec (exposes-nt i j) p) (happens (exposes-nt i j))))
;     (cv-add-rewrite pbl (cv-mk-rewrite "nr_exec" (list i j p)
;         (macro_exec (exposes-nr i) p) (happens (exposes-nr i))))))
(config.set_guided_nonce_search pbl #t)

(initialize-as-senc senc enc dec)

(define (mk-fdst2 t j p)
  (let* [ (in (macro_input t p))
    (pt (lambda (i j) (dec in (mk i j p))))
    (int (lambda (i j) (dec (unfold_msg (tag i j) p) (mk i j p))))
    ; (nt (lambda (i j) (sel2of2 (sel2of2 (pt i j))))) 
    ]
    (findst ((i Index) (k Index))
      (cand
        (eq (macro_input t p) (macro_msg (tag i k) p))
        ; (eq (sel1of2 (pt i k)) (sel1of2 (int i k)))
        ; (eq (sel2of2 (pt i k)) (sel2of2 (int i k)))
        (lt (tag i k) t)
        (macro_exec t p)) ; <- very important
      (enc
        (tuple tagR (tuple (nr j) (nt i k)))
        (rr j)
        (mk i k p))
      ko)))

(bind ((j Index) (t Time) (p Protocol))
  (let [ (tmp (findst ((i Index) (k Index))
        (cand
          (eq (sel1of2 (dec (macro_input (r2 j) p) (mk i k p))) tagT)
          (eq (sel1of2 (sel2of2 (dec (macro_input (r2 j) p) (mk i k p)))) (nr j)))
        (enc
          (tuple tagR (tuple (nr j) (nt i j)))
          (rr j)
          (mk i k p))
        ko)) ]
    (begin
      ; (displayln (cv-string-of-formula (m_ite mtrue tmp mempty)))
      
      (add-rewrite pbl (rw.new "lemma" (list t j p)
          ; (let ((x (mk-fdst1 (macro_input (r2 j) p) j p)))
          ; (m_ite mtrue x  mempty))
          ; (m_ite mtrue tmp mempty)
          ; tmp
          ; ok
          (m_ite (macro_exec (r2 j) p) (mk-fdst1 (macro_input (r2 j) p) j p) mempty)
          (m_ite (macro_exec (r2 j) p) (mk-fdst2 (r2 j) j p) mempty)
          ; ok
          )))))


(add-smt-axiom pbl (mnot (eq tagT tagR)))
(add-constrain pbl (j) (lt (r j) (r2 j)))

;; configuration
; (config.set_trace pbl #t)
(define default-timeout (b.string->duration "0.8s"))
(config.set_vampire_timeout pbl (b.mult->duration scale-timeout default-timeout))
(config.set_node_limit pbl 100000)
(config.set_prf_limit pbl 1)
(config.set_fa_limit pbl 4)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed feldhofer"))


(displayln (report.print-report (pbl.get-report pbl)))
(save-results "feldhofer" pbl)
