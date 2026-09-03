(require "./scripts/save-results.scm")
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

(define empty-cond (lambda _ mtrue))

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
      (lambda (in j . _) (mk-fdst1 in j p1))
      empty-assignements)
    (step p2 empty-cond
      (lambda (in j . _) (mk-fdst1 in j p2))
      empty-assignements)))

(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1 empty-cond
      (lambda (in i j . _)
        (enc
          (tuple tagT (tuple in (nt i j)))
          (rt i j)
          (mk i j p1)))
      empty-assignements)
    (step p2 empty-cond
      (lambda (in i j . _)
        (enc
          (tuple tagT (tuple in (nt i j)))
          (rt i j)
          (mk i j p2)))
      empty-assignements)))


(define r
  (declare-step pbl "r" (list Index)
    (step p1 empty-cond (lambda (_ i . _) (nr i)) empty-assignements)
    (step p2 empty-cond (lambda (_ i . _) (nr i)) empty-assignements)))


(initialize-as-senc senc enc dec)

(define (mk-fdst2 t j p)
  (findst ((i Index) (k Index))
    (cand
      (eq (macro_input t p) (macro_msg (tag i k) p))
      (eq (macro_input (tag i k) p) (macro_msg (r j) p))
      (lt (tag i k) t)
      (macro_exec t p)) ; <- very important
    (enc
      (tuple tagR (tuple (nr j) (nt i k)))
      (rr j)
      (mk i k p))
    ko))

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
      (add-rewrite pbl (rw.new "lemma" (list t j p)
          (m_ite (macro_exec (r2 j) p) (mk-fdst1 (macro_input (r2 j) p) j p) mempty)
          (m_ite (macro_exec (r2 j) p) (mk-fdst2 (r2 j) j p) mempty))))))


(add-smt-axiom pbl (mnot (eq tagT tagR)))
(add-constrain pbl (j) (lt (r j) (r2 j)))

;; configuration
; (config.set_trace pbl #t)
(config.set_guided_nonce_search pbl #t)
(config.set_egg_node_limit pbl 100000)
(config.set_prf_limit pbl 1)
(config.set_fa_limit pbl 4)

(run-and-save "feldhofer-S" pbl p1 p2 "150ms")
