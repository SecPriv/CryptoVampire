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
(define ptcls (list p1 p2))

(define prf (declare-cryptography pbl))

(define-function mhash pbl (prf) (Bitstring Bitstring) -> Bitstring)
(define-function ok pbl Bitstring)
(define-function ko pbl Bitstring)
(define-function k1 pbl (Index) -> Nonce)
(define-function k2 pbl (Index Index) -> Nonce)
(define-function n pbl (Index Index) -> Nonce)
(define-function nr pbl (Index) -> Nonce)

(define-alias _mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> ((unwrap-nonce k1) i))
  ([ (i Index) (j Index) ] (i j p2) -> ((unwrap-nonce k2) i j)) ])

(define mk (wrap-nonce _mk))

(define (verify s m k) (eq s (mhash m k)));; because I made too many mistakes

(define tag
  (declare-same-step pbl "tag" ptcls (list Index Index)
    (lambda _ mtrue)
    (lambda (p in i j . _)
      (tuple (n i j) (mhash (tuple in (n i j)) (mk i j p))))
    empty-assignements))

(define reader1
  (declare-step pbl "reader1" (list Index)
    (step p1 (lambda _ mtrue) (lambda (in i . _) (nr i)) empty-assignements)
    (step p2 (lambda _ mtrue) (lambda (in i . _) (nr i)) empty-assignements)))

(define reader2
  (declare-same-step pbl "reader2" ptcls (list Index)
    (lambda _ mtrue)
    (lambda (p in j . _)
      (m_ite
        (exists ((i Index) (k Index))
          (verify (sel2of2 in) (tuple (nr j) (sel1of2 in)) (mk i k p)))
        ok ko))
    empty-assignements))

(initialize-as-prf prf mhash)

(bind
  ((j Index)
    (t Time)
    (p Protocol))
  (let [ (in (macro_input t p)) ]
    (add-rewrite pbl (rw.new "lemma-2" (list t j p)
        (exists ((i Index) (k Index))
          (verify (sel2of2 in) (tuple (nr j) (sel1of2 in)) (mk i k p)))
        (exists ((i Index) (k Index))
          (cand
            (eq in (macro_msg (tag i k) p))
            (eq (macro_input (tag i k) p) (macro_msg (reader1 j) p))
            (lt (reader1 j) (tag i k))
            (lt (tag i k) t))))))); <- very important

(add-constrain pbl (i) (lt (reader1 i) (reader2 i)))

(run-and-save "hash-lock" pbl p1 p2 "150ms")
