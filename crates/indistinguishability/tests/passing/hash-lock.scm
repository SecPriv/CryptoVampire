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


(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i j . _)
        (tuple (n i j) (mhash (tuple in (n i j)) (mk i j p1))))
      empty-assignements)
    (step p2
      (lambda _ mtrue)
      (lambda (in i j . _)
        (tuple (n i j) (mhash (tuple in (n i j)) (mk i j p2))))
      empty-assignements)))

(define reader1
  (declare-step pbl "reader1" (list Index)
    (step p1 (lambda _ mtrue) (lambda (in i . _) (nr i)) empty-assignements)
    (step p2 (lambda _ mtrue) (lambda (in i . _) (nr i)) empty-assignements)))

(define rs
  (declare-step pbl "reader_success" (list Index Index)
    (step p1
      (lambda (in i j . _)
        (eq (tuple (nr i) (sel2of2 in)) (mhash (sel1of2 in) (mk i j p1))))
      (lambda _ ok)
      empty-assignements)
    (step p2
      (lambda (in i j . _)
        (eq (tuple (nr i) (sel2of2 in)) (mhash (sel1of2 in) (mk i j p2))))
      (lambda _ ok)
      empty-assignements)))

(define rf
  (declare-step pbl "reader_fail" (list Index)
    (step p1
      (lambda (in i . _)
        (mnot (exists ((j Index))
            (eq (tuple (nr i) (sel2of2 in))
              (mhash (sel1of2 in) (mk i j p1))))))
      (lambda _ ko)
      empty-assignements)
    (step p2
      (lambda (in i . _)
        (mnot (exists ((j Index))
            (eq (tuple (nr i) (sel2of2 in))
              (mhash (sel1of2 in) (mk i j p2))))))
      (lambda _ ko)
      empty-assignements)))

(initialize-as-prf prf mhash)

(bind
  ((i Index) (j Index)
    (t Time)
    (p Protocol))
  (let [ (in (macro_input t p)) (int (lambda (j) (macro_msg (tag i j) p))) ]
    (add-rewrite pbl (rw.new "lemma-2" (list i t j p)
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
; (config.set_trace pbl #t)
(define default-timeout (b.string->duration "20s"))
(config.set_vampire_timeout pbl (b.mult->duration scale-timeout default-timeout))

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed hash-lock"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results  "hash-lock" pbl)
