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

(define-alias _mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> ((unwrap-nonce k1) i))
  ([ (i Index) (j Index) ] (i j p2) -> ((unwrap-nonce k2) i j)) ])

(define mk (wrap-nonce _mk))


(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i j)
        (tuple (n i j) (mhash (n i j) (mk i j p1)))))
    (step p2
      (lambda _ mtrue)
      (lambda (in i j)
        (tuple (n i j) (mhash (n i j) (mk i j p2)))))))

(define rs
  (declare-step pbl "rs" (list Index Index)
    (step p1
      (lambda (in i j)
        (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p1))))
      (lambda _ ok))
    (step p2
      (lambda (in i j)
        (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p2))))
      (lambda _ ok))))

(define rf
  (declare-step pbl "rf" (list Index)
    (step p1
      (lambda (in i)
        (mnot (exists ((j Index))
            (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p1))))))
      (lambda _ ok))
    (step p2
      (lambda (in i)
        (mnot (exists ((j Index))
            (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p2))))))
      (lambda _ ok))))

(initialize-as-prf prf mhash)

(bind
  ((i Index) (j Index)
    (t Time)
    (p Protocol))
  (let [ (in (macro_input t p)) ]
    (add-rewrite pbl (rw.new "lemma-2" (list i t j p)
        (eq (sel2of2 in) (mhash (sel1of2 in) (mk i j p)))
        (exists ((j Index))
          (cand
            (eq (sel1of2 in) (sel1of2 (macro_msg (tag i j) p)))
            (eq (sel2of2 in) (sel2of2 (macro_msg (tag i j) p)))
            (lt (tag i j) t))))))); <- very important

;; configuration
; (cv-set-trace pbl #t)
(config.set_vampire_timeout pbl (b.string->duration "5s"))

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed basic-hash"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "basic-hash" pbl)
