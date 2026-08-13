(require "../scripts/save-results.scm")
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
(require-builtin cryptovampire/ll/builtin-functions as builtin.)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define prf1 (declare-cryptography pbl))
(define prf2 (declare-cryptography pbl))
(define-function H pbl (prf1) (Bitstring Bitstring) -> Bitstring)
(define-function G pbl (prf2) (Bitstring Bitstring) -> Bitstring)

(define-function k pbl Nonce)
(define-function kb pbl Nonce)
(define-function s0 pbl Nonce)
(define s (declare-memory-cell pbl "s" '() (lambda _ s0)))

(define O (declare-same-step pbl "O" (list p1 p2) (list Index)
    (lambda _ mtrue)
    (lambda (p in i . _) (tuple (H in k) (G in kb)))
    empty-assignements))

(define-function m pbl (Index) -> Nonce)

(define A (declare-step pbl "A" (list Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i cells . _) (G (H (cells s) k) kb))
      (lambda (_ _ cells . _) (list (store-cell s := (H (cells s) k)))))
    (step p2
      (lambda _ mtrue)
      (lambda (in i cells . _) (G (m i) kb))
      (lambda (_ i cells . _) '()))))

(initialize-as-prf prf1 H)
(initialize-as-prf prf2 G)

; axiom
(pbl.add-smt-axiom pbl (forall ((i Index) (j Index) (p Protocol)) (=> (not (idx-eq i j)) (not (eq (macro_input (O i) p) (macro_input (O j) p))))))

; provable by induction with euf-cma
(pbl.add-smt-axiom pbl (forall ((t1 Time) (t2 Time) (p Protocol)) (=> (and (happens t1) (happens t2)) (not (eq (macro_input t1 p) (macro_memory_cell s t2 p))))))
(pbl.add-smt-axiom pbl (forall ((t1 Time) (i Index) (p Protocol)) (=> (and (happens t1)) (not (eq (macro_input t1 p) (m i))))))
(pbl.add-smt-axiom pbl (forall ((t1 Time) (i Index)) (=> (and (happens (A i)) (lt t1 (A i))) (not (eq (macro_memory_cell s (A i) p1) (macro_memory_cell s t1 p1))))))

(bind ((i Index))
  (register-fresh-nonce prf1 (list i) (m i)))

;; Configuration

(run-and-save "lfmtp" pbl p1 p2 "150ms")