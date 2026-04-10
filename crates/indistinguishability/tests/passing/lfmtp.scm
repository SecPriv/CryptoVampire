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

(declare-same-step pbl "O" (list p1 p2) (list Index)
  (lambda _ mtrue)
  (lambda (p in i . _) (tuple (H in k) (H in kb)))
  empty-assignements)

(define-function m pbl (Index) -> Nonce)

(declare-step pbl "A" (list Index)
  (step p1
    (lambda _ mtrue)
    (lambda (in i cells . _) (G (H (cells s) k) kb))
    (lambda (_ _ cells . _) (list (store-cell s := (H (cells s) k)))))
  (step p2
    (lambda _ mtrue)
    (lambda (in i cells . _) (G (m i) kb))
    (lambda (_ i cells . _) (list (store-cell s := (m i))))))

;; Configuration - use short timeout
(config.set_vampire_timeout pbl (b.mult->duration scale-timeout (b.string->duration "150ms")))

;; Run the indistinguishability check
(if (run pbl p1 p2)
  (displayln "success")
  (error "failed memory-cell-simple"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "memory-cell-simple" pbl)
