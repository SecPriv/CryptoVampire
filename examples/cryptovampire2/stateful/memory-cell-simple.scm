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

(define s (declare-memory-cell pbl "s" '() (lambda (p) empty)))

(define tag
  (declare-step pbl "tag" '()
    (step p1 (lambda _ mtrue) (lambda _ mempty) (lambda (in cells) (list (store-cell s := mempty))))
    (step p2 (lambda _ mtrue) (lambda _ mempty) empty-assignements)))

;; Configuration

(run-and-save "memory-cell-simple" pbl p1 p2 "150ms")