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

;; Simple memory cell test
;; Declare a memory cell with no parameters (single value)
(define s (declare-memory-cell pbl "s" '()))

;; Tag process that reads and updates the memory cell
(define tag
  (declare-step pbl "tag" '()
    (step p1 (lambda _ mtrue) (lambda _ mempty))
    (step p2 (lambda _ mtrue) (lambda _ mempty))))

;; Configuration - use short timeout
(config.set_vampire_timeout pbl (b.mult->duration scale-timeout (b.string->duration "150ms")))

;; Run the indistinguishability check
(if (run pbl p1 p2)
  (displayln "success")
  (error "failed memory-cell-simple"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "memory-cell-simple" pbl)
