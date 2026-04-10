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

;; Cryptographic primitives
(define prf (declare-cryptography pbl))
(define hash-fun (declare-cryptography pbl))

;; Memory cells: sT(i) and sR(i) - state arrays indexed by Index
(define sT (declare-memory-cell pbl "sT" (list Index)))
(define sR (declare-memory-cell pbl "sR" (list Index)))

;; Initial state function
(define-function s0 pbl (Index) -> Bitstring)

;; Keys (constant across sessions)
(define-function k pbl Bitstring)
(define-function k-prime pbl Bitstring)

;; Hash and PRF functions
(define-function H pbl (Bitstring Bitstring) -> Bitstring)
(define-function G pbl (Bitstring Bitstring) -> Bitstring)

(define ptcls (list p1 p2))

;; Initialize memory cells in the init step
;; sT(i) = s0(i) and sR(i) = s0(i) initially
(set-init-step pbl
  (step p1 (lambda _ mtrue) (lambda (_ in) mtrue))
  (step p2 (lambda _ mtrue) (lambda (_ in) mtrue)))

;; Tag process: receives nothing, outputs G(sT(i), k')
;; Updates: sT(i) := H(sT(i), k)
(define tag
  (declare-step pbl "tag" (list Index)
    (step p1 (lambda _ mtrue)
      (lambda (cells in i)
        (tuple
          (G ((hash-ref cells (get-function sT)) i) k-prime)
          (H ((hash-ref cells (get-function sT)) i) k))))
    (step p2 (lambda _ mtrue)
      (lambda (cells in i)
        (tuple
          (G ((hash-ref cells (get-function sT)) i) k-prime)
          (H ((hash-ref cells (get-function sT)) i) k))))))

;; Set memory cell assignments for tag step
;; sT(i) := H(sT(i)@pred, k)
(bind ((i Index) (p Protocol) (t Time))
  (set-step-assignment! pbl (tag i) p sT '()
    (H (macro_memory_cell (sT i) t p) k)))

;; Reader process: receives (y1, y2), checks if y2 = G(sR(i), k')
;; If match: outputs y1 and updates sR(i) := H(sR(i), k)
;; If no match: outputs error
(define reader
  (declare-step pbl "reader" (list Index)
    (step p1 (lambda (cells in i)
               (eq (sel2of2 in) (G ((hash-ref cells (get-function sR)) i) k-prime)))
      (lambda (cells in i)
        (sel1of2 in)))  ; output y1
    (step p2 (lambda (cells in i)
               (eq (sel2of2 in) (G ((hash-ref cells (get-function sR)) i) k-prime)))
      (lambda (cells in i)
        (sel1of2 in)))))  ; output y1

;; Set memory cell assignments for reader step (conditional)
;; sR(i) := H(sR(i)@pred, k) when condition is true
(bind ((i Index) (p Protocol) (t Time))
  (set-step-assignment! pbl (reader i) p sR '()
    (H (macro_memory_cell (sR i) t p) k)))

;; Initialize cryptographic primitives
(initialize-as-prf prf H)
(initialize-as-prf hash-fun G)

;; Configuration - use short timeout for faster testing
(config.set_vampire_timeout pbl (b.mult->duration scale-timeout (b.string->duration "150ms")))

;; Run the indistinguishability check
(if (run pbl p1 p2)
  (displayln "success")
  (error "failed running-ex"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "running-ex" pbl)
