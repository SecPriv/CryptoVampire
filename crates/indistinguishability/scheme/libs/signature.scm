(provide signature signature-doc)
(require-builtin cryptovampire/ll/signature as sig->)
(require "cryptovampire/doc")

;; Documentation table for the `cryptovampire/signature` library (macro docs,
;; next to their definitions).  See `cryptovampire/doc` for the mechanism.
(define signature-doc (make-doc-table))
(define (register-syntax-doc! name . doc)
  (set! signature-doc (apply doc-add! signature-doc name doc)))
(define (register-type-doc! name . doc)
  (set! signature-doc (apply doc-add! signature-doc name doc)))

;; ---------------------------------------------------------------------------
;; signature
;;
;; A concise way to build a `Signature`: `(inputs ...) -> output`, where each
;; element is a sort value.  A bare sort is a nullary signature.
;;
;; *Examples:*
;; ```scheme
;; (signature (Index Index) -> Nonce)
;; (signature () -> Time)          ; nullary
;; (signature Nonce)               ; same as (signature () -> Nonce)
;; ```
;;
;; A `signature` is a macro, so it has no `help` entry -- the `sig->new`
;; low-level function it abbreviates is documented in the Rust bindings.
;; ---------------------------------------------------------------------------

(register-syntax-doc! 'signature
  "A concise way to build a `Signature`: `(inputs ...) -> output`.  A bare sort is a nullary signature."
  ""
  "**Usage:**"
  "```scheme"
  "(signature (Index Index) -> Nonce)"
  "(signature Nonce)   ; same as (signature () -> Nonce)"
  "```")

(define-syntax signature
  (syntax-rules (->)
    [ (_ () -> sort) (sig->new '() sort) ]
    [ (_ (sorts ...) -> sort) (sig->new (list sorts ...) sort) ]
    [ (_ sort) (sig->new  '() sort) ]))
