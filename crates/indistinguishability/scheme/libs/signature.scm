(provide signature)
(require-builtin cryptovampire/ll/signature as sig->)

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

(define-syntax signature
  (syntax-rules (->)
    [ (_ () -> sort) (sig->new '() sort) ]
    [ (_ (sorts ...) -> sort) (sig->new (list sorts ...) sort) ]
    [ (_ sort) (sig->new  '() sort) ]))
