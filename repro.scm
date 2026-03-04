(require "cryptovampire/signature")
(require "cryptovampire/sort")

(define-syntax my-alias
  (syntax-rules (->)
    [ (_ name inputs output ((((vars sorts) ...) args -> res) ...))
      (begin
        (displayln (signature inputs -> output))
        (my-rule ((vars sorts) ...) args -> res) ...) ]))

(define-syntax my-rule
  (syntax-rules (->)
    [ (_ vars args -> res)
      (begin
        (displayln vars)
        (displayln args)
        (displayln res)) ]))

(my-alias "_mk" (Index Index) Nonce (([ (i Index) ] (i p1) -> 10)))
