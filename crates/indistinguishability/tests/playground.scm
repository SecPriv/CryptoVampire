(require-builtin steel/base)

(print_formula (exists ((x Bitstring) (y Nonce)) (mand #t y)))

(define pbl (empty-problem))
; (define-alias tmp pbl "hey"  Bitstring ())
(define-alias-rule ((x Bitstring) (y Nonce)) @ ((mtuple x y) (mk-varf x)) => (mk-varf x))
; (bind ((x Bitstring) (y Nonce)) 
;   (mk-alias-rwf (list x) (list (mtuple x y)) (mk-varf x))
; )