(provide initialize-as register-fresh-nonce declare-cryptography)
(require-builtin cryptovampire/ll/cryptography as c->)
(require "cryptovampire/function")

(define (register-fresh-nonce crypto vars f)
  (c->register-fresh-nonce crypto vars (get-function f)))

(define declare-cryptography c->declare-cryptography)

(define (partial f . args)
  (lambda (. rest-args)
    (apply f (append args rest-args))))

(define (initialize-as crypto kind . funs)
  (case
    [ ('prf) (apply (partial c->init->prf crypto) funs) ]
    [ ('ddh) (apply (partial c->init->ddh crypto) funs) ]
    [ ('aenc) (apply (partial c->init->aenc crypto) funs) ]
    [ ('senc) (apply (partial c->init->senc crypto) funs) ]
    [ ('xor) (apply (partial c->init->xor crypto) funs) ]))
