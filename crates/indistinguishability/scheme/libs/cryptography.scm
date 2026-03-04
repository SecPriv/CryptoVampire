(provide initialize-as register-fresh-nonce declare-cryptography
  initialize-as-prf
  initialize-as-ddh
  initialize-as-aenc
  initialize-as-senc
  initialize-as-xor)
(require-builtin cryptovampire/ll/cryptography as c->)
(require "cryptovampire/function")

(define (register-fresh-nonce crypto vars f)
  (c->register-fresh-nonce crypto vars (get-function f)))

(define declare-cryptography c->declare-cryptography)

(define (partial f . args)
  (lambda rest-args
    (apply f (append args rest-args))))

(define (initialize-as crypto kind . funs)
  (let [ (funs (map get-function funs)) ]
    (case kind
      [ (prf) (apply (partial c->init->prf crypto) funs) ]
      [ (ddh) (apply (partial c->init->ddh crypto) funs) ]
      [ (aenc) (apply (partial c->init->aenc crypto) funs) ]
      [ (senc) (apply (partial c->init->senc crypto) funs) ]
      [ (xor) (apply (partial c->init->xor crypto) funs) ])))

(define (initialize-as-prf crypto . funs) (apply initialize-as crypto 'prf funs))
(define (initialize-as-ddh crypto . funs) (apply initialize-as crypto 'ddh funs))
(define (initialize-as-aenc crypto . funs) (apply initialize-as crypto 'aenc funs))
(define (initialize-as-senc crypto . funs) (apply initialize-as crypto 'senc funs))
(define (initialize-as-xor crypto . funs) (apply initialize-as crypto 'xor funs))
