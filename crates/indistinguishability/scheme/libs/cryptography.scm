(provide initialize-as register-fresh-nonce declare-cryptography
  initialize-as-prf
  initialize-as-ddh
  initialize-as-aenc
  initialize-as-senc
  initialize-as-xor)
(require-builtin cryptovampire/ll/cryptography as c->)
(require "cryptovampire/function")
(require "cryptovampire/doc")

(@doc (cv-help "register-fresh-nonce" " (register-fresh-nonce crypto vars f) "
    "Registers the term `f` (over the variables `vars`) as a user-provided fresh nonce for `crypto`."
    "Useful so rules such as PRF, ENC-KP or DDH unify to this nonce instead of spawning a fresh one.")
  (define (register-fresh-nonce crypto vars f)
    (c->register-fresh-nonce crypto vars f)))

(@doc (cv-help "declare-cryptography" " (declare-cryptography pbl) "
    "Declares a fresh cryptographic module in `pbl` ; returns the crypto value to pass to `initialize-as-*`."
    "Use one per cryptographic family used in the problem."
    "*Example:*"
    "```scheme
    (define prf (declare-cryptography pbl))
    ```")
  (define (declare-cryptography pbl)
    (c->declare-cryptography pbl)))

(@doc (cv-help "initialize-as" " (initialize-as crypto kind . funs) "
    "Initializes `crypto` as an instance of `kind`, with `funs` as its building functions."
    "`kind` is one of `prf`, `ddh`, `aenc`, `senc` or `xor`. Prefer the dedicated `initialize-as-prf` & co. wrappers.")
  (define (initialize-as crypto kind . funs)
    (let [ (funs (map get-function funs)) ]
      (case kind
        [ (prf) (apply (partial c->init->prf crypto) funs) ]
        [ (ddh) (apply (partial c->init->ddh crypto) funs) ]
        [ (aenc) (apply (partial c->init->aenc crypto) funs) ]
        [ (senc) (apply (partial c->init->senc crypto) funs) ]
        [ (xor) (apply (partial c->init->xor crypto) funs) ]))))

;; ---------------------------------------------------------------------------
;; initialize-as-prf / initialize-as-ddh / initialize-as-aenc / initialize-as-senc / initialize-as-xor
;;
;; Enable the corresponding axioms and rules on the crypto module.  Each takes
;; the crypto value and the functions that implement the primitive, e.g.
;; ```scheme
;; (initialize-as-prf prf mhash)
;; (initialize-as-ddh g crypto (list ...))
;; ```
;; ---------------------------------------------------------------------------

(@doc (cv-help "initialize-as-prf" " (initialize-as-prf crypto . funs) "
    "Enables *pseudo-random-function* axioms and rules on `crypto` for the given `funs`.")
  (define (initialize-as-prf crypto . funs) (apply initialize-as crypto 'prf funs)))

(@doc (cv-help "initialize-as-ddh" " (initialize-as-ddh crypto . funs) "
    "Enables *decisional Diffie-Hellman* axioms and rules on `crypto` for the given `funs`.")
  (define (initialize-as-ddh crypto . funs) (apply initialize-as crypto 'ddh funs)))

(@doc (cv-help "initialize-as-aenc" " (initialize-as-aenc crypto . funs) "
    "Enables *asymmetric encryption* axioms and rules (IND-CCA and ENC-KP) on `crypto` for the given `funs`.")
  (define (initialize-as-aenc crypto . funs) (apply initialize-as crypto 'aenc funs)))

(@doc (cv-help "initialize-as-senc" " (initialize-as-senc crypto . funs) "
    "Enables *symmetric encryption* axioms and rules (IND-CCA) on `crypto` for the given `funs`.")
  (define (initialize-as-senc crypto . funs) (apply initialize-as crypto 'senc funs)))

(@doc (cv-help "initialize-as-xor" " (initialize-as-xor crypto . funs) "
    "Enables *xor* axioms and rules on `crypto` for the given `funs`.")
  (define (initialize-as-xor crypto . funs) (apply initialize-as crypto 'xor funs)))
