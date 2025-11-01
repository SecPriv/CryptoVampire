(require-builtin cryptovampire as cv-)
(require "cryptovampire/v2")


(define pbl (mk-problem 'x))

(define-function ok pbl Nonce)

(cv-print_formula ok)