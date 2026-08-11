(provide partial)
(require "cryptovampire/doc")


(@doc
  (cv-help "partial" "(partial f . args)"
    "Returns a function that applies `f` to the given `args` followed by the arguments of the call."
    "*Example:*"
    "```scheme
    (define add1 (partial + 1))
    (add1 2) ;; => 3
    ```")
  (define (partial f . args)
    (lambda rest-args
      (apply f (append args rest-args)))))
