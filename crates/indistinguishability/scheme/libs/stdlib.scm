(provide partial)

(define (partial f . args)
  (lambda rest-args
    (apply f (append args rest-args))))