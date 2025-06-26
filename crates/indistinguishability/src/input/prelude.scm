(require-builtin cryptovampire)

(define (is-nonce f) (equal? Nonce (get-sort f)))

(define (mk-appf2 f args) 
  (let ([x (mk-appf f args)]) 
    (if (is-nonce x) (mk-appf mnonce (list x)) x)))



(define-syntax formula
  (syntax-rules  (forall exists < > @ and or =)
      [(_ (@ f)) f]
      [(_ (@ f args ...)) (f (formula args) ...)]
      [(_ (forall [(id values sorts) ...] c))
        (let ([id (mk-varf values)] ...)
          (mk-binderf forallf 
            (list values ...) 
            (list sorts ...) 
            (formula c)))]
      [(_ (exists [(id values sorts) ...] c))
        (let ([id (mk-varf values)] ...)
          (mk-binderf existsf 
            (list values ...) 
            (list sorts ...) 
            (formula c)))]
      [(_ < a b >) (formula (mtuple a b))]
      [(_ < a b ... >) (formula (mtuple a < b ...>))]
      [(_ (and a b)) (formula (bit_and a b))]
      [(_ (and a b ...)) (formula (bit_and a (and b ...)))] 
      [(_ (or a b)) (formula (bit_or a b))]
      [(_ (or a b ...)) (formula (bit_or a (or b ...)))] 
      [(_ (= a b)) (formula (meq a b))]
      [(_ (f args ...))
        (mk-appf2 f (list (formula args) ...))]
      [(_ f) 
        (if (Formula? f) 
          f 
          (if (number? f) 
            (mk-varf f) 
            (mk-appf2 f '())))]      
))

(define-syntax alias-rule
  (syntax-rules (@ =>)
    [(_ ((id values sorts) ...) @ params ... => c)
      (let ([id (mk-varf values)] ...)
        (mk-alias-rwf 
          (list values ...)
          (list sorts ...)
          (list (formula params) ...)
          (formula c)))
    ]))

(define-syntax signature
  (syntax-rules (->)
  [(_ () -> sort) (mk-signature '() sort)]
  [(_ (sorts ...) -> sort) (mk-signature (list sorts ...) sort)]
  [(_ sort) (mk-signature '() sort)]
  ))