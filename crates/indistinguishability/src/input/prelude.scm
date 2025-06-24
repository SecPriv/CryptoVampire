
(define-syntax formula
  (syntax-rules  (forall exists < >)
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
      [(_ < a b ... >) (formula (mtuple a (mtuple b ...)))]
      [(_ (f args ...))
        (mk-appf f (list (formula args) ...))]
      [(_ f)  (if (Formula? f) f (mk-appf f '()))]      
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