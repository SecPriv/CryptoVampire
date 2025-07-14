(require-builtin cryptovampire)

(define (is-nonce f) (equal? Nonce (get-sort f)))

(define (mk-appf2 f args) 
  (let ([x (mk-appf f args)]) 
    (if (is-nonce x) (mk-appf mnonce (list x)) x)))

(define (mk-if c l r)
  (if 
    (equal? Bool (get-sort c))
    (mk-appf2 bool_if_then_else (list c l r))
    (mk-appf2 bitstring_if_then_else (list c l r))))


(define-syntax formula
  (syntax-rules  (forall exists < > @ and or = tpl)
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
      [(_ (tpl a b )) (formula (mtuple a b))]
      [(_ (tpl a b ... )) (formula (mtuple a (tpl b ...)))]
      [(_ (and a b)) (formula (bit_and a b))]
      [(_ (and a b ...)) (formula (bit_and a (and b ...)))] 
      [(_ (or a b)) (formula (bit_or a b))]
      [(_ (or a b ...)) (formula (bit_or a (or b ...)))] 
      [(_ (= a b)) (formula (meq a b))]
      ; [(_ (if c l r)) (mk-if (formula c) (formula l) (formula r))]
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

(define-syntax prolog
  (syntax-rules (:-)
  [(_ name from) 
    (mk-prolog name (formula from) '())]
  [(_ name from :- to ...) 
    (mk-prolog name 
      (formula from) (list (formula to) ...  ))]
))