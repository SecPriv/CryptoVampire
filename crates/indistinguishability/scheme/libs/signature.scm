(provide signature)
(require-builtin cryptovampire/ll/signature as sig->)

(define-syntax signature
  (syntax-rules (->)
    [ (_ () -> sort) (sig->new '() sort) ]
    [ (_ (sorts ...) -> sort) (sig->new (list sorts ...) sort) ]
    [ (_ sort) (sig->new  '() sort) ]))