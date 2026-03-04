(provide
  Function? Formula? Sort? Signature? Variable?)


(require-builtin cryptovampire/ll/variable as var->)
(require-builtin cryptovampire/ll/formula as f->)
(require-builtin cryptovampire/ll/function as fun->)
(require-builtin cryptovampire/ll/sort as sort->)
(require-builtin cryptovampire/ll/signature as sig->)

(define Variable? var->Variable?)
(define Function? fun->Function?)
(define Formula? f->Formula?)
(define Sort? sort->Sort?)
(define Signature? sig->Signature?)