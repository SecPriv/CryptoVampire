(require-builtin steel/base)
(require-builtin cryptovampire)
; (define-syntax formula
;   (syntax-rules ()
;     ;; Binder: (forall ((x!0 Sort) ...) body) => custom transformation
;     ((_ (forall ((var id sort) ...) body))
;      (let ((var (mk-varf id)) ...)
;        (mk-binderf forallf
;          (list (list var sort) ...)
;          (formula body))))

;     ((_ (exists ((var id sort) ...) body))
;      (let ((var (mk-varf id)) ...)
;        (mk-binderf existsf
;          (list (list var sort) ...)
;          (formula body))))


;     ;; Constants or nullary functions: (foo) → (mk-appf 'foo '())
;     ((_ f) (if (Function? f) (mk-appf f '()) f))

;     ;; Function application: (f x y) => (mk-appf f `(arg ...))
;     ((_ (f arg ...))
;      (mk-appf f (list (formula arg) ...)))))


; (define-syntax malias-rw
;   (syntax-rules ()
;     ((_ ((vars id sort) ...) (args ...) content)
;       (let
;         ((vars (mk-varf id)) ...)
;         (alias-rw 
;           (list (list id sort) ...)
;           (list (formula args))
;           (formula content))))))



(define pbl (empty_problem))

(define p1 (declare_protocol pbl))
(define p2 (declare_protocol pbl))

(define hash (declare_function pbl (fun "hash" (signature (Bitstring Bitstring) -> Bitstring))))
(define ok (declare_function pbl (fun "ok" (signature () -> Bitstring))))
(define ko (declare_function pbl (fun "ko" (signature () -> Bitstring))))
(define k1 (declare_function pbl (fun "key1" (signature (Index) -> Nonce))))
(define k2 (declare_function pbl (fun "key2" (signature (Index Index) -> Nonce))))
(define n (declare_function pbl (fun "n" (signature (Index Index) -> Nonce))))

(define tag (declare_step pbl "tag" (list Index Index)))
(Function? tag)


(define mk (declare_function pbl (mk-alias "mkey"
  (signature (Index Index Protocol) -> Nonce) 
  (list
    (alias-rule
      ((i 0 Index) (j 1 Index)) @
        i j p1 => (k1 i))
    (alias-rule
      ((i 0 Index) (j 1 Index)) @
        i j p2 => (k2 i j))))))


(set-step-message pbl tag p1 
  (let ((i (mk-varf 0)) (j (mk-varf 1)))
  (formula <(mnonce (n i j)) (hash (mnonce (n i j)) (mnonce (mk i j p1)))>)
))

(set-step-message pbl tag p2 
  (let ((i (mk-varf 0)) (j (mk-varf 1)))
  (formula <(mnonce (n i j)) (hash (mnonce (n i j)) (mnonce (mk i j p2)))>)
))


(print_formula 
    (mk-appf 
      hash 
        (list 
          (mk-appf ko '()) 
          (mk-appf ko '())
        )
    )
)

(print_formula 
    (formula (hash ko ko))
)

(print_formula
  (formula (forall ((a 1  Bitstring)) (hash a ko)))
)
; (set-step-message tag p1 (mk-appf tuple (mk-appf (nonce (mk)))))


; (run pbl p1 p2)