(require-builtin steel/base)
(require-builtin cryptovampire)
(define-syntax formula
  (syntax-rules ()
    ;; Binder: (forall ((x!0 Sort) ...) body) => custom transformation
    ((_ (forall ((var!id sort) ...) body))
     (let ((var id) ...)
       (mk-binderf forallf
         `((var ,sort) ...)
         (formula body))))

    ((_ (exists ((var!id sort) ...) body))
     (let ((var id) ...)
       (mk-binderf existsf
         `((var ,sort) ...)
         (formula body))))

    ;; Function application: (f x y) => (mk-appf f `(arg ...))
    ((_ (f arg ...))
     (mk-appf 'f `(arg ...)))

    ;; Variables written as !x → turn into (mk-varf x)
    ((_ !x) (mk-varf 'x))

    ;; Constants or nullary functions: (foo) → (mk-appf 'foo '())
    ((_ f) (mk-appf f '()))))



(define pbl (empty_problem))

(define p1 (declare_protocol pbl))
(define p2 (declare_protocol pbl))

(define hash (declare_function pbl (fun "hash" (signature `(,Bitstring ,Bitstring) Bitstring))))
(define ok (declare_function pbl (fun "ok" (signature '() Bitstring))))
(define ko (declare_function pbl (fun "ko" (signature '() Bitstring))))
(define k1 (declare_function pbl (fun "key1" (signature `(,Index) Nonce))))
(define k2 (declare_function pbl (fun "key2" (signature `(,Index ,Index) Nonce))))
(define mk (declare_function pbl
  (alias "mkey" (signature `(,Index ,Index ,Procotol) Nonce)
    `(
      ,(alias-rw 
        `((0 ,Index) (1 ,Index))
        `(,(mk-varf 0) ,(mk-varf 1) ,(mk-appf p1 '()))
          (mk-appf k1 `(,(mk-varf 0))))
      ,(alias-rw 
        `((0 ,Index) (1 ,Index))
        `(,(mk-varf 0) ,(mk-varf 1) ,(mk-appf p2 '()))
          (mk-appf k2 `(,(mk-varf 0) ,(mk-varf 1))))))))

(define tag (declare_step pbl "tag" `(,Index ,Index)))

; (set-step-message tag p1 (mk-appf tuple (mk-appf (nonce (mk)))))


(run pbl p1 p2)