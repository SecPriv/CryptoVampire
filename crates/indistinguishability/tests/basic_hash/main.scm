(require-builtin steel/base)



(define pbl (empty_problem))

(define p1 (declare_protocol pbl))
(define p2 (declare_protocol pbl))

(define prf (declare-cryptography pbl))
(define hash (declare_function pbl (fun "hash" (signature (Bitstring Bitstring) -> Bitstring) (list prf))))
; (define hash (declare_function pbl (fun "hash" (signature (Bitstring Bitstring) -> Bitstring) '())))
(define ok (declare_function pbl (fun "ok" (signature () -> Bitstring) '())))
(define ko (declare_function pbl (fun "ko" (signature () -> Bitstring) '())))
(define k1 (declare_function pbl (mk-nonce "key1" (signature (Index) -> Nonce))))
(define k2 (declare_function pbl (mk-nonce "key2" (signature (Index Index) -> Nonce))))
(define n (declare_function pbl (mk-nonce "n" (signature (Index Index) -> Nonce))))

(define tag (declare_step pbl "tag" (list Index Index)))
(define rs (declare_step pbl "rs" (list Index Index)))
(define rf (declare_step pbl "rf" (list Index)))

(define mk (declare_function pbl (mk-alias "mkey"
  (signature (Index Index Protocol) -> Bitstring) 
  (list
    (alias-rule
      ((i 0 Index) (j 1 Index)) @
        i j p1 => (k1 i))
    (alias-rule
      ((i 0 Index) (j 1 Index)) @
        i j p2 => (k2 i j))))))

(initialize-as-prf prf hash)

(set-step-message pbl tag p1 
  (let ((i (mk-varf 0)) (j (mk-varf 1)))
  (formula (tpl (n i j) (hash (n i j) (mk i j p1))))
))

(set-step-message pbl tag p2 
  (let ((i (mk-varf 0)) (j (mk-varf 1)))
  (formula (tpl (n i j) (hash  (n i j) (mk i j p2))))
))

(define exists1 (declare_quantifier pbl (list Index Protocol) Index))
(let* 
  ([vars (exists-vars exists1)] 
    [j (mk-varf (exists-bound-var exists1))]
    [i (mk-varf (list-ref vars 0))] 
    [p (mk-varf (list-ref vars 1))]
    [in (formula (macro_input (rf i) p))])
    (set-exists-pattern exists1 (formula 
      (= (sel2of2 in) (hash (sel1of2 in) (mk i j p)))))
)


(define exists2 (declare_quantifier pbl (list Index Time Protocol) Index))
(let* 
  ([vars (exists-vars exists2)] 
    [i (mk-varf (exists-bound-var exists2))]
    [j (mk-varf (list-ref vars 0))] 
    [t (mk-varf (list-ref vars 1))] 
    [p (mk-varf (list-ref vars 2))]
    [int (formula (macro_input t p))]
    [intag (formula (macro_input (tag i j) p))])
    (set-exists-pattern exists2 (formula 
      (and
        (lt (tag i j) t) ; <- very important
        (= (sel1of2 int) (sel1of2 intag))
        (= (sel2of2 int) (sel2of2 intag))
      )
    ))
)
(define (cexists1 i p) (
  let ([e (get-exists-tlf exists1)] [sk (get-exists-skolem exists1)])
  (mk-appf e (list i p (mk-appf sk (list i p))))))
(define (cexists2 j t p) (
  let ([e (get-exists-tlf exists2)] [sk (get-exists-skolem exists2)])
  (mk-appf e (list j t p (mk-appf sk (list j t p))))))


(set-step-message pbl rs p2 (formula ok))
(set-step-message pbl rs p1 (formula ok))
(set-step-message pbl rf p2 (formula ko))
(set-step-message pbl rf p1 (formula ko))

(set-step-condition pbl rs p1
  (let* (
    [i (mk-varf 0)] [j (mk-varf 1)] 
    [in (formula (macro_input (rs i j) p1))])
  (formula (= (sel2of2 in) (hash (sel1of2 in) (mk i j p1))))))
(set-step-condition pbl rs p2
  (let* (
    [i (mk-varf 0)] [j (mk-varf 1)] 
    [in (formula (macro_input (rs i j) p2))])
  (formula (= (sel2of2 in) (hash (sel1of2 in) (mk i j p2))))))

(set-step-condition pbl rf p1
  (let* (
    [i (mk-varf 0)]  
    [in (formula (macro_input (rf i) p1))])
  (formula (bit_not (@ cexists1 i p1)))))
(set-step-condition pbl rf p2
  (let* (
    [i (mk-varf 0)]  
    [in (formula (macro_input (rf i) p2))])
  (formula (bit_not (@ cexists1 i p2)))))

(define n0 (declare_function pbl (mk-nonce "n0" (signature (Index Index Protocol) -> Nonce))))

; (add-rule pbl (let (
;   [i (mk-varf 0)]
;   [j (mk-varf 1)]
;   [h1 (mk-varf 2)]
;   [h2 (mk-varf 3)]
; ) 
;   (prolog "euf-cma"
;     (equiv h1 h2 (macro_frame (tag i j) p1) (macro_frame (tag i j) p2)) :-
;     (equiv h1 h2
;       (mtuple (mtuple (mfrom_bool (macro_exec (tag i j) p1)) 
;           (bitstring_if_then_else (macro_exec (tag i j) p1) 
;             (mtuple (n i j)  (n0 i j p1))
;             mempty)) (macro_frame (pred (tag i j)) p1))
;       (mtuple (mtuple (mfrom_bool (macro_exec (tag i j) p2)) 
;           (bitstring_if_then_else (macro_exec (tag i j) p2) 
;             (mtuple (n i j)  (n0 i j p2))
;             mempty)) (macro_frame (pred (tag i j)) p2))
;     )
; )))

(add-rewrite pbl (let* (
  [t (mk-varf 0)]
  [i (mk-varf 1)]
  [j (mk-varf 2)]
  [p (mk-varf 3)]
  [vars (list 0 1 2 3)]
  [sorts (list Time Index Index Protocol)]
  [in (formula (macro_input t p))]
)
  (mk-rewrite "lemma-2" vars sorts
    (formula (= (sel2of2 in) (hash (sel1of2 in) (mk i j p))))
    (formula (@ cexists2 j t p))
  )
))

(print_formula
  (formula (forall ((i 1  Index) (j 2 Index)) (hash (n i j) ko))))

(to-string-step pbl p1 tag)
(to-string-step pbl p2 tag)
(to-string-step pbl p1 rs)
(to-string-step pbl p2 rs)
(to-string-step pbl p1 rf)
(to-string-step pbl p2 rf)


(run pbl p1 p2)