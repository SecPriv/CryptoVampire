(require-builtin steel/base)
(define pbl (empty_problem))

(define p1 (declare_protocol pbl))
(define p2 (declare_protocol pbl))

(define hash (declare_function pbl (fun "hash" (signature (Bitstring Bitstring) -> Bitstring))))
(define ok (declare_function pbl (fun "ok" (signature () -> Bitstring))))
(define ko (declare_function pbl (fun "ko" (signature () -> Bitstring))))
(define tag1 (declare_function pbl (fun "tag1" (signature () -> Bitstring))))
(define tag2 (declare_function pbl (fun "tag2" (signature () -> Bitstring))))

(define k1 (declare_function pbl (mk-nonce "key1" (signature (Index) -> Nonce))))
(define k2 (declare_function pbl (mk-nonce "key2" (signature (Index Index) -> Nonce))))
(define nt (declare_function pbl (mk-nonce "nt" (signature (Index Index) -> Nonce))))
(define nr (declare_function pbl (mk-nonce "nr" (signature (Index) -> Nonce))))

(define tag (declare_step pbl "tag" (list Index Index)))
(define r (declare_step pbl "r" (list Index)))
(define rs (declare_step pbl "rs" (list Index Index Index)))
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


(define (m_condition_fst i j k p in) 
 (formula
  (= (sel2of2 in) (hash (tpl (tpl (nr j) (sel1of2 in)) tag1) (mk i k p)))
))

; ------------- quantifier -------------
(define exists11 (declare_quantifier pbl (list Index Index Protocol Time) Index))
(let* 
  ([vars (exists-vars exists1)] 
    [k (mk-varf (exists-bound-var exists1))]
    [i (mk-varf (list-ref vars 0))] 
    [j (mk-varf (list-ref vars 1))] 
    [p (mk-varf (list-ref vars 2))] 
    [t (mk-varf (list-ref vars 3))] 
    [in (formula (macro_input t p))])
    (set-exists-pattern exists11 (formula 
      @ m_condition_fst i j k p in)))
(define (cexists11 i j p t) (
  let ([e (get-exists-tlf exists1)] [sk (get-exists-skolem exists1)])
  (mk-appf e (list i j p t (mk-appf sk (list i j p t))))))

(define exists12 (declare_quantifier pbl (list Index Protocol Time) Index))
(let* 
  ([vars (exists-vars exists1)] 
    [i (mk-varf (exists-bound-var exists12))]
    [j (mk-varf (list-ref vars 0))] 
    [p (mk-varf (list-ref vars 1))] 
    [t (mk-varf (list-ref vars 2))] 
    [in (formula (macro_input t p))])
    (set-exists-pattern exists12 (formula @ cexists11 i j p t)))
(define (cexists12 j p t) (
  let ([e (get-exists-tlf exists1)] [sk (get-exists-skolem exists1)])
  (mk-appf e (list j p t (mk-appf sk (list j p t))))))


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
(define (cexists2 j t p) (
  let ([e (get-exists-tlf exists2)] [sk (get-exists-skolem exists2)])
  (mk-appf e (list j t p (mk-appf sk (list j t p))))))

; ----------------- steps -----------------

(set-step-message pbl r p1 (formula (nr 0)))
(set-step-message pbl r p2 (formula (nr 0)))

(set-step-message pbl tag p1 
  (let* ([i (mk-varf 0)] [ j (mk-varf 1) ] [in (macro_input (tag i j) p1)])
  (formula (tpl (nt i j) (hash (tpl in (nt i j) tag1) (mk i j p1))))))

(set-step-message pbl tag p2 
  (let* ([i (mk-varf 0)] [ j (mk-varf 1) ] [in (macro_input (tag i j) p2)])
  (formula (tpl (nt i j) (hash (tpl in (nt i j) tag1) (mk i j p2))))))

(set-step-condition pbl rs p1 (let
    ([i (mk-varf 0)] 
    [j (mk-varf 1)] 
    [k (mk-varf 2)])
  (formula
    @ m_condition_fst i j k p1 (macro_input (rs i j k) p1))))
(set-step-message pbl rs p1 (let*
    ([i (mk-varf 0)] 
    [j (mk-varf 1)] 
    [k (mk-varf 2)]
    [in (formula (macro_input (rs i j k) p1))])
  (formula
    (hash (tpl (tpl (nr j) (sel1of2 in)) tag2) (mk i k p1)))))

(set-step-condition pbl rs p2 (let
    ([i (mk-varf 0)] 
    [j (mk-varf 1)] 
    [k (mk-varf 2)])
  (formula
    @ m_condition_fst i j k p2 (macro_input (rs i j k) p2))))
(set-step-message pbl rs p2 (let*
    ([i (mk-varf 0)] 
    [j (mk-varf 1)] 
    [k (mk-varf 2)]
    [in (formula (macro_input (rs i j k) p2))])
  (formula
    (hash (tpl (tpl (nr j) (sel1of2 in)) tag2) (mk i k p2)))))
    
(set-step-condition pbl rs p1 (let
    ([j (mk-varf 0)] )
  (formula (bit_not (@ cexists12 j (rf j) p1)))))
(set-step-condition pbl rs p2 (let
    ([j (mk-varf 0)] )
  (formula (bit_not (@ cexists12 j (rf j) p2)))))

(set-step-message pbl rf p2 (formula ko))
(set-step-message pbl rf p1 (formula ko))

(run pbl p1 p2)