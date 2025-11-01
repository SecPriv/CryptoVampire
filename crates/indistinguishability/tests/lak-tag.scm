(require-builtin steel/base)
(define pbl (empty-problem default-config))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define prf (declare-cryptography pbl))

(define hash (declare-function pbl 
  (fun "hash" (signature (Bitstring Bitstring) -> Bitstring) (list prf))))
(define ok (declare-function pbl 
  (fun "ok" (signature () -> Bitstring) '())))
(define ko (declare-function pbl 
  (fun "ko" (signature () -> Bitstring) '())))
(define tag1 (declare-function pbl 
  (fun "tag1" (signature () -> Bitstring) '())))
(define tag2 (declare-function pbl 
  (fun "tag2" (signature () -> Bitstring) '())))

(define k1 (declare-function pbl (mk-nonce "key1" (signature (Index) -> Nonce))))
(define k2 (declare-function pbl (mk-nonce "key2" (signature (Index Index) -> Nonce))))
(define nt (declare-function pbl (mk-nonce "nt" (signature (Index Index) -> Nonce))))
(define nr (declare-function pbl (mk-nonce "nr" (signature (Index) -> Nonce))))

(define tag (declare-step pbl "tag" (list Index Index)))
(define r (declare-step pbl "r" (list Index)))
(define r2 (declare-step pbl "r2" (list Index)))
(initialize-as-prf prf hash)

(define mk (declare-function pbl (mk-alias "mkey"
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
(define fdst1 (declare-find-such-that pbl (list Index Protocol Time) (list Index Index)))
(let* 
  ([vars (find-such-that-cvars fdst1)] 
    [i (mk-varf (list-ref (find-such-that-bvars fdst1) 0))] 
    [j (mk-varf (list-ref vars 0))] 
    [k (mk-varf (list-ref (find-such-that-bvars fdst1) 1))]
    [p (mk-varf (list-ref vars 1))] 
    [t (mk-varf (list-ref vars 2))] 
    [in (formula (macro_input t p))])
    (begin
      (set-find-such-that-condition fdst1 (formula 
        (= (sel2of2 in) (hash (tpl (tpl (nr j) (sel1of2 in)) tag1) (mk i k p)))))
      (set-find-such-that-then-branch fdst1 (formula
        (hash (tpl (tpl (nr j) (sel1of2 in)) tag2) (mk i k p1))))
      (set-find-such-that-else-branch fdst1 (formula ko))
    ))
(define (cfdst1 j p t) (
  let* ([e (get-find-such-that-tlf fdst1)] [skk (get-find-such-that-skolems fdst1)] 
        [sk_i (list-ref skk 0)] [sk_k (list-ref skk 1)])
  (mk-appf e (list j p t (mk-appf sk_i (list j p t)) (mk-appf sk_k (list j p t))))))

(define fdst2 (declare-find-such-that pbl (list Index Protocol Time) (list Index Index)))
(let* 
  ([vars (find-such-that-cvars fdst2)] 
    [i (mk-varf (list-ref (find-such-that-bvars fdst2) 0))] 
    [j (mk-varf (list-ref vars 0))] 
    [k (mk-varf (list-ref (find-such-that-bvars fdst2) 1))]
    [p (mk-varf (list-ref vars 1))] 
    [t (mk-varf (list-ref vars 2))] 
    [in (formula (macro_input t p))]
    [intag (formula (macro_input (tag i j) p))])
    (begin
      (set-find-such-that-condition fdst2 (formula 
        (and
          (lt (tag i j) t) ; <- very important
          (= (sel1of2 in) (sel1of2 intag))
          (= (sel2of2 in) (sel2of2 intag))
        )))
      (set-find-such-that-then-branch fdst2 (formula
        (hash (tpl (tpl (nr j) (sel1of2 in)) tag2) (mk i k p1))))
      (set-find-such-that-else-branch fdst2 (formula ko))
    ))
(define (cfdst2 j p t) (
  let* ([e (get-find-such-that-tlf fdst2)] [skk (get-find-such-that-skolems fdst2)] 
        [sk_i (list-ref skk 0)] [sk_k (list-ref skk 1)])
  (mk-appf e (list j p t (mk-appf sk_i (list j p t)) (mk-appf sk_k (list j p t))))))


; ----------------- steps -----------------

(set-step-message pbl r p1 (formula (nr 0)))
(set-step-message pbl r p2 (formula (nr 0)))

(set-step-message pbl tag p1 
  (let* ([i (mk-varf 0)] [ j (mk-varf 1) ] [in (formula (macro_input (tag i j) p1))])
  (formula (tpl (nt i j) (hash (tpl in (nt i j) tag1) (mk i j p1))))))

(set-step-message pbl tag p2 
  (let* ([i (mk-varf 0)] [ j (mk-varf 1) ] [in (formula (macro_input (tag i j) p2))])
  (formula (tpl (nt i j) (hash (tpl in (nt i j) tag1) (mk i j p2))))))

(set-step-message pbl r2 p1 
  (let* ([j (mk-varf 0)] [in (formula (macro_input (r2 j) p1))])
  (formula (@ cfdst1 j p1 (r2 j)))))

(set-step-message pbl r2 p2 
  (let* ([j (mk-varf 0)] [in (formula (macro_input (r2 j) p2))])
  (formula (@ cfdst1 j p2 (r2 j)))))


(add-rewrite pbl (let* (
  [t (mk-varf 0)]
  [j (mk-varf 1)]
  [p (mk-varf 2)]
  [vars (list 0 1 2)]
  [sorts (list Time Index Protocol)]
)
  (mk-rewrite "lemma" vars sorts
    (cfdst1 j p t)
    (cfdst2 j p t)
  )
))

(add-smt-axiom pbl (formula (bit_not (= tag1 tag2))))
(add-smt-axiom pbl (formula (forall [(j 0 Index)] (lt (r j) (r2 j)))))

(run pbl p1 p2)
