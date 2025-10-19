(require-builtin steel/base)



(define pbl (empty-problem))

(define _p1 (declare-protocol pbl))
(define p1 (lift-fun _p1))
(define _p2 (declare-protocol pbl))
(define p2 (lift-fun _p2))

(define prf (declare-cryptography pbl))
(define _hash (declare-function pbl (mk-fun "hash" (signature (Bitstring Bitstring) -> Bitstring) (list prf))))
(define hash (lift-fun _hash))
; (define hash (declare-function pbl (fun "hash" (signature (Bitstring Bitstring) -> Bitstring) '())))
(define _ok (declare-function pbl (mk-fun "ok" (mk-signature '() Bitstring) '())))
(define ok (lift-fun _ok))
(define _ko (declare-function pbl (mk-fun "ko" (signature () -> Bitstring) '())))
(define ko (lift-fun _ko))
(define _k1 (declare-function pbl (mk-nonce "key1" (signature (Index) -> Nonce))))
(define k1 (lift-fun _k1))
(define _k2 (declare-function pbl (mk-nonce "key2" (signature (Index Index) -> Nonce))))
(define k2 (lift-fun _k2))
(define _n (declare-function pbl (mk-nonce "n" (signature (Index Index) -> Nonce))))
(define n (lift-fun _n))

(define s_tag (declare-step pbl "tag" (list Index Index)))
(define s_rs (declare-step pbl "rs" (list Index Index)))
(define s_rf (declare-step pbl "rf" (list Index)))
(define tag (lift-fun s_tag))
(define rs (lift-fun s_rs))
(define rf (lift-fun s_rf))

(define _mk (declare-function pbl (mk-alias "mkey"
  (signature (Index Index Protocol) -> Nonce) 
  (bind ((i Index) (j Index) ) (list
    (mk-alias-rwf (list i j) (list (mk-varf i) (mk-varf j) p1) (k1 i))
    (mk-alias-rwf (list i j) (list (mk-varf i) (mk-varf j) p2) (k2 i j)))))))
(define mk (lift-fun _mk))

(initialize-as-prf prf _hash)

(set-message pbl s_tag _p1 (lambda (in i j) 
  (mtuple (mnonce (n i j)) (hash (mnonce (n i j)) (mnonce (mk i j p1))))))

(set-message pbl s_tag _p2 (lambda (in i j) 
  (mtuple (mnonce (n i j)) (hash (mnonce (n i j)) (mnonce (mk i j p2))))))

(set-message pbl s_rs _p2 (lambda (in i j) ok))
(set-message pbl s_rs _p1 (lambda (in i j) ok))
(set-message pbl s_rf _p2 (lambda (in i) ko))
(set-message pbl s_rf _p1 (lambda (in i) ko))


; (define exists1 (declare-exists pbl (list Index Protocol) (list Index)))
; (let* 
;   ([vars (exists-cvars exists1)] 
;     [j (mk-varf (list-ref (exists-bvars exists1) 0))]
;     [i (mk-varf (list-ref vars 0))] 
;     [p (mk-varf (list-ref vars 1))]
;     [in (formula (macro_input (rf i) p))])
;     (set-exists-pattern exists1 (formula 
;       (= (sel2of2 in) (hash (sel1of2 in) (mk i j p)))))
; )


; (define exists2 (declare-exists pbl (list Index Time Protocol) (list Index)))
; (let* 
;   ([vars (exists-cvars exists2)] 
;     [i (mk-varf (list-ref (exists-bvars exists2) 0))]
;     [j (mk-varf (list-ref vars 0))] 
;     [t (mk-varf (list-ref vars 1))] 
;     [p (mk-varf (list-ref vars 2))]
;     [int (formula (macro_input t p))]
;     [intag (formula (macro_input (tag i j) p))])
;     (set-exists-pattern exists2 (formula 
;       (and
;         (lt (tag i j) t) ; <- very important
;         (= (sel1of2 int) (sel1of2 intag))
;         (= (sel2of2 int) (sel2of2 intag))
;       )
;     ))
; )
; (define (cexists1 i p) (
;   let ([e (get-exists-tlf exists1)] [sk (list-ref (get-exists-skolems exists1) 0)])
;   (mk-appf e (list i p (mk-appf sk (list i p))))))
; (define (cexists2 j t p) (
;   let ([e (get-exists-tlf exists2)] [sk (list-ref (get-exists-skolems exists2) 0)])
;   (mk-appf e (list j t p (mk-appf sk (list j t p))))))


(set-condition pbl s_rs _p1
  (lambda (in i j)
   (eq (sel2of2 in) (hash (sel1of2 in) (mnonce (mk i j p1))))))
(set-condition pbl s_rs _p2
  (lambda (in i j)
   (eq (sel2of2 in) (hash (sel1of2 in) (mnonce (mk i j p2))))))

(set-condition pbl s_rf _p1
  (lambda (in i)
   (mnot (exists ((j Index)) (eq (sel2of2 in) (hash (sel1of2 in) (mnonce (mk i j p1))))))))
(set-condition pbl s_rf _p2
  (lambda (in i)
   (mnot (exists ((j Index)) (eq (sel2of2 in) (hash (sel1of2 in) (mnonce (mk i j p2))))))))

; (set-step-condition pbl rf p1
;   (let* (
;     [i (mk-varf 0)]  
;     [in (formula (macro_input (rf i) p1))])
;   (formula (bit_not (@ cexists1 i p1)))))
; (set-step-condition pbl rf p2
;   (let* (
;     [i (mk-varf 0)]  
;     [in (formula (macro_input (rf i) p2))])
;   (formula (bit_not (@ cexists1 i p2)))))

(define n0 (declare-function pbl (mk-nonce "n0" (signature (Index Index Protocol) -> Nonce))))

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

; (add-rewrite pbl (let* (
;   [t (mk-varf 0)]
;   [i (mk-varf 1)]
;   [j (mk-varf 2)]
;   [p (mk-varf 3)]
;   [vars (list 0 1 2 3)]
;   [sorts (list Time Index Index Protocol)]
;   [in (formula (macro_input t p))]
; )
;   (mk-rewrite "lemma-2" vars sorts
;     (formula (= (sel2of2 in) (hash (sel1of2 in) (mk i j p))))
;     (formula (@ cexists2 j t p))
;   )
; ))

(bind 
  ((i Index) (j Index) (t Time) (p Protocol))
  (let [(in (macro_input t p))] 
    (add-rewrite pbl (mk-rewrite "lemma-2" (list i j t p) 
      (eq (sel2of2 in) (hash (sel1of2 in) (mnonce (mk i j p)))) 
      (exists ((i Index))
        (mand
          (lt (tag i j) t) ; <- very important
          (mand (eq (sel1of2 in) (sel1of2 (macro_input (tag i j) p)))
            (eq (sel2of2 in) (sel2of2 (macro_input (tag i j) p))))
        )
      ))))
)

; (print_formula
;   (formula (forall ((i 1  Index) (j 2 Index)) (hash (n i j) ko))))

(displayln (to-string-step pbl _p1 s_tag))
(displayln (to-string-step pbl _p2 s_tag))
(displayln (to-string-step pbl _p1 s_rs))
(displayln (to-string-step pbl _p2 s_rs))
(displayln (to-string-step pbl _p1 s_rf))
(displayln (to-string-step pbl _p2 s_rf))


(run pbl _p1 _p2)