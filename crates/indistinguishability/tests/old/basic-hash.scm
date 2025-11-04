(require-builtin steel/base)



(define pbl (empty-problem default-config))

(define _p1 (declare-protocol pbl))
(define p1 (lift-fun _p1))
(define _p2 (declare-protocol pbl))
(define p2 (lift-fun _p2))

(define prf (declare-cryptography pbl))
(define _hash (declare-function pbl (mk-fun "hash" (signature (Bitstring Bitstring) -> Bitstring) (list prf))))
(define hash (lift-fun _hash))
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

(bind 
  ((i Index) (j Index) 
    (t Time) 
    (p Protocol))
  (let [(in (macro_input t p))] 
    (add-rewrite pbl (mk-rewrite "lemma-2" (list i t j p) 
      (eq (sel2of2 in) (hash (sel1of2 in) (mnonce (mk i j p)))) 
      (exists ((i Index))
        (mand
          (lt (tag i j) t) ; <- very important
          (mand (eq (sel1of2 in) (sel1of2 (macro_input (tag i j) p)))
            (eq (sel2of2 in) (sel2of2 (macro_input (tag i j) p))))
        )
      ))))
)

(if (run pbl _p1 _p2)
  (displayln "success")
  (error "failed"))