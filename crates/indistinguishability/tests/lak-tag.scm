(require "cryptovampire/v2")
(require-builtin cryptovampire as cv-)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define prf (declare-cryptography pbl))

(define-function mhash pbl (prf) (Bitstring Bitstring) -> Bitstring)
(define-function ok pbl Bitstring)
(define-function ko pbl Bitstring)
(define-function k1 pbl (Index) -> Nonce)
(define-function k2 pbl (Index Index) -> Nonce)
(define-function _nt pbl (Index Index) -> Nonce)
(define-function _nr pbl (Index) -> Nonce)
(define-function tag1 pbl Bitstring)
(define-function tag2 pbl Bitstring)

(define-alias _mk pbl (Index Index Protocol) Nonce
  [ ([ (i Index) (j Index) ] (i j p1) -> (k1 i))
  ([ (i Index) (j Index) ] (i j p2) -> (k2 i j)) ])

(define mk (wrap-nonce _mk))
(define nt (wrap-nonce _nt))
(define nr (wrap-nonce _nr))

; (define tag (declare-step pbl "tag" (list Index Index)))
; (define r (declare-step pbl "r" (list Index)))
; (define r2 (declare-step pbl "r2" (list Index)))

(define empty-cond (lambda _ mtrue))

(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1 empty-cond
      (lambda (in i j)
        (tuple (nt i j)
          (mhash
            (tuple (tuple in (nt i j)) tag1)
            (mk i j p1)))))
    (step p2 empty-cond
      (lambda (in i j)
        (tuple (nt i j)
          (mhash
            (tuple (tuple in (nt i j)) tag1)
            (mk i j p1)))))))


(define r
  (declare-step pbl "r" (list Index)
    (step p1 empty-cond (lambda (_ i) (nr i)))
    (step p2 empty-cond (lambda (_ i) (nr i)))))

(define (mk-fdst1 in j p)
  (findst ((i Index) (k Index))
    (eq
      (sel2of2 in)
      (mhash
        (tuple (tuple (nr j) (sel1of2 in)) tag1)
        (mk i k p)))
    (mhash
      (tuple (tuple (nr j) (sel1of2 in)) tag2)
      (mk i k p))
    ko))

(define r2
  (declare-step pbl "r2" (list Index)
    (step p1 empty-cond
      (lambda (in j) (mk-fdst1 in j p1)))
    (step p2 empty-cond
      (lambda (in j) (mk-fdst1 in j p2)))))

(initialize-as-prf prf mhash)

; (define (m_condition_fst i j k p in)
;   (formula
;     (= (sel2of2 in) (mhash (tpl (tpl (nr j) (sel1of2 in)) tag1) (mk i k p)))))

; ; ------------- quantifier -------------

(define (mk-fdst2 t j p)
  (let [ (in (macro_input t p)) ]
    (findst ((i Index) (k Index))
      (cand
        (eq (sel1of2 in) (sel1of2 (macro_input (tag i j) p)))
        (eq (sel2of2 in) (sel2of2 (macro_input (tag i j) p)))
        (lt (tag i j) t)) ; <- very important
      (mhash (tuple (tuple (nr j) (sel1of2 in)) tag2) (mk i k p1))
      ko)))

; (define fdst2 (declare-find-such-that pbl (list Index Protocol Time) (list Index Index)))
; (let*
;   ([vars (find-such-that-cvars fdst2) ]
;     [i (mk-varf (list-ref (find-such-that-bvars fdst2) 0)) ]
;     [j (mk-varf (list-ref vars 0)) ]
;     [k (mk-varf (list-ref (find-such-that-bvars fdst2) 1)) ]
;     [p (mk-varf (list-ref vars 1)) ]
;     [t (mk-varf (list-ref vars 2)) ]
;     [in (formula (macro_input t p)) ]
;     [intag (formula (macro_input (tag i j) p)) ])
;   (begin
;     (set-find-such-that-condition fdst2 (formula
;         (and
;           (lt (tag i j) t) ; <- very important
;           (= (sel1of2 in) (sel1of2 intag))
;           (= (sel2of2 in) (sel2of2 intag)))))
;     (set-find-such-that-then-branch fdst2 (formula
;         (mhash (tpl (tpl (nr j) (sel1of2 in)) tag2) (mk i k p1))))
;     (set-find-such-that-else-branch fdst2 (formula ko))))
; (define (cfdst2 j p t) (let* ([e (get-find-such-that-tlf fdst2) ] [skk (get-find-such-that-skolems fdst2) ]
;       [sk_i (list-ref skk 0) ] [sk_k (list-ref skk 1) ])
;     (mk-appf e (list j p t (mk-appf sk_i (list j p t)) (mk-appf sk_k (list j p t))))))


; ; ----------------- steps -----------------

; (set-step-message pbl r p1 (formula (nr 0)))
; (set-step-message pbl r p2 (formula (nr 0)))

; (set-step-message pbl tag p1
;   (let* ([i (mk-varf 0) ] [ j (mk-varf 1) ] [in (formula (macro_input (tag i j) p1)) ])
;     (formula (tpl (nt i j) (mhash (tpl in (nt i j) tag1) (mk i j p1))))))

; (set-step-message pbl tag p2
;   (let* ([i (mk-varf 0) ] [ j (mk-varf 1) ] [in (formula (macro_input (tag i j) p2)) ])
;     (formula (tpl (nt i j) (mhash (tpl in (nt i j) tag1) (mk i j p2))))))

; (set-step-message pbl r2 p1
;   (let* ([j (mk-varf 0) ] [in (formula (macro_input (r2 j) p1)) ])
;     (formula (@ cfdst1 j p1 (r2 j)))))

; (set-step-message pbl r2 p2
;   (let* ([j (mk-varf 0) ] [in (formula (macro_input (r2 j) p2)) ])
;     (formula (@ cfdst1 j p2 (r2 j)))))


; (add-rewrite pbl (let* ([t (mk-varf 0) ]
;       [j (mk-varf 1) ]
;       [p (mk-varf 2) ]
;       [vars (list 0 1 2) ]
;       [sorts (list Time Index Protocol) ])
;     (mk-rewrite "lemma" vars sorts
;       (cfdst1 j p t)
;       (cfdst2 j p t))))

(bind ((j Index) (t Time) (p Protocol))
  (cv-add-rewrite pbl (cv-mk-rewrite "lemma" (list t j p)
      (mk-fdst1 (macro_input t p) j p)
      (mk-fdst2 t j p))))


(cv-add-smt-axiom pbl (mnot (eq tag1 tag2)))
(cv-add-smt-axiom pbl (forall [ (j Index) ] (lt (r j) (r2 j))))

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed"))

