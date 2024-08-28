(declare-sort Message 0)

(declare-sort index 0)

(declare-sort session 0)

(define-sort Condition () Bool)

(define-sort Bitstring () Message)

(declare-datatypes
  ((Step 0) (Name 0))
  (
    (
      (Pchall3bis (_1$dest_Pchall3bis_0 index))
      (init)
      (S2 (_2$dest_S2_0 index))
      (S1 (_3$dest_S1_0 index))
      (Pchall1 (_4$dest_Pchall1_0 index))
      (Pchall2 (_5$dest_Pchall2_0 index))
      (Pchall3 (_7$dest_Pchall3_0 index) (_8$dest_Pchall3_1 index)))
    (
      (b (_0$dest_b_0 index))
      (skS)
      (skP)
      (a (_6$dest_a_0 index))
      (k (_9$dest_k_0 index) (_10$dest_k_1 index)))))

(declare-fun pred (Step) Step)

(declare-fun Bool$_13$subterm_nonce (Name Bool) Bool)

(declare-fun Condition$_13$subterm_nonce (Name Condition) Bool)

(declare-fun Message$_13$subterm_nonce (Name Message) Bool)

(declare-fun Bitstring$_13$subterm_nonce (Name Bitstring) Bool)

(declare-fun index$_13$subterm_nonce (Name index) Bool)

(declare-fun session$_13$subterm_nonce (Name session) Bool)

(declare-fun Step$_13$subterm_nonce (Name Step) Bool)

(declare-fun Name$_13$subterm_nonce (Name Name) Bool)

(declare-fun ta$and (Condition Condition) Condition)

(declare-fun ta$or (Condition Condition) Condition)

(declare-fun ta$not (Condition) Condition)

(declare-fun ta$implies (Condition Condition) Condition)

(declare-fun ta$iff (Condition Condition) Condition)

(declare-fun ta$true () Condition)

(declare-fun ta$false () Condition)

(declare-fun ta$= (Message Message) Condition)

(declare-fun ta$exists$0 (index) Condition)

(declare-fun checksign (Message Message Message) Condition)

(declare-fun empty () Message)

(declare-fun g () Message)

(declare-fun ko () Message)

(declare-fun mexp (Message Message) Message)

(declare-fun mfst (Message) Message)

(declare-fun msnd (Message) Message)

(declare-fun ok () Message)

(declare-fun pk (Message) Message)

(declare-fun sign (Message Message) Message)

(declare-fun tpl (Message Message) Message)

(declare-fun cast$Message$name (Name) Message)

(declare-fun input (Step) Message)

(declare-fun ta$ite (Condition Message Message) Message)

(declare-fun evaluate_cond (Condition) Bool)

(declare-fun evaluate_msg (Message) Bitstring)

(declare-fun happens (Step) Bool)

(declare-fun lt (Step Step) Bool)


; ordering


; 1
(assert (forall ((SX0 Step)) (or (lt init SX0) (= init SX0))))

; 2
(assert (forall ((SX0 Step)) (=> (lt SX0 SX0) (= SX0 init))))

; 3
(assert
  (forall
    ((SX1 Step) (SX2 Step) (SX3 Step))
    (=> (and (lt SX1 SX2) (lt SX2 SX3)) (lt SX1 SX3))))

; 4
(assert
  (forall
    ((SX1 Step) (SX2 Step))
    (=> (and (happens SX2) (lt SX1 SX2)) (happens SX1))))

; 5
(assert
  (forall
    ((SX1 Step) (SX2 Step))
    (or
      (lt SX1 SX2)
      (lt SX2 SX1)
      (= SX1 SX2)
      (not (happens SX1))
      (not (happens SX2)))))

; 6
(assert (happens init))

; 7
(assert (forall ((SX0 Step)) (or (lt (pred SX0) SX0) (= SX0 init))))

; 8
(assert (forall ((iX0 index)) (lt (Pchall1 iX0) (Pchall2 iX0))))

; 9
(assert
  (forall ((iX0 index) (iX1 index)) (lt (Pchall2 iX0) (Pchall3 iX0 iX1))))

; 10
(assert (forall ((iX0 index)) (lt (Pchall2 iX0) (Pchall3bis iX0))))

; 11
(assert
  (forall
    ((iX0 index) (iX1 index) (iX2 index))
    (=>
      (and (happens (Pchall3 iX0 iX1)) (happens (Pchall3 iX0 iX2)))
      (= (Pchall3 iX0 iX1) (Pchall3 iX0 iX2)))))

; 12
(assert
  (forall
    ((iX0 index) (iX1 index))
    (=>
      (and (happens (Pchall3 iX0 iX1)) (happens (Pchall3bis iX0)))
      (= (Pchall3 iX0 iX1) (Pchall3bis iX0)))))

; 13
(assert (forall ((iX0 index)) (lt (S1 iX0) (S2 iX0))))


; evaluate


; 14
(assert (forall ((CX1 Condition)) (= CX1 CX1)))

; 15
(assert (forall ((MX1 Message)) (= MX1 MX1)))

; 16
(assert (= ta$false false))

; 17
(assert (= ta$true true))

; 18
(assert
  (forall
    ((CX0 Condition) (CX1 Condition))
    (= (ta$implies CX0 CX1) (=> CX0 CX1))))

; 19
(assert (forall ((CX0 Condition)) (=> (ta$not CX0) (not CX0))))

; 20
(assert
  (forall ((CX0 Condition) (CX1 Condition)) (= (ta$and CX0 CX1) (and CX0 CX1))))

; 21
(assert
  (forall ((CX0 Condition) (CX1 Condition)) (= (ta$iff CX0 CX1) (= CX0 CX1))))

; 22
(assert (forall ((MX0 Message) (MX1 Message)) (= (ta$= MX0 MX1) (= MX0 MX1))))

; 23
(assert
  (forall
    ((CX0 Condition) (MX1 Message) (MX2 Message))
    (= (ta$ite CX0 MX1 MX2) (ite CX0 MX1 MX2))))

; 24
(assert
  (forall
    ((iX0 index))
    (=>
      (ta$exists$0 iX0)
      (exists
        ((iX2 index))
        (ta$= (msnd (mfst (input (Pchall2 iX0)))) (mexp g (cast$Message$name (b iX2))))))))

; 25
(assert
  (forall ((CX0 Condition) (CX1 Condition)) (= (ta$or CX0 CX1) (or CX0 CX1))))


; crypto


; 26
(assert
  (forall
    ((NX1 Name) (NX0 Name))
    (=>
      (Message$_13$subterm_nonce NX0 (cast$Message$name NX1))
      (or (Name$_13$subterm_nonce NX0 NX1)))))

; 27
(assert
  (forall ((NX0 Name)) (=> (Condition$_13$subterm_nonce NX0 ta$false) false)))

; 28
(assert
  (forall ((NX0 Name)) (=> (Condition$_13$subterm_nonce NX0 ta$true) false)))

; 29
(assert
  (forall
    ((CX1 Condition) (CX2 Condition) (NX0 Name))
    (=>
      (Condition$_13$subterm_nonce NX0 (ta$implies CX1 CX2))
      (or
        (Condition$_13$subterm_nonce NX0 CX1)
        (Condition$_13$subterm_nonce NX0 CX2)))))

; 30
(assert
  (forall
    ((MX1 Message) (MX2 Message) (NX0 Name))
    (=>
      (Message$_13$subterm_nonce NX0 (tpl MX1 MX2))
      (or (Message$_13$subterm_nonce NX0 MX1) (Message$_13$subterm_nonce NX0 MX2)))))

; 31
(assert (forall ((NX0 Name)) (=> (Message$_13$subterm_nonce NX0 g) false)))

; 32
(assert
  (forall
    ((MX1 Message) (MX2 Message) (NX0 Name))
    (=>
      (Message$_13$subterm_nonce NX0 (sign MX1 MX2))
      (or (Message$_13$subterm_nonce NX0 MX1) (Message$_13$subterm_nonce NX0 MX2)))))

; 33
(assert
  (forall
    ((CX1 Condition) (NX0 Name))
    (=>
      (Condition$_13$subterm_nonce NX0 (ta$not CX1))
      (or (Condition$_13$subterm_nonce NX0 CX1)))))

; 34
(assert
  (forall
    ((MX1 Message) (NX0 Name))
    (=>
      (Message$_13$subterm_nonce NX0 (pk MX1))
      (or (Message$_13$subterm_nonce NX0 MX1)))))

; 35
(assert
  (forall
    ((CX1 Condition) (CX2 Condition) (NX0 Name))
    (=>
      (Condition$_13$subterm_nonce NX0 (ta$and CX1 CX2))
      (or
        (Condition$_13$subterm_nonce NX0 CX1)
        (Condition$_13$subterm_nonce NX0 CX2)))))

; 36
(assert (forall ((NX0 Name)) (=> (Message$_13$subterm_nonce NX0 ko) false)))

; 37
(assert
  (forall
    ((MX1 Message) (NX0 Name))
    (=>
      (Message$_13$subterm_nonce NX0 (msnd MX1))
      (or (Message$_13$subterm_nonce NX0 MX1)))))

; 38
(assert
  (forall
    ((MX1 Message) (NX0 Name))
    (=>
      (Message$_13$subterm_nonce NX0 (mfst MX1))
      (or (Message$_13$subterm_nonce NX0 MX1)))))

; 39
(assert
  (forall
    ((CX1 Condition) (CX2 Condition) (NX0 Name))
    (=>
      (Condition$_13$subterm_nonce NX0 (ta$iff CX1 CX2))
      (or
        (Condition$_13$subterm_nonce NX0 CX1)
        (Condition$_13$subterm_nonce NX0 CX2)))))

; 40
(assert
  (forall
    ((MX1 Message) (MX2 Message) (MX3 Message) (NX0 Name))
    (=>
      (Condition$_13$subterm_nonce NX0 (checksign MX1 MX2 MX3))
      (or
        (Message$_13$subterm_nonce NX0 MX1)
        (Message$_13$subterm_nonce NX0 MX2)
        (Message$_13$subterm_nonce NX0 MX3)))))

; 41
(assert
  (forall
    ((MX1 Message) (MX2 Message) (NX0 Name))
    (=>
      (Message$_13$subterm_nonce NX0 (mexp MX1 MX2))
      (or (Message$_13$subterm_nonce NX0 MX1) (Message$_13$subterm_nonce NX0 MX2)))))

; 42
(assert (forall ((NX0 Name)) (=> (Message$_13$subterm_nonce NX0 empty) false)))

; 43
(assert
  (forall
    ((MX1 Message) (MX2 Message) (NX0 Name))
    (=>
      (Condition$_13$subterm_nonce NX0 (ta$= MX1 MX2))
      (or (Message$_13$subterm_nonce NX0 MX1) (Message$_13$subterm_nonce NX0 MX2)))))

; 44
(assert
  (forall
    ((CX1 Condition) (MX2 Message) (MX3 Message) (NX0 Name))
    (=>
      (Message$_13$subterm_nonce NX0 (ta$ite CX1 MX2 MX3))
      (or
        (Condition$_13$subterm_nonce NX0 CX1)
        (Message$_13$subterm_nonce NX0 MX2)
        (Message$_13$subterm_nonce NX0 MX3)))))

; 45
(assert (forall ((NX0 Name)) (=> (Message$_13$subterm_nonce NX0 ok) false)))

; 46
(assert
  (forall
    ((CX1 Condition) (CX2 Condition) (NX0 Name))
    (=>
      (Condition$_13$subterm_nonce NX0 (ta$or CX1 CX2))
      (or
        (Condition$_13$subterm_nonce NX0 CX1)
        (Condition$_13$subterm_nonce NX0 CX2)))))

; 47
(assert
  (forall
    ((NX0 Name) (BX1 Bitstring))
    (not (Bitstring$_13$subterm_nonce NX0 BX1))))

; 48
(assert
  (forall ((NX0 Name) (sX1 session)) (not (session$_13$subterm_nonce NX0 sX1))))

; 49
(assert
  (forall ((NX0 Name) (iX1 index)) (not (index$_13$subterm_nonce NX0 iX1))))

; 50
(assert
  (forall ((NX0 Name) (BX1 Bool)) (not (Bool$_13$subterm_nonce NX0 BX1))))

; 51
(assert
  (forall
    ((SX4 Step) (NX3 Name))
    (=>
      (Message$_13$subterm_nonce NX3 (input SX4))
      (or
        (exists
          ((iX0 index) (iX1 index) (iX2 index))
          (or
            (and (= NX3 (b iX1)) (lt (Pchall3 iX0 iX1) SX4))
            (and (= NX3 skS) (lt (Pchall3 iX0 iX1) SX4))
            (and (= NX3 skP) (lt (Pchall3 iX0 iX1) SX4))
            (and (= NX3 (a iX0)) (lt (Pchall3 iX0 iX1) SX4))
            (and (= NX3 skS) (lt (Pchall2 iX0) SX4))
            (and (= NX3 skP) (lt (Pchall2 iX0) SX4))
            (and (= NX3 (a iX0)) (lt (Pchall2 iX0) SX4))
            (and (= NX3 (a iX0)) (lt (Pchall1 iX0) SX4))
            (and (= NX3 skP) (lt (Pchall1 iX0) SX4))
            (and (= NX3 skP) (lt (S1 iX0) SX4))
            (and (= NX3 skS) (lt (S1 iX0) SX4))
            (and (= NX3 (b iX0)) (lt (S1 iX0) SX4))
            (and (= NX3 skS) (lt (S2 iX0) SX4))
            (and (= NX3 (b iX0)) (lt (S2 iX0) SX4))
            (and (= NX3 skP) (lt (S2 iX0) SX4))
            (and (= NX3 (b iX2)) (lt (Pchall3bis iX0) SX4))
            (and (= NX3 skS) (lt (Pchall3bis iX0) SX4))
            (and (= NX3 skP) (lt (Pchall3bis iX0) SX4))
            (and (= NX3 (a iX0)) (lt (Pchall3bis iX0) SX4))))))))

; 52
(assert
  (forall
    ((iX4 index) (NX3 Name))
    (=>
      (Condition$_13$subterm_nonce NX3 (ta$exists$0 iX4))
      (or
        (exists
          ((iX0 index) (iX1 index) (iX2 index) (iX4 index))
          (or
            (and (= NX3 (b iX2)))
            (and (= NX3 (b iX1)) (lt (Pchall3 iX0 iX1) (Pchall2 iX4)))
            (and (= NX3 skS) (lt (Pchall3 iX0 iX1) (Pchall2 iX4)))
            (and (= NX3 skP) (lt (Pchall3 iX0 iX1) (Pchall2 iX4)))
            (and (= NX3 (a iX0)) (lt (Pchall3 iX0 iX1) (Pchall2 iX4)))
            (and (= NX3 skS) (lt (Pchall2 iX0) (Pchall2 iX4)))
            (and (= NX3 skP) (lt (Pchall2 iX0) (Pchall2 iX4)))
            (and (= NX3 (a iX0)) (lt (Pchall2 iX0) (Pchall2 iX4)))
            (and (= NX3 (a iX0)) (lt (Pchall1 iX0) (Pchall2 iX4)))
            (and (= NX3 skP) (lt (Pchall1 iX0) (Pchall2 iX4)))
            (and (= NX3 skP) (lt (S1 iX0) (Pchall2 iX4)))
            (and (= NX3 skS) (lt (S1 iX0) (Pchall2 iX4)))
            (and (= NX3 (b iX0)) (lt (S1 iX0) (Pchall2 iX4)))
            (and (= NX3 skS) (lt (S2 iX0) (Pchall2 iX4)))
            (and (= NX3 (b iX0)) (lt (S2 iX0) (Pchall2 iX4)))
            (and (= NX3 skP) (lt (S2 iX0) (Pchall2 iX4)))
            (and (= NX3 (b iX4)) (lt (Pchall3bis iX0) (Pchall2 iX4)))
            (and (= NX3 skS) (lt (Pchall3bis iX0) (Pchall2 iX4)))
            (and (= NX3 skP) (lt (Pchall3bis iX0) (Pchall2 iX4)))
            (and (= NX3 (a iX0)) (lt (Pchall3bis iX0) (Pchall2 iX4)))))))))

; 53
(assert
  (forall
    ((NX0 Name) (NX1 Name))
    (=> (Name$_13$subterm_nonce NX0 NX1) (= NX0 NX1))))

; 54
(assert
  (forall
    ((NX0 Name) (NX1 Name))
    (=> (= (cast$Message$name NX0) (cast$Message$name NX1)) (= NX0 NX1))))

; 55
(assert
  (forall
    ((NX0 Name) (MX1 Message))
    (=> (= (cast$Message$name NX0) MX1) (Message$_13$subterm_nonce NX0 MX1))))


; user asserts


; 56
(assert
  (forall
    ((MX0 Message) (MX1 Message))
    (and (= MX0 (mfst (tpl MX0 MX1))) (= MX1 (msnd (tpl MX0 MX1))))))


; query


; 57
(assert-not
  (forall
    ((iX0 index))
    (=>
      (happens (Pchall2 iX0))
      (=>
        (and
          true
          (checksign
            (msnd (input (Pchall2 iX0)))
            (tpl
              (tpl (mexp g (cast$Message$name (a iX0))) (msnd (mfst (input (Pchall2 iX0)))))
              (pk (cast$Message$name skP)))
            (mfst (mfst (input (Pchall2 iX0)))))
          (= (mfst (mfst (input (Pchall2 iX0)))) (pk (cast$Message$name skS))))
        (exists
          ((iX1 index))
          (= (msnd (mfst (input (Pchall2 iX0)))) (mexp g (cast$Message$name (b iX1)))))))))

(check-sat)

