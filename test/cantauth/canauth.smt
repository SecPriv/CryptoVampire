(declare-sort Message 0)

(declare-sort index 0)

(declare-sort Step 0)

(define-sort Condition () Bool)

(define-sort Bitstring () Message)

(declare-datatypes
  ((Name 0))
  (
    (
      (msgA (_0$dest_msgA_0 index) (_1$dest_msgA_1 index))
      (msgB (_2$dest_msgB_0 index) (_3$dest_msgB_1 index))
      (sk (_4$dest_sk_0 index)))))

(declare-fun ReceiverA (index index) Step)

(declare-fun ReceiverB (index index) Step)

(declare-fun SenderA (index index) Step)

(declare-fun SenderB (index index) Step)

(declare-fun init () Step)

(declare-fun pred (Step) Step)

(declare-fun Bool$_7$subterm_nonce (Name Bool) Bool)

(declare-fun Condition$_7$subterm_nonce (Name Condition) Bool)

(declare-fun Message$_7$subterm_nonce (Name Message) Bool)

(declare-fun Bitstring$_7$subterm_nonce (Name Bitstring) Bool)

(declare-fun index$_7$subterm_nonce (Name index) Bool)

(declare-fun Step$_7$subterm_nonce (Name Step) Bool)

(declare-fun Name$_7$subterm_nonce (Name Name) Bool)

(declare-fun ta$and (Condition Condition) Condition)

(declare-fun ta$or (Condition Condition) Condition)

(declare-fun ta$not (Condition) Condition)

(declare-fun ta$implies (Condition Condition) Condition)

(declare-fun ta$iff (Condition Condition) Condition)

(declare-fun ta$true () Condition)

(declare-fun ta$false () Condition)

(declare-fun ta$= (Message Message) Condition)

(declare-fun SIGN () Message)

(declare-fun empty () Message)

(declare-fun fst (Message) Message)

(declare-fun hmac (Message Message) Message)

(declare-fun mexec (Step) Condition)

(declare-fun mlt (Message Message) Condition)

(declare-fun mySucc (Message) Message)

(declare-fun myZero () Message)

(declare-fun ok () Message)

(declare-fun snd (Message) Message)

(declare-fun tpl (Message Message) Message)

(declare-fun verify (Message Message Message) Condition)

(declare-fun cellA (index Step) Message)

(declare-fun cellB (index Step) Message)

(declare-fun cast$Message$name (Name) Message)

(declare-fun input (Step) Message)

(declare-fun ta$ite (Condition Message Message) Message)

(declare-fun ta$cond (Step) Condition)

(declare-fun ta$msg (Step) Message)

(declare-fun evaluate_cond (Condition) Bool)

(declare-fun evaluate_msg (Message) Bitstring)

(declare-fun happens (Step) Bool)

(declare-fun leq (Step Step) Bool)

(declare-fun lt (Step Step) Bool)


; ordering


; 1
(assert
  (forall
    ((SX1 Step) (SX2 Step))
    (= (and (leq SX1 SX2) (not (= SX1 SX2))) (lt SX1 SX2))))

; 2
(assert (happens init))

; 3
(assert (forall ((SX1 Step)) (=> (happens SX1) (leq init SX1))))

; 4
(assert
  (forall ((SX0 Step)) (=> (happens SX0) (or (= SX0 init) (happens (pred SX0))))))

; 5
(assert
  (forall
    ((SX1 Step) (SX2 Step))
    (or (or (happens SX1) (happens SX2)) (= SX1 SX2))))

; 6
(assert
  (forall
    ((SX1 Step) (SX2 Step) (SX3 Step))
    (=> (and (leq SX1 SX2) (leq SX2 SX3)) (leq SX1 SX3))))

; 7
(assert
  (forall
    ((SX1 Step) (SX2 Step))
    (=> (and (leq SX1 SX2) (leq SX2 SX1)) (= SX1 SX2))))

; 8
(assert
  (forall
    ((SX1 Step) (SX2 Step))
    (= (and (happens SX1) (happens SX2)) (or (leq SX1 SX2) (leq SX2 SX1)))))

; 9
(assert (forall ((SX0 Step)) (=> (happens (pred SX0)) (leq (pred SX0) SX0))))

; 10
(assert (forall ((SX0 Step)) (=> (happens SX0) (not (= (pred SX0) SX0)))))

; 11
(assert (forall ((SX0 Step)) (=> (happens (pred SX0)) (happens SX0))))

; 12
(assert
  (forall
    ((SX1 Step) (SX2 Step))
    (=>
      (and (happens (pred SX1)) (happens SX2))
      (or (leq SX2 (pred SX1)) (leq SX1 SX2)))))

; 13
(assert
  (=>
    (happens init)
    (and
      (=> (= init init) true)
      (forall ((iX1 index) (iX2 index)) (not (= init (ReceiverA iX1 iX2))))
      (forall ((iX1 index) (iX2 index)) (not (= init (SenderA iX1 iX2))))
      (forall ((iX1 index) (iX2 index)) (not (= init (ReceiverB iX1 iX2))))
      (forall ((iX1 index) (iX2 index)) (not (= init (SenderB iX1 iX2)))))))

; 14
(assert
  (forall
    ((iX0 index) (iX1 index))
    (=>
      (happens (ReceiverA iX0 iX1))
      (and
        (not (= (ReceiverA iX0 iX1) init))
        (forall
          ((iX2 index) (iX3 index))
          (=> (= (ReceiverA iX0 iX1) (ReceiverA iX2 iX3)) (and (= iX0 iX2) (= iX1 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (ReceiverA iX0 iX1) (SenderA iX2 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (ReceiverA iX0 iX1) (ReceiverB iX2 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (ReceiverA iX0 iX1) (SenderB iX2 iX3))))))))

; 15
(assert
  (forall
    ((iX0 index) (iX1 index))
    (=>
      (happens (SenderA iX0 iX1))
      (and
        (not (= (SenderA iX0 iX1) init))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (SenderA iX0 iX1) (ReceiverA iX2 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (=> (= (SenderA iX0 iX1) (SenderA iX2 iX3)) (and (= iX0 iX2) (= iX1 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (SenderA iX0 iX1) (ReceiverB iX2 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (SenderA iX0 iX1) (SenderB iX2 iX3))))))))

; 16
(assert
  (forall
    ((iX0 index) (iX1 index))
    (=>
      (happens (ReceiverB iX0 iX1))
      (and
        (not (= (ReceiverB iX0 iX1) init))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (ReceiverB iX0 iX1) (ReceiverA iX2 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (ReceiverB iX0 iX1) (SenderA iX2 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (=> (= (ReceiverB iX0 iX1) (ReceiverB iX2 iX3)) (and (= iX0 iX2) (= iX1 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (ReceiverB iX0 iX1) (SenderB iX2 iX3))))))))

; 17
(assert
  (forall
    ((iX0 index) (iX1 index))
    (=>
      (happens (SenderB iX0 iX1))
      (and
        (not (= (SenderB iX0 iX1) init))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (SenderB iX0 iX1) (ReceiverA iX2 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (SenderB iX0 iX1) (SenderA iX2 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (not (= (SenderB iX0 iX1) (ReceiverB iX2 iX3))))
        (forall
          ((iX2 index) (iX3 index))
          (=> (= (SenderB iX0 iX1) (SenderB iX2 iX3)) (and (= iX0 iX2) (= iX1 iX3))))))))

; 18
(assert
  (forall
    ((SX2 Step))
    (=>
      (happens SX2)
      (or
        (= SX2 init)
        (exists ((iX0 index) (iX1 index)) (= SX2 (ReceiverA iX0 iX1)))
        (exists ((iX0 index) (iX1 index)) (= SX2 (SenderA iX0 iX1)))
        (exists ((iX0 index) (iX1 index)) (= SX2 (ReceiverB iX0 iX1)))
        (exists ((iX0 index) (iX1 index)) (= SX2 (SenderB iX0 iX1)))))))


; evaluate


; 19
(assert (forall ((CX1 Condition)) (= CX1 CX1)))

; 20
(assert (forall ((MX1 Message)) (= MX1 MX1)))

; 21
(assert (= ta$false false))

; 22
(assert (= ta$true true))

; 23
(assert
  (forall
    ((CX0 Condition) (CX1 Condition))
    (= (ta$implies CX0 CX1) (=> CX0 CX1))))

; 24
(assert (forall ((CX0 Condition)) (=> (ta$not CX0) (not CX0))))

; 25
(assert
  (forall ((CX0 Condition) (CX1 Condition)) (= (ta$and CX0 CX1) (and CX0 CX1))))

; 26
(assert
  (forall ((CX0 Condition) (CX1 Condition)) (= (ta$iff CX0 CX1) (= CX0 CX1))))

; 27
(assert (forall ((MX0 Message) (MX1 Message)) (= (ta$= MX0 MX1) (= MX0 MX1))))

; 28
(assert
  (forall
    ((CX0 Condition) (MX1 Message) (MX2 Message))
    (= (ta$ite CX0 MX1 MX2) (ite CX0 MX1 MX2))))

; 29
(assert
  (forall ((CX0 Condition) (CX1 Condition)) (= (ta$or CX0 CX1) (or CX0 CX1))))


; crypto



; uf-cma


; 30
(assert (forall ((MX1 Message) (MX0 Message)) (verify (hmac MX1 MX0) MX1 MX0)))

; 31
(assert
  (forall
    ((iX5 index) (iX4 index))
    (=>
      (verify
        (snd (input (ReceiverB iX4 iX5)))
        (tpl
          (snd (snd (fst (input (ReceiverB iX4 iX5)))))
          (fst (fst (input (ReceiverB iX4 iX5)))))
        (cast$Message$name (sk iX4)))
      (or
        (exists
          ((iX0 index) (iX1 index))
          (or
            (and
              (=
                (tpl
                  (snd (snd (fst (input (ReceiverB iX4 iX5)))))
                  (fst (fst (input (ReceiverB iX4 iX5)))))
                (tpl (cellB iX0 (SenderB iX0 iX1)) (cast$Message$name (msgB iX0 iX1))))
              (= iX4 iX0)
              (lt (SenderB iX0 iX1) (ReceiverB iX4 iX5)))
            (and
              (=
                (tpl
                  (snd (snd (fst (input (ReceiverB iX4 iX5)))))
                  (fst (fst (input (ReceiverB iX4 iX5)))))
                (tpl (cellA iX0 (SenderA iX0 iX1)) (cast$Message$name (msgA iX0 iX1))))
              (= iX4 iX0)
              (lt (SenderA iX0 iX1) (ReceiverB iX4 iX5)))))))))

; 32
(assert
  (forall
    ((iX5 index) (iX4 index))
    (=>
      (verify
        (snd (input (ReceiverA iX4 iX5)))
        (tpl
          (snd (snd (fst (input (ReceiverA iX4 iX5)))))
          (fst (fst (input (ReceiverA iX4 iX5)))))
        (cast$Message$name (sk iX4)))
      (or
        (exists
          ((iX0 index) (iX1 index))
          (or
            (and
              (=
                (tpl
                  (snd (snd (fst (input (ReceiverA iX4 iX5)))))
                  (fst (fst (input (ReceiverA iX4 iX5)))))
                (tpl (cellB iX0 (SenderB iX0 iX1)) (cast$Message$name (msgB iX0 iX1))))
              (= iX4 iX0)
              (lt (SenderB iX0 iX1) (ReceiverA iX4 iX5)))
            (and
              (=
                (tpl
                  (snd (snd (fst (input (ReceiverA iX4 iX5)))))
                  (fst (fst (input (ReceiverA iX4 iX5)))))
                (tpl (cellA iX0 (SenderA iX0 iX1)) (cast$Message$name (msgA iX0 iX1))))
              (= iX4 iX0)
              (lt (SenderA iX0 iX1) (ReceiverA iX4 iX5)))))))))

; 33
(assert
  (forall
    ((iX4 index) (iX3 index))
    (=>
      (verify
        (snd (input (ReceiverA iX3 iX4)))
        (tpl
          (snd (snd (fst (input (ReceiverA iX3 iX4)))))
          (fst (fst (input (ReceiverA iX3 iX4)))))
        (cast$Message$name (sk iX3)))
      (or
        (exists
          ((iX0 index) (iX1 index))
          (or
            (and
              (=
                (tpl
                  (snd (snd (fst (input (ReceiverA iX3 iX4)))))
                  (fst (fst (input (ReceiverA iX3 iX4)))))
                (tpl (cellB iX0 (SenderB iX0 iX1)) (cast$Message$name (msgB iX0 iX1))))
              (= iX3 iX0)
              (lt (SenderB iX0 iX1) (ReceiverA iX3 iX4)))
            (and
              (=
                (tpl
                  (snd (snd (fst (input (ReceiverA iX3 iX4)))))
                  (fst (fst (input (ReceiverA iX3 iX4)))))
                (tpl (cellA iX0 (SenderA iX0 iX1)) (cast$Message$name (msgA iX0 iX1))))
              (= iX3 iX0)
              (lt (SenderA iX0 iX1) (ReceiverA iX3 iX4)))))))))

; 34
(assert
  (forall
    ((iX4 index) (iX3 index))
    (=>
      (verify
        (snd (input (ReceiverB iX3 iX4)))
        (tpl
          (snd (snd (fst (input (ReceiverB iX3 iX4)))))
          (fst (fst (input (ReceiverB iX3 iX4)))))
        (cast$Message$name (sk iX3)))
      (or
        (exists
          ((iX0 index) (iX1 index))
          (or
            (and
              (=
                (tpl
                  (snd (snd (fst (input (ReceiverB iX3 iX4)))))
                  (fst (fst (input (ReceiverB iX3 iX4)))))
                (tpl (cellB iX0 (SenderB iX0 iX1)) (cast$Message$name (msgB iX0 iX1))))
              (= iX3 iX0)
              (lt (SenderB iX0 iX1) (ReceiverB iX3 iX4)))
            (and
              (=
                (tpl
                  (snd (snd (fst (input (ReceiverB iX3 iX4)))))
                  (fst (fst (input (ReceiverB iX3 iX4)))))
                (tpl (cellA iX0 (SenderA iX0 iX1)) (cast$Message$name (msgA iX0 iX1))))
              (= iX3 iX0)
              (lt (SenderA iX0 iX1) (ReceiverB iX3 iX4)))))))))


; nonce


; 35
(assert (forall ((NX0 Name)) (=> (Message$_7$subterm_nonce NX0 myZero) false)))

; 36
(assert
  (forall
    ((NX1 Name) (NX0 Name))
    (=>
      (Message$_7$subterm_nonce NX0 (cast$Message$name NX1))
      (or (Name$_7$subterm_nonce NX0 NX1)))))

; 37
(assert
  (forall ((NX0 Name)) (=> (Condition$_7$subterm_nonce NX0 ta$false) false)))

; 38
(assert
  (forall ((NX0 Name)) (=> (Condition$_7$subterm_nonce NX0 ta$true) false)))

; 39
(assert
  (forall
    ((CX1 Condition) (CX2 Condition) (NX0 Name))
    (=>
      (Condition$_7$subterm_nonce NX0 (ta$implies CX1 CX2))
      (or (Condition$_7$subterm_nonce NX0 CX1) (Condition$_7$subterm_nonce NX0 CX2)))))

; 40
(assert
  (forall
    ((MX1 Message) (NX0 Name))
    (=>
      (Message$_7$subterm_nonce NX0 (mySucc MX1))
      (or (Message$_7$subterm_nonce NX0 MX1)))))

; 41
(assert
  (forall
    ((MX1 Message) (MX2 Message) (NX0 Name))
    (=>
      (Condition$_7$subterm_nonce NX0 (mlt MX1 MX2))
      (or (Message$_7$subterm_nonce NX0 MX1) (Message$_7$subterm_nonce NX0 MX2)))))

; 42
(assert
  (forall
    ((MX1 Message) (MX2 Message) (NX0 Name))
    (=>
      (Message$_7$subterm_nonce NX0 (tpl MX1 MX2))
      (or (Message$_7$subterm_nonce NX0 MX1) (Message$_7$subterm_nonce NX0 MX2)))))

; 43
(assert
  (forall
    ((MX1 Message) (NX0 Name))
    (=>
      (Message$_7$subterm_nonce NX0 (snd MX1))
      (or (Message$_7$subterm_nonce NX0 MX1)))))

; 44
(assert
  (forall
    ((CX1 Condition) (NX0 Name))
    (=>
      (Condition$_7$subterm_nonce NX0 (ta$not CX1))
      (or (Condition$_7$subterm_nonce NX0 CX1)))))

; 45
(assert
  (forall
    ((MX1 Message) (MX2 Message) (MX3 Message) (NX0 Name))
    (=>
      (Condition$_7$subterm_nonce NX0 (verify MX1 MX2 MX3))
      (or
        (Message$_7$subterm_nonce NX0 MX1)
        (Message$_7$subterm_nonce NX0 MX2)
        (Message$_7$subterm_nonce NX0 MX3)))))

; 46
(assert
  (forall
    ((MX1 Message) (NX0 Name))
    (=>
      (Message$_7$subterm_nonce NX0 (fst MX1))
      (or (Message$_7$subterm_nonce NX0 MX1)))))

; 47
(assert
  (forall
    ((CX1 Condition) (CX2 Condition) (NX0 Name))
    (=>
      (Condition$_7$subterm_nonce NX0 (ta$and CX1 CX2))
      (or (Condition$_7$subterm_nonce NX0 CX1) (Condition$_7$subterm_nonce NX0 CX2)))))

; 48
(assert
  (forall
    ((CX1 Condition) (CX2 Condition) (NX0 Name))
    (=>
      (Condition$_7$subterm_nonce NX0 (ta$iff CX1 CX2))
      (or (Condition$_7$subterm_nonce NX0 CX1) (Condition$_7$subterm_nonce NX0 CX2)))))

; 49
(assert (forall ((NX0 Name)) (=> (Message$_7$subterm_nonce NX0 empty) false)))

; 50
(assert
  (forall
    ((MX1 Message) (MX2 Message) (NX0 Name))
    (=>
      (Condition$_7$subterm_nonce NX0 (ta$= MX1 MX2))
      (or (Message$_7$subterm_nonce NX0 MX1) (Message$_7$subterm_nonce NX0 MX2)))))

; 51
(assert
  (forall
    ((CX1 Condition) (MX2 Message) (MX3 Message) (NX0 Name))
    (=>
      (Message$_7$subterm_nonce NX0 (ta$ite CX1 MX2 MX3))
      (or
        (Condition$_7$subterm_nonce NX0 CX1)
        (Message$_7$subterm_nonce NX0 MX2)
        (Message$_7$subterm_nonce NX0 MX3)))))

; 52
(assert (forall ((NX0 Name)) (=> (Message$_7$subterm_nonce NX0 ok) false)))

; 53
(assert
  (forall
    ((MX1 Message) (MX2 Message) (NX0 Name))
    (=>
      (Message$_7$subterm_nonce NX0 (hmac MX1 MX2))
      (or (Message$_7$subterm_nonce NX0 MX1) (Message$_7$subterm_nonce NX0 MX2)))))

; 54
(assert
  (forall
    ((SX1 Step) (NX0 Name))
    (=>
      (Condition$_7$subterm_nonce NX0 (mexec SX1))
      (or (Step$_7$subterm_nonce NX0 SX1)))))

; 55
(assert (forall ((NX0 Name)) (=> (Message$_7$subterm_nonce NX0 SIGN) false)))

; 56
(assert
  (forall
    ((CX1 Condition) (CX2 Condition) (NX0 Name))
    (=>
      (Condition$_7$subterm_nonce NX0 (ta$or CX1 CX2))
      (or (Condition$_7$subterm_nonce NX0 CX1) (Condition$_7$subterm_nonce NX0 CX2)))))

; 57
(assert
  (forall
    ((NX0 Name) (BX1 Bitstring))
    (not (Bitstring$_7$subterm_nonce NX0 BX1))))

; 58
(assert
  (forall ((NX0 Name) (iX1 index)) (not (index$_7$subterm_nonce NX0 iX1))))

; 59
(assert (forall ((NX0 Name) (BX1 Bool)) (not (Bool$_7$subterm_nonce NX0 BX1))))

; 60
(assert
  (forall
    ((SX5 Step) (NX4 Name))
    (=>
      (Message$_7$subterm_nonce NX4 (input SX5))
      (or
        (exists
          ((iX0 index) (iX1 index))
          (or
            (and (= NX4 (sk iX0)) (lt (SenderB iX0 iX1) SX5))
            (and (= NX4 (msgB iX0 iX1)) (lt (SenderB iX0 iX1) SX5))
            (and (= NX4 (sk iX0)) (lt (ReceiverB iX0 iX1) SX5))
            (and (= NX4 (sk iX0)) (lt (SenderA iX0 iX1) SX5))
            (and (= NX4 (msgA iX0 iX1)) (lt (SenderA iX0 iX1) SX5))
            (and (= NX4 (sk iX0)) (lt (ReceiverA iX0 iX1) SX5))))))))

; 61
(assert
  (forall
    ((SX5 Step) (NX4 Name))
    (=>
      (Message$_7$subterm_nonce NX4 (ta$msg SX5))
      (or
        (exists
          ((iX0 index) (iX1 index))
          (or
            (and (= NX4 (sk iX0)) (= SX5 (SenderB iX0 iX1)))
            (and (= NX4 (msgB iX0 iX1)) (= SX5 (SenderB iX0 iX1)))
            (and (= NX4 (sk iX0)) (= SX5 (SenderA iX0 iX1)))
            (and (= NX4 (msgA iX0 iX1)) (= SX5 (SenderA iX0 iX1)))))))))

; 62
(assert
  (forall
    ((SX5 Step) (NX4 Name))
    (=>
      (Condition$_7$subterm_nonce NX4 (ta$cond SX5))
      (or
        (exists
          ((iX0 index) (iX1 index) (iX2 index) (iX3 index))
          (or
            (and (= NX4 (sk iX0)) (= SX5 (ReceiverB iX0 iX1)))
            (and
              (= NX4 (sk iX2))
              (and (= SX5 (ReceiverB iX0 iX1)) (lt (SenderB iX2 iX3) (ReceiverB iX0 iX1))))
            (and
              (= NX4 (msgB iX2 iX3))
              (and (= SX5 (ReceiverB iX0 iX1)) (lt (SenderB iX2 iX3) (ReceiverB iX0 iX1))))
            (and
              (= NX4 (sk iX2))
              (and (= SX5 (ReceiverB iX0 iX1)) (lt (ReceiverB iX2 iX3) (ReceiverB iX0 iX1))))
            (and
              (= NX4 (sk iX2))
              (and (= SX5 (ReceiverB iX0 iX1)) (lt (SenderA iX2 iX3) (ReceiverB iX0 iX1))))
            (and
              (= NX4 (msgA iX2 iX3))
              (and (= SX5 (ReceiverB iX0 iX1)) (lt (SenderA iX2 iX3) (ReceiverB iX0 iX1))))
            (and
              (= NX4 (sk iX2))
              (and (= SX5 (ReceiverB iX0 iX1)) (lt (ReceiverA iX2 iX3) (ReceiverB iX0 iX1))))
            (and (= NX4 (sk iX0)) (= SX5 (ReceiverA iX0 iX1)))
            (and
              (= NX4 (sk iX2))
              (and (= SX5 (ReceiverA iX0 iX1)) (lt (SenderB iX2 iX3) (ReceiverA iX0 iX1))))
            (and
              (= NX4 (msgB iX2 iX3))
              (and (= SX5 (ReceiverA iX0 iX1)) (lt (SenderB iX2 iX3) (ReceiverA iX0 iX1))))
            (and
              (= NX4 (sk iX2))
              (and (= SX5 (ReceiverA iX0 iX1)) (lt (ReceiverB iX2 iX3) (ReceiverA iX0 iX1))))
            (and
              (= NX4 (sk iX2))
              (and (= SX5 (ReceiverA iX0 iX1)) (lt (SenderA iX2 iX3) (ReceiverA iX0 iX1))))
            (and
              (= NX4 (msgA iX2 iX3))
              (and (= SX5 (ReceiverA iX0 iX1)) (lt (SenderA iX2 iX3) (ReceiverA iX0 iX1))))
            (and
              (= NX4 (sk iX2))
              (and (= SX5 (ReceiverA iX0 iX1)) (lt (ReceiverA iX2 iX3) (ReceiverA iX0 iX1))))))))))

; 63
(assert
  (forall
    ((iX5 index) (SX6 Step) (NX4 Name))
    (=> (Message$_7$subterm_nonce NX4 (cellB iX5 SX6)) false)))

; 64
(assert
  (forall
    ((iX5 index) (SX6 Step) (NX4 Name))
    (=> (Message$_7$subterm_nonce NX4 (cellA iX5 SX6)) false)))

; 65
(assert
  (forall
    ((NX0 Name) (NX1 Name))
    (=> (Name$_7$subterm_nonce NX0 NX1) (= NX0 NX1))))

; 66
(assert
  (forall
    ((NX0 Name) (NX1 Name))
    (=> (= (cast$Message$name NX0) (cast$Message$name NX1)) (= NX0 NX1))))

; 67
(assert
  (forall
    ((NX0 Name) (MX1 Message))
    (=> (= (cast$Message$name NX0) MX1) (Message$_7$subterm_nonce NX0 MX1))))


; cells


; 68
(assert
  (forall
    ((iX4 index) (SX3 Step))
    (=>
      (and
        (forall ((iX1 index)) (not (and (= iX4 iX1) (= SX3 init))))
        (forall
          ((iX0 index) (iX1 index))
          (not (and (= iX4 iX0) (= SX3 (ReceiverB iX0 iX1)))))
        (forall
          ((iX0 index) (iX1 index))
          (not (and (= iX4 iX0) (= SX3 (SenderB iX0 iX1))))))
      (= (cellB iX4 SX3) (cellB iX4 (pred SX3))))))

; 69
(assert
  (forall
    ((iX4 index) (SX3 Step))
    (forall
      ((iX1 index))
      (=> (and (= iX4 iX1) (= SX3 init)) (= (cellB iX4 SX3) myZero)))))

; 70
(assert
  (forall
    ((iX4 index) (SX3 Step))
    (forall
      ((iX0 index) (iX1 index))
      (=>
        (and (= iX4 iX0) (= SX3 (ReceiverB iX0 iX1)))
        (= (cellB iX4 SX3) (mySucc (cellB iX0 (pred (ReceiverB iX0 iX1)))))))))

; 71
(assert
  (forall
    ((iX4 index) (SX3 Step))
    (forall
      ((iX0 index) (iX1 index))
      (=>
        (and (= iX4 iX0) (= SX3 (SenderB iX0 iX1)))
        (= (cellB iX4 SX3) (mySucc (cellB iX0 (pred (SenderB iX0 iX1)))))))))

; 72
(assert
  (forall
    ((iX4 index) (SX3 Step))
    (=>
      (and
        (forall ((iX1 index)) (not (and (= iX4 iX1) (= SX3 init))))
        (forall
          ((iX0 index) (iX1 index))
          (not (and (= iX4 iX0) (= SX3 (ReceiverA iX0 iX1)))))
        (forall
          ((iX0 index) (iX1 index))
          (not (and (= iX4 iX0) (= SX3 (SenderA iX0 iX1))))))
      (= (cellA iX4 SX3) (cellA iX4 (pred SX3))))))

; 73
(assert
  (forall
    ((iX4 index) (SX3 Step))
    (forall
      ((iX1 index))
      (=> (and (= iX4 iX1) (= SX3 init)) (= (cellA iX4 SX3) myZero)))))

; 74
(assert
  (forall
    ((iX4 index) (SX3 Step))
    (forall
      ((iX0 index) (iX1 index))
      (=>
        (and (= iX4 iX0) (= SX3 (ReceiverA iX0 iX1)))
        (= (cellA iX4 SX3) (mySucc (cellA iX0 (pred (ReceiverA iX0 iX1)))))))))

; 75
(assert
  (forall
    ((iX4 index) (SX3 Step))
    (forall
      ((iX0 index) (iX1 index))
      (=>
        (and (= iX4 iX0) (= SX3 (SenderA iX0 iX1)))
        (= (cellA iX4 SX3) (mySucc (cellA iX0 (pred (SenderA iX0 iX1)))))))))


; user asserts


; 76
(assert
  (forall
    ((MX0 Message) (MX1 Message))
    (and (= MX0 (fst (tpl MX0 MX1))) (= MX1 (snd (tpl MX0 MX1))))))

; 77
(assert
  (forall ((MX0 Message) (MX1 Message)) (=> (= MX0 MX1) (mlt MX0 (mySucc MX1)))))

; 78
(assert
  (forall
    ((MX0 Message) (MX1 Message) (MX2 Message))
    (=> (and (mlt MX0 MX1) (mlt MX1 MX2)) (mlt MX0 MX2))))

; 79
(assert (forall ((MX0 Message)) (not (mlt MX0 MX0))))

; 80
(assert
  (forall
    ((MX0 Message) (MX1 Message))
    (=> (mlt MX0 (mySucc MX1)) (or (= MX0 MX1) (mlt MX0 MX1)))))

; 81
(assert
  (forall
    ((SX0 Step))
    (=
      (mexec SX0)
      (and
        (forall
          ((iX1 index) (iX2 index))
          (=>
            (or (lt (ReceiverA iX1 iX2) SX0) (= (ReceiverA iX1 iX2) SX0))
            (and
              (= (fst (snd (fst (input (ReceiverA iX1 iX2))))) SIGN)
              (mlt
                (cellA iX1 (pred (ReceiverA iX1 iX2)))
                (snd (snd (fst (input (ReceiverA iX1 iX2))))))
              (=
                (snd (input (ReceiverA iX1 iX2)))
                (hmac
                  (tpl
                    (snd (snd (fst (input (ReceiverA iX1 iX2)))))
                    (fst (fst (input (ReceiverA iX1 iX2)))))
                  (cast$Message$name (sk iX1)))))))
        (forall
          ((iX1 index) (iX2 index))
          (=>
            (or (lt (ReceiverB iX1 iX2) SX0) (= (ReceiverB iX1 iX2) SX0))
            (and
              (= (fst (snd (fst (input (ReceiverB iX1 iX2))))) SIGN)
              (mlt
                (cellB iX1 (pred (ReceiverB iX1 iX2)))
                (snd (snd (fst (input (ReceiverB iX1 iX2))))))
              (=
                (snd (input (ReceiverB iX1 iX2)))
                (hmac
                  (tpl
                    (snd (snd (fst (input (ReceiverB iX1 iX2)))))
                    (fst (fst (input (ReceiverB iX1 iX2)))))
                  (cast$Message$name (sk iX1)))))))
        (forall
          ((iX1 index) (iX2 index))
          (=> (or (lt (SenderA iX1 iX2) SX0) (= (SenderA iX1 iX2) SX0)) true))
        (forall
          ((iX1 index) (iX2 index))
          (=> (or (lt (SenderB iX1 iX2) SX0) (= (SenderB iX1 iX2) SX0)) true))))))

; 82
(assert
  (forall
    ((MX0 Message) (MX1 Message) (MX2 Message))
    (= (verify MX0 MX1 MX2) (= MX0 (hmac MX1 MX2)))))

; 83
(assert
  (forall
    ((iX0 index) (iX1 index) (SX2 Step))
    (=>
      (happens (ReceiverA iX0 iX1))
      (=>
        (and (lt SX2 (ReceiverA iX0 iX1)) (mexec (ReceiverA iX0 iX1)))
        (mlt (cellA iX0 SX2) (cellA iX0 (ReceiverA iX0 iX1)))))))


; query


; 84
(assert-not
  (forall
    ((iX0 index) (iX1 index))
    (=>
      (happens (ReceiverA iX0 iX1))
      (=>
        (mexec (ReceiverA iX0 iX1))
        (exists
          ((iX2 index))
          (and
            (lt (SenderB iX0 iX2) (ReceiverA iX0 iX1))
            (=
              (snd
                (tpl
                  (tpl
                    (cast$Message$name (msgB iX0 iX2))
                    (tpl SIGN (cellB iX0 (SenderB iX0 iX2))))
                  (hmac
                    (tpl (cellB iX0 (SenderB iX0 iX2)) (cast$Message$name (msgB iX0 iX2)))
                    (cast$Message$name (sk iX0)))))
              (snd (input (ReceiverA iX0 iX1))))
            (=
              (fst
                (fst
                  (tpl
                    (tpl
                      (cast$Message$name (msgB iX0 iX2))
                      (tpl SIGN (cellB iX0 (SenderB iX0 iX2))))
                    (hmac
                      (tpl (cellB iX0 (SenderB iX0 iX2)) (cast$Message$name (msgB iX0 iX2)))
                      (cast$Message$name (sk iX0))))))
              (fst (fst (input (ReceiverA iX0 iX1)))))
            (=
              (snd
                (snd
                  (fst
                    (tpl
                      (tpl
                        (cast$Message$name (msgB iX0 iX2))
                        (tpl SIGN (cellB iX0 (SenderB iX0 iX2))))
                      (hmac
                        (tpl (cellB iX0 (SenderB iX0 iX2)) (cast$Message$name (msgB iX0 iX2)))
                        (cast$Message$name (sk iX0)))))))
              (snd (snd (fst (input (ReceiverA iX0 iX1))))))
            (mlt (cellA iX0 (pred (ReceiverA iX0 iX1))) (cellB iX0 (SenderB iX0 iX2)))))))))

(check-sat)

