(declare-sort Nonce 0)
(declare-sort session 0)
(declare-sort index 0)
(declare-sort t$Bitstring 0)
(declare-datatypes
  ((Message 0) (Step 0) (t$Condition 0))
  (
    (
      (m$nonce_as_msg (d$m$nonce_as_msg_0 Nonce))
      (sel2of2 (d$sel2of2_0 Message))
      (ok)
      (ko)
      (hash (d$hash_0 Message) (d$hash_1 Message))
      (fail)
      (sel1of2 (d$sel1of2_0 Message))
      (m$ite (d$m$ite_0 t$Condition) (d$m$ite_1 Message) (d$m$ite_2 Message))
      (tuple (d$tuple_0 Message) (d$tuple_1 Message))
      (m$tfst_0 (d$m$tfst_0_0 session))
      (empty)
      (input (d$input_0 Step)))
    (
      (tag (d$tag_0 session) (d$tag_1 index))
      (reader1 (d$reader1_0 session))
      (reader2 (d$reader2_0 session))
      (s$init))
    (
      (c$true)
      (c$or (d$c$or_0 t$Condition) (d$c$or_1 t$Condition))
      (c$not (d$c$not_0 t$Condition))
      (c$and (d$c$and_0 t$Condition) (d$c$and_1 t$Condition))
      (c$false)
      (c$eq (d$c$eq_0 Message) (d$c$eq_1 Message)))))
(declare-fun key (index) Nonce)
(declare-fun b_empty () t$Bitstring)
(declare-fun b_sel2of2 (t$Bitstring) t$Bitstring)
(declare-fun b_fail () t$Bitstring)
(declare-fun b_sel1of2 (t$Bitstring) t$Bitstring)
(declare-fun b_m$nonce_as_msg (Nonce) t$Bitstring)
(declare-fun b_ko () t$Bitstring)
(declare-fun m$eval (Message) t$Bitstring)
(declare-fun b_ok () t$Bitstring)
(declare-fun lt (Step Step) Bool)
(declare-fun happens (Step) Bool)
(declare-fun nr (session) Nonce)
(declare-fun nt (session index) Nonce)
(declare-fun b_hash (t$Bitstring t$Bitstring) t$Bitstring)
(declare-fun c$eval (t$Condition) Bool)
(declare-fun b_tuple (t$Bitstring t$Bitstring) t$Bitstring)
(declare-fun r$rewriteb (t$Bitstring t$Bitstring) Bool)
(declare-fun sk$m$tfst_0_2 (session) index)
(assert
  (forall
    ((X1 index) (X2 session) (X3 session) (X4 index))
    (distinct (key X1) (nr X2) (nt X3 X4))))
(assert
  (forall ((X0 index) (X1 index)) (=> (= (key X0) (key X1)) (or (= X0 X1)))))
(assert
  (forall ((X0 session) (X1 session)) (=> (= (nr X0) (nr X1)) (or (= X0 X1)))))
(assert
  (forall
    ((X0 session) (X1 index) (X2 session) (X3 index))
    (=> (= (nt X0 X1) (nt X2 X3)) (or (= X0 X2) (= X1 X3)))))
(assert-theory (forall ((X0 Step)) (or (lt s$init X0) (= s$init X0))))
(assert-theory
  (forall
    ((X1 Step) (X2 Step) (X3 Step))
    (=> (and (lt X1 X2) (lt X2 X3)) (lt X1 X3))))
(assert-theory
  (forall ((X1 Step) (X2 Step)) (=> (and (happens X2) (lt X1 X2)) (happens X1))))
(assert-theory
  (forall
    ((X1 Step) (X2 Step))
    (or (lt X1 X2) (lt X2 X1) (= X1 X2) (not (happens X1)) (not (happens X2)))))
(declare-rewrite
  (forall
    ((X0 Nonce))
    (r$rewriteb (m$eval (m$nonce_as_msg X0)) (b_m$nonce_as_msg X0))))
(declare-rewrite
  (forall
    ((X0 Message))
    (r$rewriteb (m$eval (sel2of2 X0)) (b_sel2of2 (m$eval X0)))))
(declare-rewrite (forall () (r$rewriteb (m$eval ok) b_ok)))
(declare-rewrite (forall () (r$rewriteb (m$eval ko) b_ko)))
(declare-rewrite
  (forall
    ((X0 Message) (X1 Message))
    (r$rewriteb (m$eval (hash X0 X1)) (b_hash (m$eval X0) (m$eval X1)))))
(declare-rewrite (forall () (r$rewriteb (m$eval fail) b_fail)))
(declare-rewrite
  (forall
    ((X0 Message))
    (r$rewriteb (m$eval (sel1of2 X0)) (b_sel1of2 (m$eval X0)))))
(declare-rewrite
  (forall
    ((X0 Message) (X1 Message))
    (r$rewriteb (m$eval (tuple X0 X1)) (b_tuple (m$eval X0) (m$eval X1)))))
(declare-rewrite (forall () (r$rewriteb (m$eval empty) b_empty)))
(declare-rewrite
  (forall
    ((X1 t$Condition) (X2 t$Condition))
    (=> (c$eval (c$and X1 X2)) (and (c$eval X1) (c$eval X2)))))
(declare-rewrite
  (forall
    ((X1 t$Condition) (X2 t$Condition))
    (=> (c$eval (c$or X1 X2)) (or (c$eval X1) (c$eval X2)))))
(declare-rewrite
  (forall ((X1 t$Condition)) (=> (c$eval (c$not X1)) (not (c$eval X1)))))
(declare-rewrite
  (forall
    ((X1 Message) (X2 Message))
    (=> (c$eval (c$eq X1 X2)) (= (m$eval X1) (m$eval X2)))))
(assert (c$eval c$true))
(assert (not (c$eval c$false)))
(assert
  (forall
    ((X0 t$Condition) (X1 Message) (X2 Message))
    (= (m$eval (m$ite X0 X1 X2)) (ite (c$eval X0) (m$eval X1) (m$eval X2)))))
(assert
  (forall
    ((X2 index) (X1 session))
    (=>
      (c$eval
        (c$eq
          (hash
            (tuple (m$nonce_as_msg (nr X1)) (sel1of2 (input (reader2 X1))))
            (m$nonce_as_msg (key X2)))
          (sel2of2 (input (reader2 X1)))))
      (c$eval
        (c$eq
          (hash
            (tuple (m$nonce_as_msg (nr X1)) (sel1of2 (input (reader2 X1))))
            (m$nonce_as_msg (key (sk$m$tfst_0_2 X1))))
          (sel2of2 (input (reader2 X1))))))))
(assert
  (forall
    ((X1 session))
    (=
      (m$eval (m$tfst_0 X1))
      (ite
        (c$eval
          (c$eq
            (hash
              (tuple (m$nonce_as_msg (nr X1)) (sel1of2 (input (reader2 X1))))
              (m$nonce_as_msg (key (sk$m$tfst_0_2 X1))))
            (sel2of2 (input (reader2 X1)))))
        (m$eval ok)
        (m$eval ko)))))
(assert
  (forall
    ((X0 t$Bitstring) (X1 t$Bitstring))
    (and (= X0 (b_sel1of2 (b_tuple X0 X1))) (= X1 (b_sel2of2 (b_tuple X0 X1))))))
