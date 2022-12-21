(declare-sort index 0)

(declare-sort session 0)

(declare-sort Nonce 0)

(declare-sort t$Bitstring 0)

(declare-datatypes
  ((Message 0) (Step 0) (t$Condition 0))
  (
    (
      (empty)
      (hash (d$hash_0 Message) (d$hash_1 Message))
      (m$nonce_as_msg (d$m$nonce_as_msg_0 Nonce))
      (tuple (d$tuple_0 Message) (d$tuple_1 Message))
      (input (d$input_0 Step))
      (m$tfst_0 (d$m$tfst_0_0 session))
      (ok)
      (fail)
      (ko)
      (m$ite (d$m$ite_0 t$Condition) (d$m$ite_1 Message) (d$m$ite_2 Message))
      (sel2of2 (d$sel2of2_0 Message))
      (sel1of2 (d$sel1of2_0 Message)))
    (
      (reader1 (d$reader1_0 session))
      (tag (d$tag_0 session) (d$tag_1 index))
      (reader2 (d$reader2_0 session))
      (s$init))
    (
      (c$and (d$c$and_0 t$Condition) (d$c$and_1 t$Condition))
      (c$false)
      (c$true)
      (c$eq (d$c$eq_0 Message) (d$c$eq_1 Message))
      (c$or (d$c$or_0 t$Condition) (d$c$or_1 t$Condition))
      (c$not (d$c$not_0 t$Condition)))))

(declare-fun key (index) Nonce)

(declare-fun c$eval (t$Condition) Bool)

(declare-fun happens (Step) Bool)

(declare-fun b_sel1of2 (t$Bitstring) t$Bitstring)

(declare-fun b_empty () t$Bitstring)

(declare-fun lt (Step Step) Bool)

(declare-fun b_sel2of2 (t$Bitstring) t$Bitstring)

(declare-fun nr (session) Nonce)

(declare-fun b_m$nonce_as_msg (Nonce) t$Bitstring)

(declare-fun b_hash (t$Bitstring t$Bitstring) t$Bitstring)

(declare-fun b_tuple (t$Bitstring t$Bitstring) t$Bitstring)

(declare-fun b_fail () t$Bitstring)

(declare-fun nt (session index) Nonce)

(declare-fun m$eval (Message) t$Bitstring)

(declare-fun b_ok () t$Bitstring)

(declare-fun b_ko () t$Bitstring)

(declare-fun r$rewriteb (t$Bitstring t$Bitstring) Bool)

(declare-fun sk$m$tfst_0_2 (session) index)

(declare-subterm-relation
  sbt$euf_hash_main
  empty
  hash
  reader1
  tag
  m$nonce_as_msg
  c$and
  c$false
  tuple
  c$true
  c$eq
  ok
  reader2
  fail
  ko
  m$ite
  sel2of2
  c$or
  s$init
  c$not
  sel1of2)

(declare-subterm-relation
  sbt$euf_hash_main_bis
  empty
  hash
  reader1
  tag
  m$nonce_as_msg
  c$and
  c$false
  tuple
  c$true
  c$eq
  ok
  reader2
  fail
  ko
  m$ite
  sel2of2
  c$or
  s$init
  c$not
  sel1of2
  input)

(declare-fun sp$sbt$euf_hash_main$reader2 (Message Step) Bool)

(declare-fun sp$sbt$euf_hash_main$tag (Message Step) Bool)

(declare-fun sp$sbt$euf_hash_main$reader1 (Message Step) Bool)

(declare-fun sp$sbt$euf_hash_main$s$init (Message Step) Bool)

(declare-fun sp$sbt$euf_hash_main_bis$reader2 (Message Step) Bool)

(declare-fun sp$sbt$euf_hash_main_bis$tag (Message Step) Bool)

(declare-fun sp$sbt$euf_hash_main_bis$reader1 (Message Step) Bool)

(declare-fun sp$sbt$euf_hash_main_bis$s$init (Message Step) Bool)

(declare-subterm-relation
  sbt$euf_hash_sec
  empty
  reader1
  tag
  m$nonce_as_msg
  c$and
  c$false
  tuple
  c$true
  c$eq
  ok
  reader2
  fail
  ko
  m$ite
  sel2of2
  c$or
  s$init
  c$not
  sel1of2)

(declare-subterm-relation
  sbt$euf_hash_sec_bis
  empty
  reader1
  tag
  m$nonce_as_msg
  c$and
  c$false
  tuple
  c$true
  c$eq
  ok
  reader2
  fail
  ko
  m$ite
  sel2of2
  c$or
  s$init
  c$not
  sel1of2
  input)

(declare-fun sp$sbt$euf_hash_sec$reader2 (Nonce Step) Bool)

(declare-fun sp$sbt$euf_hash_sec$tag (Nonce Step) Bool)

(declare-fun sp$sbt$euf_hash_sec$reader1 (Nonce Step) Bool)

(declare-fun sp$sbt$euf_hash_sec$s$init (Nonce Step) Bool)

(declare-fun sp$sbt$euf_hash_sec_bis$reader2 (Nonce Step) Bool)

(declare-fun sp$sbt$euf_hash_sec_bis$tag (Nonce Step) Bool)

(declare-fun sp$sbt$euf_hash_sec_bis$reader1 (Nonce Step) Bool)

(declare-fun sp$sbt$euf_hash_sec_bis$s$init (Nonce Step) Bool)

(declare-fun sk$u$euf_cma_hash (Message Message Nonce) Message)

(declare-subterm-relation
  sbt$nonce_main
  empty
  hash
  reader1
  tag
  m$nonce_as_msg
  c$and
  c$false
  tuple
  c$true
  c$eq
  ok
  reader2
  fail
  ko
  m$ite
  sel2of2
  c$or
  s$init
  c$not
  sel1of2)

(declare-subterm-relation
  sbt$nonce_main_bis
  empty
  hash
  reader1
  tag
  m$nonce_as_msg
  c$and
  c$false
  tuple
  c$true
  c$eq
  ok
  reader2
  fail
  ko
  m$ite
  sel2of2
  c$or
  s$init
  c$not
  sel1of2
  input)

(declare-fun sp$sbt$nonce_main$reader2 (Nonce Step) Bool)

(declare-fun sp$sbt$nonce_main$tag (Nonce Step) Bool)

(declare-fun sp$sbt$nonce_main$reader1 (Nonce Step) Bool)

(declare-fun sp$sbt$nonce_main$s$init (Nonce Step) Bool)

(declare-fun sp$sbt$nonce_main_bis$reader2 (Nonce Step) Bool)

(declare-fun sp$sbt$nonce_main_bis$tag (Nonce Step) Bool)

(declare-fun sp$sbt$nonce_main_bis$reader1 (Nonce Step) Bool)

(declare-fun sp$sbt$nonce_main_bis$s$init (Nonce Step) Bool)

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

(declare-rewrite (forall () (r$rewriteb (m$eval empty) b_empty)))

(declare-rewrite
  (forall
    ((X0 Message) (X1 Message))
    (r$rewriteb (m$eval (hash X0 X1)) (b_hash (m$eval X0) (m$eval X1)))))

(declare-rewrite
  (forall
    ((X0 Nonce))
    (r$rewriteb (m$eval (m$nonce_as_msg X0)) (b_m$nonce_as_msg X0))))

(declare-rewrite
  (forall
    ((X0 Message) (X1 Message))
    (r$rewriteb (m$eval (tuple X0 X1)) (b_tuple (m$eval X0) (m$eval X1)))))

(declare-rewrite (forall () (r$rewriteb (m$eval ok) b_ok)))

(declare-rewrite (forall () (r$rewriteb (m$eval fail) b_fail)))

(declare-rewrite (forall () (r$rewriteb (m$eval ko) b_ko)))

(declare-rewrite
  (forall
    ((X0 Message))
    (r$rewriteb (m$eval (sel2of2 X0)) (b_sel2of2 (m$eval X0)))))

(declare-rewrite
  (forall
    ((X0 Message))
    (r$rewriteb (m$eval (sel1of2 X0)) (b_sel1of2 (m$eval X0)))))

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

(assert
  (forall ((X1 Message) (X2 index)) (not (subterm sbt$euf_hash_main X1 X2))))

(assert
  (forall ((X1 Message) (X2 index)) (not (subterm sbt$euf_hash_main_bis X1 X2))))

(assert
  (forall ((X1 Message) (X2 Bool)) (not (subterm sbt$euf_hash_main X1 X2))))

(assert
  (forall ((X1 Message) (X2 Bool)) (not (subterm sbt$euf_hash_main_bis X1 X2))))

(assert
  (forall ((X1 Message) (X2 session)) (not (subterm sbt$euf_hash_main X1 X2))))

(assert
  (forall
    ((X1 Message) (X2 session))
    (not (subterm sbt$euf_hash_main_bis X1 X2))))

(assert
  (forall ((X1 Message) (X2 Nonce)) (not (subterm sbt$euf_hash_main X1 X2))))

(assert
  (forall ((X1 Message) (X2 Nonce)) (not (subterm sbt$euf_hash_main_bis X1 X2))))

(assert
  (forall
    ((X1 Message) (X2 t$Bitstring))
    (not (subterm sbt$euf_hash_main X1 X2))))

(assert
  (forall
    ((X1 Message) (X2 t$Bitstring))
    (not (subterm sbt$euf_hash_main_bis X1 X2))))

(assert (forall ((X1 Message)) (subterm sbt$euf_hash_main X1 X1)))

(assert (forall ((X1 Message)) (subterm sbt$euf_hash_main_bis X1 X1)))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (sp$sbt$euf_hash_main$reader2 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader2 X1) X4)
          (or
            (subterm sbt$euf_hash_main X3 (m$tfst_0 X1))
            (subterm sbt$euf_hash_main X3 c$true)))))))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (sp$sbt$euf_hash_main$tag X3 X4)
      (exists
        ((X1 session) (X2 index))
        (and
          (lt (tag X1 X2) X4)
          (or
            (subterm
              sbt$euf_hash_main
              X3
              (tuple
                (m$nonce_as_msg (nt X1 X2))
                (hash
                  (tuple (input (tag X1 X2)) (m$nonce_as_msg (nt X1 X2)))
                  (m$nonce_as_msg (key X2)))))
            (subterm sbt$euf_hash_main X3 c$true)))))))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (sp$sbt$euf_hash_main$reader1 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader1 X1) X4)
          (or
            (subterm sbt$euf_hash_main X3 (m$nonce_as_msg (nr X1)))
            (subterm sbt$euf_hash_main X3 c$true)))))))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (sp$sbt$euf_hash_main$s$init X3 X4)
      (exists
        ()
        (and
          (lt s$init X4)
          (or (subterm sbt$euf_hash_main X3 empty) (subterm sbt$euf_hash_main X3 c$true)))))))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (subterm sbt$euf_hash_main X3 (input X4))
      (or
        (sp$sbt$euf_hash_main$reader2 X3 X4)
        (sp$sbt$euf_hash_main$tag X3 X4)
        (sp$sbt$euf_hash_main$reader1 X3 X4)
        (sp$sbt$euf_hash_main$s$init X3 X4)))))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (sp$sbt$euf_hash_main_bis$reader2 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader2 X1) X4)
          (or
            (subterm sbt$euf_hash_main_bis X3 (m$tfst_0 X1))
            (subterm sbt$euf_hash_main_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (sp$sbt$euf_hash_main_bis$tag X3 X4)
      (exists
        ((X1 session) (X2 index))
        (and
          (lt (tag X1 X2) X4)
          (or
            (subterm
              sbt$euf_hash_main_bis
              X3
              (tuple
                (m$nonce_as_msg (nt X1 X2))
                (hash
                  (tuple (input (tag X1 X2)) (m$nonce_as_msg (nt X1 X2)))
                  (m$nonce_as_msg (key X2)))))
            (subterm sbt$euf_hash_main_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (sp$sbt$euf_hash_main_bis$reader1 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader1 X1) X4)
          (or
            (subterm sbt$euf_hash_main_bis X3 (m$nonce_as_msg (nr X1)))
            (subterm sbt$euf_hash_main_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (sp$sbt$euf_hash_main_bis$s$init X3 X4)
      (exists
        ()
        (and
          (lt s$init X4)
          (or
            (subterm sbt$euf_hash_main_bis X3 empty)
            (subterm sbt$euf_hash_main_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Message) (X4 Step))
    (=>
      (subterm sbt$euf_hash_main_bis X3 (input X4))
      (or
        (sp$sbt$euf_hash_main_bis$reader2 X3 X4)
        (sp$sbt$euf_hash_main_bis$tag X3 X4)
        (sp$sbt$euf_hash_main_bis$reader1 X3 X4)
        (sp$sbt$euf_hash_main_bis$s$init X3 X4)))))

(assert
  (forall ((X1 Nonce) (X2 index)) (not (subterm sbt$euf_hash_sec X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 index)) (not (subterm sbt$euf_hash_sec_bis X1 X2))))

(assert (forall ((X1 Nonce) (X2 Bool)) (not (subterm sbt$euf_hash_sec X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 Bool)) (not (subterm sbt$euf_hash_sec_bis X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 session)) (not (subterm sbt$euf_hash_sec X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 session)) (not (subterm sbt$euf_hash_sec_bis X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 t$Bitstring)) (not (subterm sbt$euf_hash_sec X1 X2))))

(assert
  (forall
    ((X1 Nonce) (X2 t$Bitstring))
    (not (subterm sbt$euf_hash_sec_bis X1 X2))))

(assert (forall ((X1 Nonce)) (subterm sbt$euf_hash_sec X1 X1)))

(assert (forall ((X1 Nonce)) (subterm sbt$euf_hash_sec_bis X1 X1)))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$euf_hash_sec$reader2 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader2 X1) X4)
          (or
            (subterm sbt$euf_hash_sec X3 (m$tfst_0 X1))
            (subterm sbt$euf_hash_sec X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$euf_hash_sec$tag X3 X4)
      (exists
        ((X1 session) (X2 index))
        (and
          (lt (tag X1 X2) X4)
          (or
            (subterm
              sbt$euf_hash_sec
              X3
              (tuple
                (m$nonce_as_msg (nt X1 X2))
                (hash
                  (tuple (input (tag X1 X2)) (m$nonce_as_msg (nt X1 X2)))
                  (m$nonce_as_msg (key X2)))))
            (subterm sbt$euf_hash_sec X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$euf_hash_sec$reader1 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader1 X1) X4)
          (or
            (subterm sbt$euf_hash_sec X3 (m$nonce_as_msg (nr X1)))
            (subterm sbt$euf_hash_sec X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$euf_hash_sec$s$init X3 X4)
      (exists
        ()
        (and
          (lt s$init X4)
          (or (subterm sbt$euf_hash_sec X3 empty) (subterm sbt$euf_hash_sec X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (subterm sbt$euf_hash_sec X3 (input X4))
      (or
        (sp$sbt$euf_hash_sec$reader2 X3 X4)
        (sp$sbt$euf_hash_sec$tag X3 X4)
        (sp$sbt$euf_hash_sec$reader1 X3 X4)
        (sp$sbt$euf_hash_sec$s$init X3 X4)))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$euf_hash_sec_bis$reader2 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader2 X1) X4)
          (or
            (subterm sbt$euf_hash_sec_bis X3 (m$tfst_0 X1))
            (subterm sbt$euf_hash_sec_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$euf_hash_sec_bis$tag X3 X4)
      (exists
        ((X1 session) (X2 index))
        (and
          (lt (tag X1 X2) X4)
          (or
            (subterm
              sbt$euf_hash_sec_bis
              X3
              (tuple
                (m$nonce_as_msg (nt X1 X2))
                (hash
                  (tuple (input (tag X1 X2)) (m$nonce_as_msg (nt X1 X2)))
                  (m$nonce_as_msg (key X2)))))
            (subterm sbt$euf_hash_sec_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$euf_hash_sec_bis$reader1 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader1 X1) X4)
          (or
            (subterm sbt$euf_hash_sec_bis X3 (m$nonce_as_msg (nr X1)))
            (subterm sbt$euf_hash_sec_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$euf_hash_sec_bis$s$init X3 X4)
      (exists
        ()
        (and
          (lt s$init X4)
          (or
            (subterm sbt$euf_hash_sec_bis X3 empty)
            (subterm sbt$euf_hash_sec_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (subterm sbt$euf_hash_sec_bis X3 (input X4))
      (or
        (sp$sbt$euf_hash_sec_bis$reader2 X3 X4)
        (sp$sbt$euf_hash_sec_bis$tag X3 X4)
        (sp$sbt$euf_hash_sec_bis$reader1 X3 X4)
        (sp$sbt$euf_hash_sec_bis$s$init X3 X4)))))

(assert
  (forall
    ((X0 Nonce) (X1 Message) (X2 Message))
    (=>
      (subterm sbt$euf_hash_sec X0 (hash X1 X2))
      (ite
        (= X2 (m$nonce_as_msg X0))
        (subterm sbt$euf_hash_sec X0 X1)
        (or (subterm sbt$euf_hash_sec X0 X1) (subterm sbt$euf_hash_sec X0 X2))))))

(assert
  (forall
    ((X0 Nonce) (X1 Message) (X2 Message))
    (=>
      (subterm sbt$euf_hash_sec_bis X0 (hash X1 X2))
      (ite
        (= X2 (m$nonce_as_msg X0))
        (subterm sbt$euf_hash_sec_bis X0 X1)
        (or (subterm sbt$euf_hash_sec_bis X0 X1) (subterm sbt$euf_hash_sec_bis X0 X2))))))

(declare-rewrite
  (forall
    ((X1 Message) (X2 Nonce) (X3 Message))
    (=>
      (= (m$eval X1) (m$eval (hash X3 (m$nonce_as_msg X2))))
      (and
        (or
          (subterm
            sbt$euf_hash_main
            (hash (sk$u$euf_cma_hash X1 X3 X2) (m$nonce_as_msg X2))
            X1)
          (subterm
            sbt$euf_hash_main
            (hash (sk$u$euf_cma_hash X1 X3 X2) (m$nonce_as_msg X2))
            X3)
          (subterm sbt$euf_hash_sec X2 X3)
          (subterm sbt$euf_hash_sec X2 X1))
        (=
          (m$eval (hash (sk$u$euf_cma_hash X1 X3 X2) (m$nonce_as_msg X2)))
          (m$eval X1))))))

(assert (forall ((X1 Nonce) (X2 index)) (not (subterm sbt$nonce_main X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 index)) (not (subterm sbt$nonce_main_bis X1 X2))))

(assert (forall ((X1 Nonce) (X2 Bool)) (not (subterm sbt$nonce_main X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 Bool)) (not (subterm sbt$nonce_main_bis X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 session)) (not (subterm sbt$nonce_main X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 session)) (not (subterm sbt$nonce_main_bis X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 t$Bitstring)) (not (subterm sbt$nonce_main X1 X2))))

(assert
  (forall ((X1 Nonce) (X2 t$Bitstring)) (not (subterm sbt$nonce_main_bis X1 X2))))

(assert (forall ((X1 Nonce)) (subterm sbt$nonce_main X1 X1)))

(assert (forall ((X1 Nonce)) (subterm sbt$nonce_main_bis X1 X1)))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$nonce_main$reader2 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader2 X1) X4)
          (or
            (subterm sbt$nonce_main X3 (m$tfst_0 X1))
            (subterm sbt$nonce_main X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$nonce_main$tag X3 X4)
      (exists
        ((X1 session) (X2 index))
        (and
          (lt (tag X1 X2) X4)
          (or
            (subterm
              sbt$nonce_main
              X3
              (tuple
                (m$nonce_as_msg (nt X1 X2))
                (hash
                  (tuple (input (tag X1 X2)) (m$nonce_as_msg (nt X1 X2)))
                  (m$nonce_as_msg (key X2)))))
            (subterm sbt$nonce_main X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$nonce_main$reader1 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader1 X1) X4)
          (or
            (subterm sbt$nonce_main X3 (m$nonce_as_msg (nr X1)))
            (subterm sbt$nonce_main X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$nonce_main$s$init X3 X4)
      (exists
        ()
        (and
          (lt s$init X4)
          (or (subterm sbt$nonce_main X3 empty) (subterm sbt$nonce_main X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (subterm sbt$nonce_main X3 (input X4))
      (or
        (sp$sbt$nonce_main$reader2 X3 X4)
        (sp$sbt$nonce_main$tag X3 X4)
        (sp$sbt$nonce_main$reader1 X3 X4)
        (sp$sbt$nonce_main$s$init X3 X4)))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$nonce_main_bis$reader2 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader2 X1) X4)
          (or
            (subterm sbt$nonce_main_bis X3 (m$tfst_0 X1))
            (subterm sbt$nonce_main_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$nonce_main_bis$tag X3 X4)
      (exists
        ((X1 session) (X2 index))
        (and
          (lt (tag X1 X2) X4)
          (or
            (subterm
              sbt$nonce_main_bis
              X3
              (tuple
                (m$nonce_as_msg (nt X1 X2))
                (hash
                  (tuple (input (tag X1 X2)) (m$nonce_as_msg (nt X1 X2)))
                  (m$nonce_as_msg (key X2)))))
            (subterm sbt$nonce_main_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$nonce_main_bis$reader1 X3 X4)
      (exists
        ((X1 session))
        (and
          (lt (reader1 X1) X4)
          (or
            (subterm sbt$nonce_main_bis X3 (m$nonce_as_msg (nr X1)))
            (subterm sbt$nonce_main_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (sp$sbt$nonce_main_bis$s$init X3 X4)
      (exists
        ()
        (and
          (lt s$init X4)
          (or
            (subterm sbt$nonce_main_bis X3 empty)
            (subterm sbt$nonce_main_bis X3 c$true)))))))

(assert
  (forall
    ((X3 Nonce) (X4 Step))
    (=>
      (subterm sbt$nonce_main_bis X3 (input X4))
      (or
        (sp$sbt$nonce_main_bis$reader2 X3 X4)
        (sp$sbt$nonce_main_bis$tag X3 X4)
        (sp$sbt$nonce_main_bis$reader1 X3 X4)
        (sp$sbt$nonce_main_bis$s$init X3 X4)))))

(assert
  (forall
    ((X0 Nonce) (X1 Message))
    (=>
      (= (m$eval (m$nonce_as_msg X0)) (m$eval X1))
      (subterm sbt$nonce_main X0 X1))))

