(declare-sort S 0)

(declare-fun ite (S S S) S)
(declare-fun tuple (S S) S)
(declare-fun p1 (S) S)
(declare-fun p2 (S) S)
(declare-fun meq (S S) Bool)
(declare-fun leq (S S) Bool)
(declare-fun pred (S) S)
(declare-fun init () S)
(declare-fun lt (S S) Bool)
(declare-fun T (S S) S)
(declare-fun Rs (S S) S)
(declare-fun Rf (S) S)
(declare-fun equiv (S S S S) Bool)
(declare-fun deduce (S S S S S S) Bool)
(declare-fun hash (S S) S)
(declare-fun empty () S)
(declare-fun ko () S)
(declare-fun ok () S)
(declare-fun macro (S S S) S)
(declare-fun unfold (S S S ) S)
(declare-fun happens (S) Bool)
(declare-fun frame () S)
(declare-fun exec () S)
(declare-fun msg () S)
(declare-fun cond () S)
(declare-fun input () S)
(declare-fun att (S) S)
(declare-fun j () S)
(declare-fun P1 () S)
(declare-fun P2 () S)
(declare-fun nonce (S) S)
(declare-fun mk (S S S) S)
(declare-fun k1 (S) S)
(declare-fun k2 (S S) S)
(declare-fun n (S S) S)

(assert (forall ((X S) (Y S)) (=  (meq X Y) (= X Y))))



(assert (forall ((X S) (Y S))
          (= (p1 (tuple X Y)) X)))

(assert (forall ((X S) (Y S))
          (= (p2 (tuple X Y)) Y)))

(assert (forall ((X S) (Y S))
          (= (meq X Y) (= X Y))))

(assert (forall ((X S))
          (leq X X)))

(assert (forall ((X S))
          (leq (pred X) X)))

(assert (forall ((X S))
          (leq init X)))

(assert (forall ((X S) (Y S))
          (= (lt X Y) (and (leq X Y) (not (= X Y))))))

(assert (forall ((I1 S) (J1 S) (I2 S) (J2 S))
          (=> (= (T I1 J1) (T I2 J2)) (and (= I1 I2) (= J1 J2)))))

(assert (forall ((I1 S) (J1 S) (I2 S) (J2 S))
          (=> (= (T I1 J1) (T I2 J2)) (and (= I1 I2) (= J1 J2)))))

(assert (forall ((I1 S) (J1 S) (I2 S) (J2 S))
          (=> (= (Rs I1 J1) (Rs I2 J2)) (and (= I1 I2) (= J1 J2)))))

(assert (forall ((I1 S) (I2 S))
          (=> (= (Rf I1) (Rf I2)) (= I1 I2))))

(assert (forall ((I1 S) (J1 S) (I2 S) (J2 S) (J3 S))
          (distinct (T I1 J1) (Rs I2 J2)  (Rf J3) int)))
