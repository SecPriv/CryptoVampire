(declare-sort S 0)

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
(declare-fun happens (S) Bool)
(declare-fun macro_frame (S S) S)
(declare-fun macro_exec (S S) Bool)
(declare-fun macro_msg (S S) S)
(declare-fun macro_cond (S S) Bool)
(declare-fun macro_input (S S) S)
(declare-fun unfold_frame (S S) S)
(declare-fun unfold_exec (S S) Bool)
(declare-fun unfold_msg (S S) S)
(declare-fun unfold_cond (S S) Bool)
(declare-fun unfold_input (S S) S)
(declare-fun att (S) S)
(declare-fun j () S)
(declare-fun i () S)
(declare-fun i$2 () S)
(declare-fun i$1 () S)
(declare-fun sk$2 (S S S) S)
(declare-fun sk$1 (S S S) S)
(declare-fun P1 () S)
(declare-fun P2 () S)
(declare-fun nonce (S) S)
(declare-fun mk (S S S) S)
(declare-fun k1 (S) S)
(declare-fun k2 (S S) S)
(declare-fun n (S S) S)
(define-fun implies ((X Bool) (Y Bool)) Bool (=> X Y))

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
          (= (lt X Y) (leq X (pred Y)))))

(assert (forall ((I1 S) (J1 S) (I2 S) (J2 S))
          (=> (= (T I1 J1) (T I2 J2)) (and (= I1 I2) (= J1 J2)))))

(assert (forall ((I1 S) (J1 S) (I2 S) (J2 S))
          (=> (= (T I1 J1) (T I2 J2)) (and (= I1 I2) (= J1 J2)))))

(assert (forall ((I1 S) (J1 S) (I2 S) (J2 S))
          (=> (= (Rs I1 J1) (Rs I2 J2)) (and (= I1 I2) (= J1 J2)))))

(assert (forall ((I1 S) (I2 S))
          (=> (= (Rf I1) (Rf I2)) (= I1 I2))))

(assert (forall ((I1 S) (J1 S) (I2 S) (J2 S) (J3 S))
          (distinct (T I1 J1) (Rs I2 J2)  (Rf J3) init)))

(assert (happens  (Rf j)))
(assert (happens  (Rs i j)))
(assert (happens  (T i j)))
(assert (forall ((T S) (U S)) (=> (and (leq T U) (happens U)) (happens T))))

