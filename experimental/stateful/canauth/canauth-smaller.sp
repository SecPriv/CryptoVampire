
(*******************************************************************************
CANAUTH

Vincent Cheval, Véronique Cortier, and Mathieu Turuani.
“A Little More Conversation, a Little Less Action, a Lot More Satisfaction:
Global States in ProVerif”.
CSF 2018.

Sender -> Receiver : <<msg,<SIGN,ctr>>,hmac(<ctr,msg>,sk)>
                     ctr := ctr+1
Receiver -> Sender : input x, check x
                     ctr := ctr+1

An agent has a cell which is used to store a counter.
This counter is incremented at each action (receive or send).

HELPING LEMMAS
- counter increase

SECURITY PROPERTIES
- authentication
- injectivity
*******************************************************************************)

hash hmac

name sk : index -> message
name msgA : index * index -> message
name msgB : index * index -> message

abstract SIGN : message
abstract myZero : message
abstract ok : message

mutable cellA(i:index) : message = myZero
mutable cellB(i:index) : message = myZero

channel cR
channel cS

(* mySucc function for counter *)
abstract mySucc : message -> message

(* order relation for counter *)
abstract (~<) : message -> message -> bool

(* PROCESSES *)

process ReceiverA(i,j:index) =
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && cellA(i) ~< snd(snd(fst(x)))
     && snd(x) = hmac(<snd(snd(fst(x))),fst(fst(x))>,sk(i))
  then
    cellA(i) := mySucc(cellA(i));
    out(cS,ok)

process ReceiverB(i,j:index) =
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && cellB(i) ~< snd(snd(fst(x)))
     && snd(x) = hmac(<snd(snd(fst(x))),fst(fst(x))>,sk(i))
  then
    cellB(i) := mySucc(cellB(i));
    out(cS,ok)

process SenderA(i,j:index) =
  cellA(i) := mySucc(cellA(i));
  out(cR,<<msgA(i,j),<SIGN,cellA(i)>>,hmac(<cellA(i),msgA(i,j)>,sk(i))>)

process SenderB(i,j:index) =
  cellB(i) := mySucc(cellB(i));
  out(cR,<<msgB(i,j),<SIGN,cellB(i)>>,hmac(<cellB(i),msgB(i,j)>,sk(i))>)

system ((!_i !_j ReceiverA(i,j)) | (!_i !_j SenderA(i,j)) |
        (!_i !_j ReceiverB(i,j)) | (!_i !_j SenderB(i,j))).

(* AXIOMS *)

axiom orderSucc (n,n':message): n = n' => n ~< mySucc(n').

axiom orderTrans (n1,n2,n3:message): (n1 ~< n2 && n2 ~< n3) => n1 ~< n3.

axiom orderStrict (n1,n2:message): n1 = n2 => n1 ~< n2 => false.

axiom orderEqSucc (n1,n2:message):
  (n1 ~< mySucc(n2)) => ((n1 = n2) || n1 ~< n2).

(* Lemmas unsing induction *)

lemma counterIncreaseA (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellA(i)@t' ~< cellA(i)@t ||
    cellA(i)@t' = cellA(i)@t).
Proof.
  induction t.
  use orderEqSucc. use orderStrict. use orderTrans. use orderSucc.
  cryptovampire.
Qed.


lemma counterIncreaseB (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellB(i)@t' ~< cellB(i)@t ||
    cellB(i)@t' = cellB(i)@t).
Proof.
  induction t.
  use orderEqSucc. use orderStrict. use orderTrans. use orderSucc.
  cryptovampire.
Qed.


(* SECURITY PROPERTIES *)

(* 1st property w.r.t. A *)
(* This security property is actually stronger than the one stated in
   the GSVerif paper. The send action has been done by agent B, and we
   also proved a lemma regarding counters.
   Moreover, we use this 1st property (authentication) to prove the
   2nd property (injectivity). *)

print system [default].

lemma authA (i,j:index) :
  happens(ReceiverA(i,j)) => exec@ReceiverA(i,j) =>
  (exists (j':index),
    SenderB(i,j') < ReceiverA(i,j)
    && snd(output@SenderB(i,j')) = snd(input@ReceiverA(i,j))
    && fst(fst(output@SenderB(i,j'))) = fst(fst(input@ReceiverA(i,j)))
    && snd(snd(fst(output@SenderB(i,j')))) = snd(snd(fst(input@ReceiverA(i,j))))
    && cellA(i)@pred(ReceiverA(i,j)) ~< cellB(i)@SenderB(i,j')).
Proof.
  use counterIncreaseA. use counterIncreaseB.
  use orderEqSucc. use orderStrict. use orderTrans. use orderSucc.
  cryptovampire.
Qed.


(* 1st property w.r.t. B *)
lemma authB(i,j:index) :
  happens(ReceiverB(i,j)) => exec@ReceiverB(i,j) =>
  (exists (j':index),
     SenderA(i,j') < ReceiverB(i,j)
     && snd(output@SenderA(i,j')) = snd(input@ReceiverB(i,j))
     && fst(fst(output@SenderA(i,j'))) = fst(fst(input@ReceiverB(i,j)))
     && snd(snd(fst(output@SenderA(i,j')))) = snd(snd(fst(input@ReceiverB(i,j))))
     && cellB(i)@pred(ReceiverB(i,j)) ~< cellA(i)@SenderA(i,j')).
Proof.
  use counterIncreaseA. use counterIncreaseB.
  use orderEqSucc. use orderStrict. use orderTrans. use orderSucc.
  cryptovampire.
Qed.


(* 2nd property w.r.t A and A *)
lemma injectivity(i,j,j':index) :
  happens(ReceiverA(i,j)) && happens(ReceiverA(i,j')) =>
  exec@ReceiverA(i,j) && exec@ReceiverA(i,j') =>
  (fst(fst(input@ReceiverA(i,j))) = fst(fst(input@ReceiverA(i,j')))
   && snd(snd(fst(input@ReceiverA(i,j)))) = snd(snd(fst(input@ReceiverA(i,j')))))
  ||
  (fst(fst(input@ReceiverA(i,j))) <> fst(fst(input@ReceiverA(i,j')))
   && snd(snd(fst(input@ReceiverA(i,j)))) <> snd(snd(fst(input@ReceiverA(i,j'))))).



Proof.
  use counterIncreaseA. use counterIncreaseB.
  use orderEqSucc. use orderStrict. use orderTrans. use orderSucc.
  cryptovampire.
Qed.


(* 2nd property w.r.t A and B *)
lemma injectivityAB(i,j,j':index) :
  happens(ReceiverA(i,j)) && happens(ReceiverB(i,j')) =>
  exec@ReceiverA(i,j) && exec@ReceiverB(i,j') =>
  (fst(fst(input@ReceiverA(i,j))) = fst(fst(input@ReceiverB(i,j')))
   && snd(snd(fst(input@ReceiverA(i,j)))) = snd(snd(fst(input@ReceiverB(i,j')))))
  ||
  (fst(fst(input@ReceiverA(i,j))) <> fst(fst(input@ReceiverB(i,j')))
   && snd(snd(fst(input@ReceiverA(i,j)))) <> snd(snd(fst(input@ReceiverB(i,j'))))).

Proof.
  use counterIncreaseA. use counterIncreaseB.
  use orderEqSucc. use orderStrict. use orderTrans. use orderSucc.
  cryptovampire.
Qed.

lemma sanity_check : False.
Proof.
  (* use counterIncreaseA. use counterIncreaseB. *)
  (* use orderEqSucc. *) use orderStrict. use orderTrans. use orderSucc.
  cryptovampire.
Qed.

(* 2nd property w.r.t. B and B *)
(* Similar to the case w.r.t. A and A *)
