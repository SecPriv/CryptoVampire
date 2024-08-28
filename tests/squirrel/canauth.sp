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
set postQuantumSound=false./var/folders/hs/0fptdsj112q2nsknls1433x00000gn/T/cryptovampire-stdin855325.json

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


(* LIBRARIES *)

include Basic.

(* f_apply *)

lemma fst_apply (x,y : message) : x = y => fst(x) = fst(y).
Proof. auto. Qed.

lemma snd_apply (x,y : message) : x = y => snd(x) = snd(y).
Proof. auto. Qed.

(* AXIOMS *)

axiom orderSucc (n,n':message): n = n' => n ~< mySucc(n').

axiom orderTrans (n1,n2,n3:message): (n1 ~< n2 && n2 ~< n3) => n1 ~< n3.

axiom orderStrict (n1,n2:message): n1 = n2 => n1 ~< n2 => false.

axiom orderEqSucc (n1,n2:message):
  (n1 ~< mySucc(n2)) => ((n1 = n2) || n1 ~< n2).



(* The counter cellA(i) strictly increases 
   at each action SenderA(i,j) / ReceiverA(i,j). *)

lemma counterIncreaseUpdateSA(i,j:index):
  happens(SenderA(i,j)) =>
  cond@SenderA(i,j) =>
  cellA(i)@pred(SenderA(i,j)) ~< cellA(i)@SenderA(i,j).
Proof.
  use orderSucc. use orderEqSucc. use orderStrict. use orderTrans.
  cryptovampire.
Qed.
