channel c.

type T  [large]
type C  [large]
type L  [large]
type R  [large]
type LP [large]

abstract f : index -> message.

abstract to_T : message -> T.
abstract from_T : T -> message.
abstract tuple_t: (T * T) -> T.

(*------------------------------------------------------------------*)
(* Hash function *)

hash myhash where m:T h:T k:L.

process Hash =
 in(c,m);
 let mT = to_T (m) in
 new k : L;
 let a = myhash(mT,k) in
 out (c, from_T(a)).


(*------------------------------------------------------------------*)
(* Asymmetric encryption *)

aenc enc, dec, pkgen where ptxt:T ctxt:C r:R pk:LP sk:L.

process Aenc =
 in(c,m);
 let mT = to_T (m) in
 new sk : L;
 let pk : LP = pkgen(sk) in
 new r : R;
 let c : C = enc(mT,r,pk) in
 let d : T = dec(c,sk) in
 out (c, empty).

(*------------------------------------------------------------------*)
(* Symmetric encryption *)

senc sencr, sdecr where ptxt:T ctxt:C r:R k:L.

process Senc =
 in(c,m);
 let mT = to_T (m) in
 new k : L;
 new r : R;
 let c : C = sencr(mT,r,k) in
 let d : T = sdecr(c,k) in
 out (c, empty).

(*------------------------------------------------------------------*)
(* Signatures encryption *)

signature sign, checksign, spk where m:T sig:C sk:L pk:LP.

process Signature(i:index) =
 in(c,m');
 out(c, empty);
 out(c, empty);
 out(c, empty);
 in(c,m);
 let my_add_a = to_T (m) in
 let my_add_b = to_T (m') in
 let mT = tuple_t(to_T (m), to_T(m')) in
 new sk : L;
 let mypk : LP = spk(sk) in
 let s : C = sign(mT,sk) in
 let ch : boolean = checksign(mT, s, mypk) in
 if (ch && true && true) then
 out (c, empty).

system !_i Signature(i) | Senc | !_i(in(c, x); in(c, y); (out(c, <x, y>) | out(c, <y, x>)) ).

lemma trival:
  forall (s:L, m:T),
    checksign(m, sign(m, s), spk(s) ) => false.
Proof.
  cryptovampire.
