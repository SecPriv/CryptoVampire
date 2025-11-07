use egg::{Analysis, Rewrite};
use itertools::chain;

use crate::Lang;
use crate::protocol::MacroKind;
use crate::terms::{
    ATT, BITE, EMPTY, ETA, FRESH_NONCE, FROM_BOOL, Function, HAPPENS, IMPLIES, IS_FRESH_NONCE, LENGTH, LEQ, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_MSG, MITE, NONCE, PRED, PROJ_1, PROJ_2, TUPLE, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, ZEROES
};

/// Creates a set of static rewrite rules.
pub fn mk_rewrites<N: Analysis<Lang>>() -> impl Iterator<Item = Rewrite<Lang, N>> {
    let b_ite = &BITE;
    let m_ite = &MITE;
    decl_vars![t, t1, t2, a, b, c, d, v1, x, p, n];

    let main = mk_many_rewrites! {
      ["if true"] (m_ite true #a #b) => (#a).
      ["if false"] (m_ite false #a #b) => (#b).
      // ["implies def"] (=> #a #b) => (b_ite #a #b true).
      ["if simp1"] (m_ite #x #a #a) => (#a).
      ["if simp2"] (m_ite #a #a false) => (#a).
      ["if simp3"] (m_ite #a (m_ite #a #b #c) #d) => (m_ite #a #b #d).
      ["if simp4"] (m_ite #a true false) => (#a).
      ["if eq"] (m_ite (= #a #b) #a #b) => (#a).
      // ["if and"] (m_ite (and #a #b) #c #d) => (m_ite #a (m_ite #b #c #d) #d).

      ["b_if true"] (b_ite true #a #b) => (#a).
      ["b_if false"] (b_ite false #a #b) => (#b).
      ["b_if simp1"] (b_ite #x #a #a) => (#a).
      ["b_if simp2"] (b_ite #a #a false) => (#a).
      ["b_if simp4"] (b_ite #a true false) => (#a).
      ["b_if simp3"] (b_ite #a (b_ite #a #b #c) #d) => (b_ite #a #b #d).

      ["if implies simp"] (b_ite (and #a #b) #a true) => true.
      ["if implies simp2"] (b_ite #a #a true) => true.
      ["if implies trans"] (#v1 = true, #v1 = (m_ite #a #b true), #v1 = (m_ite #b #c true)) => (#v1 = (=> #a #c)).

      ["implies simp1"] (IMPLIES true #a) => (#a).
      ["implies simp2"] (IMPLIES #a true) => true.
      ["implies simp3"] (IMPLIES false #a) => true.
      ["implies simp4"] (IMPLIES #a false) => (not #a).
      ["implies trans"] (#v1 = true, #v1 = (IMPLIES #a #b), #v1 = (IMPLIES #b #c)) => (#v1 = (=> #a #c)).

      ["p1"] (PROJ_1 (TUPLE #a #b)) => (#a).
      ["p2"] (PROJ_2 (TUPLE #a #b)) => (#b).
      ["meq refl"] (= #a #a) => true.
      ["meq symm"] (= #a #b) => (= #b #a).
      ["meq nonce"] (= (NONCE #a) (NONCE #b)) => (= #a #b).

      ["and simp1"] (and #a (and #a #b)) => (and #a #b).
      ["and simp2"] (and (and #a #b) #b) => (and #a #b).
      ["and simp3"] (and (and (and #a #b) #c) #b) => (and (and #a #b) #c).
      ["and simp4"] (and #b (and #a #b)) => (and #a #b).
      ["and true l"] (and true #a) => (#a).
      ["and true r"] (and #a true) => (#a).
      ["and false r"] (and #a false) => false.
      ["and false l"] (and false #a) => false.
      ["reverse and"] (#v1 = (and #a #b), #v1 = true) => (#a = true, #b = true).

      ["not true"] (not true) => false.
      ["not false"] (not false) => true.
      ["classical not"] (not (not #a)) => (#a).

      ["unfold_exec"]  (UNFOLD_EXEC #t #p)
        => (and (MACRO_COND #t #p) (MACRO_EXEC (PRED #t) #p)).
      ["unfold_frame"] (UNFOLD_FRAME #t #p) => (TUPLE
        (TUPLE (FROM_BOOL (MACRO_EXEC #t #p)) (m_ite (MACRO_EXEC #t #p) (MACRO_MSG #t #p) EMPTY))
        (MACRO_FRAME (PRED #t) #p)
      ).
      ["unfold_input"] (UNFOLD_INPUT #t #p) => (ATT (MACRO_FRAME (PRED #t) #p)).

      ["leq refl"] (LEQ #t #t) => true.
      ["leq pred"] (LEQ (PRED #t) #t) => true.
      ["leq pred rev"] (LEQ #t (PRED #t)) => false.

      ["happens leq"]
      (#v1 = (HAPPENS #t1), #v1 = (LEQ #t2 #t1), #v1 = true) => (#v1 = (HAPPENS #t2)).

      ["fresh nonce"]
      (IS_FRESH_NONCE #n) => (#n).

      // length & co
      ["nonce length"] (LENGTH (NONCE #n)) => (ETA).
      ["length zeroes"] (LENGTH (ZEROES #a)) => (#a).
    };

    let unfold = MacroKind::all().map(|kind| {
        let mmacro = Function::macro_from_kind(kind);
        let unfold = Function::unfold_from_kind(kind);

        mk_rewrite!(format!("unfold {kind}"); (v1, v2):
          (#v1 = (HAPPENS #t), #v1 = true, #v2 = (mmacro #t #p)) =>
            (#v2 = (unfold #t #p)))
    });
    chain!(main, unfold)
}
