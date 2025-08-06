use egg::{Analysis, ENodeOrVar, Rewrite, Var};
use itertools::chain;

use crate::Lang;
use crate::protocol::MacroKind;
use crate::terms::{
    ATT, BITE, EMPTY, FROM_BOOL, Function, HAPPENS, LEQ, MACRO_COND, MACRO_EXEC, MACRO_FRAME,
    MACRO_MSG, MITE, PRED, PROJ_1, PROJ_2, TUPLE, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT,
};

macro_rules! mk_many_rewrites {
    (
        $(
            [$name:literal]
            $from:tt => $to:tt
        .)*
    ) => {
       vec![
            $(
                mk_rewrite!($name; $from => $to)
            ),*
        ]
    }
}

pub fn mk_rewrites<N: Analysis<Lang>>() -> impl Iterator<Item = Rewrite<Lang, N>> {
    let b_ite = &BITE;
    let m_ite = &MITE;
    let [t, t1, t2, a, b, c, d, v1, v2, x, p] =
        ::std::array::from_fn(|i| Var::from_u32(i as u32)).map(ENodeOrVar::Var);

    let main = mk_many_rewrites! {
      ["if true"] (m_ite true #a #b) => (#a).
      ["if false"] (m_ite false #a #b) => (#b).
      ["implies def"] (=> #a #b) => (b_ite #a #b true).
      ["if simp1"] (m_ite #x #a #a) => (#a).
      ["if simp2"] (m_ite #a #a false) => (#a).
      ["if simp3"] (m_ite #a (m_ite #a #b #c) #d) => (m_ite #a #b #d).
      ["if simp4"] (m_ite #a true false) => (#a).

      ["b_if true"] (b_ite true #a #b) => (#a).
      ["b_if false"] (b_ite false #a #b) => (#b).
      ["b_if simp1"] (b_ite #x #a #a) => (#a).
      ["b_if simp2"] (b_ite #a #a false) => (#a).
      ["b_if simp4"] (b_ite #a true false) => (#a).
      ["b_if simp3"] (b_ite #a (b_ite #a #b #c) #d) => (b_ite #a #b #d).

      ["implies simp"] (b_ite (and #a #b) #a true) => true.
      ["implies simp2"] (b_ite #a #a true) => true.
      ["classical not"] (not (not #a)) => (#a).
      // %["and symm"] (and #a #b) => (and #b #a).
      // %["and simpl"] (and #a #a) => (#a).
      // %["and assoc"] (and #a (and #b #c)) => (and (and #a #b) #c).
      ["and def"] (and #a #b) => (b_ite #a #b false).

      ["not def"] (not #a) => (b_ite #a false true).
      ["meq true"] (#v1 = (= #a #b), #v1 = true) => (#a = #b).
      ["reverse and"] (#v1 = (b_ite #a #b false), #v1 = true) => (#a = true, #b = true).
      ["implies trans"] (#v1 = true, #v1 = (m_ite #a #b true), #v1 = (m_ite #b #c true)) => (#v1 = (=> #a #c)).
      ["p1"] (PROJ_1 (TUPLE #a #b)) => (#a).
      ["p2"] (PROJ_2 (TUPLE #a #b)) => (#b).
      ["meq refl"] (= #a #a) => true.
      ["meq symm"] (= #a #b) => (= #b #a).

      ["bif true"] (b_ite true #a #b) => (#a).
      ["bif false"] (b_ite false #a #b) => (#b).
      ["bif simp1"] (b_ite #x #a #a) => (#a).
      ["bif simp3"] (b_ite #a (b_ite #a #b #c) #d) => (b_ite #a #b #d).
      ["and simp1"] (and #a (and #a #b)) => (and #a #b).
      ["and simp2"] (and (and #a #b) #b) => (and #a #b).
      ["and simp3"] (and (and (and #a #b) #c) #b) => (and (and #a #b) #c).

      ["unfold_exec"]  (UNFOLD_EXEC #t #p)
        => (and (MACRO_COND #t #p) (MACRO_EXEC (PRED #t) #p)).
      ["unfold_frame"] (UNFOLD_FRAME #t #p) => (TUPLE
        (TUPLE (FROM_BOOL (MACRO_EXEC #t #p)) (m_ite (MACRO_EXEC #t #p) (MACRO_MSG #t #p) EMPTY))
        (MACRO_FRAME (PRED #t) #p)
      ).
      ["unfold_input"] (UNFOLD_INPUT #t #p) => (ATT (MACRO_FRAME (PRED #t) #p)).

      ["leq refl"] (LEQ #t #t) => true.
      ["leq pred"] (LEQ (PRED #t) #t) => true.

      ["happens leq"]
      (#v1 = (HAPPENS #t1), #v1 = (LEQ #t2 #t1), #v1 = true) => (#v1 = (HAPPENS #t2)).
    };

    let unfold = MacroKind::all().map(|kind| {
        let mmacro = Function::macro_from_kind(kind);
        let unfold = Function::unfold_from_kind(kind);

        mk_rewrite!(format!("unfold {kind}"); 
          (#v1 = (HAPPENS #t), #v1 = true, #v2 = (mmacro #t #p)) =>
            (#v2 = (unfold #t #p)))
    });
    chain!(main, unfold)
}
