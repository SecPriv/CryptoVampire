use egg::{Analysis, Rewrite};
use itertools::{Itertools, chain};

use crate::Lang;
use crate::protocol::MacroKind;
use crate::terms::{
    ATT, EMPTY, EQUIV, EQUIV_WITH_SIDE, ETA, FROM_BOOL, Function, HAPPENS, IMPLIES, IS_FRESH_NONCE,
    LEFT, LENGTH, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_MSG, MITE, NONCE, PRED, PROJ_1,
    PROJ_2, RIGHT, TUPLE, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, ZEROES,
};

/// Creates a set of static rewrite rules.
pub fn mk_rewrites<N: Analysis<Lang>>() -> impl Iterator<Item = Rewrite<Lang, N>> {
    let m_ite = &MITE;
    decl_vars![t, t1, t2, a, b, c, v1, p, n, u, v];

    let main = mk_many_rewrites! {

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
      // ["and simp5"] (and (and #a #b) #a) => (and #a #b).
      // ["and simp6"] (AND (AND (AND #c #a) #b) #a) => (AND (AND #c #a) #b).
      // ["and simp7"] (AND (AND #b #a) (not #a)) => false.
      // ["and simp7bis"] (AND (AND #b (not #a)) #a) => false.
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

      ["fresh nonce"]
      (IS_FRESH_NONCE #n) => (#n).

      // length & co
      ["nonce length"] (LENGTH (NONCE #n)) => (ETA).
      ["length zeroes"] (LENGTH (ZEROES #a)) => (#a).
      ["length tuple"] (LENGTH (TUPLE #a #b)) => (TUPLE (LENGTH #a) (LENGTH #b)).

      // side
      ["equiv left"]
        (EQUIV_WITH_SIDE LEFT #u #v #a #b) => (EQUIV #u #v #a #b).

      ["equiv right"]
        (EQUIV_WITH_SIDE RIGHT #u #v #a #b) => (EQUIV #u #v #b #a).
    };

    let unfold = MacroKind::all()
        .into_iter()
        .flat_map(|kind| {
            let mmacro = Function::macro_from_kind(kind);
            let unfold = Function::unfold_from_kind(kind);

            [
                mk_rewrite!(format!("unfold {kind}"); (v1, v2):
          (#v1 = (HAPPENS #t), #v1 = true, #v2 = (mmacro #t #p)) =>
            (#v2 = (unfold #t #p))),
                mk_rewrite!(format!("fold {kind}"); (v1, v2):
          (#v1 = (HAPPENS #t), #v1 = true, #v2 = (unfold #t #p)) =>
            (#v2 = (mmacro #t #p))),
            ]
            .into_iter()
        })
        .collect_vec()
        .into_iter();
    chain!(main, unfold)
}
