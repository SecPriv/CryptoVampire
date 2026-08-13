use egg::{Analysis, Rewrite};
use itertools::chain;

use crate::libraries::Library;
use crate::libraries::utils::EggRewriteSink;
use crate::terms::{
    EQUIV, EQUIV_WITH_SIDE, ETA, EXISTS, FIND_SUCH_THAT, IMPLIES, IS_FRESH_NONCE, LEFT, LENGTH,
    MITE, NIL, NONCE, PROJ_1, PROJ_2, RIGHT, TUPLE, ZEROES,
};
use crate::{Lang, Problem};

/// Creates a set of base rewrite rules.
pub struct BaseRewriteLib;

impl Library for BaseRewriteLib {
    fn add_egg_rewrites<N: Analysis<Lang>>(
        &self,
        _: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
        add_logic_rewrites(sink);
        add_quantifier_rewrites(sink);
    }
}

fn add_logic_rewrites<N: Analysis<Lang>>(sink: &mut impl EggRewriteSink<N>) {
    decl_vars![a, b, c, v1, n, u, v];

    sink.extend_egg_rewrites(mk_many_rewrites! {

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
    })
}

fn add_quantifier_rewrites<N: Analysis<Lang>>(sink: &mut impl EggRewriteSink<N>) {
    decl_vars![a, b, c];

    sink.extend_egg_rewrites(mk_many_rewrites! {
        ["empty exists"]
        (EXISTS NIL #a) => (#a).
        ["empty find"]
        (FIND_SUCH_THAT NIL #a #b #c) => (MITE #a #b #c).
    })
}
