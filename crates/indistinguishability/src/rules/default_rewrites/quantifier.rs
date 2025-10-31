use egg::{Analysis, Rewrite};

use crate::terms::{EXISTS, FIND_SUCH_THAT, MITE, NIL};
use crate::{Lang, Problem};

/// Creates rewrite rules for quantifiers, including rules for empty quantifiers.
pub fn mk_rewrites<N: Analysis<Lang>>(
    _: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    decl_vars![a, b, c];

    mk_many_rewrites! {
        ["empty exists"]
        (EXISTS NIL #a) => (#a).
        ["empty find"]
        (FIND_SUCH_THAT NIL #a #b #c) => (MITE #a #b #c).
    }
    .into_iter()

    // dynamic_iter!(Tmp; A:A, B:B);
    // pbl.functions()
    //     .current_quantifiers()
    //     .flat_map(|e| match e {
    //         Quantifier::Exists(e) => Tmp::A(mk_exists_rules_one(pbl, e)),
    //         Quantifier::FindSuchThat(e) => Tmp::B(mk_fdst_rules_one(pbl, e)),
    //     })
    // [].into_iter()
}

// fn mk_exists_rules_one<'a, N: Analysis<Lang>>(
//     Problem { .. }: &'a Problem,
//     e: &'a Exists,
// ) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
//     let def = {
//         let vars = var_as_recexpr(chain![e.cvars(), e.bvars()]);
//         Rewrite::new(
//             format!("{} def", e.top_level_function().name),
//             Pattern::new(e.top_level_function().app_var(&vars)),
//             e.patt().iter().cloned().collect::<Pattern<_>>(),
//         )
//         .unwrap()
//     };

//     // TODO: sound

//     chain![[def]]
// }

// fn mk_fdst_rules_one<'a, N: Analysis<Lang>>(
//     Problem { .. }: &'a Problem,
//     e: &'a FindSuchThat,
// ) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
//     let def = {
//         let vars = var_as_recexpr(chain![e.cvars(), e.bvars()]);
//         Rewrite::new(
//             format!("{} def", e.top_level_function().name),
//             Pattern::new(e.top_level_function().app_var(&vars)),
//             Pattern::new(MITE.app_var(&[e.condition(), e.then_branch(), e.else_branch()])),
//         )
//         .unwrap()
//     };

//     // TODO: sound

//     chain![[def]]
// }
