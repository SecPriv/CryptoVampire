use egg::{Analysis, Rewrite};
use itertools::{Itertools, chain};

use crate::protocol::MacroKind;
use crate::terms::{
    ATT, EMPTY, FROM_BOOL, Function, HAPPENS, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_MSG, MITE,
    PRED, TUPLE, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT,
};
use crate::{Lang, Problem};

/// Creates a set of rewrite rules for protocol unfolding.
pub fn mk_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain![
        mk_static_unfold_rewrites(),
        mk_macro_unfold_rewrites(),
        mk_step_unfold_rewrites(pbl)
    ]
}

fn mk_static_unfold_rewrites<N: Analysis<Lang>>() -> impl Iterator<Item = Rewrite<Lang, N>> {
    let m_ite = &MITE;
    decl_vars![t, p];

    mk_many_rewrites! {
      ["unfold_exec"]  (UNFOLD_EXEC #t #p)
        => (and (MACRO_COND #t #p) (MACRO_EXEC (PRED #t) #p)).
      ["unfold_frame"] (UNFOLD_FRAME #t #p) => (TUPLE
        (TUPLE (FROM_BOOL (MACRO_EXEC #t #p)) (m_ite (MACRO_EXEC #t #p) (MACRO_MSG #t #p) EMPTY))
        (MACRO_FRAME (PRED #t) #p)
      ).
      ["unfold_input"] (UNFOLD_INPUT #t #p) => (ATT (MACRO_FRAME (PRED #t) #p)).
    }
    .into_iter()
}

fn mk_macro_unfold_rewrites<N: Analysis<Lang>>() -> impl Iterator<Item = Rewrite<Lang, N>> {
    decl_vars![t, p];
    MacroKind::all()
        .into_iter()
        .flat_map(move |kind| {
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
        .into_iter()
}

fn mk_step_unfold_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.protocols().iter().flat_map(|ptcl| {
        let steps = ptcl.steps();
        let ptcl = ptcl.name();
        steps.iter().flat_map(|s| s.mk_unfold_rewrites(ptcl))
    })
}
