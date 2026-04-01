use egg::{Analysis, Rewrite};
use itertools::{Itertools, chain};

use crate::libraries::Library;
use crate::libraries::utils::EggRewriteSink;
use crate::protocol::MacroKind;
use crate::terms::{
    ATT, EMPTY, FROM_BOOL, Function, HAPPENS, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_MSG, MITE,
    PRED, TUPLE, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT,
};
use crate::{Lang, Problem};

/// Creates a set of rewrite rules for protocol unfolding.
pub struct UnfoldLib;

impl Library for UnfoldLib {
    fn add_egg_rewrites<N: Analysis<Lang>>(
        &self,
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
        add_static_unfold_rewrites(sink);
        add_macro_unfold_rewrites(sink);
        add_step_unfold_rewrites(pbl, sink);
    }
}

fn add_static_unfold_rewrites<N: Analysis<Lang>>(sink: &mut impl EggRewriteSink<N>) {
    decl_vars![t, p];

    sink.extend_egg_rewrites(mk_many_rewrites! {
      ["unfold_exec"]  (UNFOLD_EXEC #t #p)
        => (and (MACRO_COND #t #p) (MACRO_EXEC (PRED #t) #p)).
      ["unfold_frame"] (UNFOLD_FRAME #t #p) => (TUPLE
        (TUPLE (FROM_BOOL (MACRO_EXEC #t #p)) (MITE (MACRO_EXEC #t #p) (MACRO_MSG #t #p) EMPTY))
        (MACRO_FRAME (PRED #t) #p)
      ).
      ["unfold_input"] (UNFOLD_INPUT #t #p) => (ATT (MACRO_FRAME (PRED #t) #p)).
    })
}

fn add_macro_unfold_rewrites<N: Analysis<Lang>>(sink: &mut impl EggRewriteSink<N>) {
    decl_vars![t, p];
    for kind in MacroKind::all() {
        let mmacro = Function::macro_from_kind(kind);
        let unfold = Function::unfold_from_kind(kind);

        sink.extend_egg_rewrites([
            mk_rewrite!(format!("unfold {kind}"); (v1, v2):
                  (#v1 = (HAPPENS #t), #v1 = true, #v2 = (mmacro #t #p)) =>
                    (#v2 = (unfold #t #p))),
            mk_rewrite!(format!("fold {kind}"); (v1, v2):
                  (#v1 = (HAPPENS #t), #v1 = true, #v2 = (unfold #t #p)) =>
                    (#v2 = (mmacro #t #p))),
        ]);
    }
}

fn add_step_unfold_rewrites<N: Analysis<Lang>>(pbl: &Problem, sink: &mut impl EggRewriteSink<N>) {
    for ptcl in pbl.protocols() {
        let steps = ptcl.steps();
        let ptcl = ptcl.name();
        for s in steps {
            s.add_unfold_rewrites(ptcl, sink);
        }
    }
}
