use std::fmt::Display;

use egg::{Analysis, ENodeOrVar, MultiPattern, Pattern, PatternAst, Rewrite, Var};
use golgge::PrologRule;
use itertools::{chain, Itertools};

use super::{MacroKind, ProtocolLanguage};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Step<L> {
    id: PatternAst<L>,
    cond: PatternAst<L>,
    msg: PatternAst<L>,
}

impl<L> Step<L> {
    pub fn new(id: PatternAst<L>, cond: PatternAst<L>, msg: PatternAst<L>) -> Self {
        Self { id, cond, msg }
    }

    pub fn id(&self) -> &PatternAst<L> {
        &self.id
    }

    pub fn cond(&self) -> &PatternAst<L> {
        &self.cond
    }

    pub fn msg(&self) -> &PatternAst<L> {
        &self.msg
    }

    fn vars<'a>(&'a self) -> impl Iterator<Item = egg::Var> + use<'a, L> {
        chain![self.id(), self.cond(), self.msg()].filter_map(|f| match f {
            ENodeOrVar::Var(v) => Some(*v),
            _ => None,
        })
    }

    fn max_vars(&self) -> u32 {
        self.vars()
            .filter_map(|v| Var::as_u32(&v))
            .max()
            .unwrap_or_default()
    }
}

impl<L> Step<L>
where
    L: ProtocolLanguage,
{
    pub(crate) fn mk_unfold_rewrites<N: Analysis<L>>(
        &self,
        buf: &mut Vec<Rewrite<L, N>>,
        ptcl: &PatternAst<L>,
    ) {
        let name = self.id();

        let unfold_cond = Rewrite::new(
            format!("unfold cond {name}"),
            Pattern::<L>::from(ProtocolLanguage::app_unfold(MacroKind::Cond, name, ptcl)),
            Pattern::<L>::from(self.cond().clone()),
        )
        .unwrap();
        let unfold_msg = Rewrite::new(
            format!("unfold msg {name}"),
            Pattern::<L>::from(ProtocolLanguage::app_unfold(MacroKind::Msg, name, ptcl)),
            Pattern::<L>::from(self.msg().clone()),
        )
        .unwrap();

        let macro_to_unfold = {
            let max_var = self.max_vars();
            let var1 = egg::Var::from_u32(max_var + 1);
            let var2 = egg::Var::from_u32(max_var + 2);
            let happens: PatternAst<L> = ProtocolLanguage::app_happens(self.id());
            let mtrue: PatternAst<L> = ProtocolLanguage::app_true();

            [MacroKind::Msg, MacroKind::Cond].map(|m| {
                let pre = vec![
                    (var1, happens.clone()),
                    (var1, mtrue.clone()),
                    (var2, ProtocolLanguage::app_macro(m, name, ptcl)),
                ];
                let post = vec![(var2, ProtocolLanguage::app_unfold(m, name, ptcl))];
                Rewrite::new(
                    format!("macro {m} {name}"),
                    MultiPattern::new(pre),
                    MultiPattern::new(post),
                )
                .unwrap()
            })
        };

        buf.extend(chain![[unfold_cond, unfold_msg], macro_to_unfold]);
    }
}
