mod step;
use std::fmt::Display;

use egg::{Id, RecExpr};
pub use step::Step;

#[allow(clippy::module_inception)]
mod protocol;
pub use protocol::Protocol;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum MacroKind {
    Frame,
    Input,
    Cond,
    Msg,
    Exec,
}

impl Display for MacroKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      write!(f, "{self:?}")
    }
}

pub trait ProtocolLanguage: egg::Language  + Display + Send + Sync + 'static {
    fn mk_happens(step: Id) -> Self;
    fn mk_macro_kind(kind: MacroKind) -> Self;
    fn mk_macro(kind: Id, step: Id, ptcl: Id) -> Self;
    fn mk_unfold(kind: Id, step: Id, ptcl: Id) -> Self;
    fn mk_true() -> Self;

    fn app_happens<Expr: AsRef<[Self]>>(step: Expr) -> RecExpr<Self> {
        apply_rec_exprs(&Self::mk_happens(0.into()), &[step])
    }

    fn app_macro_kind(kind: MacroKind) -> RecExpr<Self> {
        [Self::mk_macro_kind(kind)].into_iter().collect()
    }

    fn app_macro<Expr: AsRef<[Self]>>(kind: MacroKind, step: Expr, pctl: Expr) -> RecExpr<Self> {
        apply_rec_exprs(
            &Self::mk_macro(0.into(), 1.into(), 2.into()),
            &[
                Self::app_macro_kind(kind).as_ref(),
                step.as_ref(),
                pctl.as_ref(),
            ],
        )
    }

    fn app_unfold<Expr: AsRef<[Self]>>(kind: MacroKind, step: Expr, pctl: Expr) -> RecExpr<Self> {
        apply_rec_exprs(
            &Self::mk_unfold(0.into(), 1.into(), 2.into()),
            &[
                Self::app_macro_kind(kind).as_ref(),
                step.as_ref(),
                pctl.as_ref(),
            ],
        )
    }

    fn app_true() -> RecExpr<Self> {
      apply_rec_exprs::<_, &[_]>(&Self::mk_true(), &[])
    }
}

/// This is a shortcut for [join_recexprs]. It expects the childrens of `fun` to
/// be `0..args.length()`.
///
/// [join_recexprs]: egg::Language::join_recexprs
#[inline]
fn apply_rec_exprs<L, Expr>(fun: &L, args: &[Expr]) -> RecExpr<L>
where
    L: egg::Language,
    Expr: AsRef<[L]>,
{
    fun.join_recexprs(|i| &args[usize::from(i)])
}

impl<L:ProtocolLanguage> ProtocolLanguage for egg::ENodeOrVar<L> {
    fn mk_happens(step: Id) -> Self {
        Self::ENode(L::mk_happens(step))
    }

    fn mk_macro_kind(kind: MacroKind) -> Self {
        Self::ENode(L::mk_macro_kind(kind))
    }

    fn mk_macro(kind: Id, step: Id, ptcl: Id) -> Self {
        Self::ENode(L::mk_macro(kind, step, ptcl))
    }

    fn mk_unfold(kind: Id, step: Id, ptcl: Id) -> Self {
        Self::ENode(L::mk_unfold(kind, step, ptcl))
    }

    fn mk_true() -> Self {
        Self::ENode(L::mk_true())
    }
}