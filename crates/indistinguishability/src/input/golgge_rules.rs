use egg::PatternAst;
use golgge::PrologRule;
use steel_derive::Steel;

use crate::{
    input::Registerable,
    problem::{PRule, RcRule},
    terms::RecFOFormula,
};
use steel::{rvals::Result as SResult, steel_vm::register_fn::RegisterFn};

#[derive(Clone, Steel)]
pub struct Rule(pub RcRule);

impl Rule {
    fn new_prolog(name: String, from: RecFOFormula, to: Vec<RecFOFormula>) -> SResult<Self> {
        let from = from.steel_maybe_as_recexp()?.into();
        let to: SResult<Vec<_>> = to
            .iter()
            .map(|x| x.steel_maybe_as_recexp().map(|x| x.into()))
            .collect();
        let prolog = PrologRule::builder()
            .input(from)
            .name(name)
            .deps(to?)
            .build();

        Ok(Self(prolog.into_mrc()))
    }
}

impl Registerable for Rule {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module);
        module.register_fn("mk-prolog", Self::new_prolog)
    }
}
