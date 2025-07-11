use golgge::PrologRule;
use steel::rvals::Result as SResult;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::problem::{PRule, RcRule};
use crate::terms::RecFOFormula;

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
            .build()
            .unwrap();

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
