use egg::Pattern;
use golgge::PrologRule;
use itertools::Itertools;
use steel::rvals::Result as SResult;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::problem::{PRule, RcRule};
use crate::terms::Formula;

/// Represents a Golgge rule, wrapping an `RcRule`.
#[derive(Clone, Steel)]
pub struct Rule(pub RcRule);

impl Rule {
    fn new_prolog(name: String, from: Formula, to: Vec<Formula>) -> SResult<Self> {
        let from = Pattern::from(&from);
        let to = to.iter().map_into();
        let prolog = PrologRule::builder()
            .input(from)
            .name(name)
            .deps(to)
            .build()
            .unwrap();

        Ok(Self(prolog.into_mrc()))
    }
}

impl Registerable for Rule {
    /// Registers the `Rule` type and its constructor with the Steel VM.
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module);
        module.register_fn("mk-prolog", Self::new_prolog)
    }
}
