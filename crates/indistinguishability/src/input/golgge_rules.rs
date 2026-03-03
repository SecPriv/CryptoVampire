use egg::Pattern;
use golgge::PrologRule;
use itertools::Itertools;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::problem::{PRule, RcRule};
use crate::terms::Formula;

/// Represents a Golgge rule, wrapping an `RcRule`.
#[derive(Clone, Steel)]
pub struct Rule(pub RcRule);

impl Rule {}

mod msteel {
    use egg::Pattern;
    use golgge::PrologRule;
    use itertools::Itertools;
    use steel::SteelVal;
    use steel::rvals::{IntoSteelVal, Result as SResult};
    use steel::steel_vm::builtin::BuiltInModule;

    use super::Rule;
    use crate::input::Registerable;
    use crate::problem::PRule;
    use crate::terms::Formula;

    #[steel_derive::declare_steel_function(name = "new-prolog")]
    fn new_prolog(name: String, from: Formula, to: Vec<Formula>) -> SResult<SteelVal> {
        let from = Pattern::from(&from);
        let to = to.iter().map_into();
        let prolog = PrologRule::builder()
            .input(from)
            .name(name)
            .deps(to)
            .build()?;

        Ok(Rule(prolog.into_mrc()).into_steelval()?)
    }

    impl Registerable for Rule {
        fn register(modules: &mut rustc_hash::FxHashMap<String, BuiltInModule>) {
            let name = "cryptovampire/ll/rule";
            let mut module = BuiltInModule::new(name);
            module.register_native_fn_definition(NEW_PROLOG_DEFINITION);
            assert!(modules.insert(name.into(), module).is_none())
        }
    }
}
