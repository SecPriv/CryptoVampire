use serde::Serialize;
use steel::rvals::{FromSteelVal, IntoSteelVal, Result as SResult};
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::terms::{Formula, Variable};

/// When the fonction is an alias
/// Represents a collection of rewrite rules for a function alias.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Alias(pub cow![AliasRewrite]);

/// A rewrite rule for an alias
/// A single rewrite rule for an alias.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Steel, Serialize)]
#[steel(equality)]
pub struct AliasRewrite {
    /// These are the arguments to the function that one must unify with to get
    /// rewritten as [Self::to].
    pub from: cow![Formula],
    pub to: Formula,
    pub variables: cow![Variable],
}

impl Alias {
    /// Returns an iterator over the `AliasRewrite` rules.
    pub fn iter(&self) -> impl Iterator<Item = &AliasRewrite> {
        self.0.iter()
    }
}

impl FromSteelVal for Alias {
    fn from_steelval(val: &steel::SteelVal) -> SResult<Self> {
        let content: Vec<_> = FromSteelVal::from_steelval(val)?;
        Ok(Alias(content.into()))
    }
}

impl IntoSteelVal for Alias {
    fn into_steelval(self) -> SResult<steel::SteelVal> {
        let Self(c) = self;
        let c = c.into_owned();
        c.into_steelval()
    }
}

mod msteel {
    use log::trace;
    use steel::SteelVal;
    use steel::rvals::{FromSteelVal, IntoSteelVal, Result as SResult};
    use steel::steel_vm::builtin::BuiltInModule;

    use super::*;
    use crate::terms::{Formula, Variable};

    #[steel_derive::declare_steel_function(name = "new-rewrite")]
    fn new(variables: Vec<Variable>, from: Vec<Formula>, to: Formula) -> SResult<SteelVal> {
        AliasRewrite {
            from: from.into(),
            to,
            variables: variables.into(),
        }
        .into_steelval()
    }

    #[steel_derive::declare_steel_function(name = "rewrite-from")]
    fn from(rw: AliasRewrite) -> Vec<Formula> {
        rw.from.to_vec()
    }

    #[steel_derive::declare_steel_function(name = "rewrite-to")]
    fn to(rw: AliasRewrite) -> Formula {
        rw.to.clone()
    }

    #[steel_derive::declare_steel_function(name = "rewrite-variables")]
    fn variables(rw: AliasRewrite) -> Vec<Variable> {
        rw.variables.to_vec()
    }

    impl Registerable for Alias {
        fn register(modules: &mut rustc_hash::FxHashMap<String, BuiltInModule>) {
            let name = "cryptovampire/ll/alias";
            let mut module = BuiltInModule::new(name);

            AliasRewrite::register_type(&mut module);
            module
                .register_native_fn_definition(FROM_DEFINITION)
                .register_native_fn_definition(TO_DEFINITION)
                .register_native_fn_definition(VARIABLES_DEFINITION)
                .register_native_fn_definition(NEW_DEFINITION);
            trace!("defined {name} scheme module");
            assert!(modules.insert(name.into(), module).is_none())
        }
    }
}
