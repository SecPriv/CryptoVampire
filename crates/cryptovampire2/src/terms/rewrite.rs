use std::borrow::Cow;
use std::fmt::Debug;

use bon::Builder;
use serde::Serialize;
use steel_derive::Steel;

use crate::terms::{Formula, Variable};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Builder, Steel)]
pub struct Rewrite {
    /// These are the arguments to the function that one must unify with to get
    /// rewritten as [Self::to].
    pub from: Formula,
    pub to: Formula,
    #[builder(default, with = |x: impl std::iter::IntoIterator<Item = Variable>| x.into_iter().collect())]
    pub variables: cow![Variable],

    /// Can the rewrite be translated outside of [`golgee`] ?
    ///
    /// This mostly concern rewrites over functions that make use of [`PROLOG_ONLY`].
    ///
    /// [PROLOG_ONLY]: crate::::terms::flags::FunctionFlags::PROLOG_ONLY
    #[builder(default = false)]
    pub prolog_only: bool,

    #[builder(into)]
    pub name: Option<Cow<'static, str>>,
}

impl Rewrite {
    #[must_use]
    pub fn prolog_only(&self) -> bool {
        self.prolog_only
    }
}

mod msteel {
    use ::steel::rvals::IntoSteelVal;
    use log::trace;
    use rustc_hash::FxHashMap;
    use steel::SteelVal;
    use steel::rvals::Result as SResult;
    use steel::steel_vm::builtin::BuiltInModule;

    use super::Rewrite;
    use crate::input::Registerable;
    use crate::terms::{Formula, Variable};

    #[steel_derive::declare_steel_function(name = "new")]
    fn new(
        name: String,
        variables: Vec<Variable>,
        from: Formula,
        to: Formula,
    ) -> SResult<SteelVal> {
        (Rewrite {
            from,
            to,
            variables: mk_cow!(@ variables),
            prolog_only: false,
            name: Some(name.into()),
        })
        .into_steelval()
    }

    impl Registerable for Rewrite {
        fn register(modules: &mut FxHashMap<String, BuiltInModule>) {
            let name = "cryptovampire/ll/rewrite";
            let mut module = BuiltInModule::new("cryptovampire/ll/rewrite");
            module.register_native_fn_definition(NEW_DEFINITION);
            trace!("defined {name} scheme module");
            assert!(modules.insert(name.into(), module).is_none())
        }
    }
}

impl Debug for Rewrite {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Rewrite")
            .field("from", &self.from)
            .field("to", &self.to)
            .field("variables", &self.variables)
            .field("prolog_only", &self.prolog_only)
            .field("name", &self.name)
            .finish()
    }
}
