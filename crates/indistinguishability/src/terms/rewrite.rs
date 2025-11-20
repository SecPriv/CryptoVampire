use std::borrow::Cow;
use std::fmt::Debug;

use bon::Builder;
use serde::Serialize;
use steel::rvals::Result as SResult;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
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
    fn steel_new(
        name: String,
        variables: Vec<Variable>,
        from: Formula,
        to: Formula,
    ) -> SResult<Self> {
        Ok(Self {
            from,
            to,
            variables: mk_cow!(@ variables),
            prolog_only: false,
            name: Some(name.into()),
        })
    }

    #[must_use]
    pub fn prolog_only(&self) -> bool {
        self.prolog_only
    }
}

impl Registerable for Rewrite {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module).register_fn("mk-rewrite", Self::steel_new)
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
