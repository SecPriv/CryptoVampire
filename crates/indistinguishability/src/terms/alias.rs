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

impl AliasRewrite {
    fn new_steel(variables: Vec<Variable>, from: Vec<Formula>, to: Formula) -> SResult<Self> {
        Ok(AliasRewrite {
            from: from.into(),
            to,
            variables: variables.into(),
        })
    }
}

impl Registerable for AliasRewrite {
    /// Registers the `AliasRewrite` type and its constructor with the Steel VM.
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module).register_fn("mk-alias-rwf", Self::new_steel)
    }
}
