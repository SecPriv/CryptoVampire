use super::CowPattern;
use crate::{
    input::{Registerable, var::SVar},
    terms::{RecFOFormula, Sort},
};
use itertools::Itertools;
use serde::Serialize;
use steel::rvals::{FromSteelVal, IntoSteelVal};
use steel::{rvals::Result as SResult, steel_vm::register_fn::RegisterFn};
use steel_derive::Steel;

/// When the fonction is an alias
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Alias(pub cow![AliasRewrite]);

/// A rewrite rule for an alias
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Steel)]
pub struct AliasRewrite {
    /// These are the arguments to the function that one must unify with to get
    /// rewritten as [Self::to].
    pub from: cow![CowPattern],
    pub to: CowPattern,
    pub variables: cow![egg::Var],
    pub sorts: cow![Sort],
}

impl Alias {
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
    fn new_steel(
        variables: Vec<SVar>,
        sorts: Vec<Sort>,
        from: Vec<RecFOFormula>,
        to: RecFOFormula,
    ) -> SResult<Self> {
        fn convert(rec: &RecFOFormula) -> SResult<CowPattern> {
            let patt = rec.steel_maybe_as_recexp()?;
            let cow: CowPattern = patt.into_iter().collect_vec().into();
            Ok(cow)
        }
        let from: SResult<Vec<_>> = from.iter().map(convert).collect();
        let from: cow![CowPattern] = from?.into();
        let to = convert(&to)?;
        let variables = variables.into_iter().map_into().collect();
        // let (variables, sorts): (Vec<_>, Vec<_>) = vars
        //     .into_iter()
        //     .map(|(a, b)| (egg::Var::from(a), b))
        //     .unzip();
        // let variables = variables.into();
        let sorts = sorts.into();
        Ok(AliasRewrite {
            from,
            to,
            variables,
            sorts,
        })
    }
}

impl Registerable for AliasRewrite {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module).register_fn("mk-alias-rwf", Self::new_steel)
    }
}

#[macro_export]
macro_rules! mk_alias {
    ($( $($var:literal:$sort:ident),* in $($args:expr),* => $to:expr),*) => {
        {
            use $crate::terms::Sort::*;
            $crate::terms::Alias(::std::borrow::Cow::Owned(vec!
            [$($crate::terms::AliasRewrite {
                    from: ::std::borrow::Cow::Owned(vec![$($crate::terms::formula_utils::convert_to_cow($args)),*]),
                    to: $crate::terms::formula_utils::convert_to_cow($to),
                    variables: ::std::borrow::Cow::Owned(vec![$(::egg::Var::from_u32($var)),*]),
                    sorts: ::std::borrow::Cow::Owned(vec![$($sort),*]),
                }
            ),*]
            ))
        }
    };
}
