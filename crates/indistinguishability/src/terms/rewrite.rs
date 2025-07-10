use std::borrow::Cow;

use bon::{Builder, builder};
use itertools::Itertools;
use serde::Serialize;
use steel::{rvals::Result as SResult, steel_vm::register_fn::RegisterFn};
use steel_derive::Steel;

use crate::{
    LangVar,
    input::{Registerable, var::SVar},
    terms::{CowPattern, RecFOFormula, Sort, formula_utils::convert_to_cow},
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Builder, Steel)]
pub struct Rewrite {
    /// These are the arguments to the function that one must unify with to get
    /// rewritten as [Self::to].
    #[builder(with = |x: impl std::iter::IntoIterator<Item = LangVar>| convert_to_cow(x))]
    pub from: CowPattern,
    #[builder(with = |x: impl std::iter::IntoIterator<Item = LangVar>| convert_to_cow(x))]
    pub to: CowPattern,
    #[builder(with = |x: impl std::iter::IntoIterator<Item = egg::Var>| x.into_iter().collect())]
    pub variables: cow![egg::Var],
    #[builder(with = |x: impl std::iter::IntoIterator<Item = Sort>| x.into_iter().collect())]
    pub sorts: cow![Sort],

    /// Can the rewrite be translated outside of [`golgee`] ?
    ///
    /// This mostly concern rewrites over functions that make use of [`PROLOG_ONLY`].
    ///
    /// [PROLOG_ONLY]: crate::::terms::flags::FunctionFlags::PROLOG_ONLY
    #[builder(default = false)]
    pub prolog_only: bool,

    #[builder(into)]
    pub name: Option<Cow<'static, str>>
}

impl Rewrite {
    fn steel_new(
        name: String,
        variables: Vec<SVar>,
        sorts: Vec<Sort>,
        from: RecFOFormula,
        to: RecFOFormula,
    ) -> SResult<Self> {
        fn convert(rec: &RecFOFormula) -> SResult<CowPattern> {
            let patt = rec.steel_maybe_as_recexp()?;
            let cow: CowPattern = patt.into_iter().collect_vec().into();
            Ok(cow)
        }
        let from = convert(&from)?;
        let to = convert(&to)?;
        let variables = variables
            .into_iter()
            .map(egg::Var::from)
            .collect_vec()
            .into();
        let sorts = sorts.into();

        Ok(Self {
            from,
            to,
            variables,
            sorts,
            prolog_only: false,
            name: Some(name.into())
        })
    }
    
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

#[macro_export]
macro_rules! mk_rewrite {
    ($($var:literal:$sort:ident),* in $args:expr => $to:expr) => {
        {
          $crate::terms::Rewrite::builder()
            .from($args)
            .to($to)
            .sorts({ use $crate::terms::Sort::*; [$($sort),*]})
            .variables([$(egg::Var::from_u32($var)),*])
            .build()
        }
    };
}
