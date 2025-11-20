use itertools::{Itertools, izip};
use steel::rvals::IntoSteelVal;
use steel::steel_vm::register_fn::RegisterFn;
use steel::{SteelErr, rerrs};
use utils::econtinue_let;

use super::{FOBinder, Formula};
use crate::input::Registerable;
use crate::rexp;
use crate::terms::{EMPTY, Function, Sort, TUPLE, Variable};

impl Formula {
    // TODO: find such that
    fn steel_binder(head: FOBinder, vars: Vec<Variable>, arg: Vec<Formula>) -> Self {
        assert!(
            vars.iter().all(Variable::has_smt_sort),
            "Variable must have valid smt sort, see Variable::has_smt_sort"
        );
        let vars = vars.into_iter().map_into().collect();
        Self::Quantifier {
            head,
            vars,
            arg: arg.into(),
        }
    }

    fn steel_app(head: Function, args: Vec<Formula>) -> Result<Self, SteelErr> {
        let ret = Self::App {
            head,
            args: args.into(),
        };
        let Self::App { head, args } = &ret else {
            unreachable!()
        };

        // checks
        if head.arity() != args.len() {
            return Err(SteelErr::new(
                rerrs::ErrorKind::ArityMismatch,
                format!("expect {} got {}: ({ret})", head.arity(), args.len()),
            ));
        }

        for (i, (arg, &s)) in izip!(args.iter(), head.signature.inputs.iter()).enumerate() {
            econtinue_let!(let Some(s2) = arg.try_get_sort());
            if s2 != s {
                return Err(SteelErr::new(
                    rerrs::ErrorKind::TypeMismatch,
                    format!("epxected {s} got {s2} in argument {i:} of {ret}"),
                ));
            }
        }

        Ok(ret)
    }

    fn steel_var(var: Variable) -> Self {
        Self::Var(var)
    }

    fn steel_is_var(f: Formula) -> bool {
        matches!(f, Self::Var(_))
    }

    fn steel_get_sort(&self) -> Option<Sort> {
        self.try_get_sort()
    }

    fn steel_and(args: Vec<Self>) -> Self {
        Self::and(args)
    }

    fn steel_or(args: Vec<Self>) -> Self {
        Self::or(args)
    }

    fn steel_tuple(args: Vec<Self>) -> Self {
        args.into_iter()
            .rev()
            .reduce(|acc, e| rexp!((TUPLE #acc #e)))
            .unwrap_or(rexp!(EMPTY))
    }
}

impl Registerable for Formula {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        module
            .register_fn("mk-binderf", Self::steel_binder)
            .register_fn("mk-appf", Self::steel_app)
            .register_fn("mk-varf", Self::steel_var)
            .register_value("existsf", FOBinder::Exists.into_steelval().unwrap())
            .register_value("forallf", FOBinder::Forall.into_steelval().unwrap())
            .register_value("findstf", FOBinder::FindSuchThat.into_steelval().unwrap())
            .register_fn("is-varf", Self::steel_is_var)
            .register_fn("get-sort", Self::steel_get_sort)
            .register_type::<Self>("Formula?")
            .register_fn("string-of-formula", |f: Formula| format!("{f}"))
            .register_fn("cand", Self::steel_and)
            .register_fn("cor", Self::steel_or)
            .register_fn("tuple", Self::steel_tuple)
    }
}
