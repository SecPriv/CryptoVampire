use itertools::{Itertools, izip};
use log::trace;
use steel::rvals::{IntoSteelVal, Result as SResult};
use steel::steel_vm::builtin::BuiltInModule;
use steel::{SteelErr, SteelVal, rerrs};
use utils::econtinue_let;

use super::{FOBinder, Formula};
use crate::input::Registerable;
use crate::rexp;
use crate::terms::{EMPTY, Function, Sort, TUPLE, Variable};

// TODO: find such that
#[steel_derive::declare_steel_function(name = "binder")]
fn binder(head: FOBinder, vars: Vec<Variable>, arg: Vec<Formula>) -> SResult<SteelVal> {
    if !vars.iter().all(Variable::has_smt_sort) {
        return Err(rerrs::SteelErr::new(
            rerrs::ErrorKind::Generic,
            "Variable must have valid smt sort, see Variable::has_smt_sort".into(),
        ));
    }

    let vars = vars.into_iter().map_into().collect();
    Formula::Quantifier {
        head,
        vars,
        arg: arg.into(),
    }
    .into_steelval()
}

#[steel_derive::declare_steel_function(name = "app")]
fn app(head: Function, args: Vec<Formula>) -> SResult<SteelVal> {
    let ret = Formula::App {
        head,
        args: args.into(),
    };
    let Formula::App { head, args } = &ret else {
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

    ret.into_steelval()
}

#[steel_derive::declare_steel_function(name = "var")]
fn var(var: Variable) -> Formula {
    Formula::Var(var)
}

#[steel_derive::declare_steel_function(name = "var?")]
fn is_var(f: Formula) -> bool {
    matches!(f, Formula::Var(_))
}

#[steel_derive::declare_steel_function(name = "binder?")]
fn is_binder(f: Formula) -> bool {
    matches!(f, Formula::Quantifier { .. })
}

#[steel_derive::declare_steel_function(name = "app?")]
fn is_app(f: Formula) -> bool {
    matches!(f, Formula::App { .. })
}

/// Destruct a [Formula] into its component. Returns them as lists of SteelVal.
/// Use [is_var], [is_binder] and [is_app] to know which variant it is.
#[steel_derive::declare_steel_function(name = "destruct")]
fn destruct(f: Formula) -> SResult<SteelVal> {
    match f {
        Formula::Quantifier { head, vars, arg } => vec![
            head.into_steelval()?,
            vars.to_vec().into_steelval()?,
            arg.to_vec().into_steelval()?,
        ]
        .into_steelval(),
        Formula::App { head, args } => {
            vec![head.into_steelval()?, args.to_vec().into_steelval()?].into_steelval()
        }
        Formula::Var(variable) => vec![variable].into_steelval(),
    }
}

#[steel_derive::declare_steel_function(name = "get_sort")]
fn get_sort(s: Formula) -> Option<Sort> {
    s.try_get_sort()
}

#[steel_derive::declare_steel_function(name = "cand")]
fn cand(args: Vec<Formula>) -> Formula {
    Formula::and(args)
}

#[steel_derive::declare_steel_function(name = "cor")]
fn cor(args: Vec<Formula>) -> Formula {
    Formula::or(args)
}

#[steel_derive::declare_steel_function(name = "ctuple")]
fn stuple(args: Vec<Formula>) -> Formula {
    args.into_iter()
        .rev()
        .reduce(|acc, e| rexp!((TUPLE #acc #e)))
        .unwrap_or(rexp!(EMPTY))
}

impl Registerable for Formula {
    fn register(modules: &mut rustc_hash::FxHashMap<String, BuiltInModule>) {
        let name = "cryptovampire/ll/formula";
        let mut module = BuiltInModule::new(name);
        module
            .register_type::<Self>("Formula?")
            .register_native_fn_definition(BINDER_DEFINITION)
            .register_native_fn_definition(APP_DEFINITION)
            .register_native_fn_definition(VAR_DEFINITION)
            .register_native_fn_definition(IS_VAR_DEFINITION)
            .register_native_fn_definition(IS_APP_DEFINITION)
            .register_native_fn_definition(IS_BINDER_DEFINITION)
            .register_native_fn_definition(DESTRUCT_DEFINITION)
            .register_native_fn_definition(GET_SORT_DEFINITION)
            .register_native_fn_definition(CAND_DEFINITION)
            .register_native_fn_definition(COR_DEFINITION)
            .register_native_fn_definition(STUPLE_DEFINITION)
            .register_value("binder->exists", FOBinder::Exists.into_steelval().unwrap())
            .register_value("binder->forall", FOBinder::Forall.into_steelval().unwrap())
            .register_value(
                "binder->findst",
                FOBinder::FindSuchThat.into_steelval().unwrap(),
            );
        trace!("defined {name} scheme module");
        assert!(modules.insert(name.into(), module).is_none())
    }
}
