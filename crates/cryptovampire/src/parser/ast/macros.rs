use cryptovampire_macros::LocationProvider;
use pest::Span;

use crate::{error::PestLocation, CVResult};

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Macro<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: L,
    pub name: MacroName<L, S>,
    pub args: TypedArgument<L, S>,
    pub term: Term<L, S>,
    pub options: Options<L, S>,
}
boiler_plate!(@ Macro, 'a, mlet ; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, args, term, ?options] = p);
    Ok(Self {span, name, args, term, options})
});

impl<L, S> Macro<L, S> {
    pub fn args_names(&'_ self) -> impl Iterator<Item = &'_ S> + '_ {
        self.args.bindings.iter().map(|vb| vb.variable.name())
    }
}

impl<L, S: Display> Display for Macro<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            args,
            term,
            options,
            ..
        } = self;
        write!(f, "let {name}{args} = {term} {options}")
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct AppMacro<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: L,
    pub inner: InnerAppMacro<L, S>,
}

fn from_term_to_application<'a>(p: Pair<'a, Rule>) -> CVResult<Application<Span<'a>, &'a str>, PestLocation> {
    debug_rule!(p, term);
    let p = p.into_inner().next().unwrap();
    debug_rule!(p, inner_term);
    let p = p.into_inner().next().unwrap();
    debug_rule!(p, commun_base);
    let p = p.into_inner().next().unwrap();
    p.try_into()
}

boiler_plate!(@ AppMacro, 'a, macro_application; |p| {
    let span = p.as_span();
    let mut p = p.into_inner();
    let inner = {
        let name: MacroName<Span, &str> = p.next().unwrap().try_into()?;

        match name.0.content.content {
            "msg" => InnerAppMacro::Msg(from_term_to_application(p.next().unwrap())?),
            "cond" => InnerAppMacro::Cond(from_term_to_application(p.next().unwrap())?),
            _ => {
                let args : Result<Vec<_>, _> = p.map(TryInto::try_into).collect();
                InnerAppMacro::Other { name, args: args? }
            }
        }
  };

  Ok(Self{span, inner})
});

impl<L, S: Display> Display for AppMacro<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum InnerAppMacro<L, S> {
    Msg(Application<L, S>),
    Cond(Application<L, S>),
    Other {
        name: MacroName<L, S>,
        args: Vec<Term<L, S>>,
    },
}

impl<L, S: Display> Display for InnerAppMacro<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InnerAppMacro::Msg(arg) => write!(f, "msg!({arg})"),
            InnerAppMacro::Cond(arg) => write!(f, "cond!({arg})"),
            InnerAppMacro::Other { name, args } => {
                write!(f, "{name}[{}]", args.iter().format(", "))
            }
        }
    }
}
