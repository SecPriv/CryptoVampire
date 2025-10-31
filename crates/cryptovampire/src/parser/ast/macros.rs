use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;
use crate::Result;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Macro<'str, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: ASTLocation<'str>,
    pub name: MacroName<'str, S>,
    pub args: TypedArgument<'str, S>,
    pub term: Term<'str, S>,
    pub options: Options<'str, S>,
}
boiler_plate!(@ Macro, 'a, mlet ; |p| {
    let span = p.as_span();
    destruct_rule!(span in [name, args, term, ?options] = p);
    Ok(Self {span:span.into(), name, args, term, options})
});

impl<'str, S> Macro<'str, S> {
    pub fn args_names(&'_ self) -> impl Iterator<Item = &'_ S> + '_ {
        self.args.bindings.iter().map(|vb| vb.variable.name())
    }
}

impl<'str, S: Display> Display for Macro<'str, S> {
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
pub struct AppMacro<'str, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: ASTLocation<'str>,
    pub inner: InnerAppMacro<'str, S>,
}

fn from_term_to_application(p: Pair<'_, Rule>) -> Result<Application<'_, &str>> {
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
        let name: MacroName<'a, &str> = p.next().unwrap().try_into()?;

        match name.0.content.content {
            "msg" => InnerAppMacro::Msg(from_term_to_application(p.next().unwrap())?),
            "cond" => InnerAppMacro::Cond(from_term_to_application(p.next().unwrap())?),
            _ => {
                let args : Result<Vec<_>> = p.map(TryInto::try_into).collect();
                InnerAppMacro::Other { name, args: args? }
            }
        }
  };

  Ok(Self{span: span.into(), inner})
});

impl<'str, S: Display> Display for AppMacro<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum InnerAppMacro<'str, S> {
    Msg(Application<'str, S>),
    Cond(Application<'str, S>),
    Other {
        name: MacroName<'str, S>,
        args: Vec<Term<'str, S>>,
    },
}

impl<'str, S: Display> Display for InnerAppMacro<'str, S> {
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
