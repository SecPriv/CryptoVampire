use super::*;
#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct AppMacro<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub inner: InnerAppMacro<'a, S>,
}

fn from_term_to_application<'a>(p: Pair<'a, Rule>) -> MResult<Application<'a>> {
    debug_rule!(p, term);
    let p = p.into_inner().next().unwrap();
    debug_rule!(p, inner_term);
    let p = p.into_inner().next().unwrap();
    debug_rule!(p, commun_base);
    let p = p.into_inner().next().unwrap();
    p.try_into()
}

boiler_plate!(AppMacro<'a>, 'a, macro_application; |p| {
  let span = p.as_span().into();
  let mut p = p.into_inner();
  let inner = {
      let name: MacroName = p.next().unwrap().try_into()?;

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

impl<'a, S: Display> Display for AppMacro<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum InnerAppMacro<'a, S = &'a str> {
    Msg(Application<'a, S>),
    Cond(Application<'a, S>),
    Other {
        name: MacroName<'a, S>,
        args: Vec<Term<'a, S>>,
    },
}

impl<'a, S: Display> Display for InnerAppMacro<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InnerAppMacro::Msg(arg) => write!(f, "msg!({arg})"),
            InnerAppMacro::Cond(arg) => write!(f, "cond!({arg})"),
            InnerAppMacro::Other { name, args } => {
                write!(f, "{name}({})", args.iter().format(", "))
            }
        }
    }
}
