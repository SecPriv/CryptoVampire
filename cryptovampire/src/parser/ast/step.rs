use super::*;

/// The default init step when it's not defined. This is a function because
/// it needs to be generic.
///
/// See [HasInitStep::ref_init_step_ast] a degenericied version
#[allow(non_snake_case)]
pub fn INIT_STEP_AST<S>() -> Step<'static, S>
where
    S: From<&'static str>,
{
    let condition = Term::new_default_const(term_algebra::connective::TRUE_NAME.into());
    let message = Term::new_default_const(builtin::EMPTY_FUN_NAME.into());

    Step {
        span: Location::default(),
        name: StepName::from_s(INIT_STEP_NAME.into()),
        args: TypedArgument::default(),
        condition,
        message,
        assignements: Default::default(),
        options: Default::default(),
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Step<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: StepName<'a, S>,
    pub args: TypedArgument<'a, S>,
    pub condition: Term<'a, S>,
    pub message: Term<'a, S>,
    pub assignements: Option<Assignements<'a, S>>,
    pub options: Options<'a, S>,
}

impl<'a, S> Step<'a, S> {
    pub fn args_names(&'_ self) -> impl Iterator<Item = &'_ S> + '_ {
        self.args.bindings.iter().map(|vb| vb.variable.name())
    }
}
boiler_plate!(Step<'a>, 'a, step; |p| {
    let span = p.as_span().into();
    // dest_rule!(span in [name, args, condition, message, assignements] = p);
    let mut p = p.into_inner();
    let name = p.next().unwrap().try_into()?;
    let args = p.next().unwrap().try_into()?;
    let condition = p.next().unwrap().try_into()?;
    let message = p.next().unwrap().try_into()?;

    // temporary save the Rule obj
    let assignement_rule = p.next();
    let options_rule = p.next();

    // save the actual rule of the assignement for err management later
    let assignement_rule_rule = assignement_rule.as_ref().map(|a| a.as_rule());

    // replace it by the right object
    let assignements = assignement_rule.clone().map(TryInto::try_into).transpose();
    let options = {
        // if assignement is not a [Assignements<'a>] then either it is an [Options<'a>]
        // or the parsing should fail anyway
        let rule = if assignements.is_err() { assignement_rule } else { options_rule };
        rule.map(TryInto::try_into).transpose()
    };

    let (assignements, options) = match (assignements, options) {
        (Err(ea), Err(eo)) => {
            Err(match assignement_rule_rule {
                Some(Rule::assignements) => ea,
                _ => eo
            })
        }
        (a, o) => {
            // if a is an err, we know o isn't because of our current branch, so we ignore
            let a = a.ok().flatten();
            // if parsing o failed (i.e., there is something *and* it fail, we want to crash)
            let o = o?.unwrap_or(Options::empty(span));
            Ok((a, o))
        }
    }?;

    if let Some(np) = p.next() { // whatever happens, there shouldn't be anything left
        bail_at!(&np, "too many arguments (expected at most 6, got {})", (7 + p.len()))
    }

    Ok(Self { span, name, args, condition, message, assignements, options})
});

impl<'a, S: Display> Display for Step<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            args,
            condition,
            message,
            assignements,
            options,
            ..
        } = self;
        write!(f, "step {name}{args}\n\t{{{condition}}}\n\t{{{message}}}")?;
        if let Some(a) = assignements {
            write!(f, "\n\t{a}")?;
        }
        write!(f, "\n{options}")
    }
}
