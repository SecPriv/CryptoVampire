use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

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
        span: Default::default(),
        name: StepName::from_s(INIT_STEP_NAME.into()),
        args: TypedArgument::default(),
        condition,
        message,
        assignements: Default::default(),
        options: Default::default(),
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Step<'str, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: ASTLocation<'str>,
    pub name: StepName<'str, S>,
    pub args: TypedArgument<'str, S>,
    pub condition: Term<'str, S>,
    pub message: Term<'str, S>,
    pub assignements: Option<Assignements<'str, S>>,
    pub options: Options<'str, S>,
}

impl<'str, S> Step<'str, S> {
    pub fn args_names(&'_ self) -> impl Iterator<Item = &'_ S> + '_ {
        self.args.bindings.iter().map(|vb| vb.variable.name())
    }
}
boiler_plate!(@ Step, 'a, step; |p| {
    let span = p.as_span();
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
            let o = o?.unwrap_or(Options::empty(span.into()));
            Ok((a, o))
        }
    }?;

    if let Some(np) = p.next() { // whatever happens, there shouldn't be anything left
        crate::bail_at!(np.as_span(), "too many arguments (expected at most 6, got {})", (7 + p.len()))
    }

    Ok(Self { span: span.into(), name, args, condition, message, assignements, options})
});

impl<'str, S: Display> Display for Step<'str, S> {
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
            write!(f, "\n\t{{{a}}}")?;
        }
        write!(f, "\n{options}")
    }
}
