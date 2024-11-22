use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;
#[derive(Derivative, LocationProvider, PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Clone)]
pub enum Application<'str, S> {
    ConstVar {
        #[provider]
        span: ASTLocation<'str>,
        content: S,
    },
    Application {
        #[provider]
        span: ASTLocation<'str>,
        function: Function<'str, S>,
        args: Vec<Term<'str, S>>,
    },
}

impl<'str, S> Application<'str, S> {
    pub fn name(&self) -> &S {
        match self {
            Application::ConstVar { content, .. } => content,
            Application::Application { function, .. } => function.name(),
        }
    }

    pub fn args(&self) -> VecRef<'_, Term<'_, S>> {
        match self {
            Application::ConstVar { .. } => VecRef::Empty,
            Application::Application { args, .. } => args.as_slice().into(),
        }
    }
    // }
    // impl<'a> Application<'a> {
    pub fn name_span(&self) -> &ASTLocation<'str> {
        match self {
            Application::ConstVar { span, .. } => span,
            Application::Application { function, .. } => &function.0.span,
        }
    }

    pub fn span(&self) -> &ASTLocation<'str> {
        match self {
            Application::ConstVar { span, .. } | Application::Application { span, .. } => span,
        }
    }

    pub fn new_app(location: ASTLocation<'str>, fun: S, args: implvec!(Term<'str, S>)) -> Self {
        Self::Application {
            span: location,
            function: Function::from_name(fun),
            args: args.into_iter().collect(),
        }
    }
}
boiler_plate!(Application<'a, &'a str>, 'a, application; |p| {
    let span = p.as_span();
    let mut p = p.into_inner();
    let name = p.next().unwrap();

    if p.peek().is_none() {
        Ok(Application::ConstVar { span: span.into(), content: name.as_str() })
    } else {
        let args : Result<Vec<_>, _> = p.map(TryInto::try_into).collect();
        Ok(Application::Application { span: span.into(), function: name.try_into()?, args: args? })
    }
});

impl<'a, S: Display> Display for Application<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Application::ConstVar { content, .. } => content.fmt(f),
            Application::Application { function, args, .. } => {
                write!(f, "{function}({})", args.iter().format(", "))
            }
        }
    }
}

impl<'a, S> From<S> for Application<'a, S> {
    fn from(value: S) -> Self {
        Application::ConstVar {
            span: Default::default(),
            content: value,
        }
    }
}
