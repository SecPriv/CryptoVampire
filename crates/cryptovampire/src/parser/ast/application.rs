use cryptovampire_macros::LocationProvider;
use pest::Span;

use super::*;
#[derive(Derivative, LocationProvider)]
#[derivative(
    Debug,
    PartialEq,
    Eq,
    PartialOrd = "feature_allow_slow_enum",
    Ord = "feature_allow_slow_enum",
    Hash,
    Clone
)]
pub enum Application<L, S> {
    ConstVar {
        #[derivative(PartialOrd = "ignore", Ord = "ignore")]
        #[provider]
        span: L,
        content: S,
    },
    Application {
        #[derivative(PartialOrd = "ignore", Ord = "ignore")]
        #[provider]
        span: L,
        function: Function<L, S>,
        args: Vec<Term<L, S>>,
    },
}

impl<S, L> Application<L, S> {
    pub fn name(&self) -> &S {
        match self {
            Application::ConstVar { content, .. } => content,
            Application::Application { function, .. } => function.name(),
        }
    }

    pub fn args(&self) -> VecRef<'_, Term<L, S>> {
        match self {
            Application::ConstVar { .. } => VecRef::Empty,
            Application::Application { args, .. } => args.as_slice().into(),
        }
    }
    // }
    // impl<'a> Application<'a> {
    pub fn name_span(&self) -> &L {
        match self {
            Application::ConstVar { span, .. } => span,
            Application::Application { function, .. } => &function.0.span,
        }
    }

    pub fn span(&self) -> &L {
        match self {
            Application::ConstVar { span, .. } | Application::Application { span, .. } => span,
        }
    }

    pub fn new_app(location: L, fun: S, args: implvec!(Term<L, S>)) -> Self
    where
        L: Default,
    {
        Self::Application {
            span: location,
            function: Function::from_name(fun),
            args: args.into_iter().collect(),
        }
    }
}
boiler_plate!(Application<Span<'a>, &'a str>, 'a, application; |p| {
    let span = p.as_span();
    let mut p = p.into_inner();
    let name = p.next().unwrap();

    if let None = p.peek() {
        Ok(Application::ConstVar { span, content: name.as_str() })
    } else {
        let args : Result<Vec<_>, _> = p.map(TryInto::try_into).collect();
        Ok(Application::Application { span, function: name.try_into()?, args: args? })
    }
});

impl<'a, L, S: Display> Display for Application<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Application::ConstVar { content, .. } => content.fmt(f),
            Application::Application { function, args, .. } => {
                write!(f, "{function}({})", args.iter().format(", "))
            }
        }
    }
}

// impl<'a, S> From<S> for Application<'a, S> {
//     fn from(value: S) -> Self {
//         Application::ConstVar {
//             span: Default::default(),
//             content: value.into(),
//         }
//     }
// }
