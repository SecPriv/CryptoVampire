use super::*;
#[derive(Derivative)]
#[derivative(
    Debug,
    PartialEq,
    Eq,
    PartialOrd = "feature_allow_slow_enum",
    Ord = "feature_allow_slow_enum",
    Hash,
    Clone
)]
pub enum Application<'a, S = &'a str> {
    ConstVar {
        #[derivative(PartialOrd = "ignore", Ord = "ignore")]
        span: Location<'a>,
        content: S,
    },
    Application {
        #[derivative(PartialOrd = "ignore", Ord = "ignore")]
        span: Location<'a>,
        function: Function<'a, S>,
        args: Vec<Term<'a, S>>,
    },
}

impl<'a, S> Application<'a, S> {
    pub fn name(&self) -> &S {
        match self {
            Application::ConstVar { content, .. } => content,
            Application::Application { function, .. } => function.name(),
        }
    }

    pub fn args(&self) -> VecRef<'_, Term<'a, S>> {
        match self {
            Application::ConstVar { .. } => VecRef::Empty,
            Application::Application { args, .. } => args.as_slice().into(),
        }
    }
    // }
    // impl<'a> Application<'a> {
    pub fn name_span(&self) -> Location<'a> {
        match self {
            Application::ConstVar { span, .. } => *span,
            Application::Application { function, .. } => function.0.span,
        }
    }

    pub fn span(&self) -> Location<'a> {
        match self {
            Application::ConstVar { span, .. } | Application::Application { span, .. } => *span,
        }
    }

    pub fn new_app(fun: S, args: implvec!(Term<'a, S>)) -> Self {
        Self::Application {
            span: Default::default(),
            function: Function::from_name(fun),
            args: args.into_iter().collect(),
        }
    }
}
boiler_plate!(Application<'a>, 'a, application; |p| {
    let span = p.as_span().into();
    let mut p = p.into_inner();
    let name = p.next().unwrap();

    if let None = p.peek() {
        Ok(Application::ConstVar { span, content: name.as_str() })
    } else {
        let args : Result<Vec<_>, _> = p.map(TryInto::try_into).collect();
        Ok(Application::Application { span, function: name.try_into()?, args: args? })
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
            content: value.into(),
        }
    }
}
