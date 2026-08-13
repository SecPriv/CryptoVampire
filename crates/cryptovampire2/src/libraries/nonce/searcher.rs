use std::borrow::Cow;
use std::ops::ControlFlow;

use bon::bon;
use egg::{Analysis, EGraph, Id};
use utils::implvec;

use crate::libraries::nonce::searcher::nonce_builder::SetContent;
use crate::libraries::utils::formula_builder::RefFormulaBuilder;
use crate::libraries::utils::{DefaultAux, SyntaxSearcher};
use crate::terms::{Formula, Function, NONCE};
use crate::{Lang, Problem, rexp};

/// A nonce to be searched for
#[derive(Debug, Clone)]
pub struct Nonce {
    /// The content of the nonce.
    content: Formula,
    /// The name of the nonce.
    #[allow(dead_code)]
    name: Cow<'static, str>,
}

impl Nonce {
    /// Creates a new nonce from a function and its arguments
    #[allow(dead_code)]
    pub fn new_from_args(head: Function, args: implvec!(Formula)) -> Self {
        Self::builder()
            .name(head.name.clone())
            .content(Formula::app(head, args.into_iter().collect()))
            .build()
    }

    /// Returns the content of the nonce as a `RecFOFormula`
    pub fn as_recformula(&self) -> Formula {
        self.content.clone()
    }
}

impl SyntaxSearcher for Nonce {
    type Aux = DefaultAux;
    /// Returns a debug name for the nonce searcher.
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("nonce")
    }

    /// Checks if the given function represents an instance of a nonce.
    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        fun == &NONCE
    }

    /// Processes an instance of a nonce, adding a leaf to the formula builder.
    fn process_instance(
        &self,
        _: &Problem,
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[Formula],
    ) -> ControlFlow<()> {
        assert_eq!(fun, &NONCE);
        tr!("found nonce!");
        let arg = args.iter().next().expect("NONCE need a parameter");

        builder.add_leaf(rexp!((distinct #arg #(self.as_recformula()))));
        ControlFlow::Break(())
    }
}

// impl EgraphSearcher for Nonce {}

#[bon]
impl Nonce {
    /// Creates a new nonce
    #[builder(builder_type = NonceBuilder)]
    pub fn new(
        content: Formula,
        #[builder(into, default = format!("{content}"))] name: Cow<'static, str>,
    ) -> Self {
        Self { content, name }
    }
}
