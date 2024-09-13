use pest::Span;

use super::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ASTList<'str, L, S> {
    pub content: Vec<AST<L, S>>,
    pub begining: Option<Position<'str>>,
}

impl<'str, L, S> ASTList<'str, L, S> {
    pub fn shorten_ref<'a>(&'a self) -> &'a ASTList<'a, L, S> {
        self
    }

    pub fn as_slice(&self) -> &[AST<L, S>] {
        self.content.as_slice()
    }
}

impl<'a> TryFrom<&'a str> for ASTList<'a, Span<'a>, &'a str> {
    type Error = InputError;

    fn try_from(value: &'a str) -> MResult<Self> {
        trace!("running pest");
        let mut pairs = MainParser::parse(Rule::file, value).debug_continue()?;
        trace!("pest ran successfully");

        Ok(ASTList {
            content: pairs
                .next()
                .unwrap()
                .into_inner()
                .filter(|p| p.as_rule() == Rule::content)
                .map(|p| {
                    trace!(" --> {}", p.as_str());
                    p.try_into().debug_continue()
                })
                .try_collect()
                .debug_continue()?,
            begining: Some(Position::from_start(value)),
        })
    }
}

impl<'str, 'b, L, S> IntoIterator for &'b ASTList<'str, L, S> {
    type Item = &'b AST<L, S>;

    type IntoIter = Iter<'b, AST<L, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.content.iter()
    }
}

impl<'a, L, S: Display> Display for ASTList<'a, L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().iter().try_for_each(|ast| ast.fmt(f))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum AST<L, S> {
    Declaration(Arc<Declaration<L, S>>),
    Step(Arc<Step<L, S>>),
    Order(Arc<Order<L, S>>),
    AssertCrypto(Arc<AssertCrypto<L, S>>),
    Assert(Arc<Assert<L, S>>),
    Let(Arc<Macro<L, S>>),
}
boiler_plate!(l AST<Span<'a>, &'a str>, 'a, content; |p| {
    declaration => { Ok(AST::Declaration(Arc::new(p.try_into()?))) }
    step => { Ok(AST::Step(Arc::new(p.try_into()?))) }
    order => { Ok(AST::Order(Arc::new(p.try_into()?))) }
    assertion_crypto => { Ok(AST::AssertCrypto(Arc::new(p.try_into()?))) }
    assertion | query | lemma => { Ok(AST::Assert(Arc::new(p.try_into()?))) }
    mlet => { Ok(AST::Let(Arc::new(p.try_into()?))) }
});

impl<'a, L, S: Display> Display for AST<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(Self, |x| in self => Declaration | Step | Order | AssertCrypto | Assert | Let
        {writeln!(f, "{x}")})
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Declaration<L, S> {
    Type(DeclareType<L, S>),
    Function(DeclareFunction<L, S>),
    Cell(DeclareCell<L, S>),
}
boiler_plate!(l Declaration<Span<'a>, &'a str>, 'a, declaration; |p| {
    declare_type => { Ok(Declaration::Type(p.try_into()?)) }
    declare_function => { Ok(Declaration::Function(p.try_into()?)) }
    declare_cell => { Ok(Declaration::Cell(p.try_into()?)) }
});

impl<'a, L, S: Display> Display for Declaration<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(ast::Declaration, |x| in self => Type | Function | Cell
                    {x.fmt(f)})
    }
}
