use super::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ASTList<'str, S = &'str str> {
    pub content: Vec<AST<'str, S>>,
    pub begining: Option<Position<'str>>,
}

impl<'str, S> ASTList<'str, S> {
    pub fn shorten_ref<'a>(&'a self) -> &'a ASTList<'a, S> {
        self
    }
}

impl<'a> TryFrom<&'a str> for ASTList<'a, &'a str> {
    type Error = InputError;

    fn try_from(value: &'a str) -> MResult<Self> {
        let mut pairs = MainParser::parse(Rule::file, value).debug_continue()?;

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

impl<'str, 'b, S> IntoIterator for &'b ASTList<'str, S> {
    type Item = &'b AST<'str, S>;

    type IntoIter = Iter<'b, AST<'str, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.content.iter()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum AST<'a, S = &'a str> {
    Declaration(Arc<Declaration<'a, S>>),
    Step(Arc<Step<'a, S>>),
    Order(Arc<Order<'a, S>>),
    AssertCrypto(Arc<AssertCrypto<'a, S>>),
    Assert(Arc<Assert<'a, S>>),
    Let(Arc<Macro<'a, S>>),
}
boiler_plate!(l AST<'a>, 'a, content; |p| {
    declaration => { Ok(AST::Declaration(Arc::new(p.try_into()?))) }
    step => { Ok(AST::Step(Arc::new(p.try_into()?))) }
    order => { Ok(AST::Order(Arc::new(p.try_into()?))) }
    assertion_crypto => { Ok(AST::AssertCrypto(Arc::new(p.try_into()?))) }
    assertion | query | lemma => { Ok(AST::Assert(Arc::new(p.try_into()?))) }
    mlet => { Ok(AST::Let(Arc::new(p.try_into()?))) }
});

impl<'a, S: Display> Display for AST<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(Self, |x| in self => Declaration | Step | Order | AssertCrypto | Assert | Let
        {writeln!(f, "{x}")})
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Declaration<'a, S = &'a str> {
    Type(DeclareType<'a, S>),
    Function(DeclareFunction<'a, S>),
    Cell(DeclareCell<'a, S>),
}
boiler_plate!(l Declaration<'a>, 'a, declaration; |p| {
    declare_type => { Ok(Declaration::Type(p.try_into()?)) }
    declare_function => { Ok(Declaration::Function(p.try_into()?)) }
    declare_cell => { Ok(Declaration::Cell(p.try_into()?)) }
});

impl<'a, S: Display> Display for Declaration<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(ast::Declaration, |x| in self => Type | Function | Cell
                    {x.fmt(f)})
    }
}
