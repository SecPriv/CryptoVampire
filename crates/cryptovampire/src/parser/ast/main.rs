use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;
use crate::error::CVContext;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, LocationProvider)]
pub struct ASTList<'str, S> {
    pub content: Vec<AST<'str, S>>,
    #[provider]
    pub location: ASTLocation<'str>,
}

impl<'str, S> ASTList<'str, S> {
    pub fn as_slice(&self) -> &[AST<'str, S>] {
        self.content.as_slice()
    }
}

impl<'a> TryFrom<&'a str> for ASTList<'a, &'a str> {
    type Error = crate::Error;

    fn try_from(value: &'a str) -> crate::Result<Self> {
        trace!("running pest");
        let mut pairs =
            MainParser::parse(Rule::file, value).with_location(|| location::all(value))?;
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
            location: ASTLocation::all(value),
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

impl<'str, S: Display> Display for ASTList<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().iter().try_for_each(|ast| ast.fmt(f))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum AST<'str, S> {
    Declaration(Arc<Declaration<'str, S>>),
    Step(Arc<Step<'str, S>>),
    Order(Arc<Order<'str, S>>),
    AssertCrypto(Arc<AssertCrypto<'str, S>>),
    Assert(Arc<Assert<'str, S>>),
    Let(Arc<Macro<'str, S>>),
}
boiler_plate!(l AST<'a, &'a str>, 'a, content; |p| {
    declaration => { Ok(AST::Declaration(Arc::new(p.try_into()?))) }
    step => { Ok(AST::Step(Arc::new(p.try_into()?))) }
    order => { Ok(AST::Order(Arc::new(p.try_into()?))) }
    assertion_crypto => { Ok(AST::AssertCrypto(Arc::new(p.try_into()?))) }
    assertion | query | lemma => { Ok(AST::Assert(Arc::new(p.try_into()?))) }
    mlet => { Ok(AST::Let(Arc::new(p.try_into()?))) }
});

impl<'str, S: Display> Display for AST<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(Self, |x| in self => Declaration | Step | Order | AssertCrypto | Assert | Let
        {writeln!(f, "{x}")})
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Declaration<'str, S> {
    Type(DeclareType<'str, S>),
    Function(DeclareFunction<'str, S>),
    Cell(DeclareCell<'str, S>),
}
boiler_plate!(l Declaration<'a, &'a str>, 'a, declaration; |p| {
    declare_type => { Ok(Declaration::Type(p.try_into()?)) }
    declare_function => { Ok(Declaration::Function(p.try_into()?)) }
    declare_cell => { Ok(Declaration::Cell(p.try_into()?)) }
});

impl<'str, S: Display> Display for Declaration<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(ast::Declaration, |x| in self => Type | Function | Cell
                    {x.fmt(f)})
    }
}
