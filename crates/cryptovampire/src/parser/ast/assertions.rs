use cryptovampire_macros::LocationProvider;
use location::{ASTLocation, AsASTLocation};

use super::*;
use crate::Error;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Assert<'str, S> {
    Assertion(Assertion<'str, S>),
    Query(Assertion<'str, S>),
    Lemma(Assertion<'str, S>),
}

boiler_plate!(Assert<'a, &'a str>, 'a, assertion | query | lemma ; |p| {
    let span = p.ast_location();
    let rule = p.as_rule();
    let p = p.into_inner().next().unwrap();
    match rule {
        Rule::assertion => { Ok(Assert::Assertion(p.try_into()?)) }
        Rule::query => { Ok(Assert::Query(p.try_into()?)) }
        Rule::lemma => { Ok(Assert::Lemma(p.try_into()?)) }
        r => Error::from_err(span.as_location(),
            pest::error::ErrorVariant::ParsingError {
                positives: vec![Rule::assertion, Rule::query, Rule::lemma],
                negatives: vec![r] })
    }
});

impl<'str, S: Display> Display for Assert<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Assert::Assertion(a) => write!(f, "assert {a}"),
            Assert::Query(a) => write!(f, "query {a}"),
            Assert::Lemma(a) => write!(f, "lemma {a}"),
        }
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assertion<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub content: Term<'str, S>,
    pub options: Options<'str, S>,
}
boiler_plate!(Assertion<'a, &'a str>, 'a, assertion_inner ; |p| {
    let span = p.as_span();
    destruct_rule!(span in [content, ?options] = p);
    Ok(Self {span:span.into(), content, options})
});

impl<'str, S: Display> Display for Assertion<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            content, options, ..
        } = self;
        write!(f, "{content} {options}")
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct AssertCrypto<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub name: Ident<'str, S>,
    pub functions: Vec<Function<'str, S>>,
    pub options: Options<'str, S>,
}
boiler_plate!(AssertCrypto< 'a, &'a str>, 'a, assertion_crypto ; |p| {
    let span = p.as_span();
    let mut p = p.into_inner();
    let name = p.next().unwrap().try_into()?;
    let mut p = p.collect_vec();
    // try to parse the option, if it fails, it means there weren't any
    let mut options  = Options::empty(span.into());
    let mut extra_fun = None;

    if let Some(r) = p.pop() {
        if let Rule::options = r.as_rule() {
            options = r.try_into()?;
        } else {
            extra_fun = Some(r)
        }
    }

    let functions = chain!(p.into_iter(), extra_fun).map(TryInto::try_into).try_collect()?;

    Ok(Self {span:span.into(), name, functions, options})
});

impl<'str, S: Display> Display for AssertCrypto<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            functions,
            options,
            ..
        } = self;
        write!(
            f,
            "assert-crypto {name} {} {options}",
            functions.iter().format(" ")
        )
    }
}
