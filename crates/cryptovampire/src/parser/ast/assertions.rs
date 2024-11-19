use pest::Span;
use cryptovampire_macros::LocationProvider;

use crate::{error::{Location, LocationProvider}, Error};

use super::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Assert<S> {
    Assertion(Assertion< S>),
    Query(Assertion<S>),
    Lemma(Assertion< S>),
}

boiler_plate!(Assert<&'a str>, 'a, assertion | query | lemma ; |p| {
    let span = p.provide();
    let rule = p.as_rule();
    let p = p.into_inner().next().unwrap();
    match rule {
        Rule::assertion => { Ok(Assert::Assertion(p.try_into()?)) }
        Rule::query => { Ok(Assert::Query(p.try_into()?)) }
        Rule::lemma => { Ok(Assert::Lemma(p.try_into()?)) }
        r => Error::from_err(|| span,
            pest::error::ErrorVariant::ParsingError {
                positives: vec![Rule::assertion, Rule::query, Rule::lemma],
                negatives: vec![r] })
    }
});

impl<S: Display> Display for Assert<S> {
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
pub struct Assertion< S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: Location,
    pub content: Term< S>,
    pub options: Options< S>,
}
boiler_plate!(Assertion<&'a str>, 'a, assertion_inner ; |p| {
    let span = p.provide();
    destruct_rule!(span in [content, ?options] = p);
    Ok(Self {span, content, options})
});

impl<S: Display> Display for Assertion<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            content, options, ..
        } = self;
        write!(f, "{content} {options}")
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct AssertCrypto< S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: Location,
    pub name: Ident< S>,
    pub functions: Vec<Function< S>>,
    pub options: Options< S>,
}
boiler_plate!(AssertCrypto< &'a str>, 'a, assertion_crypto ; |p| {
    let span = p.provide();
    let mut p = p.into_inner();
    let name = p.next().unwrap().try_into()?;
    let mut p = p.collect_vec();
    // try to parse the option, if it fails, it means there weren't any
    let mut options  = Options::empty(span);
    let mut extra_fun = None;

    if let Some(r) = p.pop() {
        if let Rule::options = r.as_rule() {
            options = r.try_into()?;
        } else {
            extra_fun = Some(r)
        }
    }

    let functions = chain!(p.into_iter(), extra_fun).map(TryInto::try_into).try_collect()?;

    Ok(Self {span, name, functions, options})
});

impl< S: Display> Display for AssertCrypto< S> {
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
