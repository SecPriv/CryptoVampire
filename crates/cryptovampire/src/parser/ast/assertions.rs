use crate::err_at;

use super::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Assert<'a, S = &'a str> {
    Assertion(Assertion<'a, S>),
    Query(Assertion<'a, S>),
    Lemma(Assertion<'a, S>),
}
boiler_plate!(Assert<'a>, 'a, assertion | query | lemma ; |p| {
    // let span = p.as_span();
    let rule = p.as_rule();
    let p = p.into_inner().next().unwrap();
    match rule {
        Rule::assertion => { Ok(Assert::Assertion(p.try_into()?)) }
        Rule::query => { Ok(Assert::Query(p.try_into()?)) }
        Rule::lemma => { Ok(Assert::Lemma(p.try_into()?)) }
        r => Err(err_at!(&p.as_span().into(), "got a {r:?} expected assertion, query or lemma"))
    }
});

impl<'a, S: Display> Display for Assert<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Assert::Assertion(a) => write!(f, "assert {a}"),
            Assert::Query(a) => write!(f, "query {a}"),
            Assert::Lemma(a) => write!(f, "lemma {a}"),
        }
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assertion<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub content: Term<'a, S>,
    pub options: Options<'a, S>,
}
boiler_plate!(Assertion<'a>, 'a, assertion_inner ; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [content, ?options] = p);
    Ok(Self {span, content, options})
});

impl<'a, S: Display> Display for Assertion<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            content, options, ..
        } = self;
        write!(f, "{content} {options}")
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct AssertCrypto<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: Ident<'a, S>,
    pub functions: Vec<Function<'a, S>>,
    pub options: Options<'a, S>,
}
boiler_plate!(AssertCrypto<'a>, 'a, assertion_crypto ; |p| {
    let span = p.as_span().into();
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

impl<'a, S: Display> Display for AssertCrypto<'a, S> {
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
