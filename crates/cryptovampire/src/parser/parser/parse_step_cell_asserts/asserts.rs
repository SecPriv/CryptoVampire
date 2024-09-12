use crate::parser::{
    ast,
    parser::{
        parsable_trait::{Parsable, VarProxy},
        Environement,
    },
    MResult, Pstr,
};
use crate::formula::{formula::ARichFormula, sort::builtins::BOOL};
use utils::{implvec, string_ref::StrRef};

pub fn parse_assert_with_bvars<'a, 'str, 'bump, S>(
    env: &'a Environement<'bump, 'str, S>,
    assertion: &ast::Assertion<'str, S>,
    bvars: &'a mut Vec<(S, VarProxy<'bump>)>,
) -> MResult<ARichFormula<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    let ast::Assertion { content, .. } = assertion;

    bvars.clear();
    content.parse(env, bvars, env, Some(BOOL.as_sort().into()))
}

pub fn parse_asserts_with_bvars<'a, 'str, 'bump, B, S>(
    env: &'a Environement<'bump, 'str, S>,
    assertions: implvec!(&'a ast::Assertion<'str, S>),
    bvars: &'a mut Vec<(S, VarProxy<'bump>)>,
) -> MResult<B>
where
    B: FromIterator<ARichFormula<'bump>>,
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    assertions
        .into_iter()
        .map(|a| parse_assert_with_bvars(env, a, bvars))
        .collect()
}
