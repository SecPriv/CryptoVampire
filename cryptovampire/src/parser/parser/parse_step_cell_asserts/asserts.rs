use crate::parser::{
    ast,
    parser::{
        parsable_trait::{Parsable, VarProxy},
        Environement,
    }, MResult,
};
use cryptovampire_lib::formula::{formula::ARichFormula, sort::builtins::BOOL};
use utils::implvec;

pub fn parse_assert_with_bvars<'a, 'str, 'bump>(
    env: &'a Environement<'bump, 'str>,
    assertion: &ast::Assertion<'str>,
    bvars: &'a mut Vec<(&'str str, VarProxy<'bump>)>,
) -> MResult<ARichFormula<'bump>> {
    let ast::Assertion { content, .. } = assertion;

    bvars.clear();
    content.parse(env, bvars, env, Some(BOOL.as_sort().into()))
}

pub fn parse_asserts_with_bvars<'a, 'str, 'bump, B>(
    env: &'a Environement<'bump, 'str>,
    assertions: implvec!(&'a ast::Assertion<'str>),
    bvars: &'a mut Vec<(&'str str, VarProxy<'bump>)>,
) -> MResult<B>
where
    B: FromIterator<ARichFormula<'bump>>,
{
    assertions
        .into_iter()
        .map(|a| parse_assert_with_bvars(env, a, bvars))
        .collect()
}
