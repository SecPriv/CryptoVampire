use crate::{
    formula::{formula::ARichFormula, sort::builtins::BOOL},
    implvec,
    parser::{
        ast,
        parser::{
            parsable_trait::{Parsable, VarProxy},
            Environement,
        },
        E,
    },
};

pub fn parse_assert_with_bvars<'a, 'str, 'bump>(
    env: &'a Environement<'bump, 'str>,
    assertion: &ast::Assertion<'str>,
    bvars: &'a mut Vec<(&'str str, VarProxy<'bump>)>,
) -> Result<ARichFormula<'bump>, E> {
    let ast::Assertion { content, .. } = assertion;

    bvars.clear();
    content.parse(env, bvars, env.into(), Some(BOOL.as_sort().into()))
}

pub fn parse_asserts_with_bvars<'a, 'str, 'bump, B>(
    env: &'a Environement<'bump, 'str>,
    assertions: implvec!(&'a ast::Assertion<'str>),
    bvars: &'a mut Vec<(&'str str, VarProxy<'bump>)>,
) -> Result<B, E>
where
    B: FromIterator<ARichFormula<'bump>>,
{
    assertions
        .into_iter()
        .map(|a| parse_assert_with_bvars(env, a, bvars))
        .collect()
}
