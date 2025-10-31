use utils::implvec;
use utils::string_ref::StrRef;

use super::super::Environement;
use crate::container::ScopedContainer;
use crate::container::allocator::ContainerTools;
use crate::error::BaseContext;
use crate::parser::Pstr;
use crate::parser::parser::CellCache;
use crate::problem::cell::InnerMemoryCell;

pub fn parse_cells<'a, 'str, 'bump, S>(
    env: &'a Environement<'bump, 'str, S>,
    cells: implvec!(&'a CellCache<'str, 'bump, S>),
) -> crate::Result<()>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    cells
        .into_iter()
        .try_for_each(|cc @ CellCache { cell, ast, .. }| {
            let inner = parse_cell(env, cc)?;
            let r_err = unsafe {
                <ScopedContainer<'bump> as ContainerTools<InnerMemoryCell<'bump>>>::initialize(
                    cell, inner,
                )
            };

            r_err.with_context(&ast.name, || "cell already defined")
        })
}

fn parse_cell<'a, 'bump, 'str, S>(
    _env: &'a Environement<'bump, 'str, S>, // mut for safety
    cell: &CellCache<'str, 'bump, S>,
) -> crate::Result<InnerMemoryCell<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    let CellCache {
        args,
        function,
        assignements,
        ast,
        ..
    } = cell;
    let name = ast.name.name();

    let inner = InnerMemoryCell::new(
        name.to_string(),
        args.iter().cloned().collect(),
        *function,
        assignements.lock().unwrap().iter().cloned().collect(),
    );
    Ok(inner)
}
