use crate::parser::{merr, parser::CellCache, E};
use cryptovampire_lib::{
    container::{allocator::ContainerTools, ScopedContainer},
    problem::cell::InnerMemoryCell,
};
use utils::implvec;

use super::super::Environement;

pub fn parse_cells<'a, 'str, 'bump>(
    env: &'a Environement<'bump, 'str>,
    cells: implvec!(&'a CellCache<'str, 'bump>),
) -> Result<(), E> {
    cells
        .into_iter()
        .try_for_each(|cc @ CellCache { cell, ast, .. }| {
            let inner = parse_cell(env, cc)?;
            let r_err = unsafe {
                <ScopedContainer as ContainerTools<InnerMemoryCell<'bump>>>::initialize(cell, inner)
            };

            match r_err {
                Err(_) => Err(merr(
                    ast.name.span(),
                    format!("step {} has already been defined", ast.name.name()),
                )),
                Ok(()) => Ok(()),
            }
        })
}

fn parse_cell<'a, 'bump, 'str>(
    _env: &'a Environement<'bump, 'str>, // mut for safety
    cell: &CellCache<'str, 'bump>,
) -> Result<InnerMemoryCell<'bump>, E> {
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
