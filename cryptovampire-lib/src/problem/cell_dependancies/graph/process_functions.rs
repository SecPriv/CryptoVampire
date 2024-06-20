use crate::formula::formula::ARichFormula;
use crate::formula::formula::RichFormula;
use crate::formula::function::inner::term_algebra::TermAlgebra;
use crate::problem::cell::Assignement;

use utils::arc_into_iter::ArcIntoIter;

use super::super::call::InputCall;

use utils::utils::repeat_n_zip;

use super::InnerCellCall;

use super::ToNode;

use crate::formula::function::InnerFunction;

use crate::formula::sort::builtins::STEP;

use crate::formula::variable::Variable;

use crate::formula::utils::formula_iterator::IteratorFlags;

use crate::formula::utils::formula_iterator::FormulaIterator;

use super::super::call::StepCall;

use super::FromNode;

use super::Edges;

use super::GlobNode;

use std::cell::RefCell;

use crate::problem::step::Step;

/// populate `input_edges` and `edges` using the content seen in the step definitions
///
/// The `pile` is used for efficiency
pub(crate) fn process_steps<'bump>(
    steps: &Vec<Step<'bump>>,
    pile: &RefCell<Vec<((), ARichFormula<'bump>)>>,
    cells: &Vec<GlobNode<'bump>>,
    input_edges: &mut Vec<Edges<'bump>>,
    edges: &mut Vec<Edges<'bump>>,
) {
    for step in steps {
        let from = FromNode::Input { step: *step };
        let _step_call = StepCall::Step(*step);
        let mut pile = pile.borrow_mut();
        pile.clear();
        pile.extend([step.message_arc(), step.condition_arc()].map(|x| ((), x.shallow_copy())));

        let iter = FormulaIterator {
            pile,
            passed_along: Some(()),
            flags: IteratorFlags::QUANTIFIER,
            f: |_, f: ARichFormula<'bump>| match f.as_ref() {
                RichFormula::Var(Variable { sort, .. }) if sort == &STEP.as_sort() => {
                    panic!("time point variable are not allowed in protocol")
                }
                RichFormula::Fun(fun, args) => match fun.as_inner() {
                    InnerFunction::TermAlgebra(TermAlgebra::Cell(c)) => {
                        let c = c.memory_cell();
                        let cell_idx = cells.iter().position(|g| g.cell == c).unwrap();
                        let to_node = ToNode::CellCall(InnerCellCall {
                            cell_idx,
                            timepoint: StepCall::General(args.last().unwrap().shallow_copy()),
                            args: args[..args.len() - 1].iter().cloned().collect(),
                        });
                        (Some(to_node), repeat_n_zip((), [].into()))
                    }
                    InnerFunction::Step(_s) => {
                        let to_node = ToNode::Input(InputCall {
                            step: StepCall::General(f),
                        });
                        (Some(to_node), repeat_n_zip((), [].into()))
                    }
                    _ => (None, repeat_n_zip((), ArcIntoIter::from(args))),
                },
                _ => (None, repeat_n_zip((), [].into())),
            },
        };

        iter.for_each(|to_node| match &to_node {
            ToNode::Input(_) => input_edges.push(Edges {
                from: from.clone(),
                to: to_node,
            }),
            ToNode::CellCall(_) => edges.push(Edges {
                from: from.clone(),
                to: to_node,
            }),
        })
    }
}

/// populate `input_edges` and `edges` using the content seen in the cell definitions
///
/// The `pile` is used for efficiency
pub(crate) fn process_cell<'bump>(
    _steps: &Vec<Step<'bump>>,
    pile: &RefCell<Vec<((), ARichFormula<'bump>)>>,
    cells: &Vec<GlobNode<'bump>>,
    input_edges: &mut Vec<Edges<'bump>>,
    edges: &mut Vec<Edges<'bump>>,
) {
    for (cell_idx, GlobNode { cell, .. }) in cells.iter().enumerate() {
        for Assignement {
            step,
            args,
            content,
            fresh_vars: _,
        } in cell.assignements()
        {
            let from = FromNode::CellCall(InnerCellCall {
                cell_idx,
                timepoint: StepCall::Step(*step),
                args: args.clone(),
            });
            let mut pile = pile.borrow_mut();
            pile.clear();
            pile.extend([((), content.shallow_copy())]);

            let iter = FormulaIterator {
                pile,
                passed_along: Some(()),
                flags: IteratorFlags::QUANTIFIER,
                f: |_, f: ARichFormula<'bump>| match f.as_ref() {
                    RichFormula::Fun(fun, args) => match fun.as_inner() {
                        InnerFunction::TermAlgebra(TermAlgebra::Cell(c)) => {
                            let c = c.memory_cell();
                            let cell = cells.iter().position(|g| g.cell == c).unwrap();
                            let to_node = ToNode::CellCall(InnerCellCall {
                                cell_idx: cell,
                                timepoint: StepCall::General(args.last().unwrap().shallow_copy()),
                                args: args[..args.len() - 1].iter().cloned().collect(),
                            });
                            (Some(to_node), repeat_n_zip((), [].into()))
                        }
                        InnerFunction::Step(_s) => {
                            let to_node = ToNode::Input(InputCall {
                                step: StepCall::General(f),
                            });
                            (Some(to_node), repeat_n_zip((), [].into()))
                        }
                        _ => (None, repeat_n_zip((), ArcIntoIter::from(args))),
                    },
                    _ => (None, repeat_n_zip((), [].into())),
                },
            };

            iter.for_each(|to_node| match &to_node {
                ToNode::Input(_) => input_edges.push(Edges {
                    from: from.clone(),
                    to: to_node,
                }),
                ToNode::CellCall(_) => edges.push(Edges {
                    from: from.clone(),
                    to: to_node,
                }),
            })
        }
    }
}
