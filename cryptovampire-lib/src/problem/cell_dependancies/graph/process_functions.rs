use crate::formula::formula::ARichFormula;
use crate::formula::formula::RichFormula;
use crate::formula::function::inner::term_algebra::TermAlgebra;
use crate::problem::cell::Assignement;

use logic_formula::outers::OwnedPile;
use logic_formula::FormulaIterator;
use logic_formula::IteratorHelper;

use super::super::call::InputCall;

use super::InnerCellCall;

use super::ToNode;

use crate::formula::function::InnerFunction;

use crate::formula::sort::builtins::STEP;

use crate::formula::variable::Variable;

use super::super::call::StepCall;

use super::FromNode;

use super::Edges;

use super::GlobNode;

use crate::problem::step::Step;

/// populate `input_edges` and `edges` using the content seen in the step definitions
///
/// The `pile` is used for efficiency
pub(crate) fn process_steps<'bump>(
    steps: &Vec<Step<'bump>>,
    cells: &Vec<GlobNode<'bump>>,
    input_edges: &mut Vec<Edges<'bump>>,
    edges: &mut Vec<Edges<'bump>>,
) {
    for step in steps {
        let from = FromNode::Input { step: *step };
        let mut iter = OwnedPile::new(Vec::new(), StepProcessorIterator { cells });
        iter.as_mut()
            .extend_child_with_default([step.message_arc(), step.condition_arc()]);

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

struct StepProcessorIterator<'a, 'bump> {
    cells: &'a [GlobNode<'bump>],
}

impl<'a, 'bump> FormulaIterator<&'a ARichFormula<'bump>> for StepProcessorIterator<'a, 'bump> {
    type Passing = ();

    type U = ToNode<'bump>;

    fn next<H>(&mut self, current: &'a ARichFormula<'bump>, _: &Self::Passing, helper: &mut H)
    where
        H: logic_formula::IteratorHelper<
            F = &'a ARichFormula<'bump>,
            Passing = Self::Passing,
            U = Self::U,
        >,
    {
        match current.as_ref() {
            RichFormula::Var(Variable { sort, .. }) => {
                if sort == &STEP.as_sort() {
                    unreachable!("time point variable are not allowed in protocol")
                }
            }
            RichFormula::Fun(fun, args) => match fun.as_inner() {
                InnerFunction::TermAlgebra(TermAlgebra::Cell(c)) => {
                    let c = c.memory_cell();
                    let cell_idx = self.cells.iter().position(|g| g.cell == c).unwrap();
                    let to_node = ToNode::CellCall(InnerCellCall {
                        cell_idx,
                        timepoint: StepCall::General(args.last().unwrap().shallow_copy()),
                        args: args[..args.len() - 1].iter().cloned().collect(),
                    });
                    helper.push_result(to_node);
                }
                InnerFunction::Step(_s) => {
                    let to_node = ToNode::Input(InputCall {
                        step: StepCall::General(current.clone()),
                    });
                    helper.push_result(to_node);
                }
                _ => {
                    helper.extend_child_with_default(args.iter());
                }
            },
            RichFormula::Quantifier(_, arg) => {
                helper.push_child(arg, ());
            }
        }
    }
}

/// populate `input_edges` and `edges` using the content seen in the cell definitions
///
/// The `pile` is used for efficiency
pub(crate) fn process_cell<'bump>(
    _steps: &Vec<Step<'bump>>,
    // pile: &RefCell<Vec<((), ARichFormula<'bump>)>>,
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
            let mut iter = OwnedPile::new(Vec::new(), CellProcessorIterator { cells });
            iter.as_mut().push_child(content, ());

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

struct CellProcessorIterator<'a, 'bump> {
    cells: &'a [GlobNode<'bump>],
}

impl<'a, 'bump> FormulaIterator<&'a ARichFormula<'bump>> for CellProcessorIterator<'a, 'bump> {
    type Passing = ();

    type U = ToNode<'bump>;

    fn next<H>(&mut self, f: &'a ARichFormula<'bump>, _: &Self::Passing, helper: &mut H)
    where
        H: logic_formula::IteratorHelper<
            F = &'a ARichFormula<'bump>,
            Passing = Self::Passing,
            U = Self::U,
        >,
    {
        match f.as_ref() {
            RichFormula::Fun(fun, args) => match fun.as_inner() {
                InnerFunction::TermAlgebra(TermAlgebra::Cell(c)) => {
                    let c = c.memory_cell();
                    let cell = self.cells.iter().position(|g| g.cell == c).unwrap();
                    let to_node = ToNode::CellCall(InnerCellCall {
                        cell_idx: cell,
                        timepoint: StepCall::General(args.last().unwrap().shallow_copy()),
                        args: args[..args.len() - 1].iter().cloned().collect(),
                    });
                    helper.push_result(to_node);
                }
                InnerFunction::Step(_s) => {
                    let to_node = ToNode::Input(InputCall {
                        step: StepCall::General(f.clone()),
                    });
                    helper.push_result(to_node);
                }
                _ => {
                    helper.extend_child_with_default(args.iter());
                }
            },
            _ => {}
        }
    }
}
