use if_chain::if_chain;
use logic_formula::outers::RefPile;
use logic_formula::{Content, FormulaIterator, IteratorHelper};

use super::super::call::{InputCall, StepCall};
use super::{Edges, FromNode, GlobNode, InnerCellCall, ToNode};
use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::function::InnerFunction;
use crate::formula::function::inner::step::StepFunction;
use crate::formula::function::inner::term_algebra::{TermAlgebra, step_macro};
use crate::formula::sort::builtins::STEP;
use crate::formula::variable::Variable;
use crate::problem::cell::Assignement;
use crate::problem::step::Step;

/// populate `input_edges` and `edges` using the content seen in the step definitions
///
/// ## arguments
/// - `steps`: the steps of the protocol
/// - `cells`: the cells of the protocol
/// - `input_edges`: the edges to an input
/// - `edges`: the other edges
pub(crate) fn process_steps<'bump>(
    pile: &mut Vec<Content<ToNode<'bump>, ARichFormula<'bump>, ()>>,
    steps: &Vec<Step<'bump>>,
    cells: &Vec<GlobNode<'bump>>,
    input_edges: &mut Vec<Edges<'bump>>,
    edges: &mut Vec<Edges<'bump>>,
) {
    for step in steps {
        populate_edges_steps(pile, cells, step, input_edges, edges, true);
        populate_edges_steps(pile, cells, step, input_edges, edges, false);
    }
}

/// Populate the [Edges] while preprocessing for step.
///
/// This keeps tract if we came from the condition or the message of the step.
///
/// see: [process_steps]
fn populate_edges_steps<'bump>(
    pile: &mut Vec<Content<ToNode<'bump>, ARichFormula<'bump>, ()>>,
    cells: &Vec<GlobNode<'bump>>,
    step: &Step<'bump>,
    input_edges: &mut Vec<Edges<'bump>>,
    edges: &mut Vec<Edges<'bump>>,
    in_cond: bool,
) {
    // make the [FromNode]
    let from = (if in_cond {
        FromNode::condition
    } else {
        FromNode::message
    })(*step);

    // set up the iterator
    pile.clear();
    let mut iter = RefPile::new(pile, ToNodeIterator { cells });
    let m = if in_cond {
        step.condition_arc()
    } else {
        step.message_arc()
    }
    .shallow_copy();
    iter.push_child(m, ());

    // push to the to nodes to the relevant arrays
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

/// Generate an interator of [ToNode] that looks
struct ToNodeIterator<'a, 'bump> {
    cells: &'a [GlobNode<'bump>],
}

impl<'a, 'bump> FormulaIterator<ARichFormula<'bump>> for ToNodeIterator<'a, 'bump> {
    type Passing = ();

    type U = ToNode<'bump>;

    fn next<H>(&mut self, current: ARichFormula<'bump>, _: Self::Passing, helper: &mut H)
    where
        H: logic_formula::IteratorHelper<
                F = ARichFormula<'bump>,
                Passing = Self::Passing,
                U = Self::U,
            >,
    {
        match current.as_ref() {
            RichFormula::Var(Variable { sort, .. }) if sort == &STEP.as_sort() => {
                unreachable!("time point variable are not allowed in protocol")
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
                InnerFunction::TermAlgebra(TermAlgebra::Macro(m)) => {
                    assert!(
                        args.len() == 1,
                        "wrong number of arguments for a macro application"
                    );
                    let arg = args.first().unwrap();
                    let (step, args) = if_chain! {
                        if let RichFormula::Fun(f, args) = arg.as_ref();
                        if let InnerFunction::Step(StepFunction::Step(s)) = f.as_inner();
                        then {
                            (s.step(), args)
                        } else {
                            unreachable!("macros must be apply to concrete steps in protocols")
                        }
                    };
                    match m {
                        step_macro::Macro::Condition => {
                            helper.extend_child_with_default([step.apply_condition(args.as_ref())])
                        }
                        step_macro::Macro::Message => {
                            helper.extend_child_with_default([step.apply_message(args.as_ref())])
                        }
                        step_macro::Macro::Exec => unreachable!("exec is not allowed in protocols"),
                        step_macro::Macro::Input => {
                            let to_node = ToNode::Input(InputCall {
                                step: StepCall::General(current.clone()),
                            });
                            helper.push_result(to_node)
                        }
                    };
                }
                InnerFunction::Step(_) => {
                    // let to_node = ToNode::Input(InputCall {
                    //     step: StepCall::General(current.clone()),
                    // });
                    // helper.push_result(to_node);
                    unreachable!()
                }
                _ => {
                    helper.extend_child_with_default(args.iter().cloned());
                }
            },
            RichFormula::Quantifier(_, arg) => {
                helper.push_child(arg.shallow_copy(), ());
            }
            _ => {}
        }
    }
}

/// populate `input_edges` and `edges` using the content seen in the cell definitions
///
/// The `pile` is used for efficiency
pub(crate) fn process_cell<'bump>(
    pile: &mut Vec<Content<ToNode<'bump>, ARichFormula<'bump>, ()>>,
    _steps: &[Step<'bump>],
    cells: &Vec<GlobNode<'bump>>,
    input_edges: &mut Vec<Edges<'bump>>,
    edges: &mut Vec<Edges<'bump>>,
) {
    // let mut pile = Vec::new();
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
            pile.clear();
            let mut iter = RefPile::new(pile, ToNodeIterator { cells });
            iter.push_child(content.shallow_copy(), ());

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
