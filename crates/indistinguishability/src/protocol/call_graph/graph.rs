use core::num;
use std::num::NonZeroUsize;

use itertools::Itertools;
use logic_formula::FormulaIterator;
use logic_formula::outers::Content as LFContent;
use quarck::CowArc;
use steel::steel_vm::cache;
use utils::{econtinue_if, ereturn_if, ereturn_let};

use crate::protocol::call_graph::{
    CallCallee, Caller, CellRef, DescendantFlags, Graph, PreCall, StepRef,
};
use crate::protocol::{MemoryCell, Protocol, SingleAssignement, Step};
use crate::terms::{
    Formula, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MEMORY_CELL, MACRO_MSG, PRED,
    Variable,
};
use crate::{Problem, rexp};

impl PreCall {
    pub fn get_idx(self, cell_num: usize) -> usize {
        match self {
            Self::Exec(i) | Self::Frame(i) => i.0 * (cell_num + 1),
            Self::Cell { cell, time } => time.0 * (cell_num + 1) + cell.0.get(),
        }
    }

    /// NB: this lose the exec/frame distinction
    pub fn from_idx(i: usize, cell_num: usize) -> Self {
        let time = StepRef(i / (cell_num + 1));
        let rem = i % (cell_num + 1);
        match NonZeroUsize::new(rem) {
            Some(cell) => Self::Cell {
                cell: CellRef(cell),
                time,
            },
            None => Self::Frame(time),
        }
    }

    pub fn set_step(self, time: StepRef) -> Self {
        match self {
            Self::Exec(_) => Self::Exec(time),
            Self::Frame(_) => Self::Frame(time),
            Self::Cell { cell, time: _ } => Self::Cell { cell, time },
        }
    }

    pub fn get_step(self) -> StepRef {
        let (Self::Exec(time) | Self::Frame(time) | Self::Cell { time, .. }) = self;
        time
    }
}

#[allow(clippy::derivable_impls, reason = "clearer meaning of the boolean")]
impl Default for Graph {
    fn default() -> Self {
        Self {
            cell_num: Default::default(),
            callers: Default::default(),
            initialized: false,
        }
    }
}

impl Graph {
    pub fn clear(&mut self) {
        ereturn_if!(!self.initialized);

        for c in &mut self.callers {
            c.clear();
        }
        self.initialized = false
    }

    pub fn is_initialized(&self) -> bool {
        self.initialized
    }

    pub fn size(&self) -> usize {
        self.callers.len()
    }

    pub fn cell_num(&self) -> usize {
        self.cell_num
    }

    pub fn find_decendants(
        &self,
        todo: &mut Vec<(usize, DescendantFlags)>,
        descendants: &mut [DescendantFlags],
    ) {
        assert!(descendants.len() == self.callers.len());
        while let Some((next, flags)) = todo.pop() {
            econtinue_if!(descendants[next].contains(flags));
            let Caller { callees, .. } = &self.callers[next];

            todo.reserve(callees.len());
            for CallCallee {
                call, num_preds, ..
            } in callees
            {
                if *num_preds > 0 {
                    // if it is a pred we look at `next` "in all the step",
                    // this requires a bit of index manipulation
                    self.fill_todo_all_steps(
                        PreCall::from_idx(next, self.cell_num),
                        DescendantFlags::Pred,
                        todo,
                    );
                } else {
                    let next = call.get_idx(self.cell_num);
                    todo.push((next, flags));
                }
            }

            descendants[next] |= flags;
        }
    }

    /// Repopulate the graph
    pub fn reinitialize(&mut self, pbl: &Problem, ptcl: &Protocol) {
        self.clear();
        let Self {
            cell_num,
            callers,
            initialized,
        } = self;

        *cell_num = pbl.memory_cells().len();

        {
            let n = ptcl.steps().len() * (*cell_num + 1);
            callers.truncate(n);
            let diff = n - callers.len();
            if diff > 0 {
                callers.extend(::std::iter::repeat_n(Default::default(), diff));
            }
        }

        let mut cache = Vec::new();

        for (i, s) in ptcl.steps().iter().enumerate() {
            populate_step(*cell_num, callers, &mut cache, i, s);

            for (j, c) in pbl.memory_cells().iter().enumerate() {
                populate_cell(*cell_num, callers, &mut cache, i, s, j, c);
            }
        }

        *initialized = true;
    }

    fn num_steps(&self) -> usize {
        self.callers.len() / (self.cell_num + 1)
    }

    pub fn fill_todo_all_steps(
        &self,
        from: PreCall,
        flags: DescendantFlags,
        todo: &mut Vec<(usize, DescendantFlags)>,
    ) {
        todo.extend(
            self.all_steps_iter()
                .map(|s| (from.set_step(s).get_idx(self.cell_num), flags)),
        );
    }

    pub fn all_steps_iter(&self) -> impl Iterator<Item = StepRef> + use<> {
        (0..self.num_steps()).map(StepRef)
    }

    pub fn all_steps_idx(&self) -> impl Iterator<Item = usize> + use<> {
        let cell_num = self.cell_num();
        self.all_steps_iter()
            .map(PreCall::Frame)
            .map(move |c| c.get_idx(cell_num))
    }
}

fn populate_step<'v, 'a: 'v>(
    cell_num: usize,
    callers: &mut [Caller],
    cache: &'v mut Vec<LFContent<&'a Formula, &'a Formula, ()>>,
    step_idx: usize,
    s: &'a Step,
) {
    let call = PreCall::Frame(StepRef(step_idx));
    let caller = &mut callers[call.get_idx(cell_num)];

    cache.clear();
    cache.extend([&s.cond, &s.msg].map(|f| LFContent::Next {
        formula: f,
        passing: (),
    }));
    caller.populate_from_cache(cache);

    if step_idx != 0 {
        caller.callees.push(CallCallee {
            call,
            num_preds: 1,
            step_vars: vec![],
            cell_vars: vec![],
        });
    }
}

fn populate_cell<'v, 'a: 'v>(
    cell_num: usize,
    callers: &mut [Caller],
    cache: &'v mut Vec<LFContent<&'a Formula, &'a Formula, ()>>,
    step_idx: usize,
    s: &'a Step,
    cell_idx: usize,
    cell: &'a MemoryCell,
) {
    let time = StepRef(step_idx);
    let fun = cell.function();
    let cell = CellRef(NonZeroUsize::new(cell_idx + 1).unwrap());
    let mut ref_pred = step_idx != 0;

    let call = PreCall::Cell { cell, time };
    let caller = &mut callers[call.get_idx(cell_num)];

    if let Some(SingleAssignement {
        assignement_vars,
        parameter_vars,
        value,
    }) = s.assignements.get(fun)
    {
        cache.clear();
        cache.extend([value].map(|f| LFContent::Next {
            formula: f,
            passing: (),
        }));
        caller.populate_from_cache(cache);

        for CallCallee {
            step_vars,
            cell_vars,
            ..
        } in &mut caller.callees
        {
            let mut same_step_vars = false;
            let mut same_cell_vars = false;

            remap_var(parameter_vars, assignement_vars, step_vars);
            remap_var(parameter_vars, assignement_vars, cell_vars);

            if step_vars == &s.vars {
                *step_vars = vec![];
                same_step_vars = true;
            }

            if cell_vars == assignement_vars {
                *cell_vars = vec![];
                same_cell_vars = true;
            }

            if same_step_vars && same_cell_vars {
                ref_pred = false;
            }
        }
    }

    if ref_pred {
        caller.callees.push(CallCallee {
            call,
            num_preds: 1,
            step_vars: vec![],
            cell_vars: vec![],
        });
    }
}

impl Caller {
    pub fn populate_from_cache<'v, 'a: 'v>(
        &mut self,
        cache: &'v mut Vec<LFContent<&'a Formula, &'a Formula, ()>>,
    ) {
        let iter = logic_formula::outers::RefPile::new(cache, MacroCallIterator);

        for f in iter.cloned() {
            let Formula::App { mut head, mut args } = f else {
                unreachable!()
            };

            if head == MACRO_INPUT {
                let (time, ptcl) = args.iter().cloned().collect_tuple().unwrap();
                head = MACRO_FRAME.clone();
                args = CowArc::from([rexp!((PRED #time)), ptcl])
            }

            if head == MACRO_FRAME || head == MACRO_EXEC {
                let (time, _) = args.iter().collect_tuple().unwrap();
                let TimeLike {
                    num_preds,
                    step_idx,
                    var_args,
                } = TimeLike::extract(time);
                let step_ref = StepRef(step_idx);
                let call = if head == MACRO_FRAME {
                    PreCall::Frame(step_ref)
                } else {
                    PreCall::Exec(step_ref)
                };

                self.callees.push(CallCallee {
                    call,
                    num_preds,
                    step_vars: var_args,
                    cell_vars: vec![],
                });
            } else if head == MACRO_MEMORY_CELL {
                let (cell, time, _) = args.iter().collect_tuple().unwrap();
                let TimeLike {
                    num_preds,
                    step_idx,
                    var_args: step_vars,
                } = TimeLike::extract(time);
                let time = StepRef(step_idx);

                let (cell_idx, cell_vars) = extra_cell(cell);

                let cell = CellRef(NonZeroUsize::new(cell_idx + 1).unwrap());
                self.callees.push(CallCallee {
                    call: PreCall::Cell { cell, time },
                    num_preds,
                    step_vars,
                    cell_vars,
                });
            } else {
                unreachable!()
            }
        }
    }

    pub fn clear(&mut self) {
        self.callees.clear();
    }
}

fn extra_cell(cell: &Formula) -> (usize, Vec<Variable>) {
    let (cell_idx, cell_vars) = if let Formula::App { head, args } = cell
        && let Some(cell_idx) = head.get_cell_index()
    {
        let var_args = args
            .iter()
            .map(|arg| match arg {
                Formula::Var(v) => v.clone(),
                _ => unreachable!("non_variable index"),
            })
            .collect();

        (cell_idx, var_args)
    } else {
        unreachable!("this isn't a concrete cell, malformed protocol")
    };
    (cell_idx, cell_vars)
}
struct TimeLike {
    num_preds: usize,
    step_idx: usize,
    var_args: Vec<Variable>,
}

impl TimeLike {
    /// panic if something is not a contecte time (`a[i]` or `pred^n(a[i])`)
    fn extract(mut arg: &Formula) -> TimeLike {
        let mut num_preds = 0;
        while let Formula::App { head, args } = arg
            && head == &PRED
        {
            num_preds += 1;
            arg = &args[0]
        }

        if let Formula::App { head, args } = arg
            && let Some(step_idx) = head.get_step_index()
        {
            let var_args = args
                .iter()
                .map(|arg| match arg {
                    Formula::Var(v) => v.clone(),
                    _ => unreachable!("non_variable index"),
                })
                .collect();
            TimeLike {
                num_preds,
                step_idx,
                var_args,
            }
        } else {
            unreachable!("this isn't a concrete step, malformed protocol")
        }
    }
}

/// Wierd iterator helper to find macros invocations
struct MacroCallIterator;

impl<'a> FormulaIterator<&'a Formula> for MacroCallIterator {
    type Passing = ();

    type U = &'a Formula;

    fn next<H>(&mut self, current: &'a Formula, _: (), helper: &mut H)
    where
        H: logic_formula::IteratorHelper<F = &'a Formula, Passing = Self::Passing, U = Self::U>,
    {
        match current {
            Formula::Quantifier { arg, .. } => {
                helper.extend_child_with_default(arg);
            }
            Formula::Var(_) => {}
            Formula::App { head, args } if head.is_macro() => {
                assert!(
                    ![&MACRO_COND, &MACRO_MSG].contains(&head),
                    "msg and cond not supported"
                );
                helper.push_result(current);
            }
            Formula::App { args, .. } => {
                helper.extend_child_with_default(args);
            }
        }
    }
}

/// Apply the substitution (`from` -> `to`) in `into`.
///
/// It is not resistant against loops between `to` and `from`
fn remap_var(from: &[Variable], to: &[Variable], into: &mut [Variable]) {
    for v in into {
        if let Some(idx) = from.iter().position(|v2| v2 == v) {
            *v = to[idx].clone();
        }
    }
}
