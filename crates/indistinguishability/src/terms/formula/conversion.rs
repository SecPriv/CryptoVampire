use std::fmt::Debug;

use anyhow::{Context, bail, ensure};
use bon::{bon, builder};
use egg::{Analysis, EGraph, Id, Language, Pattern, RecExpr};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::AsFormula;
use logic_formula::iterators::AllFunctionsIterator;
use rustc_hash::FxHashMap;
use utils::{ereturn_if, implvec};

use super::Formula;
use crate::terms::formula::conversion::extraction::ExtractionState;
use crate::terms::formula::egg::EggLanguage;
use crate::terms::formula::list;
use crate::terms::{CONS, LAMBDA_O, LAMBDA_S, NIL, Sort, Variable};
use crate::{Lang, LangVar, fresh, rexp};

impl Formula {
    pub fn from_egg(formula: &[LangVar], sort: Option<Sort>) -> Self {
        let mut free_vars = Default::default();
        let mut db_free_vars = Default::default();
        Self::inner_from_egg(
            formula,
            Default::default(),
            0,
            &mut free_vars,
            &mut db_free_vars,
            sort,
        )
    }

    /// - formula: The formula to convert. It must be a valid reference to a `[LangVar]` slice
    /// - bound_variables: a queue use to track the De Bruijn indices and assign them names
    /// - free_variables: a map to transfrom [egg]'s free variables into cryptovampire's
    /// - possible_sort: the possible output sort of the formula
    fn inner_from_egg(
        formula: &[LangVar],
        bound_variables: rpds::Queue<Variable>,
        depth: usize,
        free_variables: &mut FxHashMap<egg::Var, Variable>,
        db_free_variables: &mut Vec<Variable>,
        possible_sort: Option<Sort>,
    ) -> Self {
        let head = formula.last().expect("we expect a non empty formula");

        use egg::ENodeOrVar::{ENode, Var};
        match head {
            Var(var) => {
                // get the variable from `free_variables` or spawn a fresh one (and save it)
                let var = free_variables
                    .entry(*var)
                    .or_insert(Variable::fresh().maybe_sort(possible_sort).call());
                Self::Var(var.clone())
            }
            ENode(Lang { head, args }) => {
                assert!(
                    possible_sort.is_none() || Some(head.signature.output) == possible_sort,
                    "the expected sort doesn't match the computed sort (expected {:?}, got {})",
                    possible_sort,
                    head.signature.output
                );
                let mut args = args.iter().map(|&i| &formula[..=usize::from(i)]);

                if head == &LAMBDA_O {
                    // `head` is a De Bruijn variable
                    assert!(
                        args.next().is_none(),
                        "De Bruijn variables shouldn't have parameters"
                    );
                    let var = match bound_variables.peek() {
                        Some(var) => var.clone(),
                        None => {
                            // this is a free De Bruijn variable
                            if db_free_variables.len() <= depth {
                                // extend the free de Bruijn variables if necessary
                                db_free_variables
                                    .extend((db_free_variables.len()..=depth).map(|_| fresh!()));
                            }
                            db_free_variables[depth].clone()
                        }
                    };
                    var.maybe_set_sort(possible_sort).unwrap();
                    Self::Var(var)
                } else if head == &LAMBDA_S {
                    // `head` is an S
                    let arg = {
                        let a1 = args.next();
                        let a2 = args.next();
                        match (a1, a2) {
                            (Some(x), None) => x,
                            _ => panic!("wrong number of argument for `S`"),
                        }
                    };

                    let (bound_variables, depth) = match bound_variables.dequeue() {
                        Some(x) => (x, depth), // if I can dequeue, the depth doesn't change
                        None => (bound_variables, depth + 1), // otherwise I increase the depth
                    };
                    Self::inner_from_egg(
                        arg,
                        bound_variables,
                        depth,
                        free_variables,
                        db_free_variables,
                        possible_sort,
                    )
                } else if let Some(binder) = head.as_fobinder() {
                    // an egg binder

                    // fetch the sort list
                    let sorts = {
                        let sort_exp = args.next().expect("a list of sorts as first arg");
                        list::try_get(Self::from(sort_exp)).expect("a list of sorts as first arg")
                    };
                    assert!(!sorts.is_empty(), "should be non-empty binder");

                    // we enque fresh variables
                    let mut bound_variables = bound_variables;
                    let mut vars = Vec::with_capacity(sorts.len());
                    for &sort in &sorts {
                        let variable = fresh!(sort);
                        vars.push(variable.clone());
                        bound_variables = bound_variables.enqueue(variable)
                    }

                    // compute the argument(s)
                    let args = Itertools::zip_eq(head.signature.inputs.iter(), args)
                        .map(|(&sort, arg)| {
                            Self::inner_from_egg(
                                arg,
                                bound_variables.clone(),
                                depth,
                                free_variables,
                                db_free_variables,
                                Some(sort),
                            )
                        })
                        .collect_vec();

                    // finish
                    assert!(
                        args.len() == binder.arity(),
                        "wrong number of argument for binder"
                    );
                    Self::Quantifier {
                        head: binder,
                        vars: vars.into(),
                        arg: args.into(),
                    }
                } else {
                    // a regular function
                    let args = Itertools::zip_eq(head.signature.inputs.iter(), args).map(
                        |(&sort, arg)| {
                            Self::inner_from_egg(
                                arg,
                                bound_variables.clone(),
                                depth,
                                free_variables,
                                db_free_variables,
                                Some(sort),
                            )
                        },
                    );
                    Self::App {
                        head: head.clone(),
                        args: Vec::from_iter(args).into(),
                    }
                }
            }
        }
    }

    /// Converts this formula into an e-graph expression with variable support.
    ///
    /// This method creates a `RecExpr<LangVar>` which can contain both ground terms
    /// and variables. This is useful for pattern matching and e-graph operations that
    /// need to express variable positions.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use crate::{rexp, Sort};
    ///
    /// let formula = rexp!((and true false));
    /// let expr = formula.as_egg_var();
    /// ```
    ///
    /// # See Also
    /// - [`as_egg_ground`] for converting to fully grounded expressions
    /// - [`add_to_egraph`] for adding directly to an e-graph
    pub fn as_egg_var(&self) -> RecExpr<LangVar> {
        RecExpr::from(self.as_egg::<LangVar>())
    }

    /// Converts this formula into a fully grounded e-graph expression.
    ///
    /// This method creates a `RecExpr<Lang>` which contains only ground terms
    /// (no variables). This is useful when you need to add the formula to an e-graph
    /// for rewriting or equality checking.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use crate::rexp;
    /// use egg::{EGraph, Runner};
    ///
    /// let formula = rexp!((and true false));
    /// let expr = formula.as_egg_ground();
    ///
    /// let mut egraph = EGraph::new(());
    /// egraph.add_expr(&expr);
    /// ```
    ///
    /// # See Also
    /// - [`as_egg_var`] for converting to expressions with variables
    /// - [`add_to_egraph`] for adding directly to an e-graph
    pub fn as_egg_ground(&self) -> RecExpr<Lang> {
        RecExpr::from(self.as_egg::<Lang>())
    }

    /// Converts this formula into an e-graph representation.
    ///
    /// # Type Parameters
    ///
    /// * `L` - The `EggLanguage` type to use for the conversion (e.g., `Lang` for ground terms
    ///   or `LangVar` for expressions with variables).
    ///
    /// # Notes
    ///
    /// This method uses capture-avoiding substitution by default. Free variables will be
    /// shifted to avoid capture by quantifiers. If you don't need capture avoidance,
    /// use [`as_egg_non_capture_avoiding`] instead.
    ///
    /// # Panics
    ///
    /// This function panics if the conversion is impossible (e.g., if the formula contains
    /// unsupported constructs).
    ///
    /// # See Also
    ///
    /// - [`as_egg_non_capture_avoiding`] for non-capture-avoiding conversion
    /// - [`as_egg_var`] for `LangVar` conversion shortcut
    /// - [`as_egg_ground`] for `Lang` conversion shortcut
    pub fn as_egg<L: EggLanguage>(&self) -> Vec<L> {
        let mut out = Vec::new();
        self.as_egg_inner(&mut out, Default::default(), Default::default(), &mut None);
        out
    }

    /// Converts this formula into an e-graph representation without capture avoidance.
    ///
    /// # Type Parameters
    ///
    /// * `L` - The `EggLanguage` type to use for the conversion.
    ///
    /// # Notes
    ///
    /// Unlike [`as_egg`], this method does not use capture-avoiding substitution. Free variables
    /// will not be shifted, which may lead to variable capture in the presence of quantifiers.
    /// This can be useful for performance reasons or when you know capture won't occur.
    ///
    /// # Panics
    ///
    /// This function panics if the conversion is impossible.
    ///
    /// # See Also
    ///
    /// - [`as_egg`] for capture-avoiding conversion
    /// - [`AsEggParam`] for configuring conversion parameters
    pub fn as_egg_non_capture_avoiding<L: EggLanguage>(&self) -> Vec<L> {
        let mut out = Vec::new();
        self.as_egg_inner(
            &mut out,
            Default::default(),
            AsEggParam {
                capture_avoiding: false,
                ..Default::default()
            },
            &mut None,
        );
        out
    }

    fn as_egg_inner<'a, L: EggLanguage>(
        &'a self,
        out: &mut Vec<L>,
        mut bvars: rpds::HashTrieMap<&'a Variable, usize>,
        param: AsEggParam,
        olocation: &mut Option<usize>,
    ) -> usize {
        match self {
            Self::Quantifier { head, vars, arg } => {
                if !vars.is_empty() {
                    let l = match olocation {
                        Some(l) => *l,
                        None => {
                            let i = out.len();
                            *olocation = Some(i);
                            out.push(L::mk_fun_application(LAMBDA_O.clone(), []));
                            i
                        }
                    };

                    // update the variables assignement
                    bvars = bvars
                        .into_iter()
                        .map(|(v, i)| {
                            let mut i = *i;
                            for _ in vars.iter() {
                                out.push(L::mk_fun_application(LAMBDA_S.clone(), [Id::from(i)]));
                                i = out.len() - 1;
                            }
                            (*v, i)
                        })
                        .collect();

                    // mk the variables
                    {
                        let mut vars = vars.iter().rev();
                        let v1 = vars.next().unwrap();
                        bvars = bvars.insert(v1, l);
                        let mut l = l;
                        for v in vars {
                            out.push(L::mk_fun_application(LAMBDA_S.clone(), [Id::from(l)]));
                            l = out.len() - 1;
                            bvars = bvars.insert(v, l);
                        }
                    }
                }

                let mut nargs = Vec::with_capacity(arg.len() + 1);
                nargs.push(mk_list(out, vars.iter().map(|v| v.get_sort().unwrap())));
                nargs.extend(
                    arg.iter()
                        .map(|arg| arg.as_egg_inner(out, bvars.clone(), param.clone(), olocation)),
                );

                let head = head.as_function().cloned().unwrap();
                let nargs = nargs.into_iter().map(Id::from);
                out.push(L::mk_fun_application(head, nargs));
            }
            Self::App { head, args } => {
                let args = args
                    .iter()
                    .map(|arg| arg.as_egg_inner(out, bvars.clone(), param.clone(), olocation))
                    .map(Id::from)
                    .collect_vec();
                out.push(L::mk_fun_application(head.clone(), args));
            }
            Self::Var(variable) => match bvars.get(variable) {
                Some(i) => {
                    // out.extend(mk_bound_var(*i));
                    return *i;
                }
                None if (!param.capture_avoiding)
                    || param.non_capture_avoiding.contains(variable) =>
                {
                    out.push(L::mk_variable(variable))
                }
                None => {
                    let nparam = AsEggParam {
                        capture_avoiding: false,
                        ..param
                    };
                    bvars
                        .iter()
                        .fold(self.clone(), |acc, _| rexp!((LAMBDA_S #acc)))
                        .as_egg_inner(out, bvars, nparam, olocation);
                }
            },
        };

        out.len() - 1
    }

    // ~~~~~~~~~~~~~~ from graph ~~~~~~~~~~~~~~~~

    // fn from_id_inner(ids: &[Id], langs: &[Option<&Lang>], current: &Lang) -> Self {
    //     let head = current.head.clone();
    //     let args = current
    //         .args
    //         .iter()
    //         .map(|id| ids.iter().position(|x| x == id).unwrap())
    //         .map(|i| langs[i].unwrap())
    //         .map(|l| Self::from_id_inner(ids, langs, l))
    //         .collect();
    //     Self::App { head, args }
    // }

    /// remove any De-Buijn indices from a [Self]
    #[allow(unused)]
    fn remove_de_bruijn(
        &self,
        bound_vars: &rpds::Queue<Variable>,
        depth: usize,
        free_vars: &mut Vec<Variable>,
    ) -> Option<Self> {
        match self {
            Self::Var(variable) => Some(Self::Var(variable.clone())),
            Self::Quantifier { head, vars, arg } => Some(Self::Quantifier {
                head: *head,
                vars: vars.clone(),
                arg: arg
                    .iter()
                    .map(|x| x.remove_de_bruijn(bound_vars, depth, free_vars))
                    .collect::<Option<cowarc![_]>>()?,
            }),
            Self::App { head, args } => {
                if head == &LAMBDA_O {
                    let var = bound_vars
                        .peek()
                        .cloned()
                        .unwrap_or_else(|| free_vars[depth].clone());
                    Some(Self::Var(var))
                } else if head == &LAMBDA_S {
                    match bound_vars.dequeue() {
                        Some(bound_vars) => {
                            args.first()?
                                .remove_de_bruijn(&bound_vars, depth, free_vars)
                        }
                        None => {
                            free_vars.push(fresh!());
                            args.first()?
                                .remove_de_bruijn(bound_vars, depth + 1, free_vars)
                        }
                    }
                } else if let Some(bind) = head.as_fobinder() {
                    let mut args = args.iter();

                    let sorts = Sort::list_from_formula(args.next()?)?;
                    let variables: cowarc![_] = sorts.into_iter().map(|s| fresh!(s)).collect();

                    let bound_vars = variables
                        .iter()
                        .fold(bound_vars.clone(), |acc, v| acc.enqueue(v.clone()));

                    let args = args
                        .map(|arg| arg.remove_de_bruijn(&bound_vars, depth, free_vars))
                        .collect::<Option<cowarc![_]>>()?;
                    ereturn_if!(args.len() != bind.arity(), None);

                    Some(Self::Quantifier {
                        head: bind,
                        vars: variables,
                        arg: args,
                    })
                } else {
                    let args = args
                        .iter()
                        .map(|x| x.remove_de_bruijn(bound_vars, depth, free_vars))
                        .collect::<Option<cowarc![_]>>()?;
                    Some(Self::App {
                        head: head.clone(),
                        args,
                    })
                }
            }
        }
    }

    /// Adds this formula to an e-graph and returns the resulting e-class id.
    ///
    /// # Parameters
    ///
    /// * `egraph` - A mutable reference to the e-graph to add to.
    ///
    /// # Returns
    ///
    /// The id of the e-class that represents this formula in the e-graph.
    ///
    /// # Notes
    ///
    /// This is a convenience method that converts the formula to a ground expression
    /// and adds it to the e-graph in one step. Equivalent to:
    ///
    /// ```ignore
    /// let recexpr = formula.as_egg_ground();
    /// egraph.add_expr(&recexpr)
    /// ```
    /// # See Also
    ///
    /// - [`Self::as_egg_ground`] for conversion without adding to e-graph
    /// - [`Self::try_from_id`] for extracting formulas back from e-graphs
    pub fn add_to_egraph<N: Analysis<Lang>>(&self, egraph: &mut EGraph<Lang, N>) -> Id {
        let recexpr = self.as_egg_ground();
        egraph.add_expr(&recexpr)
    }

    pub fn try_from_id<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        id: Id,
    ) -> anyhow::Result<Formula> {
        use extraction::*;

        let stateless = Box::new(ImmutatbleStateStruct::builder().build());

        let mut state = ExtractionState::builder()
            .egraph(egraph)
            .filter(default_extraction_filter)
            .build();

        state.extract(stateless, id).with_context(|| {
            format!(
                "couldn't convert ({id}) {}",
                egraph.id_to_expr(id).pretty(100)
            )
        })
    }

    #[deprecated]
    pub fn try_from_id_with_vars<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        id: Id,
        variables: &rpds::Queue<Variable>,
    ) -> anyhow::Result<Formula> {
        use extraction::*;

        let variables = variables.into_iter().collect_vec();

        let stateless = Box::new(
            ImmutatbleStateStruct::builder()
                .boundpile(variables.into_iter().rev().cloned().collect())
                .build(),
        );

        let mut state = ExtractionState::builder()
            .egraph(egraph)
            .filter(default_extraction_filter)
            .build();

        state.extract(stateless, id).with_context(|| {
            format!(
                "couldn't convert ({id}) {}",
                egraph.id_to_expr(id).pretty(100)
            )
        })
    }
}

#[derive(Debug, Clone)]
/// Parameters for controlling how formulas are converted to e-graph representations.
///
/// # Fields
///
/// * `capture_avoiding` - If `true`, free variables will be shifted to avoid capture by
///   quantifiers (alpha conversion). This is the default and recommended behavior for
///   correctness. Set to `false` only when you're certain capture won't occur.
///
/// * `non_capture_avoiding` - A set of variables that should be treated as if they won't
///   cause capture, even when `capture_avoiding` is `true`.
///
/// # Example
///
/// ```ignore
/// use crate::terms::Variable;
///
/// AsEggParam {
///     capture_avoiding: false,
///     non_capture_avoiding: Default::default(),
/// }
/// ```
pub struct AsEggParam {
    pub capture_avoiding: bool,
    pub non_capture_avoiding: ::rpds::HashTrieSet<Variable>,
}

impl Default for AsEggParam {
    fn default() -> Self {
        Self {
            non_capture_avoiding: Default::default(),
            capture_avoiding: true,
        }
    }
}

/// Builds a list in the e-graph representation from a collection of sorts.
///
/// This function constructs a cons-list (`CONS`/`NIL`) representation of sorts,
/// which is used for quantifier binders that need to specify the types of bound variables.
///
/// # Parameters
///
/// * `out` - The output buffer to append the list nodes to.
/// * `sorts` - A collection of sorts to create a list from.
///
/// # Returns
///
/// The index in `out` where the list head is located.
///
/// # Notes
///
/// The list is built in reverse order (last element at the head), following the
/// standard e-graph pattern for list representation.
fn mk_list<L: EggLanguage>(out: &mut Vec<L>, sorts: implvec!(Sort)) -> usize {
    let sorts = sorts.into_iter();
    let mut i = out.len();
    out.reserve(sorts.size_hint().0 * 2 + 1);
    out.push(L::mk_fun_application(NIL.clone(), []));

    for sort in sorts {
        let sort = sort.as_function().unwrap();
        out.push(EggLanguage::mk_fun_application(sort.clone(), []));
        out.push(EggLanguage::mk_fun_application(
            CONS.clone(),
            [i + 1, i].map(Id::from),
        ));
        i += 2
    }
    i
}

/// Filter any golgge specific head function, but keep lambda binders. Those
/// needs to be removed with [Formula::remove_de_bruijn]
pub fn default_extraction_filter(Lang { head, .. }: &Lang) -> bool {
    !head.is_prolog_only() || head.is_ok_for_extraction()
}

impl From<&[LangVar]> for Formula {
    fn from(v: &[LangVar]) -> Self {
        Self::from_egg(v, None)
    }
}

impl From<&RecExpr<LangVar>> for Formula {
    fn from(value: &RecExpr<LangVar>) -> Self {
        Self::from_egg(value.as_ref(), None)
    }
}

impl From<RecExpr<LangVar>> for Formula {
    fn from(value: RecExpr<LangVar>) -> Self {
        Self::from(&value)
    }
}

impl From<bool> for Formula {
    fn from(value: bool) -> Self {
        match value {
            true => Self::True(),
            false => Self::False(),
        }
    }
}

impl From<Variable> for Formula {
    fn from(value: Variable) -> Self {
        Self::Var(value)
    }
}

impl From<&Variable> for Formula {
    fn from(value: &Variable) -> Self {
        Self::Var(value.clone())
    }
}

impl From<&Formula> for RecExpr<LangVar> {
    fn from(value: &Formula) -> Self {
        value.as_egg().into()
    }
}

impl From<&Formula> for Pattern<Lang> {
    fn from(value: &Formula) -> Self {
        Pattern::from(RecExpr::from(value))
    }
}

mod extraction {
    use archery::RcK;
    use bon::{Builder, bon};
    use egg::{Analysis, EGraph, Id, Language};
    use imbl::hashmap::Entry;
    use rustc_hash::{FxBuildHasher, FxHashMap};

    use crate::terms::{Formula, Function, LAMBDA_O, LAMBDA_S, Sort, Variable, list};
    use crate::{Lang, fresh};

    declare_trace!($"extrac_from_egraph");

    #[derive(Builder)]
    pub struct ExtractionState<'a, F, N: Analysis<Lang>> {
        filter: F,
        egraph: &'a EGraph<Lang, N>,
        free_variables: Option<FxHashMap<usize, Variable>>,
    }

    #[derive(Default, Clone, Builder)]
    pub struct ImmutatbleStateStruct {
        #[builder(default = true)]
        quantifiers: bool,
        #[builder(default)]
        depth: usize,
        /// tracks if we are looping. Note that we can't cache the result because of variables
        #[builder(default)]
        id_states: imbl::GenericHashSet<Id, FxBuildHasher, RcK>,
        #[builder(default)]
        boundpile: imbl::GenericVector<Variable, RcK>,
    }

    pub type ImmutableState = Box<ImmutatbleStateStruct>;

    impl<'a, F, N: Analysis<Lang>> ExtractionState<'a, F, N> {
        #[allow(unused)]
        pub fn change_filter<F2>(self, filter: F2) -> ExtractionState<'a, F2, N> {
            let Self {
                egraph,
                free_variables,
                ..
            } = self;
            ExtractionState {
                filter,
                egraph,
                free_variables,
            }
        }
    }

    impl<'a, F: FnMut(&Lang) -> bool, N: Analysis<Lang>> ExtractionState<'a, F, N> {
        pub fn extract(&mut self, mut pile: ImmutableState, id: Id) -> Option<Formula> {
            tr!("({id}) {}", self.egraph.id_to_expr(id).pretty(100));

            // search map
            if pile.id_states.insert(id).is_some() {
                return None;
            }

            self.egraph[id]
                .iter()
                .filter_map(|f| self.extract_lang(pile.clone(), f))
                .next()
        }

        #[inline(never)]
        fn extract_lang(
            &mut self,
            mut pile: ImmutableState,
            l @ Lang { head, args }: &Lang,
        ) -> Option<Formula> {
            tr!("extract_lang: ({l})");
            if self.free_variables.is_some() || pile.quantifiers {
                if head == &LAMBDA_S {
                    return self.drop_var(pile, args[0]);
                }

                if head == &LAMBDA_O {
                    let var = self.get_first_var(*pile)?;
                    return Some(Formula::Var(var));
                }
            }
            if pile.quantifiers
                && let Some(head) = head.as_fobinder()
            {
                let mut args = args.iter().copied();
                let vars = list::try_get_egraph(self.egraph, args.next()?)?
                    .into_iter()
                    .rev() // `boundedvar` is a pile
                    .map(|s| self.push_front_var(&mut pile, s))
                    .collect();
                let args: Option<Vec<_>> =
                    args.map(|arg| self.extract(pile.clone(), arg)).collect();

                return Some(Formula::bind(head, vars, args?));
            }

            if (self.filter)(l) {
                let args: Option<_> = args
                    .iter()
                    .copied()
                    .map(|id| self.extract(pile.clone(), id))
                    .collect();
                return Some(Formula::app(head.clone(), args?));
            }

            None
        }

        /// Traverse `S`
        fn drop_var(&mut self, mut pile: ImmutableState, arg: Id) -> Option<Formula> {
            tr!(
                "drop_var: ({arg}) {}",
                self.egraph.id_to_expr(arg).pretty(100)
            );
            if pile.boundpile.pop_front().is_none() {
                // if the list was already empty, we increase the `depth` counter
                pile.depth += 1
            }
            self.extract(pile, arg)
        }

        /// when reaching a `O`
        fn get_first_var(&mut self, pile: ImmutatbleStateStruct) -> Option<Variable> {
            tr!("pop_var");
            if let Some(var) = pile.boundpile.front() {
                Some(var.clone())
            } else {
                Some(
                    self.free_variables
                        .as_mut()?
                        .entry(pile.depth)
                        .or_insert(fresh!())
                        .clone(),
                )
            }
        }

        /// add bound variables
        fn push_front_var(&mut self, pile: &mut ImmutableState, sort: Sort) -> Variable {
            tr!("enque_var: {sort}");
            let var = fresh!(sort);
            pile.boundpile.push_front(var.clone());
            var
        }
    }
}

#[cfg(test)]
mod tests {
    //! vibe coded tests
    use egg::{EGraph, Id};

    use super::*;
    use crate::terms::builtin::{AND, EXISTS, FALSE, INCOMPATIBLE, INIT, LAMBDA_O, NIL, TRUE};
    use crate::terms::{BITSTRING_SORT, BOOL_SORT};

    #[test]
    fn test_basic_extraction() {
        let mut egraph = EGraph::<Lang, ()>::default();
        let id_true = egraph.add(Lang::mk_fun_application(TRUE.clone(), []));

        let formula = Formula::try_from_id(&egraph, id_true).unwrap();
        assert!(formula.is_true());
    }

    #[test]
    fn test_backtracking_filter() {
        let mut egraph = EGraph::<Lang, ()>::default();
        let id_init = egraph.add(Lang::mk_fun_application(INIT.clone(), []));
        let id_incompatible = egraph.add(Lang::mk_fun_application(
            INCOMPATIBLE.clone(),
            [id_init, id_init],
        ));
        let id_true = egraph.add(Lang::mk_fun_application(TRUE.clone(), []));

        egraph.union(id_incompatible, id_true);
        egraph.rebuild();

        // INCOMPATIBLE is filtered out by default_extraction_filter because it is PROLOG_ONLY
        let formula = Formula::try_from_id(&egraph, id_incompatible).unwrap();
        assert!(formula.is_true());
    }

    #[test]
    fn test_loop_handling() {
        let mut egraph = EGraph::<Lang, ()>::default();
        let id_true = egraph.add(Lang::mk_fun_application(TRUE.clone(), []));
        let id_and = egraph.add(Lang::mk_fun_application(AND.clone(), [id_true, id_true]));

        // Create a loop: id_true = AND(id_true, id_true)
        egraph.union(id_true, id_and);
        egraph.rebuild();

        // It should still be able to extract TRUE by avoiding the loop in AND
        let formula = Formula::try_from_id(&egraph, id_and).unwrap();
        assert!(formula.try_evaluate().unwrap(), "{formula}");
    }

    #[test]
    fn test_multiple_valid_options() {
        let mut egraph = EGraph::<Lang, ()>::default();
        let id_true = egraph.add(Lang::mk_fun_application(TRUE.clone(), []));
        let id_false = egraph.add(Lang::mk_fun_application(FALSE.clone(), []));
        egraph.union(id_true, id_false);
        egraph.rebuild();

        let formula = Formula::try_from_id(&egraph, id_true).unwrap();
        // It should be either True or False
        assert!(formula.is_true() || formula.is_false());
    }

    #[test]
    fn test_extraction_with_vars() {
        use crate::terms::FOBinder;
        let mut egraph = EGraph::<Lang, ()>::default();

        let id_nil = egraph.add(Lang::mk_fun_application(NIL.clone(), []));
        let id_sort = egraph.add(Lang::mk_fun_application(BOOL_SORT.clone(), []));
        let id_list = egraph.add(Lang::mk_fun_application(CONS.clone(), [id_sort, id_nil]));

        // EXISTS ( [Bitstring], LAMBDA_O )
        let id_var = egraph.add(Lang::mk_fun_application(LAMBDA_O.clone(), []));
        let id_exists = egraph.add(Lang::mk_fun_application(EXISTS.clone(), [id_list, id_var]));

        let formula = Formula::try_from_id(&egraph, id_exists).unwrap();

        if let Formula::Quantifier { head, vars, arg } = formula {
            assert_eq!(head, FOBinder::Exists);
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].get_sort().unwrap(), Sort::Bool);
            assert!(matches!(&arg[0], Formula::Var(v) if v == &vars[0]));
        } else {
            panic!("expected quantifier, got {:?}", formula);
        }
    }
}
