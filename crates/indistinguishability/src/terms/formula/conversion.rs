use std::fmt::Debug;

use anyhow::{Context, bail, ensure};
use egg::{Analysis, EGraph, Id, Language, Pattern, RecExpr};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::AsFormula;
use logic_formula::iterators::AllFunctionsIterator;
use rustc_hash::FxHashMap;
use utils::{ereturn_if, implvec};

use super::Formula;
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
    ///        or `LangVar` for expressions with variables).
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

    /// Extracts a formula from an e-graph using a cached buffer for efficiency.
    ///
    /// # Parameters
    ///
    /// * `egraph` - The e-graph to extract from.
    /// * `id` - The e-class id to extract.
    /// * `cache` - A reusable buffer for the extraction process to avoid allocations.
    ///
    /// # Errors
    ///
    /// Returns an error if the extraction fails.
    ///
    /// # Notes
    ///
    /// This method uses De Bruijn indices for bound variables and removes them during
    /// extraction. The cache buffer is cleared at the start of each call.
    ///
    /// # See Also
    ///
    /// - [`try_from_id`] for non-cached extraction
    /// - [`try_from_id_with_vars`] for extraction with known bound variables
    pub fn try_from_id_cached<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        id: Id,
        cache: &mut Vec<Id>,
    ) -> anyhow::Result<Self> {
        Self::try_pull_from_egraph_full(
            egraph,
            default_extraction_filter,
            id,
            Some(&Default::default()),
            cache,
        )
    }

    /// Extracts a formula from an e-graph c-id.
    ///
    /// # Parameters
    ///
    /// * `egraph` - The e-graph to extract from.
    /// * `id` - The e-class id to extract.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The extraction fails
    /// - The formula contains prolog-only functions (which shouldn't exist in
    ///   the general-purpose representation)
    ///
    /// # Notes
    ///
    /// This method validates that no prolog-specific functions are present in the
    /// extracted formula, as these are not applicable outside the prolog context.
    ///
    /// # See Also
    ///
    /// - [`try_from_id_cached`] for cached extraction (more efficient for repeated calls)
    /// - [`try_from_id_with_vars`] for extraction with known bound variables
    pub fn try_from_id<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        id: Id,
    ) -> anyhow::Result<Self> {
        let f = Self::try_from_id_with_vars(egraph, id, &Default::default())?;
        for fun in (&f).iter_with(AllFunctionsIterator, ()) {
            if fun.is_prolog_only() {
                bail!("Failed to extract: {fun} is a prolog-only function.\nIn:\t{f}")
            }
        }
        Ok(f)
    }

    /// Extracts a formula from an e-graph c-id with known bound variables.
    ///
    /// # Parameters
    ///
    /// * `egraph` - The e-graph to extract from.
    /// * `id` - The e-class id to extract.
    /// * `vars` - A queue of variables that are bound in the current context.
    ///
    /// # Errors
    ///
    /// Returns an error if the extraction fails.
    ///
    /// # Notes
    ///
    /// The `vars` parameter provides context about which variables are bound, which
    /// helps with De Bruijn index removal during extraction.
    ///
    /// # See Also
    ///
    /// - [`try_from_id`] for extraction without known bound variables
    /// - [`try_from_id_cached`] for cached extraction
    pub fn try_from_id_with_vars<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        id: Id,
        vars: &rpds::Queue<Variable>,
    ) -> anyhow::Result<Self> {
        Self::try_pull_from_egraph_full(
            egraph,
            default_extraction_filter,
            id,
            Some(vars),
            &mut Default::default(),
        )
    }

    /// Low-level extraction from an e-graph with full customization options.
    ///
    /// # Parameters
    ///
    /// * `egraph` - The e-graph to extract from.
    /// * `filter` - A predicate function to filter which functions to include/allow.
    ///             Returns `true` to allow, `false` to skip. See [`default_extraction_filter`].
    /// * `id` - The e-class id to extract.
    /// * `bound_vars` - Optional bound variable context for De Bruijn index removal.
    /// * `recexpr_buffer` - A buffer for the recursive extraction process.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The extraction fails (no valid formula found)
    /// - De Bruijn index removal fails (if `bound_vars` is provided)
    ///
    /// # Notes
    ///
    /// This is the most flexible extraction method, allowing complete control over
    /// the extraction process through the `filter` predicate. If `bound_vars` is
    /// provided, De Bruijn indices are removed; otherwise, they remain in the result.
    ///
    /// # See Also
    ///
    /// - [`default_extraction_filter`] for the standard filter predicate
    /// - [`try_from_id`] for higher-level extraction methods
    pub fn try_pull_from_egraph_full<N: Analysis<Lang>, F: FnMut(&Lang) -> bool>(
        egraph: &EGraph<Lang, N>,
        mut filter: F,
        id: Id,
        bound_vars: Option<&rpds::Queue<Variable>>,
        recexpr_buffer: &mut Vec<Id>,
    ) -> anyhow::Result<Self> {
        recexpr_buffer.clear();
        let status = extract_from_egraph(egraph, &mut filter, id, recexpr_buffer);

        let formula = match status {
            ExtractionStatus::Looping => unreachable!(),
            ExtractionStatus::Empty => bail!(
                "impossible to translate:\n{}",
                egraph.id_to_expr(id).pretty(100)
            ),
            ExtractionStatus::Found(formula) => formula,
        };

        match bound_vars {
            Some(bvars) => formula
                .remove_de_bruijn(bvars, 0, &mut vec![fresh!()])
                .with_context(|| format!("couldn't remove de bruijin indices in {formula}")),
            None => Ok(formula),
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
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use egg::EGraph;
    /// use crate::rexp;
    ///
    /// let formula = rexp!((and true false));
    /// let mut egraph = EGraph::new(());
    /// let id = formula.add_to_egraph(&mut egraph);
    /// ```
    ///
    /// # See Also
    ///
    /// - [`as_egg_ground`] for conversion without adding to e-graph
    /// - [`try_from_id`] for extracting formulas back from e-graphs
    pub fn add_to_egraph<N: Analysis<Lang>>(&self, egraph: &mut EGraph<Lang, N>) -> Id {
        let recexpr = self.as_egg_ground();
        egraph.add_expr(&recexpr)
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
///   cause capture, even when `capture_avoiding` is `true`. This is useful for performance
///   optimization when you know certain variables can't be captured.
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

#[derive(Debug, Clone)]
/// Status of a formula extraction attempt from an e-graph.
///
/// This enum represents the possible outcomes when attempting to extract a formula
/// from an e-class in an e-graph.
///
/// # Variants
///
/// * `Looping` - The extraction would loop infinitely (cyclic structure detected).
/// * `Empty` - No valid formula could be extracted from the e-class.
/// * `Found(Formula)` - A valid formula was successfully extracted.
///
/// # Notes
///
/// The `Looping` status typically indicates a problem with the e-graph structure,
/// such as cycles caused by unsupported rewriting rules.
pub enum ExtractionStatus {
    /// The extraction would loop infinitely (cyclic structure detected).
    Looping,
    /// No valid formula could be extracted from the e-class.
    Empty,
    /// A valid formula was successfully extracted.
    Found(Formula),
}

impl ExtractionStatus {
    #[must_use]
    /// Converts the status into an `Option<Formula>`.
    ///
    /// Returns `Some(formula)` if the status is `Found`, otherwise returns `None`.
    fn into_found(self) -> Option<Formula> {
        if let Self::Found(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl From<Option<Formula>> for ExtractionStatus {
    /// Converts an `Option<Formula>` into an `ExtractionStatus`.
    ///
    /// - `Some(formula)` becomes `ExtractionStatus::Found(formula)`
    /// - `None` becomes `ExtractionStatus::Empty`
    fn from(value: Option<Formula>) -> Self {
        match value {
            Some(x) => Self::Found(x),
            None => Self::Empty,
        }
    }
}

/// Pulls a value from an egraph
///
/// # Paramters
///  - `egraph`: the egraph
///  - `filter`: a predicate to filter out unwanted functions. For instance
///    [default_extraction_filter] remove everything specific to golgge/prolog.
///  - `id`: the [Id] to extract
///  - `loop_breaker`: the set of [Id] already seen in this search to avoid
///    looping.
fn extract_from_egraph<N: Analysis<Lang>, F: FnMut(&Lang) -> bool>(
    egraph: &EGraph<Lang, N>,
    filter: &mut F,
    id: Id,
    loop_breaker: &mut Vec<Id>,
) -> ExtractionStatus {
    trace!(target: "extract_from_egraph", "({id}) {}", egraph.id_to_expr(id).pretty(100));
    if loop_breaker.contains(&id) {
        trace!(target: "extract_from_egraph", "({id}) loop");
        return ExtractionStatus::Looping;
    }

    let n = loop_breaker.len();
    loop_breaker.push(id);

    let result: ExtractionStatus = egraph[id]
        .nodes
        .iter() //.filter(|l| filter(*l))
        .filter_map(|l @ Lang { head, args }| {
            trace!(target: "extract_from_egraph", "({id}, {head}) filter: {}", filter(l));
            filter(l).then_some(())?;
            let args: Option<_> = args
                .iter()
                .copied()
                .map(|id| extract_from_egraph(egraph, filter, id, loop_breaker).into_found())
                .collect();

            trace!(target: "extract_from_egraph", "({id}, {head}) args: {args:?}");
            Some(Formula::App {
                head: head.clone(),
                args: args?,
            })
        })
        .next()
        .into();

    trace!(target: "extract_from_egraph", "({id}) result: {result:?}");

    loop_breaker.truncate(n);
    result
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

#[cfg(test)]
mod conversion_tests {
    use egg::{EGraph, Id, PatternAst, RecExpr};

    use crate::{Lang, Sort, Variable, decl_vars, rexp};

    #[test]
    fn as_egg_succ() {
        decl_vars!(a, b);
        let f = rexp!((and #a #b
                (exists ((#i Bitstring) (#j Bitstring))
                    (and #a #b (= #i #j)
                            (exists ((#i Bitstring) (#k Bitstring))
                                (and (= #i #k #j) #a))))));
        let f: PatternAst<Lang> = f.as_egg().into();
        println!("{}", f.pretty(100));
    }

    #[test]
    fn test_as_egg_var_with_constants() {
        let formula1 = rexp!(true);
        let expr1 = formula1.as_egg_var();
        assert!(!expr1.as_ref().is_empty());

        let formula2 = rexp!((and true false));
        let expr2 = formula2.as_egg_var();
        assert!(!expr2.as_ref().is_empty());

        let formula3 = rexp!((or true false));
        let expr3 = formula3.as_egg_var();
        assert!(!expr3.as_ref().is_empty());
    }

    #[test]
    fn test_as_egg_ground_with_constants() {
        let formula1 = rexp!(true);
        let expr1 = formula1.as_egg_ground();
        assert!(!expr1.as_ref().is_empty());

        let formula2 = rexp!((and true false));
        let expr2 = formula2.as_egg_ground();
        assert!(!expr2.as_ref().is_empty());

        let formula3 = rexp!((or true false));
        let expr3 = formula3.as_egg_ground();
        assert!(!expr3.as_ref().is_empty());
    }

    #[test]
    fn test_as_egg_with_variables() {
        decl_vars!(a, b);

        let formula = rexp!((and #a #b));
        let expr = formula.as_egg_var();
        assert!(!expr.as_ref().is_empty());

        let formula2 = rexp!((or #a (not #b)));
        let expr2 = formula2.as_egg_var();
        assert!(!expr2.as_ref().is_empty());
    }

    #[test]
    fn test_add_to_egraph() {
        let mut egraph = EGraph::new(());

        let formula1 = rexp!(true);
        let id1 = formula1.add_to_egraph(&mut egraph);
        let formula2 = rexp!((and true false));
        let id2 = formula2.add_to_egraph(&mut egraph);
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_add_to_egraph_with_quantifiers() {
        let mut egraph = EGraph::new(());

        let formula = rexp!((exists ((#i Bitstring)) true));
        let id = formula.add_to_egraph(&mut egraph);
        assert_ne!(id, Id::from(0));
    }

    #[test]
    fn test_extract_formula_from_egraph() {
        let mut egraph = EGraph::new(());

        let formula = rexp!((and true false));
        let id = formula.add_to_egraph(&mut egraph);

        let extracted = crate::terms::formula::Formula::try_from_id(&egraph, id);
        assert!(extracted.is_ok());
    }

    #[test]
    fn test_from_bool() {
        let f_true = crate::terms::formula::Formula::True();
        assert_eq!(f_true.as_egg_ground().as_ref().len(), 1);

        let f_false = crate::terms::formula::Formula::False();
        assert_eq!(f_false.as_egg_ground().as_ref().len(), 1);

        assert_ne!(f_true.as_egg_ground(), f_false.as_egg_ground());
    }

    #[test]
    fn test_conversion_roundtrip_bool() {
        let formula = rexp!((and (or true false) (not true)));
        let egg_expr = formula.as_egg_ground();
        let egg_var = formula.as_egg_var();
        let recovered = crate::terms::formula::Formula::from(&egg_var);
        let recovered_expr = recovered.as_egg_ground();

        assert!(egg_expr.as_ref().len() > 0);
        assert!(recovered_expr.as_ref().len() > 0);
    }

    #[test]
    fn test_extract_with_cached_buffer() {
        let mut egraph = EGraph::new(());
        let mut buffer = Vec::new();

        let formula = rexp!((and true false));
        let id = formula.add_to_egraph(&mut egraph);

        let extracted1 =
            crate::terms::formula::Formula::try_from_id_cached(&egraph, id, &mut buffer);
        assert!(extracted1.is_ok());

        let formula2 = rexp!((or true false));
        let id2 = formula2.add_to_egraph(&mut egraph);

        let extracted2 =
            crate::terms::formula::Formula::try_from_id_cached(&egraph, id2, &mut buffer);
        assert!(extracted2.is_ok());

        assert_ne!(id, id2);
    }

    #[test]
    fn test_implication_conversion() {
        let formula = rexp!((=> true false));
        let egg_expr = formula.as_egg_ground();
        assert!(!egg_expr.as_ref().is_empty());

        let formula2 = rexp!((=> false true));
        let egg_expr2 = formula2.as_egg_ground();
        assert!(!egg_expr2.as_ref().is_empty());
    }

    #[test]
    fn test_nested_booleans() {
        let formula = rexp!((and (or true false) (not (and false true))));
        let egg_expr = formula.as_egg_ground();
        assert!(!egg_expr.as_ref().is_empty());

        let mut egraph = EGraph::new(());
        let id = formula.add_to_egraph(&mut egraph);
        let extracted = crate::terms::formula::Formula::try_from_id(&egraph, id);
        assert!(extracted.is_ok());
    }

    #[test]
    fn test_multiple_variables_in_quantifier() {
        let formula = rexp!(
            (exists ((#i Bitstring) (#j Bitstring) (#k Bitstring))
                (and true true)));

        let egg_expr = formula.as_egg_ground();
        assert!(!egg_expr.as_ref().is_empty());
    }

    #[test]
    fn test_nested_quantifiers_simple() {
        let formula = rexp!((exists ((#i Bitstring))
            (exists ((#j Bitstring)) true)));

        let egg_expr = formula.as_egg_var();
        assert!(!egg_expr.as_ref().is_empty());
    }

    #[test]
    fn test_egraph_size_growth() {
        let mut egraph = EGraph::new(());
        let initial_size = egraph.classes().count();

        let formula1 = rexp!(true);
        formula1.add_to_egraph(&mut egraph);
        let size_after_first = egraph.classes().count();

        let formula2 = rexp!((and true false));
        formula2.add_to_egraph(&mut egraph);
        let size_after_second = egraph.classes().count();

        assert!(size_after_first > initial_size);
        assert!(size_after_second >= size_after_first);
    }
}
