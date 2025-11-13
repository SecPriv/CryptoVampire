use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;
use std::fmt::Write;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::{Arc, Weak};

use if_chain::if_chain;
use itertools::Itertools;
use log::{error, log_enabled, trace, warn};
use logic_formula::outers::OwnedPile;
use logic_formula::{AsFormula, FormulaIterator};
use utils::traits::NicerError;
use utils::utils::AlreadyInitialized;
use utils::{implvec, partial_order};

use crate::container::allocator::{ContainerTools, Residual};
use crate::environement::environement::Environement;
use crate::environement::traits::{KnowsRealm, Realm};
use crate::formula::file_descriptior::declare::{self, Declaration};
use crate::formula::formula::{self, ARichFormula, exists, forall, meq};
use crate::formula::function::builtin::TRUE;
use crate::formula::function::{self, Function, InnerFunction};
use crate::formula::manipulation::Unifier;
use crate::formula::sort::Sort;
use crate::formula::utils::Applicable;
use crate::formula::utils::formula_expander::{
    NO_REC_MACRO, UnfoldFlags, UnfolderBuilder, UnfoldingState, UnfoldingStateBuilder,
};
use crate::formula::variable::{IntoVariableIter, Variable, sorts_to_variables};
use crate::mforall;

pub(crate) mod kind;
pub(crate) mod traits;

use self::kind::{AbsSubtermKindG, SubtermKind, SubtermKindConstr, SubtermKindWFunction};
use self::traits::{SubtermAux, SubtermResult};
use crate::problem::Problem;
use crate::problem::protocol::Protocol;

#[derive(Debug, Clone)]
pub struct Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    aux: Aux,
    ignored_functions: Vec<Function<'bump>>,
    kind: SubtermKindWFunction<'bump>,
    #[allow(dead_code)]
    weak: Weak<Self>, // sort: Sort<'bump>,
    deeper_kind: UnfoldFlags,
}

impl<'bump, Aux> Eq for Subterm<'bump, Aux> where Aux: SubtermAux<'bump> + Eq {}
impl<'bump, Aux> Ord for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump> + Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Self::partial_cmp(self, other).unwrap()
    }
}
impl<'bump, Aux> PartialOrd for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump> + PartialOrd,
{
    partial_order!(aux, kind, ignored_functions);
}
impl<'bump, Aux> PartialEq for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump> + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
            && self.aux == other.aux
            && self.ignored_functions == other.ignored_functions
    }
}
impl<'bump, Aux> Hash for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump> + Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.aux.hash(state);
        self.ignored_functions.hash(state);
        self.kind.hash(state);
    }
}

impl<'bump, Aux> Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    pub fn new<'a, F>(
        container: &'bump impl ContainerTools<'bump, InnerFunction<'bump>, R<'bump> = Function<'bump>>,
        // env: &impl KnowsRealm,
        name: String,
        kind: &SubtermKindConstr<'a, 'bump>,
        aux: Aux,
        ignored_functions: impl IntoIterator<Item = Function<'bump>>,
        deeper_kind: UnfoldFlags,
        to_enum: F,
    ) -> Arc<Self>
    where
        F: Fn(Arc<Self>) -> function::inner::subterm::Subsubterm<'bump>,
    {
        let ignored_functions = ignored_functions.into_iter().collect();
        let self_rc = match kind {
            AbsSubtermKindG::Vampire(_) => {
                {
                    container.alloc_cyclic_with_residual(|function| {
                        let self_rc = Arc::new_cyclic(|weak| Subterm {
                            aux,
                            ignored_functions,
                            kind: SubtermKindWFunction::Vampire(*function),
                            weak: Weak::clone(weak),
                            deeper_kind,
                        });
                        //  Rc::new(subterm);
                        let inner = function::inner::subterm::Subterm::new(
                            to_enum(Arc::clone(&self_rc)),
                            name,
                            AbsSubtermKindG::vampire(),
                        );
                        Residual {
                            content: inner.into_inner_function(),
                            residual: self_rc,
                        }
                    })
                }
                .unwrap_display()
                .residual
            }
            AbsSubtermKindG::Regular(sorts) => {
                {
                    {
                        container
                        .try_alloc_mulitple_cyclic_with_residual::<_, _, _, AlreadyInitialized, _>(
                            sorts.len(),
                            |functions| {
                                let map = sorts
                                    .iter()
                                    .zip_eq(functions)
                                    .map(|(s, fun)| ((*s).into(), *fun))
                                    .collect();

                                let self_rc = Arc::new_cyclic(|weak| Subterm {
                                    aux,
                                    ignored_functions,
                                    kind: SubtermKindWFunction::Regular(map),
                                    weak: Weak::clone(weak),
                                    deeper_kind,
                                });

                                let inner = sorts.iter().map(|s| {
                                    function::inner::subterm::Subterm::new(
                                        to_enum(Arc::clone(&self_rc)),
                                        name.clone(),
                                        AbsSubtermKindG::Regular(*s),
                                    )
                                    .into_inner_function()
                                }).collect_vec();

                                Ok::<_, Infallible>(Residual {
                                    content: inner,
                                    residual: self_rc,
                                })
                            },
                        )
                    }
                }
                .unwrap_display()
                .residual
            }
        };

        self_rc
    }

    /// Generate default function assertions from a list of function
    ///
    /// This should not be used with "special functions" (it will crash anyway)
    fn generate_functions_assertions(
        &self,
        env: &impl KnowsRealm,
        funs: impl Iterator<Item = Function<'bump>>,
    ) -> Vec<ARichFormula<'bump>> {
        funs.map(|fun| {
            assert!(fun.is_default_subterm());

            let f_sorts = fun.fast_insort().expect("todo");

            let x = Variable::new(0, self.sort());
            let mut vars: Vec<_> = sorts_to_variables(1, f_sorts.iter());

            let vars_f = vars.iter().map(|v| v.into_aformula()).collect_vec();
            let x_f = x.into_aformula();

            vars.push(x);
            forall(vars, {
                let applied_fun = fun.f(vars_f.clone());

                let mut ors =
                    formula::ors(vars_f.into_iter().map(|f| self.f_a(env, x_f.clone(), f)));

                {
                    let o_sort = applied_fun.get_sort();
                    if o_sort.is_err() || o_sort.unwrap() == self.sort() {
                        ors = ors | meq(x_f.clone(), applied_fun.clone())
                    }
                }

                self.f_a(env, x_f, applied_fun) >> ors
            })
        })
        .collect()
    }

    /// List of functions declared to use default subterm
    pub fn list_default_subterm_functions<'a>(
        &'a self,
        pbl: &'a Problem<'bump>,
    ) -> impl Iterator<Item = Function<'bump>> + 'a {
        pbl.functions()
            .iter()
            .filter(|f| f.is_default_subterm())
            .filter(|fun| !self.ignored_functions.contains(fun))
            .cloned()
    }

    pub fn generate_function_assertions_from_pbl(
        &self,
        env: &impl KnowsRealm,
        pbl: &Problem<'bump>,
    ) -> Vec<ARichFormula<'bump>> {
        self.generate_functions_assertions(env, self.list_default_subterm_functions(pbl))
    }

    pub fn generate_special_functions_assertions<'a>(
        &'a self,
        funs: impl Iterator<Item = Function<'bump>> + 'a,
        env: &impl KnowsRealm,
        ptcl: &'a Protocol<'bump>,
        keep_guard: bool,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let max_var = ptcl.max_var() + 1;
        let x = Variable::new(max_var, self.sort());
        let max_var = max_var + 1;
        let x_f = x.into_aformula();
        let realm = env.get_realm();
        funs.map(move |fun| {
            debug_assert!(!fun.is_default_subterm() || self.ignored_functions.contains(&fun));

            let f_sorts = fun
                .fast_insort()
                .unwrap_or_else(|| panic!("failed here: {}", line!()));
            let vars: Vec<_> = sorts_to_variables(max_var, f_sorts.iter());
            let vars_f = vars.iter().map(|v| v.into_aformula()).collect_vec();
            let f_f = fun.f(vars_f);

            trace!("{}:{}:{}", file!(), line!(), column!());

            // no variable collision
            let f = self.preprocess_term_to_formula(
                &realm,
                ptcl,
                &x_f,
                f_f.clone(),
                Rc::new([]),
                keep_guard,
            );
            trace!("{}:{}:{}", file!(), line!(), column!());
            forall(
                vars.into_iter().chain(std::iter::once(x)),
                self.f_a(&realm, x_f.clone(), f_f) >> f,
            )
        })
    }

    pub fn preprocess_special_assertion_from_pbl<'a>(
        &'a self,
        env: &impl KnowsRealm,
        pbl: &'a Problem<'bump>,
        keep_guard: bool,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let funs = pbl
            .functions()
            .iter()
            .filter(|f| {
                f.is_term_algebra()
                    && (!f.is_default_subterm() || self.ignored_functions.contains(f))
            })
            .cloned();
        trace!("{}:{}:{}", file!(), line!(), column!());
        self.generate_special_functions_assertions(funs, env, pbl.protocol(), keep_guard)
    }

    /// whach out for variable clash
    pub fn preprocess_whole_ptcl<'a>(
        &'a self,
        env: &impl KnowsRealm,
        ptcl: &'a Protocol<'bump>,
        formula: &'a ARichFormula<'bump>,
    ) -> impl Iterator<Item = (Rc<[Variable<'bump>]>, ARichFormula<'bump>)> + 'a {
        self.preprocess_terms(
            env,
            ptcl,
            formula,
            ptcl.list_top_level_terms_short_lifetime_and_bvars(),
            false,
            NO_REC_MACRO,
        )
    }

    /// preprocess a subterm search going through inputs and cells. Returns a formula
    ///
    /// **!!! Please ensure the variables are well placed to avoid colisions !!!**
    ///
    /// This function *will not* take care of it (nor check)
    pub fn preprocess_term_to_formula<'a>(
        &'a self,
        env: &impl KnowsRealm,
        ptcl: &'a Protocol<'bump>,
        x: &ARichFormula<'bump>,
        m: ARichFormula<'bump>,
        bvars: Rc<[Variable<'bump>]>,
        keep_guard: bool,
    ) -> ARichFormula<'bump> {
        trace!(
            "preprocess_term_to_formula -> {}:{}:{}",
            file!(),
            line!(),
            column!()
        );

        let iter = self.preprocess_term(env, ptcl, x, m, bvars, keep_guard, self.deeper_kind);
        into_exist_formula(iter)
    }

    /// preprocess a subterm search going through inputs and cells. Returns a list to ored.
    ///
    /// **!!! Please ensure the variables are well placed to avoid colisions !!!**
    ///
    /// This function *will not* take care of it (nor check)
    #[allow(clippy::too_many_arguments)]
    pub fn preprocess_term<'a>(
        &'a self,
        env: &impl KnowsRealm,
        ptcl: &'a Protocol<'bump>,
        x: &'a ARichFormula<'bump>,
        m: ARichFormula<'bump>,
        bvars: Rc<[Variable<'bump>]>,
        keep_guard: bool,
        deeper_kind: UnfoldFlags,
    ) -> impl Iterator<Item = (Rc<[Variable<'bump>]>, ARichFormula<'bump>)> + 'a {
        trace!("-------------------- preprocess_term (single) ----------------");
        if cfg!(debug_assertions) && check_variable_collision(x, &m) {
            error!("collision in the variables")
        }

        if log_enabled!(log::Level::Trace) {
            // check min_var(c) > max_var(m)
        }

        self.preprocess_terms(
            env,
            ptcl,
            x,
            [FormlAndVars {
                formula: m,
                bounded_variables: bvars,
            }],
            keep_guard,
            deeper_kind,
        )
    }

    /// preprocess a subterm search going through inputs and cells. Returns a list to ored.
    ///
    /// **!!! Please ensure the variables are well placed to avoid colisions !!!**
    ///
    /// This function *will not* take care of it (nor check)
    pub fn preprocess_terms<'a, 'b>(
        &'a self,
        env: &impl KnowsRealm,
        ptcl: &'a Protocol<'bump>,
        x: &'a ARichFormula<'bump>,
        m: impl IntoIterator<Item = FormlAndVars<'bump>>,
        keep_guard: bool,
        deeper_kind: UnfoldFlags,
    ) -> impl Iterator<Item = (Rc<[Variable<'bump>]>, ARichFormula<'bump>)> + 'a {
        trace!("------------------- preprocess_terms ---------------------");
        let realm = env.get_realm();

        // let pile = vec![(ExpantionState::None, m)];
        let pile = //repeat_n_zip(ExpantionState::from_deeper_kind(deeper_kind), m).collect_vec();
            m.into_iter().map(|FormlAndVars { bounded_variables, formula }| {

                if cfg!(debug_assertions) &&
                 (check_variable_collision(x, &formula) ||
                 check_variable_collision_list(x, &bounded_variables)) {
                    // This may get triggered when locking into some part of the candidate. For instance when
                    // looking for k \sqsubseteq m, m and k might share variable and this will get triggered.
                    // But this is soundly expected.
                    warn!("collision in the variables ({:} in {:}, {:?})",x, &formula, &bounded_variables)
                }
                // (, formula)
                let passing = UnfoldingStateBuilder::default().flags(deeper_kind).bound_variables(bounded_variables).build().unwrap();
                logic_formula::Content::Next { formula, passing }
            }).collect_vec();
        OwnedPile::new(
            pile,
            PreprocessTermIterator {
                subterm: self,
                ptcl,
                realm,
                x,
                keep_guard,
            },
        )
    }

    pub fn f_a<V>(&self, env: &impl KnowsRealm, x: V, m: V) -> ARichFormula<'bump>
    where
        ARichFormula<'bump>: From<V>,
    {
        if !self.is_sound_in_smt(env) {
            TRUE.clone().into()
        } else {
            match &self.kind {
                AbsSubtermKindG::Vampire(fun) => fun.f([x, m]),
                AbsSubtermKindG::Regular(funs) => {
                    let [x, m]: [ARichFormula<'bump>; 2] = [x.into(), m.into()];
                    let sort = m.get_sort().expect_display(|| "term algebra has a sort");
                    trace!(
                        "[{}]\n{:?}",
                        funs.keys().map(|fsort| fsort.as_reference()).join(", "),
                        &funs
                    );
                    funs.get(&sort.as_fo())
                        .unwrap_or_else(|| panic!("unsupported sort: {sort}, {sort:?}"))
                        .f::<ARichFormula<'bump>, _>([x, m])
                }
            }
        }
    }

    // pub fn function(&self) -> Function<'bump> {
    //     self.function
    // }

    pub fn ignored_functions(&self) -> &[Function<'bump>] {
        self.ignored_functions.as_ref()
    }

    pub fn sort(&self) -> Sort<'bump> {
        self.aux.sort()
    }

    pub fn reflexivity(&self) -> ARichFormula<'bump> {
        mforall!(x!0:self.sort(); {
            self.f_a(&Realm::Symbolic,x, x)
        })
    }

    pub fn not_of_sort<'a>(
        &'a self,
        env: &impl KnowsRealm,
        sorts: impl IntoIterator<Item = Sort<'bump>> + 'a,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let realm = env.get_realm();
        sorts.into_iter().map(move |s| {
            debug_assert!(!s.is_term_algebra(), "because of {s}");
            mforall!(x!0:self.sort(), m!1:s; {!self.f_a(&realm, x, m)})
        })
    }

    /// Same as [Subterm::not_of_sort()] but automatically figures out the
    /// sort iterator
    pub fn not_of_sort_auto<'a>(
        &'a self,
        env: &impl KnowsRealm,
        pbl: &'a Problem<'bump>,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let realm = env.get_realm();
        let sorts = pbl
            .sorts()
            .iter()
            .filter(move |&&s| {
                (s != self.sort())
                    && !s.is_term_algebra()
                    && if let Realm::Evaluated = realm {
                        !s.is_evaluated()
                    } else {
                        true
                    }
            })
            .cloned();
        self.not_of_sort(env, sorts)
    }

    pub fn declare(
        &self,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
        declarations: &mut impl Extend<Declaration<'bump>>,
    ) {
        if self.is_sound_in_smt(env) {
            self.assert_sound_in_smt(env).unwrap();
            match &self.kind {
                AbsSubtermKindG::Vampire(function) => {
                    declarations.extend([Declaration::Subterm(declare::Subterm {
                        function: *function,
                        comutative_functions: self.list_default_subterm_functions(pbl).collect(),
                    })])
                }
                AbsSubtermKindG::Regular(funs) => {
                    declarations.extend(funs.values().map(|&fun| Declaration::FreeFunction(fun)))
                }
            }
        }
    }

    pub fn kind(&self) -> SubtermKind {
        self.kind.as_subterm_kind()
    }

    pub fn is_sound_in_smt(&self, env: &impl KnowsRealm) -> bool {
        self.sort().is_datatype(env) || !env.get_realm().is_evaluated()
    }

    pub fn assert_sound_in_smt(&self, env: &impl KnowsRealm) -> crate::Result<()> {
        if self.is_sound_in_smt(env) {
            Ok(())
        } else {
            // Err(format!("{} => {} is wrong", self.sort(), env.get_realm()))
            crate::bail!("{} => {} is wrong", self.sort(), env.get_realm())
        }
    }
}

fn check_variable_collision(x: &ARichFormula<'_>, m: &ARichFormula<'_>) -> bool {
    let varx = x
        .used_vars_iter()
        .map(|v| v.id)
        .minmax()
        .into_option()
        .map(|(a, b)| a..=b);
    let varm = m.used_vars_iter().map(|v| v.id).minmax().into_option();
    match (varx, varm) {
        (Some(r), Some((vminm, vmaxm))) if r.contains(&vminm) || r.contains(&vmaxm) => {
            warn!(
                "variable collided:\n\t- [{}, {}] {}\n\t- [{}, {}] {}",
                r.start(),
                r.end(),
                x,
                vminm,
                vmaxm,
                &m
            );
            true
        }
        _ => false,
    }
}

fn check_variable_collision_list(x: &ARichFormula<'_>, m: &[Variable<'_>]) -> bool {
    let varx = x
        .used_vars_iter()
        .map(|v| v.id)
        .minmax()
        .into_option()
        .map(|(a, b)| a..=b);
    let varm = m.iter().map(|v| v.id).minmax().into_option();
    match (varx, varm) {
        (Some(r), Some((vminm, vmaxm))) if r.contains(&vminm) || r.contains(&vmaxm) => {
            warn!(
                "variable collided with list:\n\t- [{}, {}] {}\n\t- [{}, {}]",
                r.start(),
                r.end(),
                x,
                vminm,
                vmaxm,
            );
            true
        }
        _ => false,
    }
}

pub type GuardAndBound<'bump> = UnfoldingState<'bump>;
pub struct SubtermSearchElement<'bump> {
    pub inner_state: Rc<GuardAndBound<'bump>>,
    pub unifier: Unifier<'bump>,
}

pub trait AsSubterm<'bump> {
    fn generate_function_assertions<R: KnowsRealm>(
        &self,
        env: &R,
        funs: &[Function<'bump>],
    ) -> Vec<ARichFormula<'bump>>;
    fn apply<R: KnowsRealm>(
        &self,
        env: &R,
        x: ARichFormula<'bump>,
        m: ARichFormula<'bump>,
    ) -> ARichFormula<'bump>;
    // fn function(&self) -> Function<'bump>;
    fn ignored_functions(&self) -> &[Function<'bump>];
    fn sort(&self) -> Sort<'bump>;
}

impl<'bump, Aux> AsSubterm<'bump> for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    fn generate_function_assertions<R: KnowsRealm>(
        &self,
        env: &R,
        funs: &[Function<'bump>],
    ) -> Vec<ARichFormula<'bump>> {
        Subterm::generate_functions_assertions(self, env, funs.iter().cloned())
    }

    fn apply<R: KnowsRealm>(
        &self,
        env: &R,
        x: ARichFormula<'bump>,
        m: ARichFormula<'bump>,
    ) -> ARichFormula<'bump> {
        Subterm::f_a(self, env, x, m)
    }

    fn ignored_functions(&self) -> &[Function<'bump>] {
        Self::ignored_functions(self)
    }
    fn sort(&self) -> Sort<'bump> {
        Self::sort(self)
    }
}

// -----------------------------------------------------------------------------
// --------------------------- other inner structs -----------------------------
// -----------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FormlAndVars<'bump> {
    pub bounded_variables: Rc<[Variable<'bump>]>,
    pub formula: ARichFormula<'bump>,
}

impl<'bump> FormlAndVars<'bump> {
    pub fn new(bounded_variables: Rc<[Variable<'bump>]>, formula: ARichFormula<'bump>) -> Self {
        Self {
            bounded_variables,
            formula,
        }
    }

    pub fn bounded_variables(&self) -> &[Variable<'_>] {
        self.bounded_variables.as_ref()
    }

    pub fn formula(&self) -> &ARichFormula<'bump> {
        &self.formula
    }
}

impl<'bump> From<ARichFormula<'bump>> for FormlAndVars<'bump> {
    fn from(value: ARichFormula<'bump>) -> Self {
        FormlAndVars {
            bounded_variables: Rc::new([]),
            formula: value,
        }
    }
}

pub fn into_exist_formula<'bump>(
    f: implvec!((Rc<[Variable<'bump>]>, ARichFormula<'bump>)),
) -> ARichFormula<'bump> {
    let content = f.into_iter().unique().collect_vec();
    let mut vars = BTreeMap::new();

    for (i, (inner_vars, _)) in content.iter().enumerate() {
        for var in inner_vars.as_ref() {
            vars.entry(*var)
                .and_modify(|f_idx: &mut BTreeSet<usize>| {
                    f_idx.insert(i);
                })
                .or_insert(BTreeSet::from_iter([i]));
        }
    }
    // further expand vars
    for (var, f_idx) in vars.iter_mut() {
        for (i, (vars, _)) in content.iter().enumerate() {
            if !vars.contains_var(var) {
                // if `var` doesn't clash with any variables in `vars` we can add the formula to the bag
                f_idx.insert(i);
            }
        }
    }

    if log_enabled!(log::Level::Trace) {
        let mut str = String::new();
        for s in vars.iter().map(|(v, idx)| {
            let fs = idx.iter().map(|&i| content[i].1.shallow_copy()).join(", ");
            format!("{v} -> [{fs}]")
        }) {
            writeln!(&mut str, "\t\t{s}").unwrap();
        }
        trace!("into_exists:\n{str}");
    }

    let max = {
        let max = vars
            .iter()
            .max_set_by_key(|(_, f_idx_vec)| (f_idx_vec.len(), *f_idx_vec));
        if let Some((_, max_f)) = max.first() {
            let max_f = *max_f;
            let vars: BTreeSet<_> = max.into_iter().map(|(v, _)| *v).collect();
            Some((max_f, vars))
        } else {
            None
        }
    };

    match max {
        // no bound variables
        None => {
            assert!(content.iter().all(|(v, _)| v.is_empty()));
            formula::ors(content.into_iter().map(|(_, f)| f))
        }
        // position -> set of idx of formula with boundings in vars_max
        // vars_max -> variables bindings commun to all position_max
        Some((position_max, vars_max)) => {
            let ors1 = position_max
                .iter()
                .map(|&idx| {
                    let (inner_vars, f) = content.get(idx).unwrap();
                    exists(
                        // add the remaining variables
                        inner_vars.iter().filter(|v| !vars_max.contains(v)).cloned(),
                        f,
                    )
                })
                .collect_vec();

            let mut ors = Vec::with_capacity(content.len() - position_max.len() + 1);
            ors.push(exists(vars_max, formula::ors(ors1)));
            ors.extend(
                content
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| !position_max.contains(i))
                    .map(|(_, (vars, formula))| exists(vars.iter().cloned(), formula)),
            );
            formula::ors(ors)
        }
    }
}

struct PreprocessTermIterator<'a, 'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    subterm: &'a Subterm<'bump, Aux>,
    ptcl: &'a Protocol<'bump>,
    realm: Realm,
    x: &'a ARichFormula<'bump>,
    keep_guard: bool,
}

impl<'a, 'bump, Aux> FormulaIterator<ARichFormula<'bump>> for PreprocessTermIterator<'a, 'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    type Passing = UnfoldingState<'bump>;

    type U = (Rc<[Variable<'bump>]>, ARichFormula<'bump>);

    fn next<H>(&mut self, f: ARichFormula<'bump>, state: Self::Passing, helper: &mut H)
    where
        H: logic_formula::IteratorHelper<
                F = ARichFormula<'bump>,
                Passing = Self::Passing,
                U = Self::U,
            >,
    {
        trace!("{} ⊑ {}", self.x, &f);

        // if this term "hides" some other terms to look for (e.g., macros, quantifiers) we queue them
        helper.extend_child(
            UnfolderBuilder::default()
                .state(state.clone())
                .content(f.clone())
                .build()
                .unwrap()
                .unfold(self.ptcl.steps().iter().cloned(), self.ptcl.graph())
                .into_iter()
                .map(|ec| ec.as_tuple()),
        );

        let SubtermResult { unifier, nexts } = self.subterm.aux.is_subterm_and_next(self.x, &f);
        unifier
            .map(|u| {
                let mut guard = if_chain!(
                    if let Some(ovs) = u.is_unifying_to_variable();
                    if ovs.f() == self.x;
                    then {
                        vec![self.subterm.f_a(&self.realm, self.x.clone(), f.clone())]
                    } else {
                        u.as_equalities().unwrap()
                    }
                );
                if self.keep_guard {
                    guard.extend(state.condition().into_iter().cloned())
                }
                let formula = formula::ands(guard);
                trace!("{formula}");
                (state.owned_bound_variable(), formula)
            })
            .into_iter()
            .for_each(|r| {
                helper.push_result(r);
            });

        helper.extend_child_same_passing(nexts, &state);
    }
}
