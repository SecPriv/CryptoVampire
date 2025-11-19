use FOBinder::{Exists, FindSuchThat};
use egg::{Analysis, EGraph, Id, Pattern, Searcher, Subst};
use golgge::{Dependancy, Rule};
use itertools::izip;
use rustc_hash::FxHashMap;
use utils::{ebreak_if, ebreak_let, econtinue_let, ereturn_let, match_eq};

use crate::libraries::mk_egg_rewrites;
use crate::libraries::utils::find_available_id;
use crate::libraries::utils::lambda_subst::lambda_subst;
use crate::problem::{PAnalysis, PRule, RcRule};
use crate::terms::{
    BIT_DEDUCE, BOOL_DEDUCE, CONS, EXISTS, FIND_SUCH_THAT, FOBinder, INDEX_SORT, Sort, Variable,
    list,
};
use crate::{CVProgram, Lang, Problem, fresh, rexp};

declare_trace!($"quantifier_deduce");

pub fn mk_rules(_: &Problem) -> impl Iterator<Item = RcRule> {
    [Exists, FindSuchThat]
        .map(|quantifier| {
            let (patterns, return_patterns) = QuantifierRule::mk_patterns(quantifier);
            QuantifierRule {
                quantifier,
                patterns,
                return_patterns,
            }
        })
        .map(|x| x.into_mrc())
        .into_iter()
}

/// A rule for deducing properties of quantifiers.
#[derive(Debug, Clone, PartialEq, Eq)]
struct QuantifierRule {
    /// The type of quantifier this rule applies to.
    quantifier: FOBinder,
    /// The patterns to search for in the e-graph.
    patterns: [Pattern<Lang>; 3],
    /// The patterns to return after a successful search.
    return_patterns: [Pattern<Lang>; 3],
}

macro_rules! mk_vars {
    ($($n:ident),*) => {
        /// The parameters of a quantifier rule
        #[derive(Debug, Clone)]
        struct Parameters<U = Id> {
            $(
                $n: U
            ),*
        }

        static DEFAULT_PARAMERTERS : Parameters<Variable> = Parameters {$($n: fresh!(const)),*};

        impl Parameters<Variable> {
            #[allow(dead_code)]
            fn all_params(&self) -> impl Iterator<Item = &Variable> {
                [ $(&self.$n),* ].into_iter()
            }
        }

        impl<U> FromIterator<U> for Parameters<U> {
            fn from_iter<T: IntoIterator<Item =U>>(iter: T) -> Self {
                let mut iter = iter.into_iter();
                $( let $n = iter.next().unwrap(); )*
                Parameters { $($n),* }
            }
        }
    }
}

mk_vars!(
    u, v, h1, h2, args1_1, args1_2, args1_3, args2_1, args2_2, args2_3, nargs1_1, nargs1_2,
    nargs2_1, nargs2_2, sort, sort1_cons, sort2_cons, other, new_var
);

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for QuantifierRule {
    /// Searches for matches of the quantifier rule in the e-graph and returns the dependencies.
    fn search(&self, prgm: &mut CVProgram<'a>, goal: egg::Id) -> Dependancy {
        let matches =
            izip!(self.patterns.iter(), self.return_patterns.iter()).find_map(|(pattern, ret)| {
                let matches = pattern.search_eclass(prgm.egraph(), goal)?;
                Some((ret, matches))
            });
        ereturn_let!(let Some((ret, matches)) = matches, Dependancy::impossible());
        #[cfg(debug_assertions)]
        {
            let g = prgm.egraph().id_to_expr(goal);
            tr!("quantifier deduce with: {}", g)
        }

        // let new_var = prgm
        //     .egraph_mut()
        //     .analysis
        //     .pbl_mut()
        //     .declare_function()
        //     .output(Sort::Index)
        //     .fresh_name("idx")
        //     .call();
        // let new_var = prgm.egraph_mut().add(Lang::new(new_var, []));

        let new_var = find_available_id(
            prgm.egraph_mut(),
            Sort::Index,
            matches
                .substs
                .iter()
                .flat_map(|s| s.iter())
                .map(|(_, id)| id),
        );

        let deps = matches
            .substs
            .into_iter()
            .filter_map(|mut subst| {
                'out: { // checks that the sort matches with the new variable
                    'err: {
                        ebreak_let!('err, let Some(&sid) = subst.get(DEFAULT_PARAMERTERS.sort.as_egg()));
                        ebreak_if!('out, prgm.egraph()[sid].nodes[0].head == INDEX_SORT);
                        log::error!("wrong sort: {}", &prgm.egraph()[sid].nodes[0].head);
                    }
                    panic!("only Index is supported in deduce quantifiers")
                }

                let ret=
                {
                    let egraph = prgm.egraph_mut();
                    extends_subst(egraph, new_var, &mut subst)?;
                    ret.apply_susbt(egraph, &subst)
                };

                #[cfg(debug_assertions)]
                {
                    let g = prgm.egraph().id_to_expr(ret);
                    tr!("quantifier new goal: {}", g)
                }

                Some([ret])
            })
            .collect();

        // because we introduced new constants
        let eq_rules = mk_egg_rewrites(prgm.egraph().analysis.pbl()).collect();
        prgm.set_eq_rules(eq_rules);

        deps
    }

    fn name(&self) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Borrowed(match self.quantifier {
            Exists => "quantifier deduce rule (exists)",
            FindSuchThat => "quantifier deduce rule (find)",
            _ => unimplemented!(),
        })
    }
}

fn extends_subst<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    nvar: Id,
    subst: &mut Subst,
) -> Option<()> {
    let Parameters {
        args1_1,
        args1_2,
        args2_1,
        args2_2,
        sort1_cons,
        sort2_cons,
        ..
    } = &DEFAULT_PARAMERTERS;

    let [llen, rlen] = [sort1_cons, sort2_cons].map(|s| {
        subst
            .get(s.as_egg())
            .and_then(|&id| list::try_get_egraph(egraph, id))
            .map(|s| s.len())
    });
    let mut map = FxHashMap::default();

    // left side
    for arg_v in [args1_1, args1_2] {
        econtinue_let!(let Some(arg) = subst.get(arg_v.as_egg()));
        map.clear();
        let narg = lambda_subst(egraph, &mut map, nvar, llen?, *arg)?;
        subst.insert(DEFAULT_PARAMERTERS.pair(arg_v)?.as_egg(), narg);
    }

    // right side
    for arg_v in [args2_1, args2_2] {
        econtinue_let!(let Some(arg) = subst.get(arg_v.as_egg()));
        map.clear();
        let narg = lambda_subst(egraph, &mut map, nvar, rlen?, *arg)?;
        subst.insert(DEFAULT_PARAMERTERS.pair(arg_v)?.as_egg(), narg);
    }

    Some(())
}

impl<U> Parameters<U> {
    fn pair(&self, v: &U) -> Option<&U>
    where
        U: Eq,
    {
        let Parameters {
            // args
            args1_1,
            args1_2,
            args2_1,
            args2_2,
            // nargs
            nargs1_1,
            nargs1_2,
            nargs2_1,
            nargs2_2,
            ..
        } = self;
        match_eq!(&v => {
            args1_1 => {Some(nargs1_1)},
            args1_2 => {Some(nargs1_2)},
            args2_1 => {Some(nargs2_1)},
            args2_2 => {Some(nargs2_2)},
            _ => {None}
        })
    }
}

impl QuantifierRule {
    /// Creates the patterns for the quantifier rule.
    fn mk_patterns(bind: FOBinder) -> ([Pattern<Lang>; 3], [Pattern<Lang>; 3]) {
        let Parameters {
            u,
            v,
            h1,
            h2,
            // args
            args1_1,
            args1_2,
            args1_3,
            args2_1,
            args2_2,
            args2_3,
            // nargs
            nargs1_1,
            nargs1_2,
            nargs2_1,
            nargs2_2,
            // other
            sort,
            sort1_cons,
            sort2_cons,
            other,
            ..
        } = &DEFAULT_PARAMERTERS;
        let deduce_m = &BIT_DEDUCE;
        let deduce_b = &BOOL_DEDUCE;
        let capture_pattern = match bind {
            FOBinder::Forall => unreachable!(),
            Exists => [
                rexp!((deduce_b #u #v
                    (EXISTS (CONS #sort #sort1_cons) #args1_1)
                    (EXISTS (CONS #sort #sort2_cons) #args2_1)
                    #h1 #h2)),
                rexp!((deduce_b #u #v
                    (EXISTS (CONS #sort #sort1_cons) #args1_1)
                    #other
                    #h1 #h2)),
                rexp!((deduce_b #u #v
                    #other
                    (EXISTS (CONS #sort #sort1_cons) #args1_1)
                    #h1 #h2)),
            ],
            FindSuchThat => [
                rexp!((deduce_m #u #v
                    (FIND_SUCH_THAT (CONS #sort #sort1_cons) #args1_1 #args1_2 #args1_3)
                    (FIND_SUCH_THAT (CONS #sort #sort2_cons) #args2_1 #args2_2 #args2_3)
                    #h1 #h2)),
                rexp!((deduce_m #u #v
                    (FIND_SUCH_THAT (CONS #sort #sort1_cons) #args1_1 #args1_2 #args1_3)
                    #other
                    #h1 #h2)),
                rexp!((deduce_m #u #v
                    #other
                    (FIND_SUCH_THAT (CONS #sort #sort1_cons) #args1_1 #args1_2 #args1_3)
                    #h1 #h2)),
            ],
        }
        .map(|x| Pattern::from(&x));
        let return_pattern = match bind {
            FOBinder::Forall => unreachable!(),
            Exists => [
                rexp!((deduce_b #u #v
                    (EXISTS #sort1_cons  #nargs1_1)
                    (EXISTS #sort2_cons #nargs2_1)
                    #h1 #h2)),
                rexp!((deduce_b #u #v
                    (EXISTS #sort1_cons #nargs1_1)
                    #other
                    #h1 #h2)),
                rexp!((deduce_b #u #v
                    #other
                    (EXISTS #sort1_cons #nargs1_1)
                    #h1 #h2)),
            ],
            FindSuchThat => [
                rexp!((deduce_m #u #v
                    (FIND_SUCH_THAT #sort1_cons #nargs1_1 #nargs1_2 #args1_3)
                    (FIND_SUCH_THAT #sort2_cons #nargs2_1 #nargs2_2 #args2_3)
                    #h1 #h2)),
                rexp!((deduce_m #u #v
                    (FIND_SUCH_THAT #sort1_cons #nargs1_1 #nargs1_2 #args1_3)
                    #other
                    #h1 #h2)),
                rexp!((deduce_m #u #v
                    #other
                    (FIND_SUCH_THAT #sort1_cons #nargs1_1 #nargs1_2 #args1_3)
                    #h1 #h2)),
            ],
        }
        .map(|x| Pattern::from(&x));
        // tr!("{capture_pattern}\n{return_pattern}")
        (capture_pattern, return_pattern)
    }
}

// Generate the rule for a single quantifier
// Funilly enough it's the same thing for exists and fdst
// fn mk_quantifier_deduce_rules_one<Q: QuantifierT>(_pbl: &Problem, e: &Q) -> PrologRule<Lang> {
//     let deduce = e.top_level_function().get_deduce();
//     let max_var: u32 = chain![e.cvars(), e.bvars()]
//         .flat_map(|v| v.as_u32())
//         .max()
//         .unwrap_or(0)
//         + 1;

//     // initiate the variables
//     let [u, v, h1, h2] = ::std::array::from_fn(|i| [ENodeOrVar::Var(Var::from_usize(i as u32))]);
//     let base_vars_n = 4;

//     // u, v |> exits(vecx, vecsk(vecx)), exists(vecy, vecsk(vecy)) # h1, h2
//     let input = {
//         let mk_applied = |start: u32| {
//             let cvars = e
//                 .cvars()
//                 .iter()
//                 .map(|&v| offset::var(start, v))
//                 .map(|v| vec![ENodeOrVar::Var(v)].into())
//                 .collect_vec();
//             let bvars = e.skolems().iter().map(|f| f.app_var(&cvars)).collect_vec();
//             let args = chain![cvars, bvars].collect_vec();
//             e.top_level_function().app_var(&args)
//         };

//         let left = mk_applied(base_vars_n);
//         let right = mk_applied(base_vars_n + max_var);
//         deduce.app_var(
//             &chain![
//                 [u.as_slice(), v.as_slice()],
//                 [left.deref(), right.deref()],
//                 [h1.as_slice(), h2.as_slice()]
//             ]
//             .collect_vec(),
//         )
//     };

//     // u, v |> exits(vecx, vecfresh), exists(vecy, vecfresh) # h1, h2
//     let dep = {
//         let mk_fresh = |start: u32| {
//             let cvars = e
//                 .cvars()
//                 .iter()
//                 .map(|&v| offset::var(start, v))
//                 .map(|v| vec![ENodeOrVar::Var(v)].into())
//                 .collect_vec();
//             let bvars = e
//                 .fresh_indices()
//                 .iter()
//                 .map(|f| f.app_empty_var())
//                 .collect_vec();
//             let args = chain![cvars, bvars].collect_vec();
//             e.top_level_function().app_var(&args)
//         };

//         let left = mk_fresh(base_vars_n);
//         let right = mk_fresh(base_vars_n + max_var);
//         deduce.app_var(
//             &chain![
//                 [u.as_slice(), v.as_slice()],
//                 [left.deref(), right.deref()],
//                 [h1.as_slice(), h2.as_slice()]
//             ]
//             .collect_vec(),
//         )
//     };

//     PrologRule {
//         input: Pattern::from(input),
//         deps: vec![Pattern::from(dep)],
//         cut: false,
//         require_decrease: false,
//         name: Some(format!("deduce {}", e.top_level_function().name)),
//     }
// }
