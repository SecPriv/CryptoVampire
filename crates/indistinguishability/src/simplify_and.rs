use std::collections::{HashSet, VecDeque};

use egg::{
    Analysis, Applier, EGraph, ENodeOrVar, Id, Language, Pattern, PatternAst, RecExpr, Rewrite,
    SearchMatches, Searcher, SymbolLang, Var,
};
use itertools::{chain, Itertools};
use utils::{ebreak_if, ebreak_let, ereturn_if};

pub trait WithTrue: Language {
    fn mk_true() -> Self;
    fn is_true(&self) -> bool;
}

pub trait WithAnd: WithTrue {
    fn mk_and(a: Id, b: Id) -> Self;

    fn is_and(&self) -> bool;

    fn mk_and_pattern(from: u32, n: usize) -> PatternAst<Self> {
        if n == 0 {
            return vec![ENodeOrVar::ENode(Self::mk_true())].into();
        }
        let mut ret = Vec::with_capacity(2 * n - 1);
        ret.push(ENodeOrVar::Var(Var::from_u32(from)));
        for i in 1..(n as u32) {
            ret.push(ENodeOrVar::Var(Var::from_u32(from + i)));
            ret.push(ENodeOrVar::ENode(Self::mk_and(
                ((2 * (i - 1)) as usize).into(),
                ((2 * (i - 1) + 1) as usize).into(),
            )));
        }
        ret.into()
    }
}

impl WithTrue for SymbolLang {
    fn mk_true() -> Self {
        Self::leaf("mtrue")
    }

    fn is_true(&self) -> bool {
        self.discriminant().as_str() == "mtrue"
    }
}

impl WithAnd for SymbolLang {
    fn mk_and(a: Id, b: Id) -> Self {
        Self::new("mand", vec![a, b])
    }

    fn is_and(&self) -> bool {
        self.discriminant().as_str() == "mand"
    }
}

struct MaybeRecAnd(Vec<Id>);

impl MaybeRecAnd {
    /// Wheter this should trigger any recursive call
    pub fn is_leaf(&self) -> bool {
        self.is_empty()
    }
}

impl std::ops::Deref for MaybeRecAnd {
    type Target = Vec<Id>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl FromIterator<Id> for MaybeRecAnd {
    fn from_iter<T: IntoIterator<Item = Id>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

fn get_rec_and<L: Language + WithAnd, N: Analysis<L>>(
    egraph: &EGraph<L, N>,
    eclass: Id,
) -> MaybeRecAnd {
    let mtrue = egraph.lookup_expr(&vec![L::mk_true()].into());

    egraph[eclass]
        .iter()
        .filter(|x| x.is_and())
        .flat_map(|x| x.children().iter())
        .filter(|&&x| !(x == eclass || Some(x) == mtrue))
        .copied()
        .collect()
}

fn compute_conected_component2<L: Language + WithAnd, N: Analysis<L>>(
    egraph: &EGraph<L, N>,
    eclass: Id,
    mut fuel: usize,
) -> Vec<Id> {
    /* leafs \cap todos = \empty and there are no duplicates at all time */
    let mut leafs = Vec::new(); // ids where we can go no further
    let mut todos: VecDeque<_> = [eclass].into(); // ids that can loop

    loop {
        // exit if no fuel or nothing to do
        ebreak_if!(fuel == 0);
        ebreak_let!(let Some(id) = todos.pop_front());
        fuel -= 1;

        let rec = get_rec_and(egraph, id);

        // if it's a leaf, add it to the list and continue
        if rec.is_leaf() {
            leafs.push(id);
            continue;
        }

        // add the new nodes that are no already pending
        todos.reserve(rec.len());
        for x in rec.iter() {
            if !chain!(&leafs, &todos).contains(x) {
                todos.push_back(*x);
            }
        }
    }
    if cfg!(debug_assertions) && fuel == 0 {
      println!("ran out of fuel")
    }

    // collect and sort the result
    let mut res = chain!(leafs, todos).collect_vec();
    res.sort();
    res
}

struct AndSimplifier;

impl<L: Language + WithAnd, N: Analysis<L>> Searcher<L, N> for AndSimplifier {
    fn search_eclass_with_limit(
        &self,
        egraph: &egg::EGraph<L, N>,
        eclass: Id,
        limit: usize,
    ) -> Option<egg::SearchMatches<'_, L>> {
        let res = compute_conected_component2(egraph, eclass, limit);
        ereturn_if!(res == [eclass], None); // In that case, `eclass` is already a leaf, and we don't rewrite

        // build the substitution: res[i] is pointed to by #i.
        let subst = res
            .into_iter()
            .filter(|id| id != &eclass)
            .enumerate()
            .map(|(i, id)| (Var::from_u32(i as u32), id))
            .collect();

        Some(egg::SearchMatches {
            eclass,
            ast: None,
            substs: vec![subst],
        })
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

impl<L: Language + WithAnd, N: Analysis<L>> Applier<L, N> for AndSimplifier {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<L, N>,
        eclass: Id,
        subst: &egg::Subst,
        _: Option<&PatternAst<L>>,
        name: egg::Symbol,
    ) -> Vec<Id> {
        // build the pattern of nested ands
        let id = L::mk_and_pattern(0, subst.len()).apply_susbt(egraph, subst);
        egraph.union_trusted(eclass, id, name);
        vec![id]
    }
}

pub fn and_simpl_rewrite<L: Language + WithAnd, N: Analysis<L>>() -> Rewrite<L, N> {
    Rewrite::new("and_simpl", AndSimplifier, AndSimplifier).unwrap()
}
