use std::collections::VecDeque;
use std::fmt::Display;

use egg::{
    Analysis, Applier, EClass, EGraph, ENodeOrVar, Id, Language, PatternAst, Rewrite, Searcher,
    SymbolLang, Var,
};
use itertools::{Itertools, chain};
use log::{log_enabled, trace};
use smallvec::SmallVec;
use utils::{ebreak_if, ebreak_let, econtinue_if, ereturn_if};

/// A trait for languages that have a concept of a 'true' value.
pub trait WithTrue: Language {
    /// Creates a 'true' value for the language.
    fn mk_true() -> Self;
    /// Returns `true` if the given value is a 'true' value.
    fn is_true(&self) -> bool;
}

/// A trait for languages that have a concept of a 'false' value.
#[allow(dead_code)]
pub trait WithFalse: Language {
    /// Creates a 'false' value for the language.
    fn mk_false() -> Self;
    /// Returns `true` if the given value is a 'false' value.
    fn is_false(&self) -> bool;
}

/// A trait for languages that have a concept of an 'and' operation.
pub trait WithAnd: WithTrue {
    /// Creates an 'and' expression with the given children.
    fn mk_and(a: Id, b: Id) -> Self;

    /// Returns `true` if the given value is an 'and' expression.
    fn is_and(&self) -> bool;

    /// Creates a pattern for a nested 'and' expression.
    fn mk_and_pattern(from: egg::uvar, n: usize) -> PatternAst<Self> {
        if n == 0 {
            return vec![ENodeOrVar::ENode(Self::mk_true())].into();
        }
        let mut ret = Vec::with_capacity(2 * n - 1);
        ret.push(ENodeOrVar::Var(Var::from_usize(from)));
        for i in 1..(n as egg::uvar) {
            ret.push(ENodeOrVar::Var(Var::from_usize(from + i)));
            ret.push(ENodeOrVar::ENode(Self::mk_and(
                (2 * (i - 1) as usize).into(),
                ((2 * (i - 1)) + 1 as usize).into(),
            )));
        }
        ret.into()
    }
}

impl WithTrue for SymbolLang {
    /// Creates a 'true' value for `SymbolLang`.
    fn mk_true() -> Self {
        Self::leaf("mtrue")
    }

    /// Returns `true` if the `SymbolLang` value is a 'true' value.
    fn is_true(&self) -> bool {
        self.discriminant().as_str() == "mtrue"
    }
}

impl WithFalse for SymbolLang {
    /// Creates a 'false' value for `SymbolLang`.
    fn mk_false() -> Self {
        Self::leaf("mfalse")
    }

    /// Returns `true` if the `SymbolLang` value is a 'false' value.
    fn is_false(&self) -> bool {
        self.discriminant().as_str() == "mfalse"
    }
}

impl WithAnd for SymbolLang {
    /// Creates an 'and' expression for `SymbolLang`.
    fn mk_and(a: Id, b: Id) -> Self {
        Self::new("mand", vec![a, b])
    }

    /// Returns `true` if the `SymbolLang` value is an 'and' expression.
    fn is_and(&self) -> bool {
        self.discriminant().as_str() == "mand"
    }
}

#[derive(Debug, Default)]
struct MaybeRecAnd(SmallVec<[Id; 3]>);

impl std::ops::Deref for MaybeRecAnd {
    type Target = SmallVec<[Id; 3]>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl MaybeRecAnd {
    /// Wheter this should trigger any recursive call
    pub fn is_leaf(&self) -> bool {
        self.is_empty()
    }
}

impl FromIterator<Id> for MaybeRecAnd {
    fn from_iter<T: IntoIterator<Item = Id>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl From<SmallVec<[Id; 3]>> for MaybeRecAnd {
    fn from(value: SmallVec<[Id; 3]>) -> Self {
        Self(value)
    }
}

fn get_rec_and<L: Language + WithAnd, D>(eclass: &EClass<L, D>) -> MaybeRecAnd {
    let approx_size = eclass.iter().filter(|x| x.is_and()).count() * 2;
    ereturn_if!(approx_size == 0, Default::default());
    let mut res = SmallVec::with_capacity(approx_size);
    let iter = eclass
        .iter()
        .filter(|x| x.is_and())
        .filter(|x| x.children().iter().all(|c| c != &eclass.id)) // skip self recursive calls
        .flat_map(|x| x.children().iter());
    // .filter(|&&x| !(x == eclass || Some(x) == mtrue));
    for &x in iter {
        econtinue_if!(x == eclass.id);
        res.push(x);
    }
    res.into()
}

fn compute_conected_component2<L: Language + WithAnd + WithFalse + Display, N: Analysis<L>>(
    egraph: &EGraph<L, N>,
    eclass: Id,
    mut fuel: usize,
) -> Option<Vec<Id>> {
    // leafs \cap todos = \empty and there are no duplicates at all time
    let mut leafs = Vec::new(); // ids where we can go no further
    let mut todos: VecDeque<_> = [eclass].into(); // ids that can loop

    loop {
        // exit if no fuel or nothing to do
        ebreak_if!(fuel == 0);
        ebreak_let!(let Some(id) = todos.pop_front());
        fuel -= 1;

        trace!("inspecting ({id}) {}", egraph.id_to_expr(id));
        let current_eclass = &egraph[id];

        if current_eclass.iter().any(L::is_true) {
            trace!("skipped true");
            continue;
        }; // skip true
        ereturn_if!(current_eclass.iter().any(L::is_false), None); // exit if false

        let rec = get_rec_and(current_eclass);

        // if it's a leaf, add it to the list and continue
        if rec.is_leaf() {
            leafs.push(id);
            trace!("added leaf");
            continue;
        }

        // add the new nodes that are not already pending
        let mut i = 0;
        todos.reserve(rec.len());
        for x in rec.iter() {
            if chain!(&leafs, &todos).contains(x) {
                trace!("{} is already in todo or leaf", egraph.id_to_expr(*x));
                continue;
            }
            todos.push_back(*x);
            i += 1;
        }
        trace!("added {i:} to todos")
    }
    ereturn_if!(
        todos.is_empty() && (leafs == [eclass] || leafs.is_empty()),
        None
    );

    if cfg!(debug_assertions) && fuel == 0 {
        trace!("ran out of fuel")
    }

    // collect and sort the result
    let mut res = chain!(leafs, todos).collect_vec();
    ereturn_if!(res.len() == 2, None); // would do nothing
    res.sort();
    if cfg!(debug_assertions) && res.len() != 2 {
        let expr = egraph.id_to_expr(eclass);
        trace!("({:}) : {}", res.len(), expr.pretty(80));
        for id in &res {
            trace!("-> {}", egraph.id_to_expr(*id).pretty(80))
        }
    }
    Some(res)
}

struct AndSimplifier;

impl<L: Language + WithAnd + WithFalse + Display, N: Analysis<L>> Searcher<L, N> for AndSimplifier {
    fn search_eclass_with_limit(
        &self,
        egraph: &egg::EGraph<L, N>,
        eclass: Id,
        limit: usize,
    ) -> Option<egg::SearchMatches<'_, L>> {
        let res = compute_conected_component2(egraph, eclass, limit)?;
        ereturn_if!(res == [eclass], None); // In that case, `eclass` is already a leaf, and we don't rewrite

        // build the substitution: res[i] is pointed to by #i.
        let subst = res
            .into_iter()
            .filter(|id| id != &eclass)
            .enumerate()
            .map(|(i, id)| (Var::from_usize(i as egg::uvar), id))
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

// impl<L: Language + WithAnd + WithFalse + Display + FromOp, N: Analysis<L>> Applier<L, N>
impl<N: Analysis<SymbolLang>> Applier<SymbolLang, N> for AndSimplifier {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<SymbolLang, N>,
        eclass: Id,
        subst: &egg::Subst,
        _: Option<&PatternAst<SymbolLang>>,
        name: egg::Symbol,
    ) -> Vec<Id> {
        // build the pattern of nested ands
        let id = SymbolLang::mk_and_pattern(0, subst.len()).apply_susbt(egraph, subst);
        if log_enabled!(log::Level::Trace) {
            trace!(
                "rewrote (a -> b):\na. {}\nb. {:}",
                egraph.id_to_expr(eclass).pretty(80),
                egraph.id_to_expr(id).pretty(80)
            );
            // if egraph[id].iter().any(|x| x.is_false()) {
            //     let mut explaination = egraph.explain_equivalence(
            //         &"mfalse".parse().unwrap(),
            //         &egraph.id_to_expr(id),
            //     );
            //     trace!("{}", explaination.get_flat_string());
            //     panic!()
            // }
        }
        let did_something = egraph.union_trusted(eclass, id, name);
        if did_something { vec![id] } else { vec![] }
    }
}

// pub fn and_simpl_rewrite<L: Language + WithAnd + WithFalse + Display + FromOp, N: Analysis<L>>(
/// Creates a rewrite rule for simplifying 'and' expressions.
pub fn and_simpl_rewrite<N: Analysis<SymbolLang>>() -> Rewrite<SymbolLang, N> {
    Rewrite::new("and_simpl", AndSimplifier, AndSimplifier).unwrap()
}

#[cfg(test)]
mod tests {
    use egg::{PatternAst, SymbolLang};

    use super::WithAnd;

    #[test]
    fn mk_ands() {
        for n in 0..10 {
            let p: PatternAst<SymbolLang> = SymbolLang::mk_and_pattern(0, n);
            eprintln!("({n:}) {}", p.pretty(80))
        }
    }
}
