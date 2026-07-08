//! Proof export: turn a memoized proof tree into a serializable IR.
//!
//! A proof is a tree rooted at an [`egg::Id`], walked via
//! [`Program::get_proof_item`]. Each node records the goal term, the rule that
//! was applied, and (optionally) metadata rendered from the
//! [`ProofItem`]'s type-erased payload.
//!
//! The payload is downstream-specific (e.g. an `indistinguishability`
//! `PRFProof`), so golgge cannot render it directly. Downstream crates implement
//! [`ProofRenderer`] where the concrete rule/payload types are known, and golgge
//! stays generic over `R`.
//!
//! The IR is write-only: [`ProofTree::goal`] is an S-expression string (how
//! [`RecExpr`](egg::RecExpr) serializes), so a future renderer (e.g. a LaTeX
//! proof tree) can walk it directly without depending on golgge internals.

use std::collections::HashSet;

use egg::{Id, Language};
use serde::Serialize;
use serde_json::Value;

use crate::{HasMemo, ProofItem, Program, Rule};

/// A serializable view of a single proof node.
///
/// `goal` is the S-expression of the term being proven at this node (from
/// [`egg::EGraph::id_to_expr`]); `rule` is the rule's name; `meta` is the payload
/// rendered by a [`ProofRenderer`]; `children` are the subgoals.
#[derive(Debug, Clone, Serialize)]
pub struct ProofTree {
    /// The e-class id this node proves.
    pub id: u32,
    /// The goal term, as an S-expression string.
    pub goal: String,
    /// The name of the rule applied at this node.
    pub rule: String,
    /// Metadata rendered from the node's payload, if any.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meta: Option<Value>,
    /// The subgoals, one entry per dependency.
    pub children: Vec<ProofTree>,
}

/// Renders a [`ProofItem`]'s type-erased payload into serializable metadata.
///
/// Implement this where the concrete rule type `R` and the payload type are
/// known (i.e. in the downstream crate that produced the payload), by
/// downcasting [`ProofItem::payload`] and producing a [`serde_json::Value`].
///
/// The blanket impl for `()` produces no metadata, which is useful for tests
/// and for consumers that don't care about payloads.
pub trait ProofRenderer<R> {
    /// Renders the metadata for the given proof item, if any.
    fn render(&self, item: &ProofItem<R>) -> Option<Value>;
}

/// Default renderer: produces no metadata.
impl<R> ProofRenderer<R> for () {
    fn render(&self, _item: &ProofItem<R>) -> Option<Value> {
        None
    }
}

impl<L, N, R> Program<L, N, R>
where
    L: Language + std::fmt::Display,
    N: egg::Analysis<L>,
    N::Data: HasMemo,
    R: Rule<L, N, R> + Clone + 'static + Send + Sync,
{
    /// Exports the proof rooted at `id` as a [`ProofTree`].
    ///
    /// Requires memoisation to be enabled and `id` to be `Proven`. Cycles are
    /// guarded against: a repeated `id` yields a node with empty children, so a
    /// malformed proof never infinite-loops.
    pub fn export_proof<RR>(
        &self,
        id: Id,
        renderer: &RR,
    ) -> anyhow::Result<ProofTree>
    where
        RR: ProofRenderer<R>,
    {
        let mut visited = HashSet::new();
        self.export_proof_inner(id, renderer, &mut visited)
    }

    fn export_proof_inner<RR>(
        &self,
        id: Id,
        renderer: &RR,
        visited: &mut HashSet<Id>,
    ) -> anyhow::Result<ProofTree>
    where
        RR: ProofRenderer<R>,
    {
        let item = self.get_proof_item(id)?;
        let goal = self.egraph().id_to_expr(id).to_string();
        let rule = item.rule.name().into_owned();
        let meta = renderer.render(&item);

        let children = if visited.insert(id) {
            item.ids
                .iter()
                .map(|&cid| self.export_proof_inner(cid, renderer, visited))
                .collect::<Result<_, _>>()?
        } else {
            // already expanded this id elsewhere: cut to avoid a cycle
            Vec::new()
        };

        Ok(ProofTree {
            id: u32::try_from(usize::from(id)).expect("id fits in u32"),
            goal,
            rule,
            meta,
            children,
        })
    }

    /// Dumps the proof rooted at `id` as pretty JSON to `writer`.
    pub fn dump_proof<RR, W>(
        &self,
        id: Id,
        renderer: &RR,
        mut writer: W,
    ) -> anyhow::Result<()>
    where
        RR: ProofRenderer<R>,
        W: std::io::Write,
    {
        let tree = self.export_proof(id, renderer)?;
        serde_json::to_writer_pretty(&mut writer, &tree)
            .map_err(|e| anyhow::anyhow!("failed to serialize proof: {e}"))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Config, GolggeAnalysis};
    use egg::{EGraph, SymbolLang};
    use std::borrow::Cow;

    /// A minimal rule type, only used to label proof nodes in the test.
    #[derive(Clone)]
    struct TRule(&'static str);
    impl<L: Language, N: egg::Analysis<L>> Rule<L, N, TRule> for TRule {
        fn search(&self, _: &mut Program<L, N, TRule>, _: Id) -> crate::Dependancy {
            crate::Dependancy::impossible()
        }
        fn name(&self) -> Cow<'_, str> {
            Cow::Borrowed(self.0)
        }
    }

    fn mk_program() -> (
        Program<SymbolLang, GolggeAnalysis<(), SymbolLang>, TRule>,
        Id,
        Id,
    ) {
        let egraph = EGraph::<SymbolLang, GolggeAnalysis<(), SymbolLang>>::new(
            GolggeAnalysis::new(()),
        );
        let prgm = Program::build()
            .egraph(egraph)
            .config(Config::default())
            .call();

        let mut prgm = prgm;
        let child = prgm.add_expr(&"(leaf)".parse().unwrap());
        let parent = prgm.add_expr(&"(parent)".parse().unwrap());
        (prgm, parent, child)
    }

    #[test]
    fn export_proof_dumps_a_tree() {
        let (mut prgm, parent, child) = mk_program();
        assert!(prgm.is_memo_enabled());

        // Manually memoize a 2-level proof: child is an axiom, parent uses TRule.
        use crate::analysis::erase;
        prgm.egraph_mut()[child]
            .data
            .memo_mut()
            .set_proven(erase(ProofItem {
                rule: TRule("axiom"),
                ids: vec![],
                payload: None,
            }));
        prgm.egraph_mut()[parent]
            .data
            .memo_mut()
            .set_proven(erase(ProofItem {
                rule: TRule("step"),
                ids: vec![child],
                payload: None,
            }));

        let tree = prgm.export_proof(parent, &()).expect("export");
        assert_eq!(tree.rule, "step");
        assert_eq!(tree.children.len(), 1);
        assert_eq!(tree.children[0].rule, "axiom");
        assert!(tree.children[0].children.is_empty());

        // JSON round-trip is valid and contains both goals.
        let mut buf = Vec::new();
        prgm.dump_proof(parent, &(), &mut buf).expect("dump");
        let json: Value = serde_json::from_slice(&buf).expect("valid json");
        assert_eq!(json["rule"], "step");
        assert_eq!(json["children"][0]["rule"], "axiom");
        assert!(json["children"][0]["goal"].as_str().unwrap().contains("leaf"));
    }
}
