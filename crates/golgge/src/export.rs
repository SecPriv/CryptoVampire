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
//! Human-readable formats (Graphviz, LaTeX) are produced by [`ProofTree::to_dot`]
//! / [`ProofTree::to_latex`] over an [`export_proof_pretty`] tree, whose goal
//! strings come from [`LangRender`] (overridable per-language; S-expr by default).

use std::collections::HashSet;
use std::fmt::Write as _;

use egg::{Id, Language, RecExpr};
use serde::Serialize;
use serde_json::Value;

use crate::{HasMemo, Program, ProofItem, Rule};

/// A serializable view of a single proof node.
///
/// `goal` is the goal term as a string (S-expression from
/// [`egg::EGraph::id_to_expr`], or a [`LangRender`]-rendered form);
/// `rule` is the rule's name; `meta` is the payload rendered by a
/// [`ProofRenderer`]; `children` are the subgoals.
#[derive(Debug, Clone, Serialize)]
pub struct ProofTree {
    /// The e-class id this node proves.
    pub id: u32,
    /// The goal term, as a string.
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
    ///
    /// The `goal` field is the raw S-expression. For pretty (language-aware)
    /// goals, use [`Program::export_proof_pretty`] (requires `L: LangRender`).
    pub fn export_proof<RR>(&self, id: Id, renderer: &RR) -> anyhow::Result<ProofTree>
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
    pub fn dump_proof<RR, W>(&self, id: Id, renderer: &RR, mut writer: W) -> anyhow::Result<()>
    where
        RR: ProofRenderer<R>,
        W: std::io::Write,
    {
        let tree = self.export_proof(id, renderer)?;
        serde_json::to_writer_pretty(&mut writer, &tree)
            .map_err(|e| anyhow::anyhow!("failed to serialize proof: {e}"))?;
        Ok(())
    }

    /// Dumps the proof rooted at `id` as a self-contained, collapsible HTML
    /// page to `writer`.
    ///
    /// The page is a single static `.html` file (no server, no external
    /// dependencies): the proof tree is embedded as JSON and rendered with
    /// native `<details>`/`<summary>` elements (collapsible branches and
    /// terms, zero JS for the core), with a small vanilla-JS viewer for
    /// expand-all/collapse-all.
    pub fn dump_proof_html<RR, W>(&self, id: Id, renderer: &RR, mut writer: W) -> anyhow::Result<()>
    where
        RR: ProofRenderer<R>,
        W: std::io::Write,
    {
        let tree = self.export_proof(id, renderer)?;
        let json = serde_json::to_string(&tree)
            .map_err(|e| anyhow::anyhow!("failed to serialize proof: {e}"))?;
        write!(
            writer,
            "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>Proof</title>\n<style>\n{CSS}\n</style>\n</head>\n<body>\n<div id=\"toolbar\">\n  <button onclick=\"expandAll()\">Expand all</button>\n  <button onclick=\"collapseAll()\">Collapse all</button>\n</div>\n<div id=\"proof\"></div>\n<script>\nconst PROOF = {json};\n{JS}\n</script>\n</body>\n</html>\n"
        )
        .map_err(|e| anyhow::anyhow!("failed to write html: {e}"))?;
        Ok(())
    }
}

/// Pretty-renders a language's terms for human-readable proof export.
///
/// Every `Language + Display` gets a working renderer for free via the blanket
/// impl (raw S-expression); override [`LangRender::render_goal`] for rich output
/// (e.g. math) without adding language-specific code to golgge.
pub trait LangRender: Language + std::fmt::Display {
    /// Renders a goal term for display. Default: the S-expression.
    fn render_goal(expr: &RecExpr<Self>) -> String {
        expr.to_string()
    }
}

/// Blanket impl: every `Language + Display` renders as its S-expression.
impl<L: Language + std::fmt::Display> LangRender for L {}

impl ProofTree {
    /// Renders the tree as a [Graphviz](https://graphviz.org/) `digraph`.
    ///
    /// Each node is labeled with its rule name and a truncated goal; edges point
    /// from a node to its subgoals.
    pub fn to_dot(&self) -> String {
        let mut out = String::new();
        out.push_str("digraph proof {\n");
        out.push_str("    node [shape=box];\n");
        let mut counter = NodeCounter::default();
        self.write_dot(&mut out, &mut counter);
        out.push_str("}\n");
        out
    }

    /// Renders the tree as a LaTeX `forest` proof tree.
    ///
    /// Nodes are labeled with their rule name and a node number (`N0`, `N1`, …);
    /// the full goal terms are listed verbatim in a numbered legend below the
    /// tree, so no information is truncated while keeping the tree compact.
    ///
    /// Requires `\usepackage{forest}` (and `enumitem` for the legend) in the
    /// preamble.
    pub fn to_latex(&self) -> String {
        let mut out = String::new();
        // tree on its own page (tightpage sizes the page to the tree)
        out.push_str("\\begin{preview}\n");
        out.push_str("\\begin{forest}\n");
        out.push_str(
            "  for tree={parent anchor=south, child anchor=north, draw, rounded corners}\n",
        );
        let mut counter = NodeCounter::default();
        self.write_latex(&mut out, 0, &mut counter);
        out.push_str("\\end{forest}\n");
        out.push_str("\\end{preview}\n");

        // legend on a separate page: full goal terms, verbatim
        out.push_str("\\begin{preview}\n");
        out.push_str("\\begin{description}\n");
        let mut counter2 = NodeCounter::default();
        self.write_latex_legend(&mut out, &mut counter2);
        out.push_str("\\end{description}\n");
        out.push_str("\\end{preview}\n");
        out
    }

    /// Renders the tree as a standalone, compilable LaTeX document.
    ///
    /// Same content as [`ProofTree::to_latex`] but wrapped in a default
    /// preamble (landscape A4, `forest` package) so it can be compiled directly
    /// with `pdflatex`.
    pub fn to_latex_document(&self) -> String {
        let mut out = String::new();
        out.push_str(LATEX_DOCUMENT_PREAMBLE);
        out.push_str(&self.to_latex());
        out.push_str("\\end{document}\n");
        out
    }

    fn write_dot(&self, out: &mut String, counter: &mut NodeCounter) -> u32 {
        let me = counter.next();
        let goal = truncate_str(&self.goal, 60).replace('\n', " ");
        let rule = dot_escape(&self.rule);
        let goal = dot_escape(&goal);
        writeln!(out, "    n{me} [label=\"{rule}\\n{goal}\"];").unwrap();
        for child in &self.children {
            let cid = child.write_dot(out, counter);
            writeln!(out, "    n{me} -> n{cid};").unwrap();
        }
        me
    }

    fn write_latex(&self, out: &mut String, depth: usize, counter: &mut NodeCounter) {
        let pad = "  ".repeat(depth);
        let me = counter.next();
        let label = format!(
            "\\textbf{{{}}}\\\\\\textbf{{N{me}}}",
            latex_escape(&self.rule)
        );
        if self.children.is_empty() {
            writeln!(out, "{pad}[{label}]").unwrap();
        } else {
            // forest syntax: open node, children, then close
            writeln!(out, "{pad}[{label}").unwrap();
            for child in &self.children {
                child.write_latex(out, depth + 1, counter);
            }
            writeln!(out, "{pad}]").unwrap();
        }
    }

    fn write_latex_legend(&self, out: &mut String, counter: &mut NodeCounter) {
        let me = counter.next();
        writeln!(
            out,
            "  \\item[N{me}:] \\texttt{{{}}} --- {}",
            latex_escape(&self.rule),
            latex_escape(&self.goal)
        )
        .unwrap();
        for child in &self.children {
            child.write_latex_legend(out, counter);
        }
    }
}

#[derive(Default)]
struct NodeCounter(u32);
impl NodeCounter {
    fn next(&mut self) -> u32 {
        let n = self.0;
        self.0 += 1;
        n
    }
}

/// Default LaTeX preamble for a standalone proof document.
///
/// Uses the `preview` package with `tightpage` so each proof tree and each
/// legend is rendered on its own page sized to fit the content (large trees
/// get large pages, no clipping). `\PreviewBorder` adds breathing room.
pub const LATEX_DOCUMENT_PREAMBLE: &str = "\
\\documentclass{article}
\\usepackage[active,tightpage]{preview}
\\usepackage[utf8]{inputenc}
\\usepackage[T1]{fontenc}
\\usepackage{forest}
\\usepackage{enumitem}
\\PreviewBorder=10pt
\\begin{document}
";

/// CSS for the HTML proof viewer. Graphviz-X11-ish: monospace, thin black
/// box borders, white background, indented nesting.
const CSS: &str = r#"
:root { color-scheme: light; }
body {
  font-family: monospace;
  font-size: 13px;
  margin: 0;
  padding: 8px;
  background: white;
  color: black;
}
#toolbar { margin-bottom: 8px; }
#toolbar button {
  font-family: inherit; font-size: 13px;
  margin-right: 4px; padding: 2px 8px;
}
#proof { line-height: 1.4; }
details {
  border: 1px solid #888;
  border-radius: 2px;
  margin: 1px 0 1px 14px;
  padding: 2px 4px;
  background: white;
}
summary {
  cursor: pointer;
  list-style: none;
  white-space: pre-wrap;
}
summary::-webkit-details-marker { display: none; }
.node-id { color: #0066cc; font-weight: bold; }
.rule   { font-weight: bold; }
.term {
  margin: 2px 0 2px 14px;
  padding: 2px 4px;
  border-left: 2px solid #ccc;
  white-space: pre-wrap;
  word-break: break-all;
}
.children { margin-top: 2px; }
.meta {
  margin: 2px 0 2px 14px;
  padding: 2px 4px;
  border-left: 2px solid #888;
}
.meta-title { font-style: italic; }
.smt-file { white-space: pre-wrap; word-break: break-all; }
.solver { font-weight: bold; }
"#;

/// Vanilla-JS viewer: renders PROOF (embedded JSON) as nested <details>.
///
/// Collapsed: shows [N0] rule-name. Expanded: shows the goal term inline in a
/// <div>, plus children as nested <details>. Expand-all/collapse-all via buttons.
const JS: &str = r#"
function renderNode(node) {
  const d = document.createElement('details');
  const s = document.createElement('summary');
  const id = document.createElement('span');
  id.className = 'node-id';
  id.textContent = '[N' + node.id + ']';
  const rule = document.createElement('span');
  rule.className = 'rule';
  rule.textContent = ' ' + node.rule;
  s.appendChild(id); s.appendChild(rule);
  d.appendChild(s);
  const term = document.createElement('div');
  term.className = 'term';
  term.textContent = node.goal;
  d.appendChild(term);
  if (node.meta) { d.appendChild(renderMeta(node.meta)); }
  if (node.children && node.children.length) {
    const c = document.createElement('div');
    c.className = 'children';
    node.children.forEach(ch => c.appendChild(renderNode(ch)));
    d.appendChild(c);
  }
  return d;
}
const root = renderNode(PROOF);
document.getElementById('proof').appendChild(root);
function expandAll()   { document.querySelectorAll('details').forEach(d => d.open = true); }
function collapseAll() { document.querySelectorAll('details').forEach(d => d.open = false); }
function renderMeta(meta) {
  const wrap = document.createElement('div');
  wrap.className = 'meta';
  const title = document.createElement('div');
  title.className = 'meta-title';
  title.textContent = 'solver artifacts:';
  wrap.appendChild(title);
  if (meta.smt_files) {
    meta.smt_files.forEach(f => {
      const row = document.createElement('div');
      row.className = 'smt-file';
      const solver = document.createElement('span');
      solver.className = 'solver';
      solver.textContent = f.solver + ': ';
      row.appendChild(solver);
      const a = document.createElement('a');
      a.href = 'file://' + f.path;
      a.textContent = f.path;
      row.appendChild(a);
      wrap.appendChild(row);
    });
  }
  return wrap;
}
"#;

/// Truncates `s` to at most `max` chars, appending `…` if truncated.
fn truncate_str(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        s.to_string()
    } else {
        let truncated: String = s.chars().take(max.saturating_sub(1)).collect();
        format!("{truncated}…")
    }
}

/// Escapes a string for use in a Graphviz double-quoted label.
fn dot_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Escapes a string for use in LaTeX text.
fn latex_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\textbackslash{}"),
            '&' => out.push_str("\\&"),
            '%' => out.push_str("\\%"),
            '$' => out.push_str("\\$"),
            '#' => out.push_str("\\#"),
            '_' => out.push_str("\\_"),
            '{' => out.push_str("\\{"),
            '}' => out.push_str("\\}"),
            '~' => out.push_str("\\textasciitilde{}"),
            '^' => out.push_str("\\textasciicircum{}"),
            '…' => out.push_str("\\dots"),
            'λ' => out.push_str("\\ensuremath{\\lambda}"),
            _ => out.push(c),
        }
    }
    out
}

impl<L, N, R> Program<L, N, R>
where
    L: LangRender,
    N: egg::Analysis<L>,
    N::Data: HasMemo,
    R: Rule<L, N, R> + Clone + 'static + Send + Sync,
{
    /// Exports the proof rooted at `id` as a [`ProofTree`] with pretty-rendered
    /// goals via [`LangRender::render_goal`].
    ///
    /// Like [`Program::export_proof`], but the `goal` field uses the language's
    /// rich renderer instead of the raw S-expression. Falls back to the
    /// S-expression via the blanket impl of [`LangRender`].
    pub fn export_proof_pretty<RR>(&self, id: Id, renderer: &RR) -> anyhow::Result<ProofTree>
    where
        RR: ProofRenderer<R>,
    {
        let mut visited = HashSet::new();
        self.export_proof_pretty_inner(id, renderer, &mut visited)
    }

    fn export_proof_pretty_inner<RR>(
        &self,
        id: Id,
        renderer: &RR,
        visited: &mut HashSet<Id>,
    ) -> anyhow::Result<ProofTree>
    where
        RR: ProofRenderer<R>,
    {
        let item = self.get_proof_item(id)?;
        let expr = self.egraph().id_to_expr(id);
        let goal = L::render_goal(&expr);
        let rule = item.rule.name().into_owned();
        let meta = renderer.render(&item);

        let children = if visited.insert(id) {
            item.ids
                .iter()
                .map(|&cid| self.export_proof_pretty_inner(cid, renderer, visited))
                .collect::<Result<_, _>>()?
        } else {
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

    /// Dumps the proof rooted at `id` as a Graphviz `digraph` to `writer`.
    pub fn dump_proof_dot<RR, W>(&self, id: Id, renderer: &RR, mut writer: W) -> anyhow::Result<()>
    where
        RR: ProofRenderer<R>,
        W: std::io::Write,
    {
        let tree = self.export_proof_pretty(id, renderer)?;
        write!(writer, "{}", tree.to_dot())
            .map_err(|e| anyhow::anyhow!("failed to write dot: {e}"))?;
        Ok(())
    }

    /// Dumps the proof rooted at `id` as a LaTeX `forest` tree to `writer`.
    pub fn dump_proof_latex<RR, W>(
        &self,
        id: Id,
        renderer: &RR,
        mut writer: W,
    ) -> anyhow::Result<()>
    where
        RR: ProofRenderer<R>,
        W: std::io::Write,
    {
        let tree = self.export_proof_pretty(id, renderer)?;
        write!(writer, "{}", tree.to_latex())
            .map_err(|e| anyhow::anyhow!("failed to write latex: {e}"))?;
        Ok(())
    }

    /// Dumps the proof rooted at `id` as a standalone LaTeX document.
    pub fn dump_proof_latex_document<RR, W>(
        &self,
        id: Id,
        renderer: &RR,
        mut writer: W,
    ) -> anyhow::Result<()>
    where
        RR: ProofRenderer<R>,
        W: std::io::Write,
    {
        let tree = self.export_proof_pretty(id, renderer)?;
        write!(writer, "{}", tree.to_latex_document())
            .map_err(|e| anyhow::anyhow!("failed to write latex document: {e}"))?;
        Ok(())
    }
}

/// Builds a standalone LaTeX `main.tex` that imports a set of per-step forest
/// files via `\input`, each under a `\section` heading.
///
/// `step_files` is `(display_name, filename)` pairs, where `filename` is the
/// bare `.tex` file to `\input` (relative to the main document). Used by
/// callers that dump one proof per step and want a single compilable document
/// for the whole run.
pub fn latex_main(step_files: &[(String, String)]) -> String {
    let mut out = String::new();
    out.push_str(LATEX_DOCUMENT_PREAMBLE);
    for (name, file) in step_files {
        // `tightpage` ships only `preview` environments, so a `\section` here
        // would not render; leave a source-level marker instead.
        out.push_str("% --- step: ");
        out.push_str(name);
        out.push_str(" ---\n");
        out.push_str("\\input{");
        out.push_str(file);
        out.push_str("}\n");
    }
    out.push_str("\\end{document}\n");
    out
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
        let egraph =
            EGraph::<SymbolLang, GolggeAnalysis<(), SymbolLang>>::new(GolggeAnalysis::new(()));
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
        assert!(
            json["children"][0]["goal"]
                .as_str()
                .unwrap()
                .contains("leaf")
        );
    }

    #[test]
    fn dot_and_latex_round_trip() {
        let (mut prgm, parent, child) = mk_program();
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

        let dot = prgm.dump_proof_dot_to_string(parent);
        assert!(dot.contains("digraph proof"));
        assert!(dot.contains("n0 -> n1"));

        let latex = prgm.dump_proof_latex_to_string(parent);
        assert!(latex.contains("\\begin{forest}"));
        assert!(latex.contains("\\textbf{step}"));
        assert!(latex.contains("\\textbf{axiom}"));
        // legend lists the full goals, not truncated
        assert!(latex.contains("\\begin{description}"));
        assert!(latex.contains("\\item[N0:"));
        assert!(latex.contains("leaf"));
        // tree and legend each wrapped in their own preview (auto-sized pages)
        assert_eq!(latex.matches("\\begin{preview}").count(), 2);
        // regression: a parent node must NOT self-close before its children.
        // The opening node line is `[label` (no trailing `]`); the child appears
        // on the next line, indented; only then is the parent closed.
        let parent_line = latex
            .lines()
            .find(|l| l.contains("\\textbf{step}"))
            .expect("parent line");
        assert!(
            !parent_line.trim_end().ends_with(']'),
            "parent node self-closes before children: {parent_line}"
        );
        // brackets must balance (well-formed forest)
        let opens = latex.matches('[').count();
        let closes = latex.matches(']').count();
        assert_eq!(
            opens, closes,
            "unbalanced forest brackets: {opens} open vs {closes} close"
        );
    }

    #[test]
    fn html_dumps_a_page() {
        let (mut prgm, parent, child) = mk_program();
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

        let html = prgm.dump_proof_html_to_string(parent);
        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("<style>"));
        assert!(html.contains("<script>"));
        // the JSON carries the proof; the JS renders it as <details> at runtime
        assert!(html.contains("const PROOF ="));
        assert!(html.contains("renderNode"));
        assert!(html.contains("step"));
        assert!(html.contains("leaf"));
    }

    // Small helpers so the dot/latex/html test reads cleanly; not part of the API.
    trait TestExt {
        fn dump_proof_dot_to_string(&self, id: Id) -> String;
        fn dump_proof_latex_to_string(&self, id: Id) -> String;
        fn dump_proof_html_to_string(&self, id: Id) -> String;
    }
    impl TestExt for Program<SymbolLang, GolggeAnalysis<(), SymbolLang>, TRule> {
        fn dump_proof_dot_to_string(&self, id: Id) -> String {
            let tree = self.export_proof_pretty(id, &()).unwrap();
            tree.to_dot()
        }
        fn dump_proof_latex_to_string(&self, id: Id) -> String {
            let tree = self.export_proof_pretty(id, &()).unwrap();
            tree.to_latex()
        }
        fn dump_proof_html_to_string(&self, id: Id) -> String {
            let mut buf = Vec::new();
            self.dump_proof_html(id, &(), &mut buf).unwrap();
            String::from_utf8(buf).unwrap()
        }
    }
}
