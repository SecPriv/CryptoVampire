//! to make sure the generating function don't panic since there is no error
//! handling, but they are deterministic

use super::mk_rewrites_rules;
use crate::Problem;

#[test]
fn mk_rewrite_works() {
    let _: Vec<_> = mk_rewrites_rules::<()>(&Problem::builder().build()).collect();
}
