//! to make sure the generating function don't panic since there is no error
//! handling, but they are deterministic

use crate::Problem;

use super::mk_rewrites_rules;

#[test]
fn mk_rewrite_works() {
    let _: Vec<_> = mk_rewrites_rules::<()>(&Problem::base_empty()).collect();
}
