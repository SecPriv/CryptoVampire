//! to make sure the generating function don't panic since there is no error
//! handling, but they are deterministic

use crate::{rules::default_rewrites::mk_rewrites, Problem};

#[test]
fn mk_rewrite_works() {
    let _: Vec<_> = mk_rewrites::<()>(&Problem::builder().build()).collect();
}
