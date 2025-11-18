use egg::Analysis;

use crate::Lang;

fn mk_static_rewrites<N: Analysis<Lang>>() -> impl Iterator<Item = egg::Rewrite<Lang, N>> {
    decl_vars![t, t1, t2, a, b, c, v1, v2, p, n, u, v];

    mk_many_rewrites! {
      ["public message"]
      (#v1 = (LT #t CURRENT_STEP), #v1 = true, #v2 = PARK_IS_PUBLIC) =>
        (#v2 =  (PARK_PARKER_IS_PUBLIC (MACRO_)))
    }
    .into_iter()
}
