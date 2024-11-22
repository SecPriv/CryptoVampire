#[allow(clippy::module_inception)]
mod formula;
pub use formula::*;

mod arc;
pub use arc::*;

mod expanding_formula;
pub use expanding_formula::{EitherQuantifier, Expander};

pub mod macros {
    #[macro_export]
    macro_rules! mforall {
        ($($var:ident!$n:literal:$sort:expr),*; $content:block) => {{
            $(
                let $var = $crate::formula::variable::Variable { id: $n, sort: $sort};
            )*
            $crate::formula::formula::forall([$($var),*], {
                // $(
                //     let $var = $var.into_aformula();
                // )*
                $content
            })
        }};
        ($vars:expr, $content:block) => {
            $crate::formula::formula::forall($vars, $content)
        }
    }

    #[macro_export]
    macro_rules! mexists {
        ($($var:ident!$n:literal:$sort:expr),*; $content:block) => {{
            $(
                let $var = $crate::formula::variable::Variable { id: $n, sort: $sort};
            )*
            $crate::formula::formula::exists([$($var),*], {
                // $(
                //     let $var = $var.into_aformula();
                // )*
                $content
            })
        }};
        ($vars:expr, $content:block) => {
            $crate::formula::formula::exists($vars, $content)
        }
    }

    pub use {mexists, mforall};
}
