pub mod iterators;
pub mod outers;
mod traits;

use std::{fmt::Debug, hash::Hash};

pub use traits::*;
pub use outers::Content;

pub use head::*;
mod head;

pub use desctucted::*;
mod desctucted;


// mod substitution {
//     use crate::Formula;

//     pub trait Substitution<F> where F:Formula{
//         fn get(self, var: F::Var) -> Option<F>;
//     }

//     pub struct NVarSubst<F, const N:usize> where F:Formula{
//         vars: [<F as Formula>::Var; N],
//         formulas: [F; N]
//     }

//     impl<F, const N:usize> Substitution<F> for NVarSubst<F, N> where F:Formula, F::Var:Eq{
//         fn get(self, var: <F as Formula>::Var) -> Option<F> {
//             self.vars.iter().position(|v| v == &var)
//                 .and_then(|i| self.formulas.into_iter().nth(i))
//         }
//     }
// }
// pub use substitution::Substitution;