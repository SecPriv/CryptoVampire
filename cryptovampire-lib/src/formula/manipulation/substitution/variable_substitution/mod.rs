mod one_var;
pub use one_var::{OneVarSubst, OneVarSubstF};

mod owned_var;
pub use owned_var::{MultipleVarSubst, MulitpleVarSubstF};

mod ref_substitution;
pub use ref_substitution::{FrozenMultipleVarSubst, FrozenOVSubstF, FrozenSubst, FrozenSubstF};
