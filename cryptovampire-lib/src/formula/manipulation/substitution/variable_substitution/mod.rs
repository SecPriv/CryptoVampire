mod one_var;
pub use one_var::{OneVarSubst, OneVarSubstF};

mod owned_var;
pub use owned_var::{OwnedVarSubst, OwnedVarSubstF};

mod ref_substitution;
pub use ref_substitution::{FrozenOVSubst, FrozenOVSubstF, FrozenSubst, FrozenSubstF};
