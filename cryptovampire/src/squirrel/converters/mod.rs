use thiserror::Error;

use super::ConversiontError;

/// inline lets, keep the sq types
mod stage0;
/// switch to a structure more cv like of terms, but is still a dumb transform
mod stage1;
/// get as close as possible to a format that can be typechecked by cv
mod stage2;

mod stage3;

#[allow(non_camel_case_types)]
type utuple = u8;

#[derive(Debug, Clone)]
enum SQuant {
    Forall,
    Exists,
    FindSuchThat,
}

pub type Result<A> = std::result::Result<A, ConversiontError>;
