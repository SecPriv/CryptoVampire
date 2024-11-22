#[allow(clippy::module_inception)]
mod container;
pub use container::{ScopedContainer, StaticContainer};
pub mod allocator;
pub mod contained;
pub mod reference;
pub mod utils;

const PRINT_DEREF: bool = false;
