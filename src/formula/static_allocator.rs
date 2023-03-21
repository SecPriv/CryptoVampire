use bumpalo::Bump;
use static_init::dynamic;

#[dynamic]
pub(crate) static STATIC_ALLOCATOR : Bump = Bump::new();