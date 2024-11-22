use super::*;

pub trait HasInitStep: Sized {
    fn ref_init_step_ast<'a>() -> &'a ast::Step<'a, Self>;

    // fn from_static(s:&'static str) -> Self;
}

pub trait FromStaticString {
    fn from_static(s: &'static str) -> Self;
}

#[dynamic]
static INIT_STEP_AST_STR: ast::Step<'static, &'static str> = INIT_STEP_AST();

#[dynamic]
static INIT_STEP_AST_STRREF: ast::Step<'static, StrRef<'static>> = INIT_STEP_AST();

impl<'str> HasInitStep for &'str str {
    fn ref_init_step_ast<'a>() -> &'a ast::Step<'str, Self> {
        &INIT_STEP_AST_STR
    }
}

impl<'str> FromStaticString for &'str str {
    fn from_static(s: &'static str) -> Self {
        s
    }
}

impl<'str> HasInitStep for StrRef<'str> {
    fn ref_init_step_ast<'a>() -> &'a ast::Step<'str, Self> {
        &INIT_STEP_AST_STRREF
    }
}

impl<'str> FromStaticString for StrRef<'str> {
    fn from_static(s: &'static str) -> Self {
        s.into()
    }
}

pub trait Pstr:
Borrow<str>
+ std::hash::Hash
+ Clone
+ std::fmt::Display
+ Eq
// + From<&'static str>
+ std::fmt::Debug
+ HasInitStep
+ FromStaticString
{
fn as_str(&self) -> &str {
    self.borrow()
}
}
impl<T> Pstr for T where
    T: Borrow<str>
        + std::hash::Hash
        + Clone
        + std::fmt::Display
        + Eq
        // + From<&'static str>
        + std::fmt::Debug
        + HasInitStep
        + FromStaticString
{
}
