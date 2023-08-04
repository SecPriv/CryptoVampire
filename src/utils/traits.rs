

use super::string_ref::StrRef;

pub trait Named {
    fn name(&self) -> &str;
}

pub trait RefNamed<'str> {
    fn name_ref(&self) -> StrRef<'str>;
}