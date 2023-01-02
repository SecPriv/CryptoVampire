macro_rules! fun {
    ($f:expr; $($arg:expr),*) => {
        crate::formula::formula::RichFormula::Fun($f.clone(), vec![$($arg,)*])
    };
    ($f:pat, $args:pat) => {
        crate::formula::formula::RichFormula::Fun($f, $args)
    };
}
pub(crate) use fun;
