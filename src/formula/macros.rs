macro_rules! fun {
    ($f:pat, $args:pat) => {
        crate::formula::formula::RichFormula::Fun($f, $args)
    };
    ($f:expr; $($arg:expr),*) => {
        crate::formula::formula::RichFormula::Fun($f.clone(), vec![$($arg,)*])
    }
}
pub(crate) use fun;
