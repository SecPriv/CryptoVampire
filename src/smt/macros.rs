macro_rules! sfun {
    ($fun:expr ; $($arg:expr),* ) => {
        crate::smt::smt::SmtFormula::Fun($fun.clone(), vec![$($arg.clone(),)*])
    };
    ($fun:expr) => {
        sfun!($fun;)
    };
    ($fun:expr , $args:expr ) => {
        crate::smt::smt::SmtFormula::Fun($fun.clone(), $args)
    };
}

macro_rules! sand {
    ($($arg:expr),+) => {
        crate::smt::smt::SmtFormula::And(vec![$($arg.clone(),)+])
    };
}

macro_rules! sor {
    ($($arg:expr),+) => {
        crate::smt::smt::SmtFormula::Or(vec![$($arg.clone(),)+])
    };
}

macro_rules! seq {
    ($($arg:expr),+) => {
        crate::smt::smt::SmtFormula::Eq(vec![$($arg.clone(),)+])
    };
}

macro_rules! sneq {
    ($($arg:expr),+) => {
        crate::smt::smt::SmtFormula::Neq(vec![$($arg.clone(),)+])
    };
}

macro_rules! site {
    ($arg1:expr, $arg2:expr, $arg3:expr) => {
        crate::smt::smt::SmtFormula::Ite(
            std::boxed::Box::new($arg1.clone()),
            std::boxed::Box::new($arg2.clone()),
            std::boxed::Box::new($arg3.clone()),
        )
    };
}

macro_rules! simplies {
    ($arg1:expr, $arg2:expr) => {
        crate::smt::smt::implies($arg1, $arg2)
    };
}

macro_rules! snot {
    ($arg1:expr) => {
        crate::smt::smt::not($arg1)
    };
}

macro_rules! svar {
    ($v:expr) => {
        crate::smt::smt::SmtFormula::Var($v)
    };
}

macro_rules! sforall {
    ($($name:ident ! $i:literal : $sort:expr),*; $content:block) => {{
        let f = |$($name:crate::smt::smt::SmtFormula),*| $content;
        crate::smt::smt::SmtFormula::Forall(
            vec![$(crate::formula::formula::Variable {id: $i, sort: $sort.clone()}),*],
            std::boxed::Box::new(
                f($(crate::smt::smt::SmtFormula::Var(crate::formula::formula::Variable {id: $i, sort: $sort.clone()})),*)
            )
        )
    }};
    ($vars:expr, $content:expr) => {
        crate::smt::smt::SmtFormula::Forall($vars,std::boxed::Box::new($content))
    };
}

macro_rules! sexists {
    ($($name:ident ! $i:literal : $sort:expr),*; $content:block) => {{
        let f = |$($name),*| $content;
        crate::smt::smt::SmtFormula::Exists(
            vec![$(crate::formula::formula::Variable {id: $i, sort: $sort.clone()}),*],
            std::boxed::Box::new(
                f($(crate::smt::smt::SmtFormula::Var(crate::formula::formula::Variable {id: $i, sort: $sort.clone()})),*)
            )
        )
    }};
    ($vars:expr, $content:expr) => {
        crate::smt::smt::SmtFormula::Exists($vars,std::boxed::Box::new($content))
    };
}

pub(crate) use {sand, seq, sexists, sforall, sfun, simplies, site, snot, sor, svar};
