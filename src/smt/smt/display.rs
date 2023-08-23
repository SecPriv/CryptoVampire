use std::fmt;

use crate::{environement::traits::{Realm, KnowsRealm}, formula::file_descriptior::axioms::RewriteKind};

use super::{fun_list_fmt, Smt, SmtFile, SmtFormula};

#[derive(Debug, Copy, Clone)]
pub struct SmtDisplayer<D, T> {
    pub env: D,
    pub content: T,
}

#[derive(Debug, Copy, Clone)]
pub struct SmtEnv {
    pub realm: Realm,
}

impl KnowsRealm for SmtEnv {
    fn get_realm(&self) -> Realm {
        self.realm
    }
}

impl<D, T: Copy> SmtDisplayer<D, T> {
    fn as_env_ref(&self) -> SmtDisplayer<&D, T> {
        SmtDisplayer {
            env: &self.env,
            content: self.content,
        }
    }
}

impl<D: Copy, T> SmtDisplayer<D, T> {
    fn as_content_ref(&self) -> SmtDisplayer<D, &T> {
        SmtDisplayer {
            env: self.env,
            content: &self.content,
        }
    }
}

impl<D, T> SmtDisplayer<D, T> {
    fn as_ref(&self) -> SmtDisplayer<&D, &T> {
        SmtDisplayer {
            env: &self.env,
            content: &self.content,
        }
    }

    pub fn propagate<U>(self, other: U) -> SmtDisplayer<D, U> {
        SmtDisplayer {
            content: other,
            env: self.env,
        }
    }
}


macro_rules! generate_diplay {
    ($t:ident) => {
        impl<'bump> fmt::Display for SmtDisplayer<SmtEnv, $t<'bump>> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.as_ref().fmt(f)
            }
        }

        impl<'a, 'bump> fmt::Display for SmtDisplayer<SmtEnv, &'a $t<'bump>> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.as_env_ref().fmt(f)
            }
        }

        impl<'a, 'bump> fmt::Display for SmtDisplayer<&'a SmtEnv, $t<'bump>> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.as_content_ref().fmt(f)
            }
        }
    };
}

generate_diplay!(SmtFormula);

// impl<'bump> fmt::Display for SmtDisplayer<SmtEnv, SmtFormula<'bump>> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.as_ref().fmt(f)
//     }
// }

// impl<'a, 'bump> fmt::Display for SmtDisplayer<SmtEnv, &'a SmtFormula<'bump>> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.as_env_ref().fmt(f)
//     }
// }

// impl<'a, 'bump> fmt::Display for SmtDisplayer<&'a SmtEnv, SmtFormula<'bump>> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.as_content_ref().fmt(f)
//     }
// }

impl<'a, 'bump> fmt::Display for SmtDisplayer<&'a SmtEnv, &'a SmtFormula<'bump>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.content {
            SmtFormula::Var(v) => v.fmt(f),
            SmtFormula::Fun(fun, args) if fun.is_no_op(&self.env) => {
                assert_eq!(args.len(), 1);
                args[0].prop(*self).fmt(f)
            }
            SmtFormula::Fun(fun, args) => {
                if args.len() > 0 {
                    write!(f, "({} ", fun.name())?;
                    for arg in args {
                        write!(f, "{} ", self.propagate(arg))?;
                    }
                    write!(f, ")")
                } else {
                    write!(f, "{} ", fun.name())
                }
            }
            SmtFormula::Forall(vars, formula) | SmtFormula::Exists(vars, formula)
                if vars.is_empty() =>
            {
                formula.prop(*self).fmt(f)
            }
            SmtFormula::Forall(vars, formula) => {
                write!(f, "(forall (")?;
                for v in vars.into_iter() {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                write!(f, ") {})", formula.prop(*self))
            }
            SmtFormula::Exists(vars, formula) => {
                write!(f, "(exists (")?;
                for v in vars.into_iter() {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                write!(f, ") {})", formula.prop(*self))
            }
            SmtFormula::True => write!(f, "true"),
            SmtFormula::False => write!(f, "false"),
            SmtFormula::And(args) if args.is_empty() => SmtFormula::True.prop(*self).fmt(f),
            SmtFormula::And(args) => {
                fun_list_fmt(f, "and", args.iter().map(|smt| self.propagate(smt)))
            }
            SmtFormula::Or(args) if args.is_empty() => SmtFormula::False.prop(*self).fmt(f),
            SmtFormula::Or(args) => {
                fun_list_fmt(f, "or", args.iter().map(|smt| self.propagate(smt)))
            }
            SmtFormula::Eq(args) | SmtFormula::Neq(args) if args.len() <= 1 => {
                SmtFormula::True.prop(*self).fmt(f)
            }
            SmtFormula::Eq(args) => {
                fun_list_fmt(f, "=", args.iter().map(|smt| self.propagate(smt)))
            }
            SmtFormula::Neq(args) => {
                fun_list_fmt(f, "distinct", args.iter().map(|smt| self.propagate(smt)))
            }
            SmtFormula::Ite(c, r, l) => {
                let [c, r, l] = [c, r, l].map(|smt| smt.prop(*self));
                write!(f, "(ite {c} {r} {l})")
            }
            SmtFormula::Implies(a, b) => write!(
                f,
                "(=> {} {})",
                a.prop(*self),
                b.prop(*self),
            ),
            SmtFormula::Subterm(fun, a, b) => write!(
                f,
                "(subterm {} {} {})",
                fun.name(),
                a.prop(*self),
                b.prop(*self),
            ),
            SmtFormula::Not(a) => write!(f, "(not {})", a.prop(*self)),
        }
    }
}

generate_diplay!(Smt);
impl<'a, 'bump> fmt::Display for SmtDisplayer<&'a SmtEnv, &'a Smt<'bump>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.content {
            Smt::Assert(e) => writeln!(f, "(assert {})", e.prop(*self)),
            Smt::AssertTh(e) => writeln!(f, "(assert-theory {})", e.prop(*self)),
            Smt::AssertNot(e) => writeln!(f, "(assert-not {})", e.prop(*self)),
            Smt::DeclareFun(fun) => {
                write!(f, "(declare-fun {} (", fun.name())?;
                for s in fun.fast_insort().expect(&format!(
                    "all function defined here have known sort: {}",
                    fun.name()
                )) {
                    write!(f, "{} ", s.name())?;
                }
                writeln!(f, ") {})", fun.fast_outsort().unwrap())
            }
            Smt::DeclareSort(sort) => writeln!(f, "(declare-sort {} 0)", sort),
            Smt::DeclareSortAlias { from, to } => {
                writeln!(f, "(define-sort {} () {})", to.name(), from.name())
            }
            Smt::DeclareSubtermRelation(fun, funs) => {
                write!(f, "(declare-subterm-relation {} ", fun.name())?;
                for fun in funs {
                    write!(f, "{} ", fun.name())?;
                }
                writeln!(f, ")")
            }
            Smt::DeclareRewrite {
                rewrite_fun,
                vars,
                lhs,
                rhs,
            } => {
                write!(f, "(declare-rewrite (forall (")?;
                for v in vars.into_iter() {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                let op = match rewrite_fun {
                    RewriteKind::Bool => "=>".into(),
                    RewriteKind::Other(f) => f.name(),
                };
                writeln!(f, ") ({} {} {})))", op, lhs.prop(*self), rhs.prop(*self))
            }
            Smt::DeclareDatatypes { sorts, cons } => {
                write!(f, "(declare-datatypes\n")?;
                // name of types
                write!(f, "\t(")?;
                for s in sorts.into_iter() {
                    write!(f, "({} 0) ", s)?;
                }
                write!(f, ")\n\t(\n")?;

                // cons
                for (j, vc) in cons.iter().enumerate() {
                    write!(f, "\t\t(\n")?;
                    for c in vc {
                        assert_eq!(sorts[j], c.fun.fast_outsort().unwrap());

                        write!(f, "\t\t\t({} ", c.fun.name())?;

                        for (i, s) in c.fun.fast_insort().expect("todo").iter().enumerate() {
                            write!(f, "({} {}) ", c.dest.get(i).unwrap().name(), s)?;
                        }
                        write!(f, ")\n")?;
                    }
                    write!(f, "\t\t)\n")?;
                }
                writeln!(f, "\t)\n)")
            }

            Smt::CheckSat => writeln!(f, "(check-sat)"),
            Smt::Comment(s) => writeln!(f, "\n; {}\n", s),
            Smt::GetProof => writeln!(f, "(get-proof)"),
            Smt::SetOption(option, arg) => writeln!(f, "(set-option :{} {})", option, arg),
            Smt::SetLogic(logic) => writeln!(f, "(set-logic {})", logic),
        }
    }
}

generate_diplay!(SmtFile);
impl<'a, 'bump> fmt::Display for SmtDisplayer<&'a SmtEnv, &'a SmtFile<'bump>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if cfg!(debug_assertions) {
            self.content.content
                .iter()
                .filter_map(|smt| match smt {
                    Smt::DeclareFun(f) => Some(f),
                    _ => None,
                })
                .for_each(|f| println!("trying to define {}", f.name()))
        }

        self.content
            .content
            .iter()
            .map(|smt| smt.prop(*self))
            .try_for_each(|smt| writeln!(f, "{smt}"))
    }
}
