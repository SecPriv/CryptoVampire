use std::fmt;

use super::{Smt, SmtFile, SmtFormula};
use crate::environement::traits::{KnowsRealm, Realm};
use crate::smt::smt::SmtDisplay;

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

impl<D, T> SmtDisplayer<D, T> {
    pub fn propagate<U>(self, other: U) -> SmtDisplayer<D, U> {
        SmtDisplayer {
            content: other,
            env: self.env,
        }
    }
}

impl<'bump> SmtDisplay<'bump> for SmtFormula<'bump> {
    fn into_display(self, env: &impl KnowsRealm) -> impl fmt::Display + 'bump {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }
    fn as_display(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }
}

impl<'bump> SmtDisplay<'bump> for Smt<'bump> {
    fn into_display(self, env: &impl KnowsRealm) -> impl fmt::Display + 'bump {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }
    fn as_display(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }
}

impl<'bump> SmtDisplay<'bump> for SmtFile<'bump> {
    fn into_display(self, _: &impl KnowsRealm) -> impl fmt::Display + 'bump {
        ""
    }
    fn as_display(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }
}

impl<D: KnowsRealm> fmt::Display for SmtDisplayer<D, SmtFormula<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.content)
    }
}

impl<D: KnowsRealm> fmt::Display for SmtDisplayer<D, &SmtFormula<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.content)
    }
}

impl<D: KnowsRealm> fmt::Display for SmtDisplayer<D, Smt<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.content)
    }
}

impl<D: KnowsRealm> fmt::Display for SmtDisplayer<D, &Smt<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.content)
    }
}

impl<D: KnowsRealm> fmt::Display for SmtDisplayer<D, SmtFile<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for smt in &self.content.content {
            writeln!(f, "{}", smt)?;
        }
        Ok(())
    }
}

impl<D: KnowsRealm> fmt::Display for SmtDisplayer<D, &SmtFile<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for smt in &self.content.content {
            writeln!(f, "{}", smt)?;
        }
        Ok(())
    }
}
