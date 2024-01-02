use crate::formula::{
    formula::RichFormula, function::Function, quantifier::Quantifier, variable::Variable,
};
use if_chain::if_chain;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct ApplicationArgs<'bump, 'f> {
    vars: &'f [Variable<'bump>],
    args: &'f [RichFormula<'bump>],
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum Rec<'bump, 'f> {
    Simple(&'f RichFormula<'bump>),
    Rec(Box<MapF<'f, 'bump>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MapF<'bump, 'f> {
    app: Option<ApplicationArgs<'bump, 'f>>,
    formula: Rec<'bump, 'f>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum MapFLike<'bump, 'f> {
    Var(&'f Variable<'bump>),
    Fun(Function<'bump>, Vec<MapF<'bump, 'f>>),
    Quantifier(&'f Quantifier<'bump>, Box<MapF<'bump, 'f>>),
}

impl<'bump, 'f> MapF<'bump, 'f> {
    fn next(self) -> MapFLike<'bump, 'f> {
        fn do_var<'bump, 'f>(
            v: &'f Variable<'bump>,
            app: Option<ApplicationArgs<'bump, 'f>>,
        ) -> MapFLike<'bump, 'f> {
            if_chain! {
                if let Some(a) = app.as_ref();
                if let Some(i) = a.vars.iter().position(|v2| v2 == v);
                then {
                    MapF { formula: Rec::Simple(&a.args[i]), app:None } .next()
                } else {
                    MapFLike::Var(v)
                }
            }
        }

        match self.formula {
            Rec::Simple(formula) => match formula {
                RichFormula::Var(v) => do_var(v, self.app),
                RichFormula::Fun(fun, args) => MapFLike::Fun(
                    *fun,
                    args.iter()
                        .map(|f| MapF {
                            formula: Rec::Simple(f),
                            ..self.clone()
                        })
                        .collect(),
                ),
                RichFormula::Quantifier(q, f) => {
                    assert_ne!(
                        Some(true),
                        self.app
                            .as_ref()
                            .map(|a| a.vars.iter().any(|v| q.get_variables().contains(v)))
                    );
                    MapFLike::Quantifier(
                        q,
                        Box::new(MapF {
                            formula: Rec::Simple(&*f),
                            ..self
                        }),
                    )
                }
            },
            Rec::Rec(m) => match m.next() {
                MapFLike::Var(v) => do_var(v, self.app),
                MapFLike::Fun(fun, args) => MapFLike::Fun(
                    fun,
                    args.into_iter()
                        .map(|f| MapF {
                            formula: Rec::Rec(Box::new(f)),
                            app: self.app.clone(),
                        })
                        .collect(),
                ),
                MapFLike::Quantifier(q, f) => {
                    assert_ne!(
                        Some(true),
                        self.app
                            .as_ref()
                            .map(|a| a.vars.iter().any(|v| q.get_variables().contains(v)))
                    );
                    MapFLike::Quantifier(
                        q,
                        Box::new(MapF {
                            formula: Rec::Rec(f),
                            app: self.app.clone(),
                        }),
                    )
                }
            },
        }
    }

    pub fn apply(self) -> RichFormula<'bump> {
        match self.next() {
            MapFLike::Var(v) => RichFormula::Var(*v),
            MapFLike::Fun(f, args) => {
                RichFormula::Fun(f, args.into_iter().map(Self::apply).collect())
            }
            MapFLike::Quantifier(q, f) => RichFormula::Quantifier(q.clone(), Box::new(f.apply())),
        }
    }

    pub fn map(self, vars: &'f [Variable<'bump>], args: &'f [RichFormula<'bump>]) -> Self {
        MapF {
            app: Some(ApplicationArgs { vars, args }),
            formula: Rec::Rec(Box::new(self)),
        }
    }
}

impl<'f, 'bump> From<&'f RichFormula<'bump>> for MapF<'bump, 'f> {
    fn from(value: &'f RichFormula<'bump>) -> Self {
        Self {
            app: None,
            formula: Rec::Simple(value),
        }
    }
}

impl<'f, 'bump> Into<RichFormula<'bump>> for MapF<'bump, 'f> {
    fn into(self) -> RichFormula<'bump> {
        self.apply()
    }
}
