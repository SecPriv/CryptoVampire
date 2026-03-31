use logic_formula::AsFormula;
use quarck::CowArc;
use rustc_hash::FxHashSet;
use utils::match_eq;

use crate::terms::{AND, EQ, FOBinder, Formula, IMPLIES, MITE, NOT, OR};

impl Formula {
    pub fn optimise(&self) -> Self {
        match self {
            Self::Quantifier { head, vars, arg } => {
                let args: CowArc<'static, _> = arg.iter().map(Self::optimise).collect();
                let fv: FxHashSet<_> = args.iter().flat_map(|f| f.free_vars_iter()).collect();
                let vars: CowArc<'static, _> =
                    vars.iter().filter(|v| fv.contains(v)).cloned().collect();

                if vars.is_empty() {
                    return match head {
                        FOBinder::FindSuchThat => Self::App {
                            head: MITE.clone(),
                            args,
                        },
                        _ => arg[0].clone(),
                    };
                }

                Self::Quantifier {
                    head: *head,
                    vars,
                    arg: args,
                }
            }
            Self::App { head, args } => {
                let args: CowArc<'static, _> = args.iter().map(Self::optimise).collect();
                match_eq!(head => {
                    EQ => {
                      if args[0] == args[1] { return Self::True() }
                      self.clone()
                    },
                    AND => {
                      if args[0].is_true() { return args[1].clone() }
                      if args[1].is_true() { return args[0].clone() }
                      if args[0].is_false() || args[1].is_false() { return Self::False() }
                      self.clone()
                    },
                    OR => {
                      if args[0].is_false() { return args[1].clone() }
                      if args[1].is_false() { return args[0].clone() }
                      if args[0].is_true() || args[1].is_true() { return Self::True() }
                      self.clone()
                    },
                    NOT => {
                      if args[0].is_true() { return Self::False() }
                      if args[0].is_false() { return Self::True() }
                      self.clone()
                    },
                    IMPLIES => {
                      if args[0].is_true() { return args[1].clone() }
                      if args[0].is_false() || args[1].is_true() { return Self::True() }
                      self.clone()
                    },
                    _ => { self.clone() }
                })
            }
            x => x.clone(),
        }
    }
}
