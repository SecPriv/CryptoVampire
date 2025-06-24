use crate::environement::environement::Environement;

pub trait FromEnv<'bump, U> {
    fn with_env(env: &Environement<'bump>, other: U) -> Self;
}
