use crate::{
    formula::{
        builtins::types::{MSG, NONCE},
        env::Environement,
        function::Function,
    },
    smt::{
        smt::Smt,
        writer::{subterm::generate_subterm, Ctx},
    },
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CryptoAssumption {
    EufCmaHash(Function),
}

impl CryptoAssumption {
    pub(crate) fn generate_smt(
        &self,
        env: &Environement,
        assertions: &mut Vec<Smt>,
        declarations: &mut Vec<Smt>,
        ctx: &Ctx<'_>,
    ) {
        match self {
            CryptoAssumption::EufCmaHash(f) => {
                generate_smt_euf_sma_hash(env, assertions, declarations, ctx, f)
            }
        }
    }
}

fn generate_smt_euf_sma_hash(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
    f: &Function,
) {
    let subt_main = generate_subterm(
        env,
        assertions,
        declarations,
        ctx,
        "sbt$euf_hash_main",
        &MSG,
        vec![],
    );
    let subt_sec = generate_subterm(
        env,
        assertions,
        declarations,
        ctx,
        "sbt$euf_hash_sec",
        &NONCE,
        vec![f],
    );
}
