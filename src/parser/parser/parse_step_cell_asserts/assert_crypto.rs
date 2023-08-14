use pest::Span;

use crate::{
    destvec,
    environement::traits::Realm,
    formula::function::signature::Signature,
    implvec,
    parser::{ast, merr, parser::Environement, IntoRuleResultFunction, E},
    problem::crypto_assumptions::{
        CryptoAssumption, EufCmaMac, EufCmaSign, Nonce, EUF_CMA_MAC_SIGNATURE,
        EUF_CMA_PK_SIGNATURE, EUF_CMA_SIGN_SIGNATURE, EUF_CMA_VERIFY_SIGNATURE,
        INT_CTXT_DEC_SIGNATURE, INT_CTXT_ENC_SIGNATURE, INT_CTXT_VERIFY_SIGNATURE,
    },
};

pub fn parse_asserts_crypto<'a, 'str, 'bump, B>(
    env: &'a Environement<'bump, 'str>,
    crypto: implvec!(&'a ast::AssertCrypto<'str>),
) -> Result<B, E>
where
    B: FromIterator<CryptoAssumption<'bump>>,
{
    crypto
        .into_iter()
        .map(|ac| parse_assert_crypto(env, ac))
        .collect()
}

pub fn parse_assert_crypto<'str, 'bump>(
    env: &Environement<'bump, 'str>,
    crypto: &ast::AssertCrypto<'str>,
) -> Result<CryptoAssumption<'bump>, E> {
    let ast::AssertCrypto {
        span,
        name,
        functions,
    } = crypto;

    match name.content {
        "nonce" => Ok(CryptoAssumption::Nonce(Nonce)),
        "euf-cma" => parse_euf_cma(env, functions, *span),
        "int-ctxt" => parse_int_ctxt(env, functions, *span),
        _ => Err(merr(name.span, "unknown crypto assertion".to_string())),
    }
}

macro_rules! verify_sign {
    ($env:ident; $ast:ident, $fun:ident, $signature:ident, $arity:literal) => {
        let $fun = *$env.find_function($ast.span(), $ast.name()).and_then(|f| {
            f.as_function()
                .ok_or_else(|| merr($ast.span(), format!("{} should be a function", $ast.name())))
        })?;
        $signature
            .as_ref()
            .unify(&$fun.signature(), &Realm::Symbolic)
            .into_rr($ast.span(), [$ast.span(); $arity])?;
    };
}

fn parse_euf_cma<'str, 'bump>(
    env: &Environement<'bump, 'str>,
    functions: &[ast::Function<'str>],
    span: Span<'str>,
) -> Result<CryptoAssumption<'bump>, E> {
    match functions.len() {
        2 => {
            destvec!([ast_mac, ast_verify] = functions);
            verify_sign!(env; ast_mac, mac, EUF_CMA_MAC_SIGNATURE, 2);
            verify_sign!(env; ast_verify, verify, EUF_CMA_VERIFY_SIGNATURE, 3);
            Ok(CryptoAssumption::EufCmaMac(EufCmaMac { mac, verify }))
        }
        3 => {
            destvec!([ast_sign, ast_verify, ast_pk] = functions);
            verify_sign!(env; ast_sign, sign, EUF_CMA_SIGN_SIGNATURE, 2);
            verify_sign!(env; ast_verify, verify, EUF_CMA_VERIFY_SIGNATURE, 3);
            verify_sign!(env; ast_pk, pk, EUF_CMA_PK_SIGNATURE, 1);
            Ok(CryptoAssumption::EufCmaSign(EufCmaSign {
                sign,
                verify,
                pk,
            }))
        }
        i => Err(merr(
            span,
            format!("wrong number of arguments: expected 2 or 3, got {i}"),
        )),
    }
}

fn parse_int_ctxt<'str, 'bump>(
    env: &Environement<'bump, 'str>,
    functions: &[ast::Function<'str>],
    span: Span<'str>,
) -> Result<CryptoAssumption<'bump>, E> {
    match functions.len() {
        3 => {
            destvec!([ast_enc, ast_dec, ast_verify] = functions);
            verify_sign!(env; ast_enc, enc, INT_CTXT_ENC_SIGNATURE, 3);
            verify_sign!(env; ast_dec, dec, INT_CTXT_DEC_SIGNATURE, 2);
            verify_sign!(env; ast_verify, verify, INT_CTXT_VERIFY_SIGNATURE, 2);

            todo!()
        }
        i => Err(merr(
            span,
            format!("wrong number of arguments: expected 3, got {i}"),
        )),
    }
}
