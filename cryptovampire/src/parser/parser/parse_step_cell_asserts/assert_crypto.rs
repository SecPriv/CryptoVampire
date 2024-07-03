use pest::Span;

use crate::parser::{ast::{self, MOption, Options}, merr, parser::Environement, IntoRuleResultFunction, E};
use cryptovampire_lib::{
    environement::traits::Realm,
    formula::function::{self, signature::Signature},
    problem::crypto_assumptions::{
        CryptoAssumption, EufCma, IntCtxt, Nonce, UfCmaBuilder, EUF_CMA_PK_SIGNATURE, EUF_CMA_SIGN_SIGNATURE, EUF_CMA_VERIFY_SIGNATURE, INT_CTXT_DEC_SIGNATURE, INT_CTXT_ENC_SIGNATURE, INT_CTXT_VERIFY_SIGNATURE, UF_CMA_MAC_SIGNATURE, UF_CMA_VERIFY_SIGNATURE
    },
};
use utils::{destvec, implvec, traits::NicerError};

pub fn parse_asserts_crypto<'a, 'str, 'bump>(
    env: &'a Environement<'bump, 'str>,
    crypto: implvec!(&'a ast::AssertCrypto<'str>),
) -> Result<Vec<CryptoAssumption<'bump>>, E> {
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
        options,
    } = crypto;

    match name.content {
        "nonce" => Ok(CryptoAssumption::Nonce(Nonce)),
        "memory_cell" => Ok(CryptoAssumption::MemoryCell(Default::default())),
        "euf-cma" => parse_euf_cma(env, functions, options, *span),
        "uf-cma" => parse_uf_cma(env, functions, options, *span),
        "int-ctxt" => parse_int_ctxt(env, functions, *span),
        _ => Err(merr(name.span, "unknown crypto assertion".to_string())),
    }
    .debug_continue()
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
    options: &Options<'str>,
    span: Span<'str>,
) -> Result<CryptoAssumption<'bump>, E> {
    match functions.len() {
        2 => {
            parse_uf_cma(env, functions, options, span)
        }
        3 => {
            destvec!([ast_sign, ast_verify, ast_pk] = functions);
            verify_sign!(env; ast_sign, sign, EUF_CMA_SIGN_SIGNATURE, 2);
            verify_sign!(env; ast_verify, verify, EUF_CMA_VERIFY_SIGNATURE, 3);
            verify_sign!(env; ast_pk, pk, EUF_CMA_PK_SIGNATURE, 1);
            Ok(CryptoAssumption::EufCmaSign(EufCma { sign, verify, pk }))
        }
        i => Err(merr(
            span,
            format!("wrong number of arguments: expected 2 or 3, got {i}"),
        )),
    }
}

fn parse_uf_cma<'str, 'bump>(
    env: &Environement<'bump, 'str>,
    functions: &[ast::Function<'str>],
    options:&Options<'str>,
    s: Span<'str>,
) -> Result<CryptoAssumption<'bump>, E> {
    let mut builder = UfCmaBuilder::default();
    if let [ast_mac, ast_verify] = functions {
            verify_sign!(env; ast_mac, mac, UF_CMA_MAC_SIGNATURE, 2);
            verify_sign!(env; ast_verify, verify, UF_CMA_VERIFY_SIGNATURE, 3);
        builder.mac(mac).verify(verify);
    } else {
        return Err(merr(s, format!("wrong number of arguments: expected 2, got {:}", functions.len())))
    }
    if options.contains("hmac") {
        builder.hmac(true);
    }

    Ok(CryptoAssumption::UfCma(builder.build().unwrap()))
}

fn parse_int_ctxt<'str, 'bump>(
    env: &Environement<'bump, 'str>,
    functions: &[ast::Function<'str>],
    span: Span<'str>,
) -> Result<CryptoAssumption<'bump>, E> {
    let functions = match functions.len() {
        3 | 4 => Ok(&functions[..3]),
        i => Err(merr(
            span,
            format!("wrong number of arguments: expected 3 (or 4), got {i}"),
        )),
    }
    .debug_continue()?;
    destvec!([ast_enc, ast_dec, ast_verify] = functions);

    verify_sign!(env; ast_enc, enc, INT_CTXT_ENC_SIGNATURE, 3);
    verify_sign!(env; ast_dec, dec, INT_CTXT_DEC_SIGNATURE, 2);
    verify_sign!(env; ast_verify, verify, INT_CTXT_VERIFY_SIGNATURE, 2);

    Ok(CryptoAssumption::IntCtxtSenc(IntCtxt { enc, dec, verify }))
}
