pub mod basic_hash {
    use crate::{
        Problem, decl_fun, mk_alias, mk_signature,
        protocol::{self, Step},
        rexp,
        terms::{
            Exists, Function, FunctionFlags, InnerFunction, MACRO_INPUT, NONCE, PROJ_1, PROJ_2,
            Sort, TUPLE,
        },
    };
    use egg::{Id, Var};

    pub struct MFunction {
        hash: Function,
        k1: Function,
        k2: Function,
        p1: Function,
        p2: Function,
        mk: Function,
        n: Function,
        tag: Function,
        rf: Function,
        rs: Function,
        mexists: Function,
        msk: Function,
        ok: Function,
        ko: Function,
    }

    pub fn populate_functions(pbl: &mut Problem) -> MFunction {
        let hash = decl_fun!(pbl; "hash": (Bitstring) -> Bitstring);
        let k1 = decl_fun!(pbl; "key1": (Index) -> Nonce);
        let k2 = decl_fun!(pbl; "key2": (Index, Index) -> Nonce);
        let p1 = pbl.declare_new_protocol().name().clone();
        let p2 = pbl.declare_new_protocol().name().clone();
        let n = decl_fun!(pbl; "n": (Index, Index) -> Nonce);
        let ok = decl_fun!(pbl; "ok": () -> Bitstring);
        let ko = decl_fun!(pbl; "ko": () -> Bitstring);

        let mk = {
            let alias = mk_alias! {
                0:Index, 1:Index
                    in rexp!(#0), rexp!(#1), rexp!(p1) => rexp!((k1 #0)),
                0:Index, 1:Index
                    in rexp!(#0), rexp!(#1), rexp!(p2) => rexp!((k2 #0 #1))
            };
            let inner = InnerFunction {
                alias: Some(alias),
                ..InnerFunction::new(
                    "mkey".into(),
                    mk_signature!((Index, Index, Protocol) -> Nonce),
                )
            };
            let mk = Function::new(inner);
            pbl.function.add(mk.clone());
            mk
        };

        let tag = {
            let signature = mk_signature!((Sort::Index, Sort::Index) -> Sort::Time);
            let id = Function::new(InnerFunction {
                flags: FunctionFlags::STEP,
                step_idx: 0,
                ..InnerFunction::new("tag".into(), signature)
            });
            pbl.function.add(id.clone());
            id
        };

        let rs = {
            let signature = mk_signature!((Sort::Index, Sort::Index) -> Sort::Time);
            let id = Function::new(InnerFunction {
                flags: FunctionFlags::STEP,
                step_idx: 1,
                ..InnerFunction::new("Rs".into(), signature)
            });
            pbl.function.add(id.clone());
            id
        };

        let rf = {
            let signature = mk_signature!((Sort::Index) -> Sort::Time);
            let id = Function::new(InnerFunction {
                flags: FunctionFlags::STEP,
                step_idx: 2,
                ..InnerFunction::new("Rf".into(), signature)
            });
            pbl.function.add(id.clone());
            id
        };

        let mexists;
        let msk;
        {
            let Exists {
                vars,
                bound_var,
                patt,
                tlf,
                skolem,
                ..
            } = pbl
                .function
                .add_exists_function([Sort::Index, Sort::Protocol], Sort::Index);
            *vars = [0, 1].map(Var::from_u32).to_vec();
            *bound_var = Var::from_u32(2);
            *patt = rexp!((= (PROJ_2 (MACRO_INPUT (rf #0) #1)) (hash (PROJ_1 (MACRO_INPUT (rf #0) #1)) (NONCE (mk #0 #2 #1)))))
                .to_vec().into();
            mexists = tlf.clone();
            msk = skolem.clone();
        };

        MFunction {
            hash,
            k1,
            k2,
            p1,
            p2,
            mk,
            n,
            tag,
            rf,
            rs,
            mexists,
            msk,
            ok,
            ko,
        }
    }

    pub fn insert_tag(pbl: &mut Problem, funs: &MFunction) {
        let MFunction {
            hash,
            mk,
            n,
            p1,
            p2,
            tag,
            ..
        } = funs;

        let s1 = Step {
            id: tag.clone(),
            vars: [0, 1].map(Var::from_u32).to_vec(),
            cond: rexp!(true).to_vec().into(),
            msg: rexp!((TUPLE (NONCE (n #0 #1)) (hash (NONCE (n #0 #1)) (mk #0 #1 p1))))
                .to_vec()
                .into(),
        };
        let s2 = Step {
            msg: rexp!((TUPLE (NONCE (n #0 #1)) (hash (NONCE (n #0 #1)) (mk #0 #1 p2))))
                .to_vec()
                .into(),
            ..s1.clone()
        };
        pbl.protocols[0].add_step(s1);
        pbl.protocols[1].add_step(s2);
    }

    pub fn insert_rs(pbl: &mut Problem, funs: &MFunction) {
        let MFunction {
            hash,
            mk,
            p1,
            p2,
            rs,
            ok,
            ..
        } = funs;

        let s1 = Step {
            id: rs.clone(),
            vars: [0, 1].map(Var::from_u32).to_vec(),
            cond: rexp!((= (PROJ_2 (MACRO_INPUT (rs #0 #1) p1)) (hash (PROJ_1 (MACRO_INPUT (rs #0 #1) p1)) (NONCE (mk #0 #1 p1)))))
                .to_vec()
                .into(),
            msg: rexp!(ok).to_vec().into()
        };
        let s2 = Step {
            cond: rexp!((= (PROJ_2 (MACRO_INPUT (rs #0 #1) p2)) (hash (PROJ_1 (MACRO_INPUT (rs #0 #1) p2)) (NONCE (mk #0 #1 p2)))))
                .to_vec()
                .into(),
                ..s1.clone()
        };
        pbl.protocols[0].add_step(s1);
        pbl.protocols[1].add_step(s2);
    }

    pub fn insert_rf(pbl: &mut Problem, funs: &MFunction) {
        let MFunction {
            p1,
            p2,
            rf,
            ko,
            mexists,
            msk,
            ..
        } = funs;

        let s1 = Step {
            id: rf.clone(),
            vars: [0].map(Var::from_u32).to_vec(),
            cond: rexp!((not (mexists #0 p1 (msk #0 p1)))).to_vec().into(),
            msg: rexp!(ko).to_vec().into(),
        };
        let s2 = Step {
            cond: rexp!((not (mexists #0 p2 (msk #0 p2)))).to_vec().into(),
            ..s1.clone()
        };
        pbl.protocols[0].add_step(s1);
        pbl.protocols[1].add_step(s2);
    }
}
