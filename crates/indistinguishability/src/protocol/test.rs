pub mod basic_hash {
    use crate::{
        Problem, decl_fun, mk_alias, mk_rewrite, mk_signature,
        protocol::Step,
        rexp,
        terms::{
            Exists, Function, FunctionFlags, InnerFunction, LT, MACRO_INPUT, NONCE, PROJ_1,
            PROJ_2, Sort, TUPLE,
        },
    };
    use egg::Var;

    pub struct MFunction {
        pub hash: Function,
        pub k1: Function,
        pub k2: Function,
        pub p1: Function,
        pub p2: Function,
        pub mk: Function,
        pub n: Function,
        pub tag: Function,
        pub rf: Function,
        pub rs: Function,
        pub mexists1: Function,
        pub msk1: Function,
        pub mexists2: Function,
        pub msk2: Function,
        pub ok: Function,
        pub ko: Function,
    }

    pub fn populate_functions(pbl: &mut Problem) -> MFunction {
        use Sort::*;
        let hash = decl_fun!(pbl; "hash": (Bitstring, Bitstring) -> Bitstring);
        let p1 = pbl.declare_new_protocol().name().clone();
        let p2 = pbl.declare_new_protocol().name().clone();
        let ok = decl_fun!(pbl; "ok": () -> Bitstring);
        let ko = decl_fun!(pbl; "ko": () -> Bitstring);
        let k1 = decl_fun!(pbl; "key1": (Index) -> Nonce);
        let k2 = decl_fun!(pbl; "key2": (Index, Index) -> Nonce);
        let n = decl_fun!(pbl; "n": (Index, Index) -> Nonce);

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

        // let init = {
        //     let signature = mk_signature!(() -> Sort::Time);
        //     let id = Function::new(InnerFunction {
        //         flags: FunctionFlags::STEP,
        //         step_idx: 0,
        //         ..InnerFunction::new("init".into(), signature)
        //     });
        //     pbl.function.add(id.clone());
        //     id
        // };

        let tag = {
            let signature = mk_signature!((Sort::Index, Sort::Index) -> Sort::Time);
            let id = Function::new(InnerFunction {
                flags: FunctionFlags::STEP,
                step_idx: 1,
                ..InnerFunction::new("tag".into(), signature)
            });
            pbl.function.add(id.clone());
            id
        };

        let rs = {
            let signature = mk_signature!((Sort::Index, Sort::Index) -> Sort::Time);
            let id = Function::new(InnerFunction {
                flags: FunctionFlags::STEP,
                step_idx: 2,
                ..InnerFunction::new("Rs".into(), signature)
            });
            pbl.function.add(id.clone());
            id
        };

        let rf = {
            let signature = mk_signature!((Sort::Index) -> Sort::Time);
            let id = Function::new(InnerFunction {
                flags: FunctionFlags::STEP,
                step_idx: 3,
                ..InnerFunction::new("Rf".into(), signature)
            });
            pbl.function.add(id.clone());
            id
        };

        let mexists1;
        let msk1;
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
            mexists1 = tlf.clone();
            msk1 = skolem.clone();
        };

        let mexists2;
        let msk2;
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
                .add_exists_function([Sort::Index, Sort::Time, Sort::Protocol], Sort::Index);
            *vars = [0, 1, 2].map(Var::from_u32).to_vec();
            *bound_var = Var::from_u32(3);
            *patt = rexp!((and
                (= (PROJ_1 (MACRO_INPUT #1 #2)) (PROJ_1 (MACRO_INPUT (tag #3 #0) #2)))
                (= (PROJ_2 (MACRO_INPUT #1 #2)) (PROJ_2 (MACRO_INPUT (tag #3 #0) #2)))
                (LT (tag #3 #0) #1) // <- the order matters ^^'
            ))
            .to_vec()
            .into();
            mexists2 = tlf.clone();
            msk2 = skolem.clone();
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
            mexists1,
            msk1,
            mexists2,
            msk2,
            ok,
            ko,
        }
    }

    // pub fn insert_init(pbl: &mut Problem, funs: &MFunction) {
    //     let MFunction { init, .. } = funs;

    //     let s1 = Step {
    //         id: init.clone(),
    //         vars: vec![],
    //         cond: rexp!(true).to_vec().into(),
    //         msg: rexp!(EMPTY).to_vec().into(),
    //     };
    //     pbl.protocols[0].add_step(s1.clone());
    //     pbl.protocols[1].add_step(s1);
    // }

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
            msg: rexp!((TUPLE (NONCE (n #0 #1)) (hash (NONCE (n #0 #1)) (NONCE (mk #0 #1 p1)))))
                .to_vec()
                .into(),
        };
        let s2 = Step {
            msg: rexp!((TUPLE (NONCE (n #0 #1)) (hash (NONCE (n #0 #1)) (NONCE (mk #0 #1 p2)))))
                .to_vec()
                .into(),
            ..s1.clone()
        };
        pbl.push_steps([s1, s2]);
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
        pbl.push_steps([s1, s2]);
    }

    pub fn insert_rf(pbl: &mut Problem, funs: &MFunction) {
        let MFunction {
            p1,
            p2,
            rf,
            ko,
            mexists1: mexists,
            msk1: msk,
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
        pbl.push_steps([s1, s2]);
    }

    pub fn insert_rw(pbl: &mut Problem, funs: &MFunction) {
        let MFunction {
            mexists2,
            msk2,
            hash,
            mk,
            ..
        } = funs;
        let rw = mk_rewrite!(
            0:Time, 1:Index, 2:Index, 3:Protocol in
            rexp!((= (PROJ_2 (MACRO_INPUT #0 #3)) (hash (PROJ_1 (MACRO_INPUT #0 #3)) (NONCE (mk #1 #2 #3))))) =>
                rexp!((mexists2 #2 #0 #3 (msk2 #2 #0 #3)))
        );

        pbl.extra_rewrite_mut().push(rw);
    }
}
