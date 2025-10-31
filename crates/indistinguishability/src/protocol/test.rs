pub mod basic_hash {
    use egg::Var;
    use itertools::Itertools;

    use crate::protocol::Step;
    use crate::terms::{
        Exists, Function, FunctionFlags, INDEX_SORT, InnerFunction, LT, MACRO_INPUT, NONCE, PROJ_1,
        PROJ_2, QuantifierT, Sort, TUPLE,
    };
    use crate::{Problem, decl_fun, mk_alias, mk_rewrite, mk_signature, rexp};

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
        let hash = decl_fun!(pbl; "hash": (Bitstring, Bitstring) -> Bitstring);
        let p1 = pbl.declare_new_protocol().name().clone();
        let p2 = pbl.declare_new_protocol().name().clone();
        let ok = decl_fun!(pbl; "ok": () -> Bitstring);
        let ko = decl_fun!(pbl; "ko": () -> Bitstring);
        let k1 = decl_fun!(pbl; "key1": (Index) -> Nonce);
        let k2 = decl_fun!(pbl; "key2": (Index, Index) -> Nonce);
        let n = decl_fun!(pbl; "n": (Index, Index) -> Nonce);

        let mk = {
            use Sort::*;
            let alias = mk_alias! {
                0:Index, 1:Index
                    in rexp!(#0), rexp!(#1), rexp!(p1) => rexp!((k1 #0)),
                0:Index, 1:Index
                    in rexp!(#0), rexp!(#1), rexp!(p2) => rexp!((k2 #0 #1))
            };
            // let mk = Function::new(inner);
            // pbl.functions_mut().add(mk.clone());
            pbl.declare_function()
                .alias(alias)
                .name("key")
                .inputs([Index, Index, Protocol])
                .output(Nonce)
                .call()
        };

        let tag = pbl
            .declare_function()
            .name("tag")
            .step(1)
            .inputs([Sort::Index; 2])
            .call();

        let rs = pbl
            .declare_function()
            .name("Rs")
            .step(2)
            .inputs([Sort::Index; 2])
            .call();

        let rf = pbl
            .declare_function()
            .name("Rf")
            .step(3)
            .inputs([Sort::Index])
            .call();

        let mexists1;
        let msk1;
        {
            use Sort::{Index, Protocol};
            let e = Exists::insert()
                .pbl(pbl)
                .cvars_sort([Index, Protocol])
                .bvars_sorts([Index])
                .call();
            let (j, p) = e.cvars_as_lang().collect_tuple().unwrap();
            let i = e.bvars_as_lang().next().unwrap();
            e.set_patt(rexp!((= (PROJ_2 (MACRO_INPUT (rf #j) #p)) (hash (PROJ_1 (MACRO_INPUT (rf #j) #p)) (NONCE (mk #i #j #p))))));
            mexists1 = e.top_level_function().clone();
            msk1 = e.skolems()[0].clone();
        };

        let mexists2;
        let msk2;
        {
            use Sort::{Index, Protocol, Time};
            let e = Exists::insert()
                .pbl(pbl)
                .cvars_sort([Index, Time, Protocol])
                .bvars_sorts([Index])
                .call();
            let (j, t, p) = e.cvars_as_lang().collect_tuple().unwrap();
            let i = e.bvars_as_lang().next().unwrap();
            e.set_patt(rexp!((and
                (= (PROJ_1 (MACRO_INPUT #t #p)) (PROJ_1 (MACRO_INPUT (tag #i #j) #p)))
                (= (PROJ_2 (MACRO_INPUT #t #p)) (PROJ_2 (MACRO_INPUT (tag #t #j) #p)))
                (LT (tag #3 #0) #1) // <- the order matters ^^'
            )));
            mexists2 = e.top_level_function().clone();
            msk2 = e.skolems()[0].clone();
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
            vars: [0, 1].map(Var::from_usize).to_vec(),
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
            vars: [0, 1].map(Var::from_usize).to_vec(),
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
            vars: [0].map(Var::from_usize).to_vec(),
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
