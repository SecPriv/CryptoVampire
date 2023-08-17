// #![allow(dead_code)]
// // #![feature(box_syntax)]
// // #![feature(box_patterns)]

// use std::{
//     fs::{self, read_to_string, File},
//     io::{self, Read, Write},
//     path::{Path, PathBuf},
//     rc::Rc,
// };

// use automator::{
//     formula::{cli::Args, env::Environement},
//     parser::parse_protocol,
//     smt::{
//         smt::Smt,
//         writer::{problem_smts_with_lemma, problem_to_smt},
//     },
// };
// use clap::Parser;

// extern crate pest_derive;

// extern crate paste;

use std::{
    fs::{self, read_to_string, File},
    io::{self, Read},
    path::{Path, PathBuf},
};

use automator::{
    container::ScopedContainer,
    environement::{cli::Args, environement::Environement},
    formula::{function::builtin::BUILT_IN_FUNCTIONS, sort::builtins::BUILT_IN_SORTS},
    parser,
    problem::{PblIterator, Problem},
    smt::smt::SmtFile,
    utils::traits::{MyWriteTo, NicerError},
};

const USE_MIRI: bool = false;

fn main() {
    // let args = Args::parse();
    let args = Args {
        file: Some(PathBuf::from("/tmp/basic-hash-1.ptcl")),
        output_location: PathBuf::from("../test.smt"),
        lemmas: false,
        eval_rewrite: false,
        crypto_rewrite: false,
        vampire_subterm: false,
        assert_theory: false,
        skolemnise: false,
        preprocessing: false,
        legacy_evaluate: false,
        no_bitstring: false,
        cvc5: false,
        no_symbolic: false,
    };

    ScopedContainer::scoped(|container| {
        debug_print::debug_println!("start");
        let env = Environement::from_args(&args, &*container);

        // let str = ;
        debug_print::debug_println!("read input...");
        let str = if USE_MIRI {
            TEST_FILE.to_string()
        } else {
            if let Some(file) = &args.file {
                read_to_string(file).unwrap_or_else(|_| {
                    panic!(
                        "file \"{}\" not found",
                        file.to_str().unwrap_or("[non-unicode file name]")
                    )
                })
            } else {
                let mut buf = String::new();
                Read::read_to_string(&mut io::stdin(), &mut buf).expect("unable to read stdin");
                buf
            }
        };

        let pbl = Problem::try_from_str(
            container,
            BUILT_IN_SORTS.iter().cloned(),
            BUILT_IN_FUNCTIONS.iter().cloned(),
            parser::USED_KEYWORDS.iter().map(|s| s.to_string()),
            &str,
        )
        .expect_display("parsing error:");

        if USE_MIRI {
            println!(
                "\n\n\n\n\n\n{}",
                SmtFile::from_general_file(&env, pbl.into_general_file(&env))
            )
        } else {
            if args.lemmas {
                assert!(!args.output_location.is_file());

                fs::create_dir_all(&args.output_location).expect("couldn't create dir");

                let mut i = 0;
                // for (i, smt) in smts.enumerate() {
                //     let path = args.output_location.join(Path::new(&format!("{}.smt", i)));
                //     write_to_file(&path, smt);
                // }

                let mut pbliter = PblIterator::from(pbl);

                while let Some(pbl) = pbliter.next() {
                    let path = args.output_location.join(Path::new(&format!("{}.smt", i)));

                    write_to_file(
                        &path,
                        SmtFile::from_general_file(&env, pbl.into_general_file(&env)),
                    );

                    i += 1;
                }
            } else {
                assert!(!args.output_location.is_dir());
                let smt = SmtFile::from_general_file(&env, pbl.into_general_file(&env));
                write_to_file(&args.output_location, smt);
            }
        }
    });

    //     let pbl = match parse_protocol(env, &str) {
    //         Ok(p) => p,
    //         Err(e) => {
    //             let file = if let Some(f) = &args.file {
    //                 f.to_str().unwrap_or("[non-unicode file name]")
    //             } else {
    //                 "stdin"
    //             };
    //             panic!("error while parsing {}:\n{}", file, e)
    //         }
    //     };

    //     if args.lemmas {
    //         assert!(!args.output_location.is_file());

    //         fs::create_dir_all(&args.output_location).expect("couldn't create dir");

    //         let smts = problem_smts_with_lemma(pbl);
    //         for (i, smt) in smts.enumerate() {
    //             let path = args.output_location.join(Path::new(&format!("{}.smt", i)));
    //             write_to_file(&path, smt);
    //         }
    //     } else {
    //         assert!(!args.output_location.is_dir());
    //         let smt = problem_to_smt(pbl);
    //         write_to_file(&args.output_location, smt);
    //     }

    //     // println!("{:?}", p)

    //     // for s in smt {
    //     //     println!("{}\n", s);
    //     // }
    // }
}

fn write_to_file(path: &PathBuf, smt: impl MyWriteTo) {
    let mut f = File::options()
        .write(true)
        .truncate(true)
        .create(true)
        .open(path)
        .unwrap_or_else(|_| {
            panic!(
                "error while open the file {}",
                path.as_os_str().to_str().unwrap_or("invalid")
            )
        });

    smt.write_to_io(&mut f).unwrap()
}

// fn main() {
//     // parser::parse_string("").unwrap()
// }

const TEST_FILE: &'static str = r"


type index;
fun tpl(Message, Message):Message

type session

fun hash(Message, Message):Message
fun verify(Message, Message, Message):Bool

fun sel1of2(Message):Message;
fun sel2of2(Message):Message
fun ok:Message
fun ko:Message

/* the Nonces */
fun nt(session, index): Name
fun nr(session): Name
fun key(index):Name

step reader(i:session, j:index)
    /*{ (hash(sel1of2(input(reader(i, j))), key(j))
                    == sel2of2(input(reader(i, j)))) }*/
    { verify(
        sel2of2(input(reader(i, j))),
        sel1of2(input(reader(i, j))),
        key(j)
    ) }
    { ok }

step reader_fail(i:session)
    { not(exists (j:index) {cond(reader(i, j))}) }
    { ko }

step tag(i:session, j:index)
    { true }
    { tpl(
        nt(i,j),
        hash(
            nt(i,j),
            key(j)
        )
    )}

assert
    forall (m1:Message, m2:Message) {
        (
            (m1 == sel1of2(tpl(m1,m2))) 
            && (m2 == sel2of2(tpl(m1,m2)))
        )
    }

assert
    forall (s:Message, m:Message, k:Nonce) {
        (verify(s, m, k) <=> (s == hash(m, k)))
    }

order forall (i:session, j:index) 
    { reader_fail(i) <> reader(i, j) }

order forall (i:session, j:index, j2:index) 
    { reader(i, j2) <> reader(i, j) }

let conclusion!(i:session, j:index) = exists (k:session) {(
    lt(tag(k, j), reader(i, j))
    && (sel1of2(msg(tag(k, j))) == sel1of2(input(reader(i, j))))
    && (sel2of2(msg(tag(k, j))) == sel2of2(input(reader(i, j))))
)}

let premise!(i:session, j:index) = /*(
    hash(sel1of2(input(reader(i, j))), key(j)) 
                    == sel2of2(input(reader(i, j)))
)*/ cond!(reader(i, j))

query forall (i:session, j:index) {(
    happens(reader(i, j))
        => (conclusion![i, j] <=> premise![i, j]) 
)}

assert-crypto euf-cma hash verify;
assert-crypto nonce;

";
