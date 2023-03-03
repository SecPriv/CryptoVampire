// #![feature(box_syntax)]
// #![feature(box_patterns)]

use std::{
    fs::{self, read_to_string, File},
    io::{self, Read, Write},
    path::{Path, PathBuf},
    rc::Rc,
};

use automator::{
    formula::{cli::Args, env::Environement},
    parser::parse_protocol,
    smt::{
        smt::Smt,
        writer::{problem_smts_with_lemma, problem_to_smt},
    },
};
use clap::Parser;

extern crate pest_derive;

extern crate paste;

fn main() {
    let args = Rc::new(Args::parse());
    let env = Environement::empty(Rc::clone(&args));

    let str = if let Some(file) = &args.file {
        read_to_string(file).unwrap_or_else(|_| panic!("file \"{}\" not found",
            file.to_str().unwrap_or("[non-unicode file name]")))
    } else {
        let mut buf = String::new();
        Read::read_to_string(&mut io::stdin(), &mut buf).expect("unable to read stdin");
        buf
    };

    let pbl = match parse_protocol(env, &str) {
        Ok(p) => p,
        Err(e) => {
            let file = if let Some(f) = &args.file {
                f.to_str().unwrap_or("[non-unicode file name]")
            } else {
                "stdin"
            };
            panic!("error while parsing {}:\n{}", file, e)
        }
    };

    if args.lemmas {
        assert!(!args.output_location.is_file());

        fs::create_dir_all(&args.output_location).expect("couldn't create dir");

        let smts = problem_smts_with_lemma(pbl);
        for (i, smt) in smts.enumerate() {
            let path = args.output_location.join(Path::new(&format!("{}.smt", i)));
            write_to_file(&path, smt);
        }
    } else {
        assert!(!args.output_location.is_dir());
        let smt = problem_to_smt(pbl);
        write_to_file(&args.output_location, smt);
    }

    // println!("{:?}", p)

    // for s in smt {
    //     println!("{}\n", s);
    // }
}

fn write_to_file(path: &PathBuf, smt: Vec<Smt>) {
    let mut f = File::options()
        .write(true)
        .truncate(true)
        .create(true)
        .open(path)
        .unwrap_or_else(|_| panic!("error while open the file {}",
            path.as_os_str().to_str().unwrap_or("invalid")));

    for s in smt.into_iter() {
        write!(f, "{}\n\n", s).expect("couldn't write");
    }
}
