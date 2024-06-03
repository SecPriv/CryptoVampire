use std::{
    fs::{self, read_to_string, File},
    io::{self, BufWriter, Read},
    path::{Path, PathBuf},
};

use clap::Parser;
use cryptovampire::{
    cli::Args,
    parser, problem_try_from_str,
    runner::{
        run_multiple_time,
        vampire_runner::{VampireArg, VampireExec},
    },
    smt::smt::SmtFile,
};
use cryptovampire_lib::{
    container::ScopedContainer,
    environement::environement::Environement,
    formula::{function::builtin::BUILT_IN_FUNCTIONS, sort::builtins::BUILT_IN_SORTS},
    problem::PblIterator,
};
use log::trace;
use std::io::Write;
use utils::{
    from_with::FromWith,
    traits::{MyWriteTo, NicerError},
};

const USE_MIRI: bool = false;

fn main() {
    let args = Args::parse();

    env_logger::Builder::new()
        .format(|buf, record| {
            let str = record.args().to_string().replace("\n", "\n\t");
            writeln!(
                buf,
                "[{}] in {}:{}\n\t{}",
                record.level(),
                record.file().unwrap_or("unknown"),
                record.line().unwrap_or(0),
                str
            )
        })
        .parse_default_env()
        // .filter_level(log::LevelFilter::Trace)
        .init();

    ScopedContainer::scoped(|container| {
        trace!("start");
        let env = Environement::from_with(&args, &*container);

        // let str = ;
        trace!("read input...");
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

        let mut pbl = problem_try_from_str(
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
                SmtFile::from_general_file(&env, pbl.into_general_file(&env)).as_diplay(&env)
            )
        } else {
            if args.lemmas {
                assert!(
                    !args.auto_retry,
                    "Can't auto run vampire with lemma ativated"
                );
                assert!(
                    !args.output_location.is_file(),
                    "the oupput is a file, it should be a directory"
                );

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
                        SmtFile::from_general_file(&env, pbl.into_general_file(&env))
                            .as_diplay(&env),
                    );

                    i += 1;
                }
            } else if args.auto_retry {
                let vampire = VampireExec {
                    location: args.vampire_location,
                    extra_args: vec![VampireArg::TimeLimit(args.vampire_exec_time)],
                };
                print!(
                    "{:}",
                    run_multiple_time(args.num_of_retry, &vampire, &env, &mut pbl).unwrap()
                )
            } else {
                assert!(!args.output_location.is_dir());
                let smt = SmtFile::from_general_file(&env, pbl.into_general_file(&env));
                write_to_file(&args.output_location, smt.as_diplay(&env));
            }
        }
    });
}

fn write_to_file(path: &PathBuf, smt: impl MyWriteTo) {
    let f = File::options()
        .write(true)
        .truncate(true)
        .create(true)
        .open(path)
        .unwrap_display();
    let mut bw = BufWriter::new(f);

    smt.write_to_io(&mut bw).unwrap()
}
const TEST_FILE: &'static str = include_str!("../../test/basic-hash-1.ptcl");
