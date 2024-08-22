use std::{
    fs::read_to_string,
    io::{self, Read},
};

use clap::Parser;
use cryptovampire::{cli::Args, init_logger, run_from_cv, squirrel::run_from_json};

use log::trace;

fn main() {
    let args = Args::parse();

    init_logger();

    trace!("start");
    trace!("read input...");
    let str = {
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
    match args.input_format {
        cryptovampire::cli::Input::Cryptovampire => run_from_cv(args, &str),
        cryptovampire::cli::Input::SquirrelJSON => run_from_json(args, &str),
    }
    .unwrap();

    trace!("done")
}

#[cfg(test)]
mod tests {

    // #[test]
    // fn debug() {
    //     let args = Args::parse_from([&"./examples/feldhofer-2.ptcl"]);

    //     init_logger();

    //     trace!("start");
    //     trace!("read input...");
    //     let str = {
    //         if let Some(file) = &args.file {
    //             read_to_string(file).unwrap_or_else(|_| {
    //                 panic!(
    //                     "file \"{}\" not found",
    //                     file.to_str().unwrap_or("[non-unicode file name]")
    //                 )
    //             })
    //         } else {
    //             let mut buf = String::new();
    //             Read::read_to_string(&mut io::stdin(), &mut buf).expect("unable to read stdin");
    //             buf
    //         }
    //     };
    //     run(args, &str).unwrap();
    //     trace!("done")
    // }
}
