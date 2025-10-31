use std::fs::read_to_string;
use std::io::{self, Read};

use clap::Parser;
use cryptovampire::cli::Args;
use cryptovampire::squirrel::run_from_json;
use cryptovampire::{Return, init_logger, run_from_cv};
use log::trace;

fn main() {
    let args = Args::parse();
    let output_format = args.output_format;

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
    trace!("input read");
    let res = match args.input_format {
        cryptovampire::cli::Input::Cryptovampire => run_from_cv(args, &str),
        cryptovampire::cli::Input::SquirrelJSON => run_from_json(args, &str).map(Return::Many),
    };

    let res = if cfg!(debug_assertions) {
        Ok(res.unwrap())
    } else {
        res
    };

    match output_format {
        cryptovampire::cli::Output::Quiet => (),
        cryptovampire::cli::Output::Stdout => match res {
            Err(e) => panic!("error: {e}"),
            Ok(res) => eprintln!("{res}"),
        },
        cryptovampire::cli::Output::JSON => {
            let res = res.map_err(|e| format!("{e:}"));
            println!("{}", serde_json::to_string(&res).unwrap())
        }
        cryptovampire::cli::Output::PrettyJSON => {
            let res = res.map_err(|e| format!("{e:}"));
            println!("{}", serde_json::to_string(&res).unwrap())
        }
    }

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
