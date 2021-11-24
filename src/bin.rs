mod parser;
mod tecs_file;
mod interpreter;

use aterms::parse_term_from_file;
use clap::{App, Arg};
use interpreter::Interpreter;

fn main() {
    let matches = App::new("Tecs")
        .version("0.0.1")
        .author("Matthijs Bijman <matthijs@bijman.org>")
        .about("Term checker for language implementation")
        .arg(
            Arg::with_name("tecs_file")
                .short("t")
                .long("tecs")
                .value_name("FILE")
                .required(true),
        )
        .arg(
            Arg::with_name("input_file")
                .short("i")
                .long("input")
                .value_name("FILE")
                .required(true),
        )
        .arg(
            Arg::with_name("rule")
                .short("r")
                .long("rule")
                .value_name("NAME")
                .required(true),
        )
        .get_matches();

    let tecs_file = matches.value_of("tecs_file").unwrap();
    let term_name = matches.value_of("input_file").unwrap();
    let rule_name = matches.value_of("rule").unwrap();
    let input_term = parse_term_from_file(&String::from(term_name)).unwrap();
    
    let engine = Interpreter::new(tecs_file);
    match engine.run(input_term, rule_name) {
        Ok(r) => {
            println!("{:?}", r);
        },
        Err(err) => {
            eprintln!("Failure:\n{}", err);
        }
    }
}
