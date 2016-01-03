extern crate clap;
extern crate jmespath;

use std::io::prelude::*;
use std::io;
use std::fs::File;
use std::process::exit;
use std::rc::Rc;

use clap::{Arg, App};
use jmespath::{Variable, Expression};

macro_rules! err_quit(
    ($msg:expr, $code:expr) => (
        match writeln!(&mut ::std::io::stderr(), "{}", $msg) {
            Ok(_) => exit($code),
            Err(x) => panic!("Unable to write to stderr: {}", x),
        }
    )
);

fn main() {
    let matches = App::new("jp")
        .version("1.0")
        .author("Michael Dowling <mtdowling@gmail.com>")
        .about("JMESPath command line interface")
        .arg(Arg::with_name("filename")
            .help("Read input JSON from a file instead of stdin.")
            .short("f")
            .takes_value(true)
            .long("filename"))
        .arg(Arg::with_name("unquoted")
            .help("If the final result is a string, it will be printed without quotes.")
            .short("u")
            .long("unquoted")
            .multiple(false))
        .arg(Arg::with_name("ast")
            .help("Only print the AST of the parsed expression.  Do not rely on this output, \
                  only useful for debugging purposes.")
            .long("ast")
            .multiple(false))
        .arg(Arg::with_name("expr-file")
            .help("Read JMESPath expression from the specified file.")
            .short("e")
            .takes_value(true)
            .long("expr-file")
            .conflicts_with("expression")
            .required(true))
        .arg(Arg::with_name("expression")
            .help("JMESPath expression to evaluate")
            .index(1)
            .conflicts_with("expr-file")
            .required(true))
        .get_matches();

    let expr = match get_expr(matches.value_of("expr-file"), matches.value_of("expression")) {
        Ok(e) => e,
        Err(e) => err_quit!(format!("{}", e), 2)
    };

    if matches.is_present("ast") {
        println!("{}", expr.ast);
        exit(0);
    }

    let json = match get_json(matches.value_of("filename")) {
        Ok(json) => json,
        Err(e) => err_quit!(format!("{}", e), 1)
    };

    match expr.search(json) {
        Err(e) => err_quit!(format!("{}", e), 4),
        Ok(result) => show_result(result, matches.is_present("unquoted"))
    }
}

fn show_result(result: Rc<Variable>, unquoted: bool) {
    if unquoted && result.is_string() {
        println!("{}", result.as_string().unwrap());
    } else {
        match result.to_pretty_string() {
            Some(s) => println!("{}", s),
            None => err_quit!(format!("Error converting result to string: {:?}", result), 3),
        }
    }
}

fn read_file(label: &str, filename: &str) -> Result<String, String> {
    let mut buffer = String::new();
    let mut f = match File::open(filename) {
        Ok(result) => result,
        Err(e) => return Err(format!("Error opening {} file at {:?}: {}", label, filename, e))
    };
    if let Err(e) = f.read_to_string(&mut buffer) {
        Err(format!("Error reading {} from {:?}: {}", label, filename, e))
    } else {
        Ok(buffer)
    }
}

fn get_json(filename: Option<&str>) -> Result<Variable, String> {
    let buffer = match filename {
        Some(f) => try!(read_file("JSON", f)),
        None => {
            let mut buffer = String::new();
            match io::stdin().read_to_string(&mut buffer) {
                Ok(_) => buffer,
                Err(e) => return Err(format!("Error reading JSON from stdin: {}", e))
            }
        }
    };
    Variable::from_str(&buffer).map_err(|e| format!("Error parsing JSON: {:?}", e))
}

fn get_expr(expr_file: Option<&str>, expr_string: Option<&str>) -> Result<Expression, String> {
    match expr_string {
        Some(s) => Expression::new(s),
        None => {
            let buffer = try!(read_file("expression", expr_file.unwrap()));
            Expression::new(&buffer)
        }
    }.map_err(|e| format!("{}", e))
}
