use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::rc::Rc;

use clap::Parser;
use jmespath::{Rcvar, Variable, compile};

#[derive(Parser, Debug, Default)]
#[command(name = "jp", version, about = "JMESPath command line interface")]
pub struct JpArgs {
    /// Read input JSON from a file instead of stdin.
    #[arg(short = 'f', long = "filename")]
    pub filename: Option<String>,

    /// If the final result is a string, it will be printed without quotes.
    #[arg(short = 'u', long = "unquoted")]
    pub unquoted: bool,

    /// Only print the AST of the parsed expression. Do not rely on this output, only useful for debugging purposes.
    #[arg(long = "ast")]
    pub ast: bool,

    /// Read JMESPath expression from the specified file.
    #[arg(short = 'e', long = "expr-file", conflicts_with = "expression")]
    pub expr_file: Option<String>,

    /// JMESPath expression to evaluate
    #[arg(conflicts_with = "expr_file", required_unless_present = "expr_file")]
    pub expression: Option<String>,
}

#[derive(Debug)]
pub struct JpOutput {
    pub stdout: String,
    pub stderr: String,
}

pub fn run(args: JpArgs) -> Result<JpOutput, JpOutput> {
    run_with_stdin(args, None)
}

pub fn run_with_stdin(args: JpArgs, stdin_data: Option<&str>) -> Result<JpOutput, JpOutput> {
    let make_error = |msg: String| JpOutput {
        stdout: String::new(),
        stderr: format!("{}\n", msg),
    };

    let expr_str = if let Some(ref expr_file) = args.expr_file {
        match read_file("expression", expr_file) {
            Ok(content) => content,
            Err(e) => return Err(make_error(e)),
        }
    } else {
        args.expression.clone().unwrap()
    };

    let expr = match compile(&expr_str) {
        Ok(e) => e,
        Err(e) => return Err(make_error(e.to_string())),
    };

    if args.ast {
        return Ok(JpOutput {
            stdout: format!("{:#?}\n", expr.as_ast()),
            stderr: String::new(),
        });
    }

    let json = match get_json(args.filename.as_deref(), stdin_data) {
        Ok(j) => Rc::new(j),
        Err(e) => return Err(make_error(e)),
    };

    match expr.search(&json) {
        Err(e) => Err(make_error(e.to_string())),
        Ok(result) => Ok(JpOutput {
            stdout: format_result(result, args.unquoted),
            stderr: String::new(),
        }),
    }
}

fn format_result(result: Rcvar, unquoted: bool) -> String {
    if unquoted && result.is_string() {
        format!("{}\n", result.as_string().unwrap())
    } else {
        let mut buf = Vec::new();
        serde_json::to_writer_pretty(&mut buf, &result).unwrap();
        buf.push(b'\n');
        String::from_utf8(buf).unwrap()
    }
}

fn read_file(label: &str, filename: &str) -> Result<String, String> {
    match File::open(filename) {
        Err(e) => Err(format!(
            "Error opening {} file at {}: {}",
            label, filename, e
        )),
        Ok(mut file) => {
            let mut buffer = String::new();
            file.read_to_string(&mut buffer)
                .map_err(|e| format!("Error reading {} from {}: {}", label, filename, e))?;
            Ok(buffer)
        }
    }
}

fn get_json(filename: Option<&str>, stdin_data: Option<&str>) -> Result<Variable, String> {
    let buffer = match (filename, stdin_data) {
        (Some(f), _) => read_file("JSON", f)?,
        (None, Some(data)) => data.to_string(),
        (None, None) => {
            let mut buffer = String::new();
            io::stdin()
                .read_to_string(&mut buffer)
                .map_err(|e| format!("Error reading JSON from stdin: {}", e))?;
            buffer
        }
    };
    Variable::from_json(&buffer).map_err(|e| format!("Error parsing JSON: {}", e))
}
