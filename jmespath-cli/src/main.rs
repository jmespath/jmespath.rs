use clap::Parser;
use jmespath_cli::{JpArgs, run};

fn main() {
    let args = JpArgs::parse();
    match run(args) {
        Ok(output) => {
            print!("{}", output.stdout);
        }
        Err(output) => {
            eprint!("{}", output.stderr);
            std::process::exit(1);
        }
    }
}
