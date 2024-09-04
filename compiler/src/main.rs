mod compile;
mod verify_scope;

use std::fs;
use std::path::PathBuf;

use clap::Parser;
use compile::compile;
use parsers::parse;
use std::io::Result;

#[derive(clap::Parser)]
struct Args {
    path: PathBuf,
    #[clap(short, long, default_value = "compiled_policy.rs")]
    out: PathBuf,
}

fn run(args: &Args) -> Result<()> {
    let policy = fs::read_to_string(&args.path).expect("Could not read policy file");

    let res = parse(&policy);
    match res {
        Ok((_, policy)) => compile(policy, &args.out),
        Err(e) => panic!("{}", e),
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    run(&args)
}
