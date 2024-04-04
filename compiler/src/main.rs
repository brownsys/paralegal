mod compile;
mod verify_scope;

use std::env;
use std::fs;

use parsers::parse;
use compile::compile;
use std::io::Result;

fn run(args: &Vec<String>) -> Result<()> {
    if args.len() < 2 {
        panic!("Need to pass path to policy file");
    }
    let policy_file = &args[1];
    let policy = fs::read_to_string(policy_file)
        .expect("Could not read policy file");

    let res = parse(&policy);
    dbg!(&res);
    match res {
        Ok((_, policy)) => compile(policy),
        Err(e) => panic!("{}", e),
    }
}

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    run(&args)?;
    // Command::new("rustfmt compiled-policy.rs").output().expect("failed to run cargo fmt");
    Ok(())
}
