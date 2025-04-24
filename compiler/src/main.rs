use std::fs;
use std::path::PathBuf;

use clap::Parser;
use parsers::parse;
use std::io::Result;

mod compile;

use common::{verify_scope::*, Policy};

/// A compiler for Paralegal's Controlled Natural Language (CNL) policies.
///
/// By default this generates a Rust namespace (`mod`) that contains a function
/// `check` which, when called, enforces your policy. You should use the
/// framework in
/// [`paralegal_policy`](https://brownsys.github.io/paralegal/libs/paralegal_policy/)
/// to create a suitable binary that calls this function. It depends on the
/// crates `paralegal_policy` and `anyhow`.
///
/// Alternatively you may use the `--bin` argument, which will instead create a
/// Rust source file with a `main` function and necessary boilerplate to call
/// the policy. The file created with this method additionally depends on the
/// `clap` crate with the `derive` feature enabled.
#[derive(clap::Parser)]
struct Args {
    /// Path to the policy file.
    path: PathBuf,
    /// Also generate boilerplate for a runnable policy. The output file
    /// contains a `main` function that runs both the PDG generation as well as
    /// the policy.
    #[clap(long)]
    bin: bool,
    /// Name of the output file.
    #[clap(short, long, default_value = "compiled_policy.rs")]
    out: PathBuf,
}

fn create_environment(policy: &Policy) -> Environment {
    let mut env = Environment::new();
    verify_definitions_scope(&policy.definitions, &mut env);
    verify_scope(&policy.body, &mut env);
    env
}

fn run(args: &Args) -> Result<()> {
    let policy = fs::read_to_string(&args.path).expect("Could not read policy file");

    let res = parse(&policy);
    match res {
        Ok((_, mut policy)) => {
            // Verify that variables in definitions & policy are properly scoped.
            // If this fails, then the user made a mistake writing their policy.
            create_environment(&policy);
            optimizer::optimize(&mut policy);
            let env = create_environment(&policy);
            compile::compile(
                policy,
                args.path
                    .file_name()
                    .map_or("<unnamed>", |n| n.to_str().unwrap()),
                &args.out,
                &env,
                args.bin,
            )
        }
        Err(e) => match e {
            nom::Err::Incomplete(_) => {
                panic!("Incomplete parse")
            }
            nom::Err::Failure(e) => {
                panic!("Parse failure: {}", e)
            }
            nom::Err::Error(e) => {
                for (loc, context) in e.errors {
                    eprintln!("Error in context {context:?}:\n{loc}\n");
                }
                panic!("Parse error")
            }
        },
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    run(&args)
}
