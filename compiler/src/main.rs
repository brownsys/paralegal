mod compile;
mod verify_scope;

use std::fs;
use std::path::PathBuf;

use clap::Parser;
use compile::compile;
use parsers::parse;
use std::io::Result;

/// A compiler for Paralegal's Controlled Natural Language (CNL) policies.
///
/// By default this generates a Rust namespace (`mod`) that contains a function
/// `check` which, when called, enforces your policy. You should use the
/// framework in [`paralegal_policy`] to create a suitable binary that calls
/// this function. It depends on the crates `paralegal_policy` and `anyhow`.
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

fn run(args: &Args) -> Result<()> {
    let policy = fs::read_to_string(&args.path).expect("Could not read policy file");

    let res = parse(&policy);
    match res {
        Ok((_, policy)) => compile(
            policy,
            args.path
                .file_name()
                .map_or("<unnamed>", |n| n.to_str().unwrap()),
            &args.out,
            args.bin,
        ),
        Err(e) => panic!("{}", e),
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    run(&args)
}
