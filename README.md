# paralegal-compiler

A compiler for Paralegal's Controlled Natural Language (CNL) policies.

By default this generates a Rust namespace (`mod`) that contains a function
`check` which, when called, enforces your policy. You should use the framework
in
[`paralegal_policy`](https://brownsys.github.io/paralegal/libs/paralegal_policy/)
to create a suitable binary that calls this function. It depends on the crates
`paralegal_policy` and `anyhow`.

Alternatively you may use the `--bin` argument, which will instead create a Rust source file with a
`main` function and necessary boilerplate to call the policy. The file created with this method
additionally depends on the `clap` crate with the `derive` feature enabled.

## Usage

Install the compiler with `cargo install`, then run it as `paralegal-compiler`.

For more information use `--help`.
