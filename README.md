# paralegal-compiler

To run the compiler, `cd` into the `compile` directory and run `cargo run -- policy.txt`. That should output a file called `compiled-policy.rs`.

To test it against the toy program, copy and paste the file into the `main.rs` file of the `test-programs` directory. Write the line `pub mod program` somewhere in the file, then run `cargo run`. You should see "Policy successful."
You need the `pub mod program` because I'm running the policy in the same directory as the toy program for simplicity.
Later, I'll write `compiled-policy.rs` to its own cargo project with its own Cargo.toml, etc. so the policy will work as written.
