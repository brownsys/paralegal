# DFPP

A Rust compiler plugin for extracting Forge model code via dataflow analysis powered by Flowistry.

### Requirements

* A patched Rust compiler (`rustc`)
* A patched version of `cargo`

XXX TODO: what patches to apply and where to find them?

### Getting Started

Within the root of your local checkout of this repo, create a symlink to the patched stage 2
Rust compiler:
```shell
$ ln -s PATH_TO_PATCHED_RUSTC rust-dfpp-patch
```

XXX TODO: and then? cargo run?
