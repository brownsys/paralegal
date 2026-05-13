# Paralegal test infrastructure

Quick reference for writing regression tests. Most tests compile a snippet of Rust source in-process with the embedded `rustc_driver`, then run paralegal on it.

## Where things live

- `crates/plugin/tests/` — the bulk of the test suite; one `.rs` file per integration-test binary (each is its own `cargo test --test <name>`).
- `crates/plugin/tests/fixtures/` — `.toml` marker files passed via `with_marker_file` / `with_markers`.
- `crates/plugin/tests/{async-tests,stub-tests,cross-crate}/` — auxiliary cargo crates compiled and linked into inline tests via `with_dependency_environment` / `with_manifest`, or analyzed end-to-end via `cross-crate.rs`.
- `crates/plugin/tests/purity/` — submodule re-exported by `purity-tests.rs` (one file per scenario).
- `crates/plugin/src/test_utils.rs` — the public test API (`InlineTestBuilder`, `inline_test!`, `PreFrg`, `CtrlRef`, `FlowsTo`, `DependencyEnvironment`, …) re-exported as `paralegal_flow::test_utils::*`.
- `crates/rustc-utils/src/test_utils.rs` — low-level `CompileBuilder` / `CompileResult`; only directly used by `pdg.rs` and downstream of `InlineTestBuilder`.
- `crates/policy/src/test_utils.rs` — `test_ctx()` for testing the policy layer against `tests/test-crate`.

## Pick-the-right-helper cheat sheet

| Test goal | Use |
| --- | --- |
| Assert flow facts on a generated PDG with marker annotations | `inline_test! { … }.check_ctrl(|ctrl| …)` |
| Same, but you need the source as a `&str` constant or computed | `InlineTestBuilder::new(src).check_ctrl(…)` |
| Assert that compilation/analysis *fails* | `InlineTestBuilder::…expect_fail_compile()` |
| Bare PDG-level assertion (no markers, no `paralegal_flow::Args` plumbing) | `pdg_test!` (only defined in `crates/plugin/tests/pdg.rs`) |
| Test against a real cargo crate (cross-crate inlining, build-config) | `paralegal_flow_command(dir).args(…).status()` plus `define_flow_test_template!` |
| Need stdlib or external deps inside `inline_test!` | build a `DependencyEnvironment` once via `OnceLock`, pass with `with_dependency_environment(&env)` |
| Policy-layer test (operates on a `RootContext`) | `paralegal_policy::test_utils::test_ctx()` |

### `inline_test!` and `InlineTestBuilder`

```rust
use paralegal_flow::{inline_test, test_utils::*};

#[test]
fn my_test() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn src() -> i32 { 0 }
        #[paralegal_flow::marker(sink, arguments = [0])]
        fn snk(_: i32) {}
        fn main() { snk(src()); }
    }
    .with_extra_args(["--include=crate", "--no-adaptive-approximation"])
    .check_ctrl(|graph| {
        let s = graph.call_site(&graph.function("src"));
        let t = graph.call_site(&graph.function("snk"));
        assert!(s.output().flows_to_data(&t.input()));
    });
}
```

`inline_test! { … }` is sugar for `InlineTestBuilder::new(stringify!(…))`. The default analysis entrypoint is `crate::main`; override with `with_entrypoint("crate::foo")` or drop it with `without_entrypoint()`. Use raw `#[paralegal_flow::marker(…)]` attributes (not `#[paralegal::marker(…)]`) — the `paralegal` library is not linked into inline tests. Other builder knobs: `with_extra_args` (paralegal CLI flags), `with_rustc_args`, `with_marker_file` (`.toml` external annotations), `with_build_config`, `with_dependency_environment`. Terminal calls: `check_ctrl(|CtrlRef| …)`, `run(|PreFrg| …) -> Result`, `run_with_tcx(|tcx, PreFrg| …)`, `expect_fail_compile()`.

### `pdg_test!` (only `tests/pdg.rs`)

Tests the raw PDG construction without going through paralegal's marker/policy machinery. Macro defined locally in `pdg.rs` (not exported). Signature:

```rust
pdg_test!(
    $(#[$attr])* $name,
    { $($items)* },         // crate body; must contain a `fn main`
    $configure_expr,        // optional: |tcx, &mut MemoPdgConstructor| { … }
    $($constraint),*        // zero or more constraints (see DSL below)
);
```

The configure expression is optional — when omitted it defaults to a no-op closure. The constraint list may be empty (e.g. the `opaque_impl*` tests in `pdg.rs`); use that when the assertion is just "analysis completes without panicking". Helpers nearby: `pdg(input, configure, tests)` is the underlying function the macro expands to and is what you call when you need a custom assertion closure rather than DSL constraints. `connects(tcx, body_cache, &g, src, dst, edge)` is the predicate the DSL desugars to.

### `define_flow_test_template!` (cross-crate / on-disk crate tests)

Defined in `crates/plugin/src/test_utils.rs` and exported. Usage pattern (see `cross-crate.rs`):

```rust
lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = paralegal_flow_command(CRATE_DIR)
        .args(["--include", "dependency", "--target", "entry"]).status().unwrap().success();
}
macro_rules! define_test {
    ($name:ident: $ctrl:ident -> $block:block) => {
        paralegal_flow::define_flow_test_template!(
            TEST_CRATE_ANALYZED, CRATE_DIR, $name: $ctrl, $name -> $block);
    };
}
define_test!(basic: graph -> { /* assertions on CtrlRef */ });
```

Each test re-loads the previously-dumped artifact via `PreFrg::from_file_at`. Add `skip "<reason>"` between the name and `:` to `#[ignore]` a test with a mandatory justification.

## CompileBuilder / CompileResult

`paralegal_rustc_utils::test_utils::CompileBuilder` is a thin wrapper around `rustc_driver::run_compiler` that:

- accepts a source string (no on-disk file required — uses an in-memory `FileLoader`),
- generates a random crate name,
- pins the rustc invocation (`-Zidentify-regions -Zmir-opt-level=0 -Zmaximal-hir-to-mir-coverage`, edition 2021, sysroot from `rustc --print sysroot`),
- invokes a callback with `CompileResult { tcx, crate_name }` after expansion, then stops the compilation.

Typical use:

```rust
CompileBuilder::new(source)
    .with_args(EXTRA_RUSTC_ARGS.iter().copied().map(ToOwned::to_owned))
    .with_args(extra_rustc_args)
    .compile(|CompileResult { tcx, .. }| { /* ... */ })?; // -> Result<(), FatalError>
// or `.expect_compile(…)` to unwrap.
```

`InlineTestBuilder` is built on top of this and additionally runs the paralegal `Callbacks` to produce a `PreFrg`. Reach for `CompileBuilder` directly only when you need raw `TyCtxt` access without paralegal's analysis (currently only `pdg.rs` does this).

## Constraint DSL (`pdg_constraint!`)

Defined alongside `pdg_test!` in `crates/plugin/tests/pdg.rs`. Operands are local-variable names from the `main` function in the test body; surrounding parens are stripped, so write `(x -> y)` not `x -> y`.

| Syntax | Meaning |
| --- | --- |
| `(src -> dst)` | there exists a path from `src` to `dst` |
| `(src -/> dst)` | no path from `src` to `dst` |
| `(src -op> dst)` | a path exists, and at least one edge along it is a call to function `op` |
| `(src -op/> dst)` | no path exists that uses an edge calling `op` |

`src` and `dst` are matched against MIR `Place` display strings (i.e. local names debug-info-mapped from the source). Field projections like `(x.0 -> y)` are tokenized but field-sensitive constraints are currently disabled in many tests — check the file for examples before relying on it.

## Idioms

- **Regression test for an analyzer panic that you want to fail today and pass after the fix.** Don't use `#[should_panic]` — it makes the test pass while the bug still exists, hiding regressions if the panic moves. Write the test as a normal test that would pass once fixed (typically `pdg_test!` with zero constraints, or `inline_test!{…}.check_ctrl(|_| {})`), then `#[ignore = "blocked on #NNN"]` it. Remove the `#[ignore]` in the same commit that lands the fix. Ad-hoc convention in this repo, see e.g. the `#[ignore = "Fixme"]` `spawn_and_loop_await` test in `pdg.rs`.
- **Analysis-completes-without-panic, no flow assertions.** Both macros accept zero constraints/empty assertion closures: `pdg_test!(name, { fn main(){} },)` (note the trailing comma after the body — required by the macro arms) or `inline_test!{ fn main(){} }.check_ctrl(|_| {})`.
- **Sharing a heavy `DependencyEnvironment` across tests in a file.** Wrap construction in a `OnceLock` getter (see `async_tests.rs`, `stub-tests.rs`); building a manifest-backed env runs `cargo build` for every dependency.
- **Asserting a compile/analysis failure.** `InlineTestBuilder::…expect_fail_compile()` (see `rejection.rs`).
- **Choosing an entrypoint other than `main`.** `with_entrypoint("crate::path::to::fn")` or for trait impls `"<crate::Type as crate::Trait>::method"` (see `external_resolution_tests.rs`).
- **Common CLI flag pair.** `["--include=crate", "--no-adaptive-approximation"]` — used by most flow tests to keep the analysis target predictable.

## Choosing a framework for a regression test

The "Pick-the-right-helper cheat sheet" above maps test *goals* to helpers; this section is about matching a *bug shape* to a framework. Lesson learned from writing three regressions for one bug class (visibility-filtered field-index miscalculation in `all_visible_fields(...).enumerate()`): each framework has a sweet spot and picking wrong wastes iterations.

- **Bug panics during analysis** → `pdg_test!` with zero constraints — the test passes once the analysis completes. Cheap to write, reads naturally. The constraint DSL is local-name granularity only, so it cannot express precision assertions; don't reach for it when you need one. See `regression_visibility_filter_struct_decomp_oor` in `crates/plugin/tests/pdg.rs`.
- **Bug causes wrong taint flow** (over- or under-tainting) and the affected place can be marker-tagged → `inline_test!` with marker-driven flow assertions (`flows_to_data`, `flows_to(_, _, EdgeSelection::Data)`). More expressive than `pdg_test!` because markers tag specific projections, so field-level flows are distinguishable. See `regression_visibility_filter_use_move_struct_overtaint` in `crates/plugin/tests/marker_tests.rs`.
- **Bug is in a low-level utility** (visitor, projection builder, alias collector) and surfacing it through the full pipeline is hard or noisy → unit test in the utility's own `#[cfg(test)]` module using `Placer` + `compare_sets` (e.g. `Placer::new(tcx, body).local("x").field(N).mk()`). Bypasses the PDG pipeline entirely — fastest feedback loop, but only tests the utility in isolation. See the existing `mod test` in `crates/rustc-utils/src/mir/place.rs`.

Caveats:

- `pdg_test!`'s default callback (`LocalLoadingOnly`) inlines all local fns. If your bug fires only on the call-destination decomposition path (`emit_call_destination_mutation`), force a function to be skipped via a `CallChangeCallbackFn` configure callback — see `regression_visibility_filter_struct_decomp_oor` for the pattern.
- `compile_body` (used by the `place.rs`-style unit tests) picks the **first** `fn` item in the source. Declare `fn main()` first if you want the test to operate on `main`'s body; modules with `pub fn ...` can come after.

## Running tests

`cargo test` from the repo root. Per-binary: `cargo test --test <file_stem>` (e.g. `cargo test --test pdg`). Convenience tasks in `Makefile.toml`:

- `cargo make fast-test` — small representative subset.
- `cargo make cargo-tests` — full `cargo test --no-fail-fast`.
- `cargo make ci-tests` — `cargo-tests` plus the `guide-project` smoke run.

Toolchain: pinned to `nightly-2026-04-20` in `rust-toolchain.toml` with `rustc-dev` and `rust-src` components — required because the test infrastructure links against `rustc_driver` / `rustc_borrowck`. Don't override it.

Environment variables:

- `DUMP_MIR=1` — `pdg.rs` only; dumps MIR for the analyzed body via `MemoPdgConstructor::with_dump_mir`.
- `VIZ=1` — referenced (currently commented out) in `pdg_test!`; previously triggered Graphviz dump of the SPDG to `target/<test>.pdf`.
- `CI=true` — switches `cargo make` to verbose output.
- `RUST_LOG` — standard `tracing-subscriber` filter; `setup_logging()` is called automatically.
