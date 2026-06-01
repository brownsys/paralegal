//! Reproducers for the unhandled `TyKind::Alias` cases that surface as
//! `unimplemented Alias(..)` warnings from
//! `paralegal_rustc_utils::mir::place::visit_ty` (place.rs:584) and
//! `paralegal_flow::analysis::pdg::local::is_split` (local/mod.rs:985) when
//! analyzing `mcp-servers/developer`.
//!
//! Three shapes are covered:
//! - `Alias(Opaque, ..)` from an `async fn` method. Matches the developer
//!   warnings of the form `..::{impl#N}::<method>::{opaque#0}`.
//! - `Alias(Projection, ..)` whose Self is a foreign unsized type (`str`),
//!   reached via an ADT field declared as `<str as Owns>::Owned`. Mirrors
//!   the `<str as ToOwned>::Owned` warnings in developer.
//! - `Alias(Projection, ..)` whose Self is the local crate's own ADT,
//!   reached via a parameterized wrapper struct that monomorphizes to a
//!   field of type `<IntProducer as Producer>::Output`.
//!
//! In both projection cases the projection survives the visitor reaching it
//! because `FieldDef::ty(tcx, subst)` only substitutes generic args — it does
//! not normalize projections — so the recursive `visit_ty` lands on the
//! `Alias(Projection, ..)` shape that has no match arm.
//!
//! Each test asserts only that the marked source flows to the marked sink so
//! the assertion does not couple to PDG details that may evolve.

#![feature(rustc_private)]

use paralegal_flow::inline_test;
use paralegal_flow::test_utils::*;

#[test]
fn opaque_alias_from_async_method() {
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn make_secret() -> i64 { 42 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn consume_secret(_: i64) {}

        struct Worker;
        impl Worker {
            async fn forward(&self, x: i64) -> i64 { x }
        }

        async fn main() {
            let w = Worker;
            let s = make_secret();
            let s2 = w.forward(s).await;
            consume_secret(s2);
        }
    }
    .check_ctrl(|graph| {
        let src_fn = graph.function("make_secret");
        let snk_fn = graph.function("consume_secret");
        let src = graph.call_site(&src_fn);
        let snk = graph.call_site(&snk_fn);
        assert!(src.output().flows_to_data(&snk.input()));
    });
}

#[test]
fn projection_alias_from_concrete_assoc_field() {
    // `Wrapper<str>` has a field declared as `<B as Owns>::Owned`. When the
    // visitor walks the local's ADT, it asks `FieldDef::ty(tcx, [str])` for the
    // field's type, which substitutes `B := str` without normalizing — so the
    // recursive `visit_ty` sees `Alias(Projection { .. ToOwned-style assoc .. })`
    // with concrete `args: [str]` and falls into the catch-all warn arm.
    inline_test! {
        trait Owns {
            type Owned;
        }
        impl Owns for str {
            type Owned = String;
        }

        struct Wrapper<B: ?Sized + Owns> {
            val: <B as Owns>::Owned,
            _marker: core::marker::PhantomData<*const B>,
        }

        #[paralegal_flow::marker(source, return)]
        fn make_secret() -> String { String::from("s") }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn consume_secret(_: String) {}

        fn main() {
            let s = make_secret();
            let w: Wrapper<str> = Wrapper { val: s, _marker: core::marker::PhantomData };
            let s2: String = w.val;
            consume_secret(s2);
        }
    }
    .check_ctrl(|graph| {
        let src_fn = graph.function("make_secret");
        let snk_fn = graph.function("consume_secret");
        let src = graph.call_site(&src_fn);
        let snk = graph.call_site(&snk_fn);
        assert!(src.output().flows_to_data(&snk.input()));
    });
}

#[test]
fn projection_alias_from_generic_assoc_field() {
    // `Wrapped<P>`'s field is declared as `<P as Producer>::Output`. After
    // monomorphization at the call from `main`, the locals end up holding
    // `Wrapped<IntProducer>`, whose field type substitutes to
    // `<IntProducer as Producer>::Output` (Self is the local crate's own
    // ADT, not a foreign primitive like in the other projection test).
    inline_test! {
        trait Producer {
            type Output;
            fn produce(self) -> Self::Output;
        }

        struct IntProducer(i64);
        impl Producer for IntProducer {
            type Output = i64;
            fn produce(self) -> Self::Output { self.0 }
        }

        struct Wrapped<P: Producer> {
            val: <P as Producer>::Output,
        }

        fn wrap<P: Producer>(p: P) -> Wrapped<P> {
            Wrapped { val: p.produce() }
        }

        fn unwrap<P: Producer>(w: Wrapped<P>) -> <P as Producer>::Output {
            w.val
        }

        #[paralegal_flow::marker(source, return)]
        fn make_secret() -> i64 { 42 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn consume_secret(_: i64) {}

        fn main() {
            let s = make_secret();
            let p = IntProducer(s);
            let w = wrap(p);
            let r = unwrap(w);
            consume_secret(r);
        }
    }
    .check_ctrl(|graph| {
        let src_fn = graph.function("make_secret");
        let snk_fn = graph.function("consume_secret");
        let src = graph.call_site(&src_fn);
        let snk = graph.call_site(&snk_fn);
        assert!(src.output().flows_to_data(&snk.input()));
    });
}

// Stress tests for the `try_normalize_alias` path: each case targets a
// specific invariant the substitution depends on. Each test verifies that
// the analyzer doesn't panic and that the source-to-sink flow survives.

#[test]
fn gat_projection_with_late_bound_region() {
    // Invariant: `EarlyBinder::bind` rejects late-bound regions; we erase
    // before binding. A GAT projection `<C as Container>::Item<'_>` is the
    // canonical way to make late-bound regions surface in an `Alias` ty.
    // If `erase_and_anonymize_regions` doesn't cover late-bound regions
    // synthesized by the GAT, the binder would panic the way it did for
    // the `purity::misc::side_effect_tcp` ReVar case.
    inline_test! {
        trait Container {
            type Item<'a> where Self: 'a;
            fn first<'a>(&'a self) -> Self::Item<'a>;
        }

        struct Holder(i64);
        impl Container for Holder {
            type Item<'a> = &'a i64;
            fn first<'a>(&'a self) -> Self::Item<'a> { &self.0 }
        }

        struct Wrapped<C: Container> {
            // Field type is `<C as Container>::Item<'static>` — a GAT
            // projection with a late-bound region argument.
            val: <C as Container>::Item<'static>,
        }

        #[paralegal_flow::marker(source, return)]
        fn make_secret() -> &'static i64 { &42 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn consume_secret(_: &i64) {}

        fn main() {
            let s = make_secret();
            let w: Wrapped<Holder> = Wrapped { val: s };
            consume_secret(w.val);
        }
    }
    .check_ctrl(|graph| {
        let src_fn = graph.function("make_secret");
        let snk_fn = graph.function("consume_secret");
        let src = graph.call_site(&src_fn);
        let snk = graph.call_site(&snk_fn);
        assert!(src.output().flows_to_data(&snk.input()));
    });
}

#[test]
fn opaque_alias_resolves_to_coroutine_carrying_reference() {
    // Invariant: when an Opaque is normalized, the result is a Coroutine
    // (the `async fn` state machine), which the visitor has a dedicated
    // arm for. The Future's `Output` here is a reference, so the upvar
    // tuple ends up carrying a `&i64`. After normalization erases regions
    // the inner `&i64` has `ReErased`, which `visit_region` returns
    // early on — verifying that this doesn't crash or produce spurious
    // region edges.
    inline_test! {
        #[paralegal_flow::marker(source, return)]
        fn make_secret() -> &'static i64 { &42 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn consume_secret(_: &i64) {}

        struct Server;
        impl Server {
            async fn forward<'a>(&self, x: &'a i64) -> &'a i64 { x }
        }

        async fn main() {
            let s = Server;
            let secret = make_secret();
            let r = s.forward(secret).await;
            consume_secret(r);
        }
    }
    .check_ctrl(|graph| {
        let src_fn = graph.function("make_secret");
        let snk_fn = graph.function("consume_secret");
        let src = graph.call_site(&src_fn);
        let snk = graph.call_site(&snk_fn);
        assert!(src.output().flows_to_data(&snk.input()));
    });
}

#[test]
fn polymorphic_helper_carries_caller_args_through_walk() {
    // Invariant: at recursive call sites, the analyzer reaches the callee
    // via `LocalAnalysis::new(memo, root: Instance, ...)`. `root.args`
    // is what we thread into the walk. If those args ever carried
    // body-local `ReVar` (the user's specific worry) and that leaked into
    // the descended types, we'd see spurious region edges in the alias
    // map. This test calls a polymorphic helper twice from `main` with
    // different generic args; the helper's body contains a projection
    // field. A leak would conflate the two call sites' aliases.
    inline_test! {
        trait Producer {
            type Output;
            fn produce(self) -> Self::Output;
        }

        struct IntProducer(i64);
        impl Producer for IntProducer {
            type Output = i64;
            fn produce(self) -> Self::Output { self.0 }
        }

        struct OtherProducer(u32);
        impl Producer for OtherProducer {
            type Output = u32;
            fn produce(self) -> Self::Output { self.0 }
        }

        struct Wrapped<P: Producer> {
            val: <P as Producer>::Output,
        }

        fn wrap<P: Producer>(p: P) -> Wrapped<P> {
            Wrapped { val: p.produce() }
        }

        #[paralegal_flow::marker(source, return)]
        fn make_secret() -> i64 { 42 }

        #[paralegal_flow::marker(sink, arguments = [0])]
        fn consume_secret(_: i64) {}

        fn make_noise() -> u32 { 99 }

        fn main() {
            let s = make_secret();
            // First call: `wrap::<IntProducer>` — Wrapped<IntProducer>'s
            // field projects to <IntProducer as Producer>::Output.
            let w = wrap(IntProducer(s));
            // Second call: `wrap::<OtherProducer>` with different generic
            // args. Distinct projection target.
            let _noise = wrap(OtherProducer(make_noise()));
            consume_secret(w.val);
        }
    }
    .check_ctrl(|graph| {
        let src_fn = graph.function("make_secret");
        let snk_fn = graph.function("consume_secret");
        let src = graph.call_site(&src_fn);
        let snk = graph.call_site(&snk_fn);
        assert!(src.output().flows_to_data(&snk.input()));
        // The noise source must NOT flow to the secret sink. If args from
        // one wrap-instance leaked into the walk of the other, the alias
        // analysis would conflate them and the assertion above could still
        // pass spuriously while this one fires.
        let noise_fn = graph.function("make_noise");
        let noise = graph.call_site(&noise_fn);
        assert!(!noise.output().flows_to_data(&snk.input()));
    });
}
