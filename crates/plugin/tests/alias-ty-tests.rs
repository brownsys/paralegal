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
