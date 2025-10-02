//! These tests check that replacement models work.
//!
//! At the moment it only checks that replacing `std::thread::spawn(f)` being
//! replaced by `f()` and analogous for `tokio::spawn` works.

#![feature(rustc_private)]

#[macro_use]
extern crate lazy_static;

use flowistry_pdg_construction::body_cache::BodyCache;
use paralegal_flow::{
    define_flow_test_template, test_utils::*, utils::resolve::expect_resolve_string_to_def_id,
};
use paralegal_spdg::Identifier;
use rustc_utils::test_utils::CompileBuilder;

extern crate rustc_middle;
use rustc_middle::{mir, ty};
extern crate either;

const TEST_CRATE_NAME: &str = "tests/stub-tests";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump_and(
        TEST_CRATE_NAME,
        ["--include=crate", "--no-adaptive-approximation"]
    );
}

macro_rules! define_test {
    ($($t:tt)*) => {
        define_flow_test_template!(TEST_CRATE_ANALYZED, TEST_CRATE_NAME, $($t)*);
    };
}

fn check_source_pass_target(graph: CtrlRef<'_>) {
    let src = graph.marked(Identifier::new_intern("source"));
    let pass = graph.marked(Identifier::new_intern("pass"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!pass.is_empty());
    assert!(!target.is_empty());

    assert!(src.flows_to_data(&pass));
    assert!(pass.flows_to_data(&target));
}

define_test!(thread_spawn: graph -> {
    check_source_pass_target(graph);
});

define_test!(marked_thread_spawn: graph -> {
    simple_source_target_flow(graph);
});

define_test!(async_spawn: graph -> {
    check_source_pass_target(graph);
});

define_test!(marked_async_spawn: graph -> {
    simple_source_target_flow(graph);
});

define_test!(blocking_with_marker: graph -> {
    simple_source_target_flow(graph);
});

define_test!(marked_blocking_like: graph -> {
    simple_source_target_flow(graph);
});

define_test!(test_blocking_like: graph -> {
    simple_source_target_flow(graph);
});

fn simple_source_target_flow(graph: CtrlRef<'_>) {
    let src = graph.marked(Identifier::new_intern("source"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!target.is_empty());

    assert!(src.flows_to_data(&target));
}

define_test!(block_fn: graph -> {
    simple_source_target_flow(graph)
});

define_test!(test_blocking_with_let_bound_closure: graph -> {
    simple_source_target_flow(graph)
});

define_test!(block_closure: graph -> {
    simple_source_target_flow(graph)
});

define_test!(strategic_overtaint: graph -> {
    simple_source_target_flow(graph)
});

define_test!(strategic_overtaint_2: graph -> {
    simple_source_target_flow(graph)
});

define_test!(no_taint_without_connection: graph -> {

    let src = graph.marked(Identifier::new_intern("source"));
    let target = graph.marked(Identifier::new_intern("target"));

    assert!(!src.is_empty());
    assert!(!target.is_empty());

    assert!(!src.flows_to_data(&target));
});

struct ConstantPrinter<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    context: Option<either::Either<mir::Statement<'tcx>, mir::Terminator<'tcx>>>,
}

impl<'tcx> ConstantPrinter<'tcx> {
    fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        Self { tcx, context: None }
    }
}

impl<'tcx> mir::visit::Visitor<'tcx> for ConstantPrinter<'tcx> {
    fn visit_statement(&mut self, statement: &mir::Statement<'tcx>, location: mir::Location) {
        self.context = Some(either::Left(statement.clone()));
        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: mir::Location) {
        self.context = Some(either::Right(terminator.clone()));
        self.super_terminator(terminator, location);
    }

    fn visit_const_operand(&mut self, constant: &mir::ConstOperand<'tcx>, _: mir::Location) {
        if let Some(context) = self.context.take() {
            match context {
                either::Left(statement) => {
                    println!("In {:?}", statement.kind);
                }
                either::Right(terminator) => {
                    println!("In {:?}", terminator.kind);
                }
            }
        }

        print!("  {constant:?}");

        match constant.const_ {
            mir::Const::Val(ct, ty) => print!(
                " val, converted to {:?}",
                Constant::from_const_value(self.tcx, ty, ct)
            ),
            mir::Const::Unevaluated(..) => print!(" uneval"),
            mir::Const::Ty(_t, v) => {
                print!(" ty");
                match v.kind() {
                    ty::ConstKind::Param(..) => print!(" param"),
                    ty::ConstKind::Value(..) => print!(" value"),
                    ty::ConstKind::Infer(..) => print!(" infer"),
                    ty::ConstKind::Error(..) => print!(" error"),
                    ty::ConstKind::Placeholder(..) => print!(" placeholder"),
                    ty::ConstKind::Unevaluated(..) => print!(" unevaluated"),
                    ty::ConstKind::Expr(..) => print!(" expr"),
                    ty::ConstKind::Bound(..) => print!(" bound"),
                }
            }
        }

        println!();
    }
}

#[derive(Debug)]
enum Constant {
    Int(i64),
    Uint(u64),
    // Placeholder. Floats in the rust compiler are a bit weird so I'll skip them for now.
    Float(f64),
    Bool(bool),
    String(String),
    Unknown(String),
}

impl Constant {
    fn from_const_value<'tcx>(
        tcx: ty::TyCtxt<'tcx>,
        ty: ty::Ty<'tcx>,
        ct: mir::ConstValue<'tcx>,
    ) -> Self {
        // largely from rustc_middle/mir/pretty.rs.html#1952-1962
        match (ct, ty.kind()) {
            (_, ty::Ref(_, inner_ty, _)) if matches!(inner_ty.kind(), ty::Str) => {
                if let Some(data) = ct.try_get_slice_bytes_for_diagnostics(tcx) {
                    return Self::String(String::from_utf8_lossy(data).to_string());
                }
                ()
            }
            (mir::ConstValue::Scalar(mir::interpret::Scalar::Int(int)), tyk) => match tyk {
                ty::Bool => return Self::Bool(int.try_to_bool().unwrap()),
                // Skipping floats for now.
                // ty::Float(fty) => Self::Float(match fty {
                //     ty::FloatTy::F16 => int.to_f16() as f64,
                //     ty::FloatTy::F32 => int.to_f32() as f64,
                //     ty::FloatTy::F64 => int.to_f64() as f64,
                // }),
                ty::Int(ity) => {
                    return Self::Int(match ity {
                        ty::IntTy::I8 => int.to_u8() as i64,
                        ty::IntTy::I16 => int.to_u16() as i64,
                        ty::IntTy::I32 => int.to_u32() as i64,
                        ty::IntTy::I64 => int.to_u64() as i64,
                        ty::IntTy::Isize => int.to_target_isize(tcx) as i64,
                        ty::IntTy::I128 => return Self::Unknown("unsupported i128".to_string()),
                    })
                }
                ty::Uint(uty) => {
                    return Self::Uint(match uty {
                        ty::UintTy::U8 => int.to_u8() as u64,
                        ty::UintTy::U16 => int.to_u16() as u64,
                        ty::UintTy::U32 => int.to_u32() as u64,
                        ty::UintTy::U64 => int.to_u64() as u64,
                        ty::UintTy::Usize => int.to_target_usize(tcx) as u64,
                        ty::UintTy::U128 => return Self::Unknown("unsupported u128".to_string()),
                    })
                }
                _ => (),
            },
            _ => (),
        }
        Self::Unknown(mir::Const::Val(ct, ty).to_string())
    }
}

#[test]
fn print_constants() {
    CompileBuilder::new(stringify! {
        fn main() {
            let c1 = 1;
            let c2 = 2_usize;
            let c3 = "str";
        }
    })
    .compile(|res| {
        use flowistry::mir::FlowistryInput;
        use mir::visit::Visitor;

        let body_cache = BodyCache::new(res.tcx);
        let def_id = expect_resolve_string_to_def_id(res.tcx, "crate::main", false).unwrap();

        let body = body_cache.get(def_id);

        let mut vis = ConstantPrinter::new(res.tcx);
        vis.visit_body(body.body());
    })
    .unwrap()
}
