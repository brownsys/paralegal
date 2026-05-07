use rustc_middle::{
    mir::{self, visit, Operand, Place, Rvalue},
    ty::TyCtxt,
};

#[derive(Clone)]
enum InterpretationState<'tcx> {
    Uninitialized,
    Argument,
    Set(Place<'tcx>),
    Err(String),
}

pub struct SimpleInterpreter<'tcx> {
    tcx: TyCtxt<'tcx>,
    locals: Vec<InterpretationState<'tcx>>,
}

impl<'tcx> SimpleInterpreter<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, num_args: usize, num_locals: usize) -> Self {
        assert!(num_args < num_locals);
        let mut locals = vec![InterpretationState::Uninitialized; num_locals];
        for i in 0..(num_args + 1) {
            locals[i] = InterpretationState::Argument;
        }
        Self { tcx, locals }
    }

    pub fn resolve(&self, place: Place<'tcx>) -> Result<Place<'tcx>, String> {
        match self.locals.get(place.local.as_usize()) {
            Some(InterpretationState::Argument) => Ok(place),
            Some(InterpretationState::Set(p)) => self
                .resolve(*p)
                .map(|p| p.project_deeper(place.projection, self.tcx)),
            Some(InterpretationState::Err(e)) => Err(e.clone()),
            _ => Err(format!("Uninitialized local {place:?}")),
        }
    }

    pub fn interpret_body(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Result<Self, String> {
        let mut interpreter = SimpleInterpreter::new(tcx, body.arg_count, body.local_decls.len());
        use visit::Visitor;
        interpreter.visit_body(body);
        Ok(interpreter)
    }
}

impl<'tcx> visit::Visitor<'tcx> for SimpleInterpreter<'tcx> {
    fn visit_assign(
        &mut self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: mir::Location,
    ) {
        let state = &mut self.locals[place.local.as_usize()];
        match rvalue {
            Rvalue::Use(Operand::Move(place)) | Rvalue::Use(Operand::Copy(place)) => match state {
                InterpretationState::Uninitialized => {
                    *state = InterpretationState::Set(*place);
                }
                InterpretationState::Set(prior) => {
                    *state = InterpretationState::Err(format!("Duplicate assignment to local {place:?} at {location:?}. Previous assignment {prior:?}"));
                }
                _ => (),
            },
            _ => {
                *state = InterpretationState::Err(format!("Unsupported rvalue: {rvalue:?}"));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_abi::FieldIdx;
    use rustc_borrowck::consumers::BodyWithBorrowckFacts;
    use rustc_middle::mir::{self, ProjectionElem};
    use paralegal_rustc_utils::test_utils::CompileBuilder;
    use std::collections::HashMap;

    fn clear_projection_elem<V, T>(e: ProjectionElem<V, T>) -> ProjectionElem<(), ()> {
        match e {
            ProjectionElem::Deref => ProjectionElem::Deref,
            ProjectionElem::Field(f, _) => ProjectionElem::Field(f, ()),
            ProjectionElem::Index(_) => ProjectionElem::Index(()),
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            },
            ProjectionElem::Subslice { from, to, from_end } => {
                ProjectionElem::Subslice { from, to, from_end }
            }
            ProjectionElem::Downcast(ty, variant_index) => {
                ProjectionElem::Downcast(ty, variant_index)
            }
            ProjectionElem::OpaqueCast(..) => ProjectionElem::OpaqueCast(()),
            ProjectionElem::UnwrapUnsafeBinder(_) => ProjectionElem::UnwrapUnsafeBinder(()),
        }
    }

    fn projections_from_string(s: &str) -> Vec<ProjectionElem<(), ()>> {
        s.split_whitespace()
            .map(|s| match s {
                _ if s.starts_with('.') => {
                    ProjectionElem::Field(FieldIdx::from_u32(s[1..].parse().unwrap()), ())
                }
                "*" => ProjectionElem::Deref,
                _ => panic!("Invalid projection element: {s}"),
            })
            .collect()
    }

    struct TestHelper<'tcx> {
        name_map: HashMap<&'tcx str, Place<'tcx>>,
        tcx: TyCtxt<'tcx>,
        body: &'tcx BodyWithBorrowckFacts<'tcx>,
        interpreter: SimpleInterpreter<'tcx>,
    }

    impl<'tcx> TestHelper<'tcx> {
        fn new(tcx: TyCtxt<'tcx>, body: &'tcx BodyWithBorrowckFacts<'tcx>) -> Self {
            let name_map = body
                .body
                .var_debug_info
                .iter()
                .filter_map(|info| {
                    if let mir::VarDebugInfoContents::Place(p) = info.value {
                        Some((info.name.as_str(), p))
                    } else {
                        None
                    }
                })
                .collect::<HashMap<&str, Place>>();
            let interpreter = SimpleInterpreter::interpret_body(tcx, &body.body).unwrap();
            Self {
                tcx,
                body,
                interpreter,
                name_map,
            }
        }

        fn assert_resolves_to(&self, name: &str, base: &str, projections: &str) {
            let start = self.name_map[name];
            let base = self.name_map[base];
            let resolved = self.interpreter.resolve(start).unwrap();
            assert_eq!(resolved.local, base.local);
            assert_eq!(
                resolved
                    .projection
                    .iter()
                    .map(clear_projection_elem)
                    .collect::<Vec<_>>(),
                base.projection
                    .iter()
                    .map(clear_projection_elem)
                    .chain(projections_from_string(projections))
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    #[ignore = "Somehow this can't load MIR bodies???"]
    fn test_simple_interpreter() {
        CompileBuilder::new(stringify! {
            fn foo(x: ((i32, i32), i32)) {
                let y = x.0;
                let z = y.0;
            }
        })
        .compile(|result| {
            let (_, body) = result.as_body();
            let helper = TestHelper::new(result.tcx, body);
            helper.assert_resolves_to("y", "x", ".0");
            helper.assert_resolves_to("z", "x", ".0 .0");
        })
        .unwrap();
    }
}
