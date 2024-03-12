//! Identifies the mutated places in a MIR instruction via modular approximation based on types.

use log::debug;
use rustc_middle::{
    mir::{visit::Visitor, *},
    ty::{AdtKind, TyKind},
};
use rustc_target::abi::FieldIdx;
use rustc_utils::{mir::place::PlaceCollector, AdtDefExt, OperandExt, PlaceExt};

use flowistry::mir::{
    placeinfo::PlaceInfo,
    utils::{self, AsyncHack},
};

/// Indicator of certainty about whether a place is being mutated.
/// Used to determine whether an update should be strong or weak.
#[derive(Debug)]
pub enum MutationStatus {
    /// A place is definitely mutated, e.g. `x = y` definitely mutates `x`.
    Definitely,

    /// A place is possibly mutated, e.g. `f(&mut x)` possibly mutates `x`.
    Possibly,
}

/// Why did this mutation occur
#[derive(Debug)]
pub enum MutationReason {
    /// It was a function argument
    MutArgument(u8),
    /// It was target of an assign (via return or regular assign)
    AssignTarget,
}

/// Information about a particular mutation.
#[derive(Debug)]
pub struct Mutation<'tcx> {
    /// The place that is being mutated.
    pub mutated: Place<'tcx>,

    /// Simplified reason why this mutation occurred.
    pub mutation_reason: MutationReason,

    /// For function calls contains the argument index this dependency came from
    pub operand_index: Option<u8>,

    /// The set of inputs to the mutating operation.
    pub inputs: Vec<Place<'tcx>>,

    /// The certainty of whether the mutation is happening.
    pub status: MutationStatus,
}

/// MIR visitor that invokes a callback for every [`Mutation`] in the visited object.
///
/// Construct the visitor with [`ModularMutationVisitor::new`], then call one of the
/// MIR [`Visitor`] methods.
pub struct ModularMutationVisitor<'a, 'tcx, F>
where
    F: FnMut(Location, Mutation<'tcx>),
{
    f: F,
    place_info: &'a PlaceInfo<'tcx>,
}

impl<'a, 'tcx, F> ModularMutationVisitor<'a, 'tcx, F>
where
    F: FnMut(Location, Mutation<'tcx>),
{
    /// Constructs a new visitor.
    pub fn new(place_info: &'a PlaceInfo<'tcx>, f: F) -> Self {
        ModularMutationVisitor { place_info, f }
    }

    fn handle_special_rvalues(
        &mut self,
        mutated: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) -> bool {
        let body = self.place_info.body;
        let tcx = self.place_info.tcx;

        match rvalue {
            // In the case of _1 = aggregate { field1: op1, field2: op2, ... },
            // then destructure this into a series of mutations like
            // _1.field1 = op1, _1.field2 = op2, and so on.
            Rvalue::Aggregate(agg_kind, ops) => {
                let (mutated, tys) = match &**agg_kind {
                    AggregateKind::Adt(def_id, idx, substs, _, _) => {
                        let adt_def = tcx.adt_def(*def_id);
                        let variant = adt_def.variant(*idx);
                        let mutated = match adt_def.adt_kind() {
                            AdtKind::Enum => mutated.project_deeper(
                                &[ProjectionElem::Downcast(Some(variant.name), *idx)],
                                tcx,
                            ),
                            AdtKind::Struct | AdtKind::Union => *mutated,
                        };
                        let fields = variant.fields.iter();
                        let tys = fields
                            .map(|field| field.ty(tcx, substs))
                            .collect::<Vec<_>>();
                        (mutated, tys)
                    }
                    AggregateKind::Tuple => {
                        let ty = rvalue.ty(body.local_decls(), tcx);
                        (*mutated, ty.tuple_fields().to_vec())
                    }
                    AggregateKind::Closure(_, args) => {
                        let ty = args.as_closure().upvar_tys();
                        (*mutated, ty.to_vec())
                    }
                    _ => return false,
                };

                if tys.is_empty() {
                    return false;
                }
                let fields =
                    tys.into_iter()
                        .enumerate()
                        .zip(ops.iter())
                        .map(|((i, ty), input_op)| {
                            let field = PlaceElem::Field(FieldIdx::from_usize(i), ty);
                            let input_place = input_op.as_place();
                            (mutated.project_deeper(&[field], tcx), input_place)
                        });

                for (mutated, input) in fields {
                    (self.f)(
                        location,
                        Mutation {
                            mutated,
                            mutation_reason: MutationReason::AssignTarget,
                            inputs: input.into_iter().collect::<Vec<_>>(),
                            status: MutationStatus::Definitely,
                            operand_index: None,
                        },
                    )
                }
                true
            }

            // In the case of _1 = _2 where _2 : struct Foo { x: T, y: S, .. },
            // then destructure this into a series of mutations like
            // _1.x = _2.x, _1.y = _2.y, and so on.
            Rvalue::Use(Operand::Move(place) | Operand::Copy(place)) => {
                let place_ty = place.ty(&body.local_decls, tcx).ty;
                let TyKind::Adt(adt_def, substs) = place_ty.kind() else {
                    return false;
                };
                if !adt_def.is_struct() {
                    return false;
                };
                let mut fields = adt_def
                    .all_visible_fields(self.place_info.def_id, self.place_info.tcx)
                    .enumerate()
                    .map(|(i, field_def)| {
                        PlaceElem::Field(FieldIdx::from_usize(i), field_def.ty(tcx, substs))
                    })
                    .peekable();
                if fields.peek().is_none() {
                    (self.f)(
                        location,
                        Mutation {
                            mutated: *mutated,
                            mutation_reason: MutationReason::AssignTarget,
                            inputs: vec![*place],
                            status: MutationStatus::Definitely,
                            operand_index: None,
                        },
                    )
                }
                for field in fields {
                    let mutated_field = mutated.project_deeper(&[field], tcx);
                    let input_field = place.project_deeper(&[field], tcx);
                    (self.f)(
                        location,
                        Mutation {
                            mutated: mutated_field,
                            mutation_reason: MutationReason::AssignTarget,
                            inputs: vec![input_field],
                            status: MutationStatus::Definitely,
                            operand_index: None,
                        },
                    )
                }

                true
            }

            // The actual value of the referred place doesn't affect the value of the
            // reference, except for the provenance of reborrows.
            Rvalue::Ref(_, _, place) => {
                let inputs = place
                    .refs_in_projection()
                    .map(|(place_ref, _)| Place::from_ref(place_ref, tcx))
                    .collect::<Vec<_>>();
                (self.f)(
                    location,
                    Mutation {
                        mutated: *mutated,
                        mutation_reason: MutationReason::AssignTarget,
                        inputs,
                        operand_index: None,
                        status: MutationStatus::Definitely,
                    },
                );
                true
            }

            _ => false,
        }
    }
}

impl<'tcx, F> Visitor<'tcx> for ModularMutationVisitor<'_, 'tcx, F>
where
    F: FnMut(Location, Mutation<'tcx>),
{
    fn visit_assign(&mut self, mutated: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        debug!("Checking {location:?}: {mutated:?} = {rvalue:?}");

        if !self.handle_special_rvalues(mutated, rvalue, location) {
            let mut collector = PlaceCollector::default();
            collector.visit_rvalue(rvalue, location);
            (self.f)(
                location,
                Mutation {
                    mutated: *mutated,
                    mutation_reason: MutationReason::AssignTarget,
                    inputs: collector.0,
                    operand_index: None,
                    status: MutationStatus::Definitely,
                },
            );
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        debug!("Checking {location:?}: {:?}", terminator.kind);
        let tcx = self.place_info.tcx;

        match &terminator.kind {
            TerminatorKind::Call {
                /*func,*/ // TODO: deal with func
                args,
                destination,
                ..
            } => {
                let async_hack = AsyncHack::new(
                    self.place_info.tcx,
                    self.place_info.body,
                    self.place_info.def_id,
                );
                let mut arg_places = utils::arg_places(args);
                arg_places.retain(|(_, place)| !async_hack.ignore_place(*place));

                let ret_is_unit = destination
                    .ty(self.place_info.body.local_decls(), tcx)
                    .ty
                    .is_unit();
                let dest_inputs = if ret_is_unit {
                    Vec::new()
                } else {
                    arg_places.clone()
                };

                for (num, place) in arg_places.iter() {
                    (self.f)(
                        location,
                        Mutation {
                            mutated: *destination,
                            inputs: vec![*place],
                            operand_index: Some(*num as u8),
                            mutation_reason: MutationReason::AssignTarget,
                            status: MutationStatus::Definitely,
                        },
                    );
                }

                for (num, arg) in arg_places.iter().copied() {
                    let inputs = self
                        .place_info
                        .reachable_values(arg, Mutability::Not)
                        .into_iter()
                        .copied()
                        .collect();
                    (self.f)(
                        location,
                        Mutation {
                            mutated: arg,
                            mutation_reason: MutationReason::AssignTarget,
                            inputs,
                            operand_index: Some(num as u8),
                            status: MutationStatus::Definitely,
                        },
                    );
                    for arg_mut in self.place_info.reachable_values(arg, Mutability::Mut) {
                        if *arg_mut == arg {
                            continue;
                        }
                        (self.f)(
                            location,
                            Mutation {
                                mutated: *arg_mut,
                                mutation_reason: MutationReason::MutArgument(num as u8),
                                operand_index: None,
                                inputs: arg_places.iter().copied().map(|(_, arg)| arg).collect(),
                                status: MutationStatus::Possibly,
                            },
                        );
                    }
                }
            }

            _ => {}
        }
    }
}
