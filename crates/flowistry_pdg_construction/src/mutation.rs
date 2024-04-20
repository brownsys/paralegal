//! Identifies the mutated places in a MIR instruction via modular approximation based on types.

use flowistry_pdg::{rustc_portable::Place, TargetUse};
use itertools::Itertools;
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

use crate::utils::ty_resolve;

/// Indicator of certainty about whether a place is being mutated.
/// Used to determine whether an update should be strong or weak.
#[derive(Debug)]
pub enum MutationStatus {
    /// A place is definitely mutated, e.g. `x = y` definitely mutates `x`.
    Definitely,

    /// A place is possibly mutated, e.g. `f(&mut x)` possibly mutates `x`.
    Possibly,
}

/// Information about a particular mutation.
#[derive(Debug)]
pub struct Mutation<'tcx> {
    /// The place that is being mutated.
    pub mutated: Place<'tcx>,

    /// Simplified reason why this mutation occurred.
    pub mutation_reason: TargetUse,

    /// The set of inputs to the mutating operation.
    pub inputs: Vec<(Place<'tcx>, Option<u8>)>,

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
                    match input {
                        // If we have an aggregate of aggregates, then recursively destructure sub-aggregates
                        Some(input_place) => self.visit_assign(
                            &mutated,
                            &Rvalue::Use(Operand::Move(input_place)),
                            location,
                        ),
                        // Otherwise, just record the mutation.
                        None => (self.f)(
                            location,
                            Mutation {
                                mutated,
                                mutation_reason: TargetUse::Assign,
                                inputs: input.map(|i| (i, None)).into_iter().collect::<Vec<_>>(),
                                status: MutationStatus::Definitely,
                            },
                        ),
                    }
                }
                true
            }

            // In the case of _1 = _2 where _2 : struct Foo { x: T, y: S, .. },
            // then destructure this into a series of mutations like
            // _1.x = _2.x, _1.y = _2.y, and so on.
            Rvalue::Use(Operand::Move(place) | Operand::Copy(place)) => {
                let place_ty = ty_resolve(place.ty(&body.local_decls, tcx).ty, tcx);
                let fields = match place_ty.kind() {
                    TyKind::Adt(adt_def, substs) => {
                        if !adt_def.is_struct() {
                            return false;
                        };
                        adt_def
                            .all_visible_fields(self.place_info.def_id, self.place_info.tcx)
                            .enumerate()
                            .map(|(i, field_def)| {
                                PlaceElem::Field(FieldIdx::from_usize(i), field_def.ty(tcx, substs))
                            })
                            .collect_vec()
                    }
                    TyKind::Generator(_, args, _) => {
                        let ty = args.as_generator().prefix_tys();
                        ty.iter()
                            .enumerate()
                            .map(|(i, ty)| PlaceElem::Field(FieldIdx::from_usize(i), ty))
                            .collect_vec()
                    }

                    _ty => return false,
                };
                if fields.is_empty() {
                    (self.f)(
                        location,
                        Mutation {
                            mutated: *mutated,
                            mutation_reason: TargetUse::Assign,
                            inputs: vec![(*place, None)],
                            status: MutationStatus::Definitely,
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
                            mutation_reason: TargetUse::Assign,
                            inputs: vec![(input_field, None)],
                            status: MutationStatus::Definitely,
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
                    .map(|(place_ref, _)| (Place::from_ref(place_ref, tcx), None))
                    .collect::<Vec<_>>();
                (self.f)(
                    location,
                    Mutation {
                        mutated: *mutated,
                        mutation_reason: TargetUse::Assign,
                        inputs,
                        status: MutationStatus::Definitely,
                    },
                );
                true
            }

            _ => false,
        }
    }

    #[allow(dead_code)]
    fn handle_call_with_combine_on_return(
        &mut self,
        arg_places: Vec<(usize, Place<'tcx>)>,
        location: Location,
        destination: Place<'tcx>,
    ) {
        // Make sure we combine all inputs in the arguments.
        let inputs = arg_places
            .iter()
            .copied()
            .flat_map(|(num, arg)| {
                self.place_info
                    .reachable_values(arg, Mutability::Not)
                    .iter()
                    .map(move |v| (*v, Some(num as u8)))
            })
            .collect::<Vec<_>>();

        for (num, arg) in arg_places.iter().copied() {
            for arg_mut in self.place_info.reachable_values(arg, Mutability::Mut) {
                if *arg_mut != arg {
                    (self.f)(
                        location,
                        Mutation {
                            mutated: *arg_mut,
                            mutation_reason: TargetUse::MutArg(num as u8),
                            inputs: inputs.clone(),
                            status: MutationStatus::Possibly,
                        },
                    )
                }
            }
        }

        (self.f)(
            location,
            Mutation {
                mutated: destination,
                inputs,
                mutation_reason: TargetUse::Return,
                status: MutationStatus::Definitely,
            },
        );
    }

    #[allow(dead_code)]
    fn handle_call_with_combine_on_args(
        &mut self,
        arg_places: Vec<(usize, Place<'tcx>)>,
        location: Location,
        destination: Place<'tcx>,
    ) {
        let arg_place_inputs = arg_places
            .iter()
            .copied()
            .map(|(i, arg)| (arg, Some(i as u8)))
            .collect::<Vec<_>>();
        // Make sure we combine all inputs in the arguments.
        for (_, arg) in arg_places.iter().copied() {
            let inputs = self
                .place_info
                .reachable_values(arg, Mutability::Not)
                .iter()
                .map(|v| (*v, None))
                .collect();
            (self.f)(
                location,
                Mutation {
                    mutated: arg,
                    mutation_reason: TargetUse::Assign,
                    inputs,
                    status: MutationStatus::Definitely,
                },
            );
        }

        for (num, arg) in arg_places.iter().copied() {
            for arg_mut in self.place_info.reachable_values(arg, Mutability::Mut) {
                if *arg_mut != arg {
                    (self.f)(
                        location,
                        Mutation {
                            mutated: *arg_mut,
                            mutation_reason: TargetUse::MutArg(num as u8),
                            inputs: arg_place_inputs.clone(),
                            status: MutationStatus::Possibly,
                        },
                    )
                }
            }
        }
        (self.f)(
            location,
            Mutation {
                mutated: destination,
                inputs: arg_place_inputs,
                mutation_reason: TargetUse::Return,
                status: MutationStatus::Definitely,
            },
        );
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
                    mutation_reason: TargetUse::Assign,
                    inputs: collector.0.into_iter().map(|p| (p, None)).collect(),
                    status: MutationStatus::Definitely,
                },
            )
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        debug!("Checking {location:?}: {:?}", terminator.kind);

        if let TerminatorKind::Call {
            /*func,*/ // TODO: deal with func
            args,
            destination,
            ..
        } = &terminator.kind
        {
            let async_hack = AsyncHack::new(
                self.place_info.tcx,
                self.place_info.body,
                self.place_info.def_id,
            );
            let mut arg_places = utils::arg_places(args);
            arg_places.retain(|(_, place)| !async_hack.ignore_place(*place));

            // let ret_is_unit = destination
            //     .ty(self.place_info.body.local_decls(), tcx)
            //     .ty
            //     .is_unit();

            // The PDG construction relies on the fact that mutations are
            // executed "in-order". This means we must first mutate the
            // argument places and then the return and mutable arguments.
            //
            // TODO: What happens if these argument places overlap?
            self.handle_call_with_combine_on_args(arg_places, location, *destination)
        }
    }
}
