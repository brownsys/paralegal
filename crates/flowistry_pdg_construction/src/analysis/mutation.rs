//! Identifies the mutated places in a MIR instruction via modular approximation based on types.

use flowistry_pdg::{rustc_portable::Place, TargetUse};
use itertools::Itertools;
use log::trace;
use rustc_middle::{
    mir::{self, visit::Visitor, *},
    ty::{self, AdtKind, CoroutineArgsExt, TyKind},
};
use rustc_span::source_map::Spanned;
use rustc_target::abi::FieldIdx;

use rustc_utils::{AdtDefExt, OperandExt, PlaceExt};

use flowistry::mir::{placeinfo::PlaceInfo, utils::AsyncHack};

use crate::{
    constants::{ConstConversionError, PlaceOrConst},
    utils::ty_resolve,
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

/// Information about a particular mutation.
#[derive(Debug)]
pub struct Mutation<'tcx> {
    /// The place that is being mutated.
    pub mutated: Place<'tcx>,

    /// Simplified reason why this mutation occurred.
    pub mutation_reason: TargetUse,

    /// The set of inputs to the mutating operation.
    pub inputs: Vec<(PlaceOrConst<'tcx>, Option<u8>)>,

    #[allow(dead_code)]
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
    time: Time,
}

/// A classification on when this visitor is executed. This is designed to allow
/// splitting of the effect of a function call into the argument unification and
/// the return/mut arg modification.
///
/// [Self::Before] means we are evaluating the state before the call happens, so
/// we are only concerned with mutations if the argument places that read all
/// their reachable values.
///
/// [Self::After] means we are evaluating the state when the call is taking
/// place. That is to say the modification it performs on any reachable mutable
/// places or the return value.
///
/// [Self::Unspecified] mean do both.
///
/// This has no effect on any statements or terminators besides function calls.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Time {
    Unspecified,
    Before,
    After,
}

impl<'a, 'tcx, F> ModularMutationVisitor<'a, 'tcx, F>
where
    F: FnMut(Location, Mutation<'tcx>),
{
    /// Constructs a new visitor.
    pub fn new(place_info: &'a PlaceInfo<'tcx>, f: F) -> Self {
        ModularMutationVisitor {
            place_info,
            f,
            time: Time::Unspecified,
        }
    }

    /// Set when this visitor is executing. See [Time] for more details.
    pub fn set_time(&mut self, time: Time) {
        self.time = time;
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
                                inputs: input
                                    .map(|i| (i.into(), None))
                                    .into_iter()
                                    .collect::<Vec<_>>(),
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
                    TyKind::Coroutine(_, args) => {
                        let ty = args.as_coroutine().prefix_tys();
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
                            inputs: vec![(place.into(), None)],
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
                            inputs: vec![(input_field.into(), None)],
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
                    .refs_in_projection(self.place_info.body, self.place_info.tcx)
                    .map(|(place_ref, _)| (Place::from_ref(place_ref, tcx).into(), None))
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
    fn handle_call_with_combine_on_args(
        &mut self,
        arg_places: Vec<(usize, PlaceOrConst<'tcx>)>,
        location: Location,
        destination: Place<'tcx>,
    ) {
        let arg_place_inputs = arg_places
            .iter()
            .copied()
            .map(|(i, arg)| (arg, Some(i as u8)))
            .collect::<Vec<_>>();

        if matches!(self.time, Time::Unspecified | Time::Before) {
            // Make sure we combine all inputs in the arguments.
            for (_, arg) in arg_places.iter().copied() {
                let PlaceOrConst::Place(arg) = arg else {
                    continue;
                };
                let inputs = self
                    .place_info
                    .reachable_values(arg, Mutability::Not)
                    .iter()
                    .map(|v| (v.into(), None))
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
        }
        if matches!(self.time, Time::Unspecified | Time::After) {
            for (num, arg) in arg_places.iter().copied() {
                let PlaceOrConst::Place(arg) = arg else {
                    continue;
                };
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
}

impl<'tcx, F> Visitor<'tcx> for ModularMutationVisitor<'_, 'tcx, F>
where
    F: FnMut(Location, Mutation<'tcx>),
{
    fn visit_assign(&mut self, mutated: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        trace!("Checking {location:?}: {mutated:?} = {rvalue:?}");

        if self.handle_special_rvalues(mutated, rvalue, location) {
            return;
        }
        let mut collector = PlaceAndConstCollector::new(self.place_info.tcx);
        collector.visit_rvalue(rvalue, location);
        let inputs = collector
            .values
            .into_iter()
            .filter_map(|p| match p {
                Ok(v) => Some((v, None)),
                Err(e) => {
                    self.place_info.tcx.dcx().span_err(
                        self.place_info.body.source_info(location).span,
                        e.to_string(),
                    );
                    None
                }
            })
            .collect();
        (self.f)(
            location,
            Mutation {
                mutated: *mutated,
                mutation_reason: TargetUse::Assign,
                inputs,
                status: MutationStatus::Definitely,
            },
        )
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        trace!("Checking {location:?}: {:?}", terminator.kind);

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
            let mut arg_places = arg_places(self.place_info.tcx, args);
            arg_places.retain(|(_, place)| {
                place
                    .place()
                    .is_none_or(|place| !async_hack.ignore_place(*place))
            });

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

fn arg_places<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
) -> Vec<(usize, PlaceOrConst<'tcx>)> {
    args.iter()
        .enumerate()
        .filter_map(
            |(i, arg)| match PlaceOrConst::try_from_operand(tcx, &arg.node) {
                Ok(place) => Some((i, place)),
                Err(e) => {
                    tcx.dcx().span_err(arg.span, e.to_string());
                    None
                }
            },
        )
        .collect::<Vec<_>>()
}

struct PlaceAndConstCollector<'tcx> {
    values: Vec<Result<PlaceOrConst<'tcx>, ConstConversionError<'tcx>>>,
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> PlaceAndConstCollector<'tcx> {
    fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        Self {
            values: Vec::new(),
            tcx,
        }
    }
}

impl<'tcx> Visitor<'tcx> for PlaceAndConstCollector<'tcx> {
    fn visit_place(&mut self, place: &mir::Place<'tcx>, _: mir::visit::PlaceContext, _: Location) {
        self.values.push(Ok(place.into()));
    }

    fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, _: Location) {
        self.values
            .push(PlaceOrConst::try_from_operand(self.tcx, operand));
    }

    // Should we reflect constants from the type system?
    // fn visit_ty_const(&mut self, const_: ty::Const<'tcx>, _: Location) {
    //     ???
    // }
}
