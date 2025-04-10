use std::borrow::Cow;

use flowistry_pdg::rustc_portable::DefId;
use log::trace;
use rustc_abi::FieldIdx;

use rustc_middle::{
    mir::{Body, HasLocalDecls, Operand, Place, PlaceElem, RETURN_PLACE},
    ty::TyCtxt,
};

use crate::{
    async_support::AsyncInfo,
    local_analysis::CallKind,
    utils::{self, ShimType},
};

/// Describes how the formal parameters of a given function call relate to the
/// actual parameters.
#[derive(Debug, strum::AsRefStr)]
pub enum CallingConvention<'tcx> {
    /// 1 to 1 mapping
    Direct(Box<[Operand<'tcx>]>),
    /// First argument is the closed-over environment. Second argument is a
    /// tuple that contains the actual argument to the call of the closure
    /// function.
    Indirect {
        shim: Option<ShimType>,
        closure_arg: Operand<'tcx>,
        tupled_arguments: Operand<'tcx>,
    },
    /// An async generator. Only has one argument, which is the generator state.
    Async(Place<'tcx>),
}

/// The result of calculating a translation from a child place (in a called
/// function) to a parent place (in the caller).
///
/// This is partially translated and thus allows us to either complete the
/// translation to a precise parent place ([`Self::make_translated_place`]),
/// e.g. one that corresponds to the child 1-1, or to just use the parent place,
/// for strategic overtaint, e.g. discarding the child projections
/// ([`Self::base_place`]).
pub struct PlaceTranslation<'a, 'tcx> {
    new_base: Place<'tcx>,
    additional_projection: &'tcx [PlaceElem<'tcx>],
    scope: &'a PlaceTranslator<'a, 'tcx>,
}

impl<'a, 'tcx> PlaceTranslation<'a, 'tcx> {
    /// Complete the translation and return a precise parent place.
    pub fn make_translated_place(&self) -> Place<'tcx> {
        let base_place_projected = self
            .new_base
            .project_deeper(self.additional_projection, self.scope.tcx);
        trace!("  ⮑ Translated to: {base_place_projected:?}");
        utils::retype_place(
            base_place_projected,
            self.scope.tcx,
            self.scope.parent_body,
            self.scope.parent_body_def_id,
        )
    }

    /// Return the base version of the parent place with no child projections applied.
    pub fn base_place(&self) -> Place<'tcx> {
        self.new_base
    }
}

impl<'tcx> CallingConvention<'tcx> {
    pub fn from_call_kind(
        kind: &CallKind<'tcx>,
        args: Cow<'_, [Operand<'tcx>]>,
    ) -> CallingConvention<'tcx> {
        match kind {
            CallKind::AsyncPoll(poll) => CallingConvention::Async(poll.generator_data),
            CallKind::Direct => CallingConvention::Direct(args.into()),
            CallKind::Indirect { shim: once_shim } => CallingConvention::Indirect {
                shim: *once_shim,
                closure_arg: args[0].clone(),
                tupled_arguments: args[1].clone(),
            },
        }
    }
}

/// This struct represents all the information necessary to translate places
/// from a child (the callee) to its parent (caller) at the boundary of a
/// particular function call.
pub struct PlaceTranslator<'a, 'tcx> {
    async_info: &'a AsyncInfo,
    parent_body_def_id: DefId,
    parent_body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    destination: Place<'tcx>,
    calling_convention: &'a CallingConvention<'tcx>,
    /// Governs whether the translation produces precise results (1-1
    /// child-parent translations) or approximate one's (discarding child
    /// projections).
    precise: bool,
}

impl<'a, 'tcx> PlaceTranslator<'a, 'tcx> {
    /// `destination` must be the place to which the return is assigned in the
    /// parent (caller).
    ///
    /// The `precise` parameter governs whether the translation produces precise
    /// results (1-1 child-parent translations) or approximate one's (discarding
    /// child projections).
    pub(crate) fn new(
        async_info: &'a AsyncInfo,
        parent_body_def_id: DefId,
        parent_body: &'a Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        destination: Place<'tcx>,
        calling_convention: &'a CallingConvention<'tcx>,
        precise: bool,
    ) -> Self {
        Self {
            async_info,
            parent_body,
            parent_body_def_id,
            tcx,
            destination,
            calling_convention,
            precise,
        }
    }

    /// Returns a fully translated parent place. If `self.precise == true` this
    /// place will be a precise 1-1 translation, otherwise just the base parent
    /// place.
    ///
    /// Returns `None` if the input child cannot be represented in the parent.
    pub(crate) fn translate_to_parent(&self, child: Place<'tcx>) -> Option<Place<'tcx>> {
        let translation = self.handle_translate(child)?;
        Some(if self.precise {
            translation.make_translated_place()
        } else {
            translation.base_place()
        })
    }

    /// Returns a calculated translation that needs to be finished.
    ///
    /// Returns `None` if the input child cannot be represented in the parent.
    pub(crate) fn handle_translate<'b>(
        &'b self,
        child: Place<'tcx>,
    ) -> Option<PlaceTranslation<'b, 'tcx>> {
        let (new_base, additional_projection) = match self.calling_convention {
            // Async return must be handled special, because it gets wrapped in `Poll::Ready`
            CallingConvention::Async { .. } if child.local == RETURN_PLACE => {
                let in_poll = self.destination.project_deeper(
                    &[PlaceElem::Downcast(
                        None,
                        self.async_info.poll_ready_variant_idx,
                    )],
                    self.tcx,
                );
                let field_idx = self.async_info.poll_ready_field_idx;
                let child_inner_return_type = in_poll
                    .ty(self.parent_body.local_decls(), self.tcx)
                    .field_ty(self.tcx, field_idx);
                (
                    in_poll.project_deeper(
                        &[PlaceElem::Field(field_idx, child_inner_return_type)],
                        self.tcx,
                    ),
                    &child.projection[..],
                )
            }
            _ if child.local == RETURN_PLACE => (self.destination, &child.projection[..]),
            // Map arguments to the argument array
            CallingConvention::Direct(args) => (
                args[child.local.as_usize() - 1].place()?,
                &child.projection[..],
            ),
            // Map arguments to projections of the future, the poll's first argument
            CallingConvention::Async(ctx) => {
                if child.local.as_usize() == 1 {
                    (*ctx, &child.projection[..])
                } else {
                    return None;
                }
            }
            // Map closure captures to the first argument.
            // Map formal parameters to the second argument.
            CallingConvention::Indirect {
                shim,
                closure_arg,
                tupled_arguments,
            } => {
                // Accounting for FnPtrShim
                //
                // The shim gets an extra first argument (the function pointer)
                // but we replace it with the function iself which doesn't have
                // that argument, so we need to adjust the indices
                let local = if matches!(shim, Some(ShimType::FnPtr)) && child.local != RETURN_PLACE
                {
                    child.local + 1
                } else {
                    child.local
                };
                if local.as_usize() == 1 {
                    // Accounting for shims
                    let next_idx = if matches!(shim, Some(ShimType::Once)) {
                        // If this is a once shim then the signature of the
                        // function and its call don't match fully. (We are
                        // calling a closure that takes it's `self` by reference
                        // with a `self` by value.)
                        if let Some(fst) = child.projection.first() {
                            // If there is a first place it must be a deref
                            assert_eq!(fst, &PlaceElem::Deref);
                        } else {
                            // We cannot remap the raw first place as it is a
                            // reference that does not exist in the caller (as
                            // the caller passes `self` by value.)
                            return None;
                        }
                        // We skip the first projection element (a deref) to
                        // account for the difference in signature
                        1
                    } else {
                        0
                    };
                    (closure_arg.place()?, &child.projection[next_idx..])
                } else {
                    let tuple_arg = tupled_arguments.place()?;
                    let _projection = child.projection.to_vec();
                    let field = FieldIdx::from_usize(local.as_usize() - 2);
                    let field_ty = tuple_arg
                        .ty(self.parent_body, self.tcx)
                        .field_ty(self.tcx, field);
                    (
                        tuple_arg.project_deeper(&[PlaceElem::Field(field, field_ty)], self.tcx),
                        &child.projection[..],
                    )
                }
            }
        };
        Some(PlaceTranslation {
            new_base,
            additional_projection,
            scope: self,
        })
    }
}
