use std::borrow::Cow;

use flowistry_pdg::rustc_portable::DefId;
use log::trace;
use rustc_abi::FieldIdx;

use rustc_middle::{
    mir::{Body, HasLocalDecls, Operand, Place, PlaceElem, RETURN_PLACE},
    ty::TyCtxt,
};

use crate::{async_support::AsyncInfo, local_analysis::CallKind, utils};

#[derive(Debug)]
pub enum CallingConvention<'tcx> {
    Direct(Box<[Operand<'tcx>]>),
    Indirect {
        closure_arg: Operand<'tcx>,
        tupled_arguments: Operand<'tcx>,
    },
    Async(Place<'tcx>),
}

pub struct PlaceTranslation<'a, 'tcx> {
    new_base: Place<'tcx>,
    additional_projection: &'tcx [PlaceElem<'tcx>],
    scope: &'a PlaceTranslator<'a, 'tcx>,
}

impl<'a, 'tcx> PlaceTranslation<'a, 'tcx> {
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
            CallKind::Indirect => CallingConvention::Indirect {
                closure_arg: args[0].clone(),
                tupled_arguments: args[1].clone(),
            },
        }
    }

    // pub(crate) fn translate_to_parent(
    //     &self,
    //     child: Place<'tcx>,
    //     async_info: &AsyncInfo,
    //     tcx: TyCtxt<'tcx>,
    //     parent_body: &Body<'tcx>,
    //     parent_def_id: DefId,
    //     destination: Place<'tcx>,
    // ) -> Option<Place<'tcx>> {
    //     trace!("  Translating child place: {child:?}");
    //     let (parent_place, child_projection) =
    //         self.handle_translate(async_info, tcx, child, destination, parent_body)?;

    //     let parent_place_projected = parent_place.project_deeper(child_projection, tcx);
    //     trace!("  ⮑ Translated to: {parent_place_projected:?}");
    //     Some(utils::retype_place(
    //         parent_place_projected,
    //         tcx,
    //         parent_body,
    //         parent_def_id,
    //     ))
    // }
}

pub struct PlaceTranslator<'a, 'tcx> {
    async_info: &'a AsyncInfo,
    parent_body_def_id: DefId,
    parent_body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    destination: Place<'tcx>,
    calling_convention: &'a CallingConvention<'tcx>,
    precise: bool,
}

impl<'a, 'tcx> PlaceTranslator<'a, 'tcx> {
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

    pub(crate) fn translate_to_parent(&self, child: Place<'tcx>) -> Option<Place<'tcx>> {
        let translation = self.handle_translate(child)?;
        Some(if self.precise {
            translation.make_translated_place()
        } else {
            translation.base_place()
        })
    }

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
                closure_arg,
                tupled_arguments,
            } => {
                if child.local.as_usize() == 1 {
                    (closure_arg.place()?, &child.projection[..])
                } else {
                    let tuple_arg = tupled_arguments.place()?;
                    let _projection = child.projection.to_vec();
                    let field = FieldIdx::from_usize(child.local.as_usize() - 2);
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
