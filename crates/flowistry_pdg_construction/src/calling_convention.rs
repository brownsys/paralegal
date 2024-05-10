use flowistry_pdg::rustc_portable::{DefId, LocalDefId};
use log::trace;
use rustc_abi::FieldIdx;

use rustc_middle::{
    mir::{Body, HasLocalDecls, Operand, Place, PlaceElem, RETURN_PLACE},
    ty::TyCtxt,
};

use crate::async_support::AsyncInfo;
use crate::construct::CallKind;

pub enum CallingConvention<'tcx, 'a> {
    Direct(&'a [Operand<'tcx>]),
    Indirect {
        closure_arg: &'a Operand<'tcx>,
        tupled_arguments: &'a Operand<'tcx>,
    },
    Async(Place<'tcx>),
}

impl<'tcx, 'a> CallingConvention<'tcx, 'a> {
    pub fn from_call_kind(
        kind: &CallKind<'tcx>,
        args: &'a [Operand<'tcx>],
    ) -> CallingConvention<'tcx, 'a> {
        match kind {
            CallKind::AsyncPoll(_, _, ctx) => CallingConvention::Async(*ctx),
            CallKind::Direct => CallingConvention::Direct(args),
            CallKind::Indirect => CallingConvention::Indirect {
                closure_arg: &args[0],
                tupled_arguments: &args[1],
            },
        }
    }

    pub(crate) fn translate_to_parent(
        &self,
        child: Place<'tcx>,
        async_info: &AsyncInfo,
        tcx: TyCtxt<'tcx>,
        parent_body: &Body<'tcx>,
        parent_def_id: DefId,
        destination: Place<'tcx>,
    ) -> Option<Place<'tcx>> {
        trace!("  Translating child place: {child:?}");
        let (parent_place, child_projection) =
            self.handle_translate(async_info, tcx, child, destination, parent_body)?;

        let parent_place_projected = parent_place.project_deeper(child_projection, tcx);
        trace!("  ⮑ Translated to: {parent_place_projected:?}");
        Some(utils::retype_place(
            parent_place_projected,
            tcx,
            parent_body,
            parent_def_id,
        ))
    }

    pub(crate) fn handle_translate(
        &self,
        async_info: &AsyncInfo,
        tcx: TyCtxt<'tcx>,
        child: Place<'tcx>,
        destination: Place<'tcx>,
        parent_body: &Body<'tcx>,
    ) -> Option<(Place<'tcx>, &[PlaceElem<'tcx>])> {
        let result = match self {
            // Async return must be handled special, because it gets wrapped in `Poll::Ready`
            Self::Async { .. } if child.local == RETURN_PLACE => {
                let in_poll = destination.project_deeper(
                    &[PlaceElem::Downcast(None, async_info.poll_ready_variant_idx)],
                    tcx,
                );
                let field_idx = async_info.poll_ready_field_idx;
                let child_inner_return_type = in_poll
                    .ty(parent_body.local_decls(), tcx)
                    .field_ty(tcx, field_idx);
                (
                    in_poll.project_deeper(
                        &[PlaceElem::Field(field_idx, child_inner_return_type)],
                        tcx,
                    ),
                    &child.projection[..],
                )
            }
            _ if child.local == RETURN_PLACE => (destination, &child.projection[..]),
            // Map arguments to the argument array
            Self::Direct(args) => (
                args[child.local.as_usize() - 1].place()?,
                &child.projection[..],
            ),
            // Map arguments to projections of the future, the poll's first argument
            Self::Async(ctx) => {
                if child.local.as_usize() == 1 {
                    (*ctx, &child.projection[..])
                } else {
                    return None;
                }
            }
            // Map closure captures to the first argument.
            // Map formal parameters to the second argument.
            Self::Indirect {
                closure_arg,
                tupled_arguments,
            } => {
                if child.local.as_usize() == 1 {
                    (closure_arg.place()?, &child.projection[..])
                } else {
                    let tuple_arg = tupled_arguments.place()?;
                    let _projection = child.projection.to_vec();
                    let field = FieldIdx::from_usize(child.local.as_usize() - 2);
                    let field_ty = tuple_arg.ty(parent_body, tcx).field_ty(tcx, field);
                    (
                        tuple_arg.project_deeper(&[PlaceElem::Field(field, field_ty)], tcx),
                        &child.projection[..],
                    )
                }
            }
        };
        Some(result)
    }
}
