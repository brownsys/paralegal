extern crate rustc_ast;

use rustc_abi::FieldIdx;
use rustc_middle::{
    mir::{Body, HasLocalDecls, Operand, Place, PlaceElem, RETURN_PLACE},
    ty::{Region, RegionKind, Ty, TyCtxt, TypeAndMut},
};

use crate::async_support::AsyncInfo;
use crate::construct::CallKind;

#[derive(Debug)]
pub enum CallingConvention<'tcx, 'a> {
    Direct(&'a [Operand<'tcx>]),
    Indirect {
        closure_arg: &'a Operand<'tcx>,
        tupled_arguments: &'a Operand<'tcx>,
    },
    Async(&'a [Operand<'tcx>]),
}

impl<'tcx, 'a> CallingConvention<'tcx, 'a> {
    pub fn from_call_kind(
        kind: &CallKind,
        args: &'a [Operand<'tcx>],
    ) -> CallingConvention<'tcx, 'a> {
        match kind {
            CallKind::AsyncPoll => CallingConvention::Async(args),
            CallKind::Direct => CallingConvention::Direct(args),
            CallKind::Indirect => CallingConvention::Indirect {
                closure_arg: &args[0],
                tupled_arguments: &args[1],
            },
        }
    }

    pub(crate) fn handle_translate(
        &self,
        async_info: &AsyncInfo,
        tcx: TyCtxt<'tcx>,
        child: Place<'tcx>,
        destination: Place<'tcx>,
        parent_body: &Body<'tcx>,
        child_body: &Body<'tcx>,
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
            Self::Async(args) => {
                if child.local.as_usize() == 1 {
                    log::trace!(
                        "Parent is of type {:?}",
                        args[0].place()?.ty(parent_body, tcx).ty
                    );
                    // In this rustc version the actual argument to an async
                    // closure is Pin<&mut GENERATOR>, but the actual closure
                    // function pretends to receive GENERATOR. So we must
                    // project out the Pin's first field and dereference the
                    // &mut.
                    let closure_ty = Place::from(child.local).ty(child_body, tcx).ty;
                    (
                        args[0].place()?.project_deeper(
                            &[
                                PlaceElem::Field(
                                    FieldIdx::from_u32(0),
                                    Ty::new_ref(
                                        tcx,
                                        Region::new_from_kind(tcx, RegionKind::ReErased),
                                        TypeAndMut {
                                            ty: closure_ty,
                                            mutbl: rustc_ast::Mutability::Mut,
                                        },
                                    ),
                                ),
                                PlaceElem::Deref,
                            ],
                            tcx,
                        ),
                        &child.projection[..],
                    )
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
