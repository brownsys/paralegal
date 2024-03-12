use rustc_abi::FieldIdx;
use rustc_index::IndexSlice;
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
    Async(AsyncCallingConvention<'tcx, 'a>),
}

impl<'tcx, 'a> CallingConvention<'tcx, 'a> {
    pub fn from_call_kind(
        kind: &CallKind<'tcx, 'a>,
        args: &'a [Operand<'tcx>],
    ) -> CallingConvention<'tcx, 'a> {
        match kind {
            CallKind::AsyncPoll(_, _, args) => CallingConvention::Async(*args),
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
            Self::Async(cc) => {
                if child.local.as_usize() == 1 {
                    let PlaceElem::Field(idx, _) = child.projection[0] else {
                        panic!("Unexpected non-projection of async context")
                    };
                    let op = match cc {
                        AsyncCallingConvention::Fn(args) => &args[idx.as_usize()],
                        AsyncCallingConvention::Block(args) => &args[idx],
                    };
                    (op.place()?, &child.projection[1..])
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

#[derive(Clone, Copy)]
pub enum AsyncCallingConvention<'tcx, 'a> {
    Fn(&'a [Operand<'tcx>]),
    Block(&'a IndexSlice<FieldIdx, Operand<'tcx>>),
}
