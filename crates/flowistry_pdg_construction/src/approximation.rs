use log::trace;

use rustc_abi::VariantIdx;

use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{visit::Visitor, AggregateKind, Location, Place, Rvalue},
    ty::TyKind,
};
use rustc_span::Span;

use crate::{local_analysis::LocalAnalysis, utils::ArgSlice};

pub(crate) type ApproximationHandler<'tcx, 'a, K> = fn(
    &LocalAnalysis<'tcx, 'a, K>,
    &mut dyn Visitor<'tcx>,
    ArgSlice<'a, 'tcx>,
    Place<'tcx>,
    Location,
);

impl<'tcx, 'a, K> LocalAnalysis<'tcx, 'a, K> {
    /// Special case behavior for calls to functions used in desugaring `await` desugarings.
    ///
    /// Ensures that functions like `Pin::new_unchecked` are not modularly-approximated.
    pub(crate) fn can_approximate_async_functions(
        &self,
        def_id: DefId,
        span: Span,
    ) -> Option<ApproximationHandler<'tcx, 'a, K>> {
        if span.desugaring_kind() != Some(rustc_span::DesugaringKind::Await) {
            return None;
        }
        let lang_items = self.tcx().lang_items();
        if Some(def_id) == lang_items.new_unchecked_fn() {
            Some(Self::approximate_new_unchecked)
        } else if Some(def_id) == lang_items.into_future_fn()
            // FIXME: better way to get retrieve this stdlib DefId?
            || self.tcx().def_path_str(def_id) == "<F as std::future::IntoFuture>::into_future"
        {
            Some(Self::approximate_into_future)
        } else {
            None
        }
    }

    fn approximate_into_future(
        &self,
        vis: &mut dyn Visitor<'tcx>,
        args: ArgSlice<'_, 'tcx>,
        destination: Place<'tcx>,
        location: Location,
    ) {
        trace!("Handling into_future as assign for {destination:?}");
        let [op] = args else {
            unreachable!();
        };
        vis.visit_assign(&destination, &Rvalue::Use(op.node.clone()), location);
    }

    fn approximate_new_unchecked(
        &self,
        vis: &mut dyn Visitor<'tcx>,
        args: ArgSlice<'_, 'tcx>,
        destination: Place<'tcx>,
        location: Location,
    ) {
        let lang_items = self.tcx().lang_items();
        let [op] = args else {
            unreachable!();
        };
        let mut operands = IndexVec::new();
        operands.push(op.node.clone());
        let TyKind::Adt(adt_id, generics) = destination.ty(&self.mono_body, self.tcx()).ty.kind()
        else {
            unreachable!()
        };
        assert_eq!(adt_id.did(), lang_items.pin_type().unwrap());
        let aggregate_kind =
            AggregateKind::Adt(adt_id.did(), VariantIdx::from_u32(0), generics, None, None);
        let rvalue = Rvalue::Aggregate(Box::new(aggregate_kind), operands);
        trace!("Handling new_unchecked as assign for {destination:?}");
        vis.visit_assign(&destination, &rvalue, location);
    }
}
