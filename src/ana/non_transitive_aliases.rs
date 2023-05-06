use crate::ty::RegionVid;
use crate::utils::DfppBodyExt;
use crate::{
    rust::{
        hir::def_id::LocalDefId,
        mir::{Terminator, TerminatorKind},
        rustc_borrowck::{self, BodyWithBorrowckFacts},
    },
    Either, TyCtxt,
};
use flowistry::mir::{aliases::Aliases, borrowck_facts::CachedSimplifedBodyWithFacts};
extern crate polonius_engine;

/// For some reason I can't find a canonical place where the `LocationIndex`
/// type from [`rustc_borrowck`] is exported. So instead I alias it here using
/// the [`polonius_engine::FactTypes`] trait through which it *must* be
/// exported.
///
/// Some of our type signatures need to refer to this type which this alias
/// makes easier.
type LocationIndex = <rustc_borrowck::consumers::RustcFacts as polonius_engine::FactTypes>::Point;

/// The constraint selector is essentially a closure. The function that it
/// encapsulates is [`Self::select`] and it is constructed with
/// [`Self::location_based`].
///
/// This type, as a selector, is handed to
/// [`flowistry::mir::aliases::Aliases::build_with_fact_selection`]. This is
/// done during construction of the [`CallOnlyFlow`] where we require a
/// non-transitive alias analysis. This struct facilitates this by severing
/// lifetime entailments over function calls which makes the alias analysis
/// non-transitive with respect to function calls.
struct ConstraintSelector<'tcx, 'a> {
    body_with_facts: &'a BodyWithBorrowckFacts<'tcx>,
}

impl<'a, 'tcx> ConstraintSelector<'tcx, 'a> {
    /// Now the only constructor for this type
    fn location_based(body_with_facts: &'a BodyWithBorrowckFacts<'tcx>) -> Self {
        Self { body_with_facts }
    }

    /// Selects whether to keep a fact from `BodyWithBorrowckFacts.all_facts.subset_base`
    fn select(&self, _: RegionVid, _: RegionVid, idx: LocationIndex) -> bool {
        use rustc_borrowck::consumers::RichLocation;
        let rich_loc = self.body_with_facts.location_table.to_location(idx);
        let loc = match rich_loc {
            RichLocation::Mid(l) => l,
            RichLocation::Start(l) => l,
        };
        let stmt = self.body_with_facts.body.stmt_at_better_err(loc);
        !matches!(
            stmt,
            Either::Right(Terminator {
                kind: TerminatorKind::Call { .. },
                ..
            })
        )
    }
}

pub fn compute<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body_with_facts: &'tcx CachedSimplifedBodyWithFacts<'tcx>,
) -> Aliases<'tcx, 'tcx> {
    let selector = ConstraintSelector::location_based(body_with_facts.body_with_facts());
    Aliases::build_with_fact_selection(tcx, def_id.to_def_id(), body_with_facts, |r1, r2, idx| {
        selector.select(r1, r2, idx)
    })
}
