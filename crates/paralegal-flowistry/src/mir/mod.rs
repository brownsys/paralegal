//! Infrastructure for analyzing MIR that supports the information flow analysis.

use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_middle::mir::Body;
use rustc_type_ir::RegionVid;

pub mod aliases;
pub mod placeinfo;
pub mod utils;

/// The per-procedure information the analysis needs. Most of the time this is
/// going to be
/// [BodyWithBorrowckFacts]
pub trait FlowistryInput<'tcx, 'a>: Copy {
    fn body(self) -> &'tcx Body<'tcx>;
    fn input_facts_subset_base(self) -> Box<dyn Iterator<Item = (RegionVid, RegionVid)> + 'a>;
}

impl<'tcx> FlowistryInput<'tcx, 'tcx> for &'tcx BodyWithBorrowckFacts<'tcx> {
    fn body(self) -> &'tcx Body<'tcx> {
        &self.body
    }

    fn input_facts_subset_base(self) -> Box<dyn Iterator<Item = (RegionVid, RegionVid)> + 'tcx> {
        Box::new(
            self.input_facts
                .as_ref()
                .unwrap()
                .subset_base
                .iter()
                .map(|&(r1, r2, _)| (r1.into(), r2.into())),
        )
    }
}
