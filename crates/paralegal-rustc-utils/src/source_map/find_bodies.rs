use rustc_hir::{intravisit::Visitor, BodyId};
use rustc_middle::{hir::nested_filter::OnlyBodies, ty::TyCtxt};
use rustc_span::Span;

struct BodyFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    bodies: Vec<(Span, BodyId)>,
}

impl<'tcx> Visitor<'tcx> for BodyFinder<'tcx> {
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_nested_body(&mut self, id: BodyId) {
        let hir = self.nested_visit_map();

        // const/static items are considered to have bodies, so we want to exclude
        // them from our search for functions
        if !hir
            .body_owner_kind(hir.body_owner_def_id(id))
            .is_fn_or_closure()
        {
            return;
        }

        let body = hir.body(id);
        self.visit_body(body);

        let hir = self.tcx.hir();
        let span = hir.span_with_body(hir.body_owner(id));
        if !span.from_expansion() {
            self.bodies.push((span, id));
        }
    }
}

/// Finds all bodies in the current crate
pub fn find_bodies(tcx: TyCtxt) -> Vec<(Span, BodyId)> {
    let mut finder = BodyFinder {
        tcx,
        bodies: Vec::new(),
    };
    tcx.hir().visit_all_item_likes_in_crate(&mut finder);
    finder.bodies
}

/// Finds all the bodies that enclose the given span, from innermost to outermost
pub fn find_enclosing_bodies(tcx: TyCtxt, sp: Span) -> impl Iterator<Item = BodyId> {
    let mut bodies = find_bodies(tcx);
    bodies.retain(|(other, _)| other.contains(sp));
    bodies.into_iter().map(|(_, id)| id)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_utils::{self, CompileResult};

    #[test]
    fn test_find_bodies() {
        let input = r"
// Ignore constants
const C: usize = 0;

fn a() {
  // Catch nested bodies
  fn b() {}
}

fn c() {}

macro_rules! m {
  () => { fn d() {} }
}

// Ignore macro-generated bodies
m!{}
";
        test_utils::CompileBuilder::new(input).compile(|CompileResult { tcx, .. }| {
            assert_eq!(find_bodies(tcx).len(), 3);
        });
    }
}
