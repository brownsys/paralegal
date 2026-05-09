//! Utilities for analyzing places: children, aliases, etc.

use std::ops::ControlFlow;

use paralegal_rustc_utils::{
    MutabilityExt, PlaceExt,
    cache::{Cache, CopyCache},
    mir::place::UNKNOWN_REGION,
};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::*,
    ty::{Region, RegionKind, RegionVid, Ty, TyCtxt, TyKind, TypeSuperVisitable, TypeVisitor},
};

use super::{FlowistryInput, aliases::Aliases, utils::PlaceSet};

/// Utilities for analyzing places: children, aliases, etc.
pub struct PlaceInfo<'tcx> {
    /// Type context
    pub tcx: TyCtxt<'tcx>,
    /// The body this info refers to
    pub body: &'tcx Body<'tcx>,
    /// Id of the function this info refers to
    pub def_id: DefId,

    // Core computed data structure
    aliases: Aliases<'tcx>,

    // Caching for derived analysis
    normalized_cache: CopyCache<Place<'tcx>, Place<'tcx>>,
    aliases_cache: Cache<Place<'tcx>, PlaceSet<'tcx>>,
    conflicts_cache: Cache<Place<'tcx>, PlaceSet<'tcx>>,
    reachable_cache: Cache<(Place<'tcx>, Mutability), PlaceSet<'tcx>>,
}

impl<'tcx> PlaceInfo<'tcx> {
    /// Computes all the metadata about places used within the infoflow analysis.
    pub fn build<'a>(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        input: impl FlowistryInput<'tcx, 'a>,
    ) -> Self {
        Self::build_from_input_facts(tcx, def_id, input)
    }
    /// Computes all the metadata about places used within the infoflow analysis.
    pub fn build_from_input_facts<'a>(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        input: impl FlowistryInput<'tcx, 'a>,
    ) -> Self {
        let body = input.body();
        let aliases = Aliases::build(tcx, def_id, input);

        PlaceInfo {
            aliases,
            tcx,
            body,
            def_id,
            aliases_cache: Cache::default(),
            normalized_cache: CopyCache::default(),
            conflicts_cache: Cache::default(),
            reachable_cache: Cache::default(),
        }
    }

    /// Returns the MIR body this `PlaceInfo` was built from.
    pub fn body(&self) -> &'tcx Body<'tcx> {
        self.body
    }

    /// Normalizes a place via [`PlaceExt::normalize`] (cached).
    ///
    /// See the `PlaceExt` documentation for details on how normalization works.
    pub fn normalize(&self, place: Place<'tcx>) -> Place<'tcx> {
        self.normalized_cache
            .get(&place, |place| place.normalize(self.tcx, self.def_id))
    }

    /// Computes the aliases of a place (cached).
    ///
    /// For example, if `x = &y`, then `*x` aliases `y`.
    /// Note that an alias is NOT guaranteed to be of the same type as `place`!
    pub fn aliases(&self, place: Place<'tcx>) -> &PlaceSet<'tcx> {
        // note: important that aliases are computed on the unnormalized place
        // which contains region information
        self.aliases_cache
            .get(&self.normalize(place), move |_| self.aliases.aliases(place))
    }

    /// Returns all reachable fields of `place` without going through references.
    ///
    /// For example, if `x = (0, 1)` then `children(x) = {x, x.0, x.1}`.
    pub fn children(&self, place: Place<'tcx>) -> PlaceSet<'tcx> {
        PlaceSet::from_iter(place.interior_places(self.tcx, self.body, self.def_id))
    }

    /// Returns all places that *directly* conflict with `place`, i.e. that a mutation to `place`
    /// would also be a mutation to the conflicting place.
    ///
    /// For example, if `x = ((0, 1), 2)` then `conflicts(x.0) = {x, x.0, x.0.0, x.0.1}`, but not `x.1`.
    ///
    /// For indirect places, this function follows conflicting parents up until a reference point.
    /// So if `x = (0, &(box 1, 2))` then conflicts(*(*(x.1).0)) = {*(*(x.1).0), *(x.1).0, *(x.1)}
    pub fn conflicts(&self, place: Place<'tcx>) -> &PlaceSet<'tcx> {
        self.conflicts_cache.get(&place, |place| {
            let children = self.children(place);
            let parents = place
                .projection
                .iter()
                .enumerate()
                .map(|(i, elem)| {
                    let place = PlaceRef {
                        local: place.local,
                        projection: &place.projection[..i],
                    };
                    (place, elem)
                })
                .take_while(|(place, elem)| {
                    place.ty(self.body.local_decls(), self.tcx).ty.is_box()
                        || !matches!(elem, PlaceElem::Deref)
                })
                .map(|(place_ref, _)| Place::from_ref(place_ref, self.tcx));
            children.into_iter().chain(parents).collect()
        })
    }

    /// Returns all [direct](PlaceExt::is_direct) places that are reachable from `place`
    /// and can be used at the provided level of [`Mutability`] (cached).
    ///
    /// For example, if `x = 0` and `y = (0, &x)`, then `reachable_values(y, Mutability::Not)`
    /// is `{y, x}`. With `Mutability::Mut`, then the output is `{y}` (no `x`).
    pub fn reachable_values(&self, place: Place<'tcx>, mutability: Mutability) -> &PlaceSet<'tcx> {
        self.reachable_cache.get(&(place, mutability), |_| {
            let passes_filter = |p: Place<'tcx>| {
                if let Some((pref, _)) = p.refs_in_projection(self.body, self.tcx).last() {
                    let ty = pref.ty(self.body.local_decls(), self.tcx).ty;
                    if ty.is_box() || ty.is_raw_ptr() {
                        return true;
                    }
                }
                p.is_direct(self.body, self.tcx)
            };

            let mut result = PlaceSet::default();
            let mut worklist = vec![place];

            while let Some(p) = worklist.pop() {
                if !passes_filter(p) || !result.insert(p) {
                    continue;
                }
                let ty = p.ty(self.body.local_decls(), self.tcx).ty;
                worklist.extend(self.collect_loans(ty, mutability));
            }

            result
        })
    }

    fn collect_loans(&self, ty: Ty<'tcx>, mutability: Mutability) -> PlaceSet<'tcx> {
        let mut collector = LoanCollector {
            aliases: &self.aliases,
            unknown_region: Region::new_var(self.tcx, UNKNOWN_REGION),
            target_mutability: mutability,
            stack: vec![],
            loans: PlaceSet::default(),
        };
        let _ = collector.visit_ty(ty);
        collector.loans
    }
}

// TODO: this visitor shares some structure with the PlaceCollector in mir utils.
// Can we consolidate these?
struct LoanCollector<'a, 'tcx> {
    aliases: &'a Aliases<'tcx>,
    unknown_region: Region<'tcx>,
    target_mutability: Mutability,
    stack: Vec<Mutability>,
    loans: PlaceSet<'tcx>,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for LoanCollector<'_, 'tcx> {
    type Result = ControlFlow<()>;

    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            // For reference types: only visit the region to collect loans, then
            // return Continue so sibling references in the same compound type are
            // also visited. The inner type is intentionally skipped here; the
            // worklist in reachable_values handles transitive traversal by
            // following each loan's own type.
            TyKind::Ref(region, _, mutability) => {
                self.stack.push(*mutability);
                self.visit_region(*region)?;
                self.stack.pop();
                return ControlFlow::Continue(());
            }
            _ if ty.is_box() || ty.is_raw_ptr() => {
                self.visit_region(self.unknown_region)?;
            }
            _ => {}
        };

        ty.super_visit_with(self)?;
        ControlFlow::Continue(())
    }

    fn visit_region(&mut self, region: Region<'tcx>) -> Self::Result {
        let region = match region.kind() {
            RegionKind::ReVar(region) => region,
            RegionKind::ReStatic => RegionVid::from_usize(0),
            // TODO: do we need to handle bound regions?
            // e.g. shows up with closures, for<'a> ...
            RegionKind::ReErased | RegionKind::ReBound(..) => {
                return ControlFlow::Continue(());
            }
            _ => unreachable!("{region:?}"),
        };
        if let Some(loans) = self.aliases.loans.get(&region) {
            let under_immut_ref = self.stack.contains(&Mutability::Not);
            self.loans
                .extend(loans.iter().filter_map(|(place, mutability)| {
                    let loan_mutability = if under_immut_ref {
                        Mutability::Not
                    } else {
                        *mutability
                    };
                    self.target_mutability
                        .is_permissive_as(loan_mutability)
                        .then_some(place)
                }))
        }

        ControlFlow::Continue(())
    }
}

#[cfg(test)]
mod test {
    use paralegal_rustc_utils::{
        hashset,
        test_utils::{self, Placer, compare_sets},
    };

    use super::*;

    fn placeinfo_harness(
        input: &str,
        f: impl for<'tcx> FnOnce(TyCtxt<'tcx>, &Body<'tcx>, PlaceInfo<'tcx>) + Send,
    ) {
        test_utils::compile_body(input, |tcx, body_id, body_with_facts| {
            let body = &body_with_facts.body;
            let def_id = tcx.hir_body_owner_def_id(body_id);
            let place_info = PlaceInfo::build(tcx, def_id.to_def_id(), body_with_facts);

            f(tcx, body, place_info)
        });
    }

    #[test]
    fn test_placeinfo_basic() {
        let input = r#"
fn main() {
  let a = 0;
  let mut b = 1;
  let c = ((0, &a), &mut b);
  let d = 0;
  let e = &d;
  let f = &e;
}
    "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let c = p.local("c");
            compare_sets(
                hashset! {
                  c.mk(),
                  c.field(0).mk(),
                  c.field(0).field(0).mk(),
                  c.field(0).field(1).mk(),
                  c.field(1).mk(),
                },
                place_info.children(c.mk()),
            );

            compare_sets(
                &hashset! {
                  c.mk(),
                  c.field(0).mk(),
                  c.field(0).field(0).mk(),
                  c.field(0).field(1).mk(),
                  // c.field(1) not part of the set
                },
                place_info.conflicts(c.field(0).mk()),
            );

            // a and b are reachable at immut-level
            compare_sets(
                &hashset! {
                  c.mk(),
                  p.local("a").mk(),
                  p.local("b").mk()
                },
                place_info.reachable_values(c.mk(), Mutability::Not),
            );

            // only b is reachable at mut-level
            compare_sets(
                &hashset! {
                  c.mk(),
                  p.local("b").mk()
                },
                place_info.reachable_values(c.mk(), Mutability::Mut),
            );

            // handles transitive references
            compare_sets(
                &hashset! {
                  p.local("f").mk(),
                  p.local("e").mk(),
                  p.local("d").mk()
                },
                place_info.reachable_values(p.local("f").mk(), Mutability::Not),
            )
        });
    }

    /// children of a scalar (leaf) place is just that place itself — no subfields.
    #[test]
    fn test_children_scalar() {
        let input = r#"
fn main() {
  let x: i32 = 42;
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let x = p.local("x");
            compare_sets(hashset! { x.mk() }, place_info.children(x.mk()));
        });
    }

    /// children of a reference is just the reference itself — we do not cross
    /// the reference boundary.
    #[test]
    fn test_children_reference_is_leaf() {
        let input = r#"
fn main() {
  let a: i32 = 1;
  let r = &a;
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let r = p.local("r");
            // r is &i32; children stops at the reference — no deref.
            compare_sets(hashset! { r.mk() }, place_info.children(r.mk()));
        });
    }

    /// children of a flat tuple enumerates all immediate fields.
    #[test]
    fn test_children_flat_tuple() {
        let input = r#"
fn main() {
  let t = (1_i32, 2_i32, 3_i32);
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let t = p.local("t");
            compare_sets(
                hashset! {
                    t.mk(),
                    t.field(0).mk(),
                    t.field(1).mk(),
                    t.field(2).mk(),
                },
                place_info.children(t.mk()),
            );
        });
    }

    /// conflicts of a scalar place is just that place — no parent, no children.
    #[test]
    fn test_conflicts_scalar() {
        let input = r#"
fn main() {
  let x: i32 = 0;
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let x = p.local("x");
            compare_sets(&hashset! { x.mk() }, place_info.conflicts(x.mk()));
        });
    }

    /// conflicts of the root of a nested struct includes all descendants.
    #[test]
    fn test_conflicts_root_includes_all_children() {
        let input = r#"
fn main() {
  let t = ((1_i32, 2_i32), 3_i32);
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let t = p.local("t");
            // conflicts(t) = children(t) (no ancestors since t is the root)
            compare_sets(
                &hashset! {
                    t.mk(),
                    t.field(0).mk(),
                    t.field(0).field(0).mk(),
                    t.field(0).field(1).mk(),
                    t.field(1).mk(),
                },
                place_info.conflicts(t.mk()),
            );
        });
    }

    /// conflicts of a deeply nested leaf includes all ancestors up to the root
    /// but not the siblings along the path.
    #[test]
    fn test_conflicts_deep_leaf_no_siblings() {
        let input = r#"
fn main() {
  let t = ((1_i32, 2_i32), 3_i32);
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let t = p.local("t");
            // conflicts(t.0.0) = {t, t.0, t.0.0}  — NOT t.0.1 or t.1
            compare_sets(
                &hashset! {
                    t.mk(),
                    t.field(0).mk(),
                    t.field(0).field(0).mk(),
                },
                place_info.conflicts(t.field(0).field(0).mk()),
            );
        });
    }

    /// conflicts stops at a shared-reference boundary: ancestors through a `&`
    /// are NOT included, but the deref itself and its children are.
    #[test]
    fn test_conflicts_stops_at_ref_boundary() {
        let input = r#"
fn main() {
  let inner = (1_i32, 2_i32);
  let r = &inner;
  let outer = (r, 3_i32);
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            // outer: (&(i32, i32), i32)
            // outer.0 is &(i32, i32); *outer.0 should NOT appear in conflicts of outer.0
            // because outer.0 is a reference — the deref is on the other side of a ref boundary.
            let outer = p.local("outer");
            // conflicts(outer.0) = {outer, outer.0}  — stops at the ref, does not go into *outer.0
            compare_sets(
                &hashset! {
                    outer.mk(),
                    outer.field(0).mk(),
                },
                place_info.conflicts(outer.field(0).mk()),
            );
        });
    }

    /// aliases: for a simple `x = &y`, `*x` should alias `y`.
    #[test]
    fn test_aliases_simple_borrow() {
        let input = r#"
fn main() {
  let y: i32 = 0;
  let x = &y;
  let _ = *x;
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let x = p.local("x");
            let y = p.local("y");
            // *x should alias y
            let aliases = place_info.aliases(x.deref().mk());
            compare_sets(&hashset! { y.mk() }, aliases);
        });
    }

    /// aliases: a mutable borrow `x = &mut y` means `*x` aliases `y`.
    #[test]
    fn test_aliases_mut_borrow() {
        let input = r#"
fn main() {
  let mut y: i32 = 0;
  let x = &mut y;
  *x = 1;
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let x = p.local("x");
            let y = p.local("y");
            let aliases = place_info.aliases(x.deref().mk());
            compare_sets(&hashset! { y.mk() }, aliases);
        });
    }

    /// reachable_values of a scalar place is just that place itself.
    #[test]
    fn test_reachable_values_scalar() {
        let input = r#"
fn main() {
  let x: i32 = 5;
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let x = p.local("x");
            compare_sets(
                &hashset! { x.mk() },
                place_info.reachable_values(x.mk(), Mutability::Not),
            );
            compare_sets(
                &hashset! { x.mk() },
                place_info.reachable_values(x.mk(), Mutability::Mut),
            );
        });
    }

    /// reachable_values with Mutability::Mut on a place that only holds an
    /// immutable reference returns just the place itself (the referent is excluded).
    #[test]
    fn test_reachable_values_immut_ref_excluded_from_mut() {
        let input = r#"
fn main() {
  let a: i32 = 1;
  let r = &a;
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let r = p.local("r");
            // Mutability::Not includes a
            compare_sets(
                &hashset! { r.mk(), p.local("a").mk() },
                place_info.reachable_values(r.mk(), Mutability::Not),
            );
            // Mutability::Mut excludes a (behind immutable &)
            compare_sets(
                &hashset! { r.mk() },
                place_info.reachable_values(r.mk(), Mutability::Mut),
            );
        });
    }

    /// reachable_values follows a chain of mutable references transitively.
    #[test]
    fn test_reachable_values_transitive_mut_refs() {
        let input = r#"
fn main() {
  let mut a: i32 = 0;
  let mut b = &mut a;
  let c = &mut b;
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let c = p.local("c");
            // c: &mut &mut i32 → through mutable chain we reach b then a
            compare_sets(
                &hashset! {
                    c.mk(),
                    p.local("b").mk(),
                    p.local("a").mk(),
                },
                place_info.reachable_values(c.mk(), Mutability::Mut),
            );
        });
    }

    /// reachable_values: a mixed chain where an immutable ref sits in the middle
    /// means Mut stops before crossing the immutable boundary, but Not goes all the way.
    ///
    /// The chain is: c (&mut bc) -> bc (&i32 copy of b's borrow of a) -> a.
    /// Because `bc = b` is a Copy assignment (both are &i32), the loan graph
    /// records that bc's region points directly to `a`, not to `b`. So `b`
    /// does not appear in the reachable set — only `bc` and `a` do (plus `c`
    /// itself).
    #[test]
    fn test_reachable_values_mixed_mut_immut_chain() {
        let input = r#"
fn main() {
  let a: i32 = 1;
  let b = &a;      // b: &i32  (immutable)
  let mut bc = b;  // bc: &i32, copy of b — same loan region points to a
  let c = &mut bc; // c: &mut &i32
}
        "#;
        placeinfo_harness(input, |tcx, body, place_info| {
            let p = Placer::new(tcx, body);
            let c = p.local("c");
            // c: &mut &i32
            // Not: c, bc, a (bc's region loans a directly; b is not in the chain)
            compare_sets(
                &hashset! {
                    c.mk(),
                    p.local("bc").mk(),
                    p.local("a").mk(),
                },
                place_info.reachable_values(c.mk(), Mutability::Not),
            );
            // Mut: c, bc (bc is directly reachable via &mut), but a is behind &i32
            compare_sets(
                &hashset! {
                    c.mk(),
                    p.local("bc").mk(),
                },
                place_info.reachable_values(c.mk(), Mutability::Mut),
            );
        });
    }
}
