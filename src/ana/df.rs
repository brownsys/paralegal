use std::{cell::RefCell, rc::Rc};

use crate::rust::{
    mir::{visit::Visitor, *},
    rustc_data_structures::fx::{FxHashMap as HashMap, FxHashSet as HashSet},
    rustc_hir::{def_id::DefId, BodyId},
    rustc_mir_dataflow::{self, Analysis, AnalysisDomain, Forward, JoinSemiLattice},
    ty::TyCtxt,
};

use flowistry::infoflow::mutation::{ModularMutationVisitor, MutationStatus};
use flowistry::{
    extensions::{is_extension_active, ContextMode, MutabilityMode},
    indexed::{
        impls::{LocationDomain, LocationSet},
        IndexMatrix, IndexSet, IndexedDomain, RefSet,
    },
    mir::{
        aliases::Aliases,
        control_dependencies::ControlDependencies,
        engine,
        utils::{OperandExt, PlaceExt},
    },
};
pub type FlowResults<'a, 'tcx> = engine::AnalysisResults<'tcx, FlowAnalysis<'a, 'tcx>>;

pub type FlowDomainMatrix<'tcx> = IndexMatrix<Place<'tcx>, Location>;

#[derive(PartialEq, Eq, Clone)]
pub struct FlowDomain<'tcx> {
    matrix: FlowDomainMatrix<'tcx>,
    overrides: HashMap<Place<'tcx>, Location>,
}

impl<'tcx> FlowDomain<'tcx> {
    fn override_(&mut self, row: Place<'tcx>, at: Location) -> bool {
        let r = self.overrides.insert(row, at);
        if let Some(old) = r {
            if old != at {
                warn!("Duplicate override for key {row:?}, old:{old:?} new:{at:?}");
            }
        }
        r.is_none()
    }
}

impl<'tcx> FlowDomain<'tcx> {
    fn matrix(&self) -> &FlowDomainMatrix<'tcx> {
        &self.matrix
    }
    fn matrix_mut<'a>(&mut self) -> &mut FlowDomainMatrix<'tcx> {
        &mut self.matrix
    }
    fn row<'a>(&'a self, row: Place<'tcx>) -> IndexSet<Location, RefSet<'a, Location>> {
        self.matrix.row_set(row)
    }
    fn union_after<S: flowistry::indexed::ToSet<Location>>(
        &mut self,
        row: Place<'tcx>,
        _from: &IndexSet<Location, S>,
        at: Location,
    ) -> bool {
        self.override_(row, at)
    }
    fn from_location_domain(dom: &Rc<LocationDomain>) -> Self {
        Self {
            matrix: FlowDomainMatrix::new(dom),
            overrides: HashMap::default(),
        }
    }
    fn include(&mut self, row: Place<'tcx>, at: Location) -> bool {
        self.override_(row, at)
    }
}

impl<'tcx> JoinSemiLattice for FlowDomain<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        other.matrix.rows().for_each(|(r, s)| {
            changed |= if other.overrides.contains_key(&r) {
                false
            } else {
                self.matrix.union_into_row(r, &s)
            };
        });
        other
            .overrides
            .iter()
            .for_each(|(p, l)| changed |= self.matrix.insert(*p, *l));
        changed
    }
}

pub struct FlowAnalysis<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub def_id: DefId,
    pub body: &'a Body<'tcx>,
    pub control_dependencies: ControlDependencies,
    pub aliases: Aliases<'a, 'tcx>,
    recurse_cache: RefCell<HashMap<BodyId, FlowResults<'a, 'tcx>>>,
}

impl<'a, 'tcx> FlowAnalysis<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body: &'a Body<'tcx>,
        aliases: Aliases<'a, 'tcx>,
        control_dependencies: ControlDependencies,
    ) -> Self {
        let recurse_cache = RefCell::new(HashMap::default());
        FlowAnalysis {
            tcx,
            def_id,
            body,
            aliases,
            control_dependencies,
            recurse_cache,
        }
    }

    pub fn location_domain(&self) -> &Rc<LocationDomain> {
        self.aliases.location_domain()
    }

    fn transfer_function(
        &self,
        state: &mut FlowDomain<'tcx>,
        mutated: Place<'tcx>,
        inputs: &[(Place<'tcx>, Option<PlaceElem<'tcx>>)],
        location: Location,
        mutation_status: MutationStatus,
    ) {
        debug!("  Applying mutation to {mutated:?} with inputs {inputs:?}");
        let location_domain = self.location_domain();

        let all_aliases = &self.aliases;
        let mutated_aliases = all_aliases.aliases(mutated);
        trace!("    Mutated aliases: {mutated_aliases:?}");
        assert!(!mutated_aliases.is_empty());

        // Clear sub-places of mutated place (if sound to do so)
        if matches!(mutation_status, MutationStatus::Definitely) && mutated_aliases.len() == 1 {
            let mutated_direct = mutated_aliases.iter().next().unwrap();
            for sub in all_aliases.children(*mutated_direct).iter() {
                state.matrix_mut().clear_row(all_aliases.normalize(*sub));
            }
        }

        let mut input_location_deps = LocationSet::new(location_domain);
        input_location_deps.insert(location);

        let add_deps = |place: Place<'tcx>, location_deps: &mut LocationSet| {
            let reachable_values = all_aliases.reachable_values(place, Mutability::Not);
            let provenance = place
                .refs_in_projection()
                .into_iter()
                .flat_map(|(place_ref, _)| {
                    all_aliases
                        .aliases(Place::from_ref(place_ref, self.tcx))
                        .iter()
                });
            for relevant in reachable_values.iter().chain(provenance) {
                let deps = state.row(all_aliases.normalize(*relevant));
                trace!("    For relevant {relevant:?} for input {place:?} adding deps {deps:?}");
                location_deps.union(&deps);
            }
        };

        // Add deps of mutated to include provenance of mutated pointers
        add_deps(mutated, &mut input_location_deps);

        // Add deps of all inputs
        let mut children = Vec::new();
        for (place, elem) in inputs.iter() {
            add_deps(*place, &mut input_location_deps);

            // If the input is associated to a specific projection of the mutated
            // place, then save that input's dependencies with the projection
            if let Some(elem) = elem {
                let mut projection = mutated.projection.to_vec();
                projection.push(*elem);
                let mut child_deps = LocationSet::new(location_domain);
                add_deps(*place, &mut child_deps);
                children.push((
                    Place::make(mutated.local, &projection, self.tcx),
                    child_deps,
                ));
            }
        }

        // Add control dependencies
        let controlled_by = self.control_dependencies.dependent_on(location.block);
        let body = self.body;
        for block in controlled_by.into_iter().flat_map(|set| set.iter()) {
            input_location_deps.insert(body.terminator_loc(block));

            // Include dependencies of the switch's operand
            let terminator = body.basic_blocks()[block].terminator();
            if let TerminatorKind::SwitchInt { discr, .. } = &terminator.kind {
                if let Some(discr_place) = discr.to_place() {
                    add_deps(discr_place, &mut input_location_deps);
                }
            }
        }

        if children.len() > 0 {
            // In the special case of mutated = aggregate { x: .., y: .. }
            // then we ensure that deps(mutated.x) != deps(mutated)

            // First, ensure that all children have the current in their deps.
            // See test struct_read_constant for where this is needed.
            for child in all_aliases.children(mutated) {
                state.include(all_aliases.normalize(child), location);
            }

            // Then for constructor arguments that were places, add dependencies of those places.
            for (child, deps) in children {
                state.union_after(all_aliases.normalize(child), &deps, location);
            }

            // Finally add input_location_deps *JUST* to mutated, not conflicts of mutated.
            state.union_after(
                all_aliases.normalize(mutated),
                &input_location_deps,
                location,
            );
        } else {
            // Union dependencies into all conflicting places of the mutated place
            let mut mutable_conflicts = all_aliases.conflicts(mutated).to_owned();

            // Remove any conflicts that aren't actually mutable, e.g. if x : &T ends up
            // as an alias of y: &mut T. See test function_lifetime_alias_mut for an example.
            let ignore_mut =
                is_extension_active(|mode| mode.mutability_mode == MutabilityMode::IgnoreMut);
            if !ignore_mut {
                let body = self.body;
                let tcx = self.tcx;
                mutable_conflicts = mutable_conflicts
                    .iter()
                    .filter(|place| {
                        place.iter_projections().all(|(sub_place, _)| {
                            let ty = sub_place.ty(body.local_decls(), tcx).ty;
                            !matches!(ty.ref_mutability(), Some(Mutability::Not))
                        })
                    })
                    .copied()
                    .collect::<HashSet<_>>();
            };

            debug!("  Mutated conflicting places: {mutable_conflicts:?}");
            debug!("    with deps {input_location_deps:?}");

            for place in mutable_conflicts.into_iter() {
                state.union_after(all_aliases.normalize(place), &input_location_deps, location);
            }
        }
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for FlowAnalysis<'a, 'tcx> {
    type Domain = FlowDomain<'tcx>;
    type Direction = Forward;
    const NAME: &'static str = "FlowAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        FlowDomain::from_location_domain(self.location_domain())
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        for (arg, loc) in self.aliases.all_args() {
            for place in self.aliases.conflicts(arg) {
                debug!(
                    "arg={arg:?} / place={place:?} / loc={:?}",
                    self.location_domain().value(loc)
                );
                state
                    .matrix_mut()
                    .insert(self.aliases.normalize(*place), loc);
            }
        }
    }
}

impl<'a, 'tcx> Analysis<'tcx> for FlowAnalysis<'a, 'tcx> {
    fn apply_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        ModularMutationVisitor::new(
            &self.aliases,
            |mutated: Place<'tcx>,
             inputs: &[(Place<'tcx>, Option<PlaceElem<'tcx>>)],
             location: Location,
             mutation_status: MutationStatus| {
                self.transfer_function(state, mutated, inputs, location, mutation_status)
            },
        )
        .visit_statement(statement, location);
    }

    fn apply_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        ModularMutationVisitor::new(
            &self.aliases,
            |mutated: Place<'tcx>,
             inputs: &[(Place<'tcx>, Option<PlaceElem<'tcx>>)],
             location: Location,
             mutation_status: MutationStatus| {
                self.transfer_function(state, mutated, inputs, location, mutation_status)
            },
        )
        .visit_terminator(terminator, location);
    }

    fn apply_call_return_effect(
        &self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: rustc_mir_dataflow::CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}
