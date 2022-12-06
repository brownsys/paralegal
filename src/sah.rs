//! Semantics aware hashing for MIR slices.
//!
//! There are several weaknesses with this at the moment so it is actually not
//! used at the moment.
extern crate either;

use either::Either;

use crate::{consts, desc::*, rust::*, HashMap, HashSet, utils::LocationExt};
use rustc_middle::ty::{self, TyCtxt};
use std::cell::RefCell;

pub struct HashVerifications(usize);

impl HashVerifications {
    fn new() -> Self {
        Self(0)
    }

    fn discharge(self) {
        assert_eq!(
            self.0, 0,
            "{} verification hashes were not present or invalid. Please review, update and rerun.",
            self.0
        );
    }

    pub fn with<T, F: FnOnce(&mut Self) -> T>(f: F) -> T {
        let mut s = Self::new();
        let r = f(&mut s);
        s.discharge();
        r
    }

    #[allow(dead_code)]
    pub fn handle<'tcx>(
        &mut self,
        ann: &ExceptionAnnotation,
        tcx: TyCtxt<'tcx>,
        t: &mir::Terminator<'tcx>,
        body: &mir::Body<'tcx>,
        loc: mir::Location,
        matrix: &Matrix<'tcx>,
    ) {
        let hash = compute_verification_hash_for_stmt_2(tcx, t, loc, body, matrix);
        if let Some(old_hash) = ann.verification_hash {
            if hash != old_hash {
                self.0 += 1;
                error!("Verification hash checking failed for exception annotation. Please review the code and then paste in the updated hash \"{hash:032x}\"");
            }
        } else {
            self.0 += 1;
            error!("Exception annotation is missing a verification hash. Please submit this code for review and once approved add `{} = \"{hash:032x}\"` into the annotation.", consts::VERIFICATION_HASH_SYM.as_str());
        }
    }
}

#[derive(Clone)]
struct Reindexer<I: ReindexableWith> {
    mapper: HashMap<I::Reindexed, I::Reindexed>,
    source: I,
}

impl<I: ReindexableWith> Reindexer<I> {
    fn new(base_val: I) -> Self {
        Self {
            mapper: HashMap::new(),
            source: base_val,
        }
    }
}

trait ReindexableWith {
    type Reindexed;
    fn advance(&mut self, old: &Self::Reindexed) -> Self::Reindexed;
    fn default(&mut self) -> Self::Reindexed {
        unimplemented!()
    }
}

trait ReindexWithAdd: std::ops::Add<usize, Output = Self> + Copy {}

impl<T: ReindexWithAdd> ReindexableWith for T {
    type Reindexed = Self;
    fn advance(&mut self, _old: &T) -> T {
        let new = *self;
        *self = *self + 1;
        new
    }
    fn default(&mut self) -> T {
        *self
    }
}

impl ReindexWithAdd for mir::BasicBlock {}
impl ReindexWithAdd for mir::Local {}
impl ReindexWithAdd for mir::Promoted {}
impl ReindexWithAdd for ty::RegionVid {}

impl<I> Reindexer<I>
where
    I: ReindexableWith,
    I::Reindexed: Eq + std::hash::Hash + Copy,
{
    fn reindex(&mut self, old: I::Reindexed) -> I::Reindexed {
        let ref mut src = self.source;
        *self.mapper.entry(old).or_insert_with(|| src.advance(&old))
    }
}

impl Default for Reindexer<mir::BasicBlock> {
    fn default() -> Self {
        Reindexer::new(mir::BasicBlock::from_usize(0))
    }
}

/// A struct with the task of renaming/repayloading all MIR values of numerical
/// nature to create consistent code slices. Currently only `mir::Place` and
/// basic block indices, e.g. `mir::BasicBlock` are renamed.
struct MirReindexer<'tcx, F> {
    local_reindexer: Reindexer<mir::Local>,
    bb_reindexer: Reindexer<mir::BasicBlock>,
    promotion_reindexer: Reindexer<mir::Promoted>,
    region_reindexer: Reindexer<ty::RegionVid>,
    tcx: TyCtxt<'tcx>,
    bb_select: F,
}

impl<'tcx, F> MirReindexer<'tcx, F> {
    fn new(tcx: TyCtxt<'tcx>, basic_block_selector: F) -> Self {
        MirReindexer {
            tcx,
            local_reindexer: Reindexer::new(mir::Local::from_usize(0)),
            bb_reindexer: Reindexer::default(),
            promotion_reindexer: Reindexer::new(mir::Promoted::from_usize(0)),
            region_reindexer: Reindexer::new(ty::RegionVid::from_usize(0)),
            bb_select: basic_block_selector,
        }
    }
    fn reindex_basic_block(&mut self, bb: mir::BasicBlock) -> mir::BasicBlock
    where
        F: FnMut(mir::BasicBlock) -> Option<Option<mir::BasicBlock>>,
    {
        // TODO(hazard): THIS IS NOT CORRECT. If the return is `None`, we are
        // looking at a back edge that COULD go to a block that is contained in
        // the slice and thus might have a valid renaming!!!. But I am lazy
        // right now and don't want to split this into the multiple passes
        // required to do this properly.
        match (self.bb_select)(bb) {
            Some(Some(other)) => self.reindex_basic_block(other),
            None => DROPPED_BB,
            Some(None) => self.bb_reindexer.reindex(bb),
        }
    }
}

impl<'tcx, F> TypeFolder<'tcx> for MirReindexer<'tcx, F> {
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match r.kind() {
            ty::ReVar(v) => self
                .tcx
                .mk_region(ty::ReVar(self.region_reindexer.reindex(v))),
            _ => r,
        }
    }
}

impl<'tcx, F: FnMut(mir::BasicBlock) -> Option<Option<mir::BasicBlock>>>
    mir::visit::MutVisitor<'tcx> for MirReindexer<'tcx, F>
{
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn visit_place(
        &mut self,
        place: &mut mir::Place<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        place.local = self.local_reindexer.reindex(place.local);
        self.super_place(place, context, location);
    }
    fn visit_terminator(
        &mut self,
        terminator: &mut mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        terminator
            .successors_mut()
            .for_each(|suc| *suc = self.reindex_basic_block(*suc));
        terminator
            .unwind_mut()
            .and_then(Option::as_mut)
            .map(|s| *s = self.reindex_basic_block(*s));
        self.super_terminator(terminator, location);
    }

    fn visit_operand(&mut self, operand: &mut mir::Operand<'tcx>, location: mir::Location) {
        match operand {
            mir::Operand::Constant(op) => match op.literal {
                mir::ConstantKind::Ty(ref mut t) => {
                    let mut new_val = t.val();
                    match new_val {
                        ty::ConstKind::Unevaluated(ref mut unev) => {
                            if unev
                                .promoted
                                .as_mut()
                                .map(|p| {
                                    *p = self.promotion_reindexer.reindex(*p);
                                })
                                .is_some()
                            {
                                *t = self.tcx.mk_const(ty::ConstS {
                                    ty: t.ty(),
                                    val: new_val,
                                });
                                println!("{operand:?}");
                            };
                        }
                        _ => (),
                    }
                }
                _ => (),
            },
            _ => (),
        };
        self.super_operand(operand, location);
    }

    fn visit_const(&mut self, constant: &mut ty::Const<'tcx>, _: mir::Location) {
        let new_ty = self.fold_ty(constant.ty());
        *constant = self.tcx.mk_const(ty::ConstS {
            ty: new_ty,
            val: constant.val(),
        });
        self.super_const(constant)
    }
    /// This is necessary so that we set `user_ty` to `None` everywhere prior to
    /// hashing. The reason is that it is again a linearly generated index and
    /// it influences hashing, but has no semantic meaning to us.
    fn visit_constant(&mut self, constant: &mut mir::Constant<'tcx>, location: mir::Location) {
        constant.user_ty = None;
        self.super_constant(constant, location);
    }

    fn visit_ty(&mut self, ty: &mut ty::Ty<'tcx>, _ctx: mir::visit::TyContext) {
        *ty = self.fold_ty(*ty);
        self.super_ty(ty)
    }
    fn visit_region(&mut self, region: &mut ty::Region<'tcx>, _loc: mir::Location) {
        *region = self.fold_region(*region);
        self.super_region(region)
    }
}

enum MemoEntry<'tcx> {
    Computing,
    Dropped(Option<mir::BasicBlock>),
    Consolidated,
    Processed {
        slice: mir::BasicBlockData<'tcx>,
        self_idx: mir::BasicBlock,
    },
}

impl<'tcx> MemoEntry<'tcx> {
    fn into_processed(self) -> Option<(mir::BasicBlock, mir::BasicBlockData<'tcx>)> {
        match self {
            MemoEntry::Processed { slice, self_idx } => Some((self_idx, slice)),
            MemoEntry::Computing => unreachable!(),
            _ => None,
        }
    }
}

const DROPPED_BB: mir::BasicBlock = mir::BasicBlock::from_usize(1337);

use ty::fold::TypeFolder;

use crate::rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_query_system::ich::StableHashingContext;

#[allow(dead_code)]
fn order_independent_hash<CTX, T: HashStable<CTX>, I: Iterator<Item = T>>(
    i: I,
    hctx: &mut CTX,
    hasher: &mut StableHasher,
) {
    let n = i
        .map(|it| {
            let mut hasher = StableHasher::new();
            it.hash_stable(hctx, &mut hasher);
            hasher.finish::<u128>()
        })
        .reduce(|one, two| one.wrapping_add(two))
        .unwrap_or(0);
    n.hash_stable(hctx, hasher);
}

fn terminator_location(bb: mir::BasicBlock, dat: &mir::BasicBlockData) -> mir::Location {
    mir::Location {
        block: bb,
        statement_index: dat.statements.len(),
    }
}

fn slice_basic_block<'tcx, F: FnMut(mir::Location) -> bool>(
    mut is_contained: F,
    idx: mir::BasicBlock,
    body: &mir::BasicBlockData<'tcx>,
) -> Either<Vec<mir::Statement<'tcx>>, mir::BasicBlockData<'tcx>> {
    let termloc = terminator_location(idx, body);
    let new_stmts: Vec<mir::Statement> = body
        .statements
        .iter()
        .enumerate()
        .filter_map(|(stmtidx, stmt)| {
            let loc = mir::Location {
                block: idx,
                statement_index: stmtidx,
            };
            if is_contained(loc) {
                Some(stmt.clone())
            } else {
                None
            }
        })
        .collect();
    if is_contained(termloc) {
        Either::Right(mir::BasicBlockData {
            statements: new_stmts,
            terminator: body.terminator.clone(),
            is_cleanup: body.is_cleanup,
        })
    } else {
        Either::Left(new_stmts)
    }
}

mod graphviz_out {
    pub extern crate dot;
    use super::Either;
    use crate::rust::mir;
    use crate::HashSet;
    pub struct DotGraph<'a, 'tcx> {
        pub body: &'a mir::Body<'tcx>,
        pub loc_set: &'a HashSet<mir::Location>,
    }
    type N = mir::BasicBlock;
    type E = (mir::BasicBlock, usize, mir::BasicBlock);
    impl<'tcx, 'a> dot::GraphWalk<'a, N, E> for DotGraph<'a, 'tcx> {
        fn nodes(&'a self) -> dot::Nodes<'a, N> {
            self.body
                .basic_blocks()
                .indices()
                .collect::<Vec<_>>()
                .into()
        }
        fn edges(&'a self) -> dot::Edges<'a, E> {
            self.body
                .basic_blocks()
                .iter_enumerated()
                .flat_map(|(bb, bbdat)| {
                    bbdat
                        .terminator()
                        .successors()
                        .enumerate()
                        .map(move |(i, s)| (bb, i, s))
                })
                .collect::<Vec<_>>()
                .into()
        }
        fn source(&'a self, edge: &E) -> N {
            edge.0
        }
        fn target(&'a self, edge: &E) -> N {
            edge.2
        }
    }
    impl<'tcx, 'a> dot::Labeller<'a, N, E> for DotGraph<'a, 'tcx> {
        fn graph_id(&'a self) -> dot::Id<'a> {
            dot::Id::new("g").unwrap()
        }
        fn node_id(&'a self, n: &N) -> dot::Id<'a> {
            dot::Id::new(format!("{:?}", n)).unwrap()
        }
        fn node_label(&'a self, bb: &N) -> dot::LabelText<'a> {
            use std::fmt::Write;
            let bbdat = &self.body.basic_blocks()[*bb];
            let (stmts, term) =
                match super::slice_basic_block(|l| self.loc_set.contains(&l), *bb, &bbdat) {
                    Either::Left(stmts) => (stmts, None),
                    Either::Right(bbdat) => (bbdat.statements, bbdat.terminator),
                };
            let mut label = String::new();
            writeln!(label, "{bb:?}").unwrap();
            for s in stmts.iter() {
                writeln!(label, "{:?}", s.kind).unwrap();
            }
            if let Some(t) = term {
                writeln!(label, "{:?}", t.kind).unwrap();
            }
            dot::LabelText::LabelStr(label.into())
        }
        fn edge_label(&'a self, e: &E) -> dot::LabelText<'a> {
            dot::LabelText::LabelStr(format!("{:?}", e.1).into())
        }
    }
}

pub type Matrix<'tcx> = flowistry::infoflow::FlowDomainMatrix<'tcx>;

#[allow(dead_code)]
pub fn compute_verification_hash_for_stmt_2<'tcx>(
    tcx: TyCtxt<'tcx>,
    t: &mir::Terminator<'tcx>,
    loc: mir::Location,
    body: &mir::Body<'tcx>,
    matrix: &Matrix<'tcx>,
) -> VerificationHash {
    use mir::visit::Visitor;

    let mut hasher = StableHasher::new();
    tcx.create_stable_hashing_context()
        .while_hashing_spans(false, |hctx| {
            use mir::visit::MutVisitor;
            let mut loc_set = HashSet::<mir::Location>::new();
            crate::utils::PlaceVisitor(|pl: &mir::Place<'tcx>| {
                loc_set.extend(
                    matrix
                        .row(*pl)
                        .filter(|l| l.is_real(body)),
                );
            })
            .visit_terminator(t, loc);

            let memoization = RefCell::new(HashMap::new());
            let mut basic_renamer =
                MirReindexer::new(tcx, |bb| match memoization.borrow().get(&bb) {
                    Some(MemoEntry::Dropped(Some(other))) => Some(Some(*other)),
                    None | Some(MemoEntry::Dropped(None)) => None,
                    _ => Some(None),
                });

            // I am not 100% sure that using postorder here actually gives a
            // consistent ordering over the slice. To be absolutely correct the
            // self renaming should happen in a second pass following only the
            // connections that are actually in the slice.
            mir::traversal::postorder(body).for_each(|(bb, bbdat)| {
                memoization.borrow_mut().insert(bb, MemoEntry::Computing);
                let new_entry = match slice_basic_block(|l| loc_set.contains(&l), bb, bbdat)
                    .left_and_then(|consolidate| {
                        let mut memoization = memoization.borrow_mut();
                        let its = bbdat
                            .terminator()
                            .successors()
                            .filter_map(|s| memoization.get(&s).map(|v| (s, v)))
                            .filter_map(|(s, entry)| match entry {
                                MemoEntry::Processed { .. } => Some(s),
                                MemoEntry::Computing | MemoEntry::Consolidated => {
                                    unreachable!("{bb:?} -> {s:?}")
                                }
                                MemoEntry::Dropped(next) => *next,
                            })
                            .collect::<Vec<_>>();
                        assert!(its.len() <= 1);
                        if consolidate.is_empty() {
                            Either::Left(its.first().copied())
                        } else {
                            let s = its.first().unwrap();
                            let (_, mut slice) = std::mem::replace(
                                memoization.get_mut(&s).unwrap(),
                                MemoEntry::Consolidated,
                            )
                            .into_processed()
                            .unwrap();
                            if !consolidate.is_empty() {
                                slice.statements = consolidate
                                    .into_iter()
                                    .chain(slice.statements.iter().cloned())
                                    .collect();
                            }
                            Either::Right(slice)
                        }
                    }) {
                    Either::Right(mut slice) => {
                        // Otherwise we're double renaming it on consolidation
                        let self_idx = basic_renamer.bb_reindexer.reindex(bb);
                        basic_renamer.visit_basic_block_data(bb, &mut slice);

                        MemoEntry::Processed { self_idx, slice }
                    }
                    Either::Left(mnext) => MemoEntry::Dropped(mnext),
                };

                memoization.borrow_mut().insert(bb, new_entry);
            });

            let mut complete_slice = memoization
                .take()
                .into_iter()
                .filter_map(|(_, v)| v.into_processed())
                .collect::<Vec<_>>();
            complete_slice.sort_by_key(|p| p.0);
            // Maltes genius idea of just hashing the slice, because that
            // doesn't contain any of the hidden values that have inconsistent
            // ids
            use std::fmt::Write;
            let mut buf = String::new();
            for (bb, bbdat) in complete_slice.iter() {
                for stmt in bbdat.statements.iter() {
                    write!(buf, "{:?}", stmt.kind).unwrap();
                    buf.hash_stable(hctx, &mut hasher);
                    buf.clear();
                }
                let term = bbdat.terminator();
                write!(buf, "{:?}", term.kind).unwrap();
                buf.hash_stable(hctx, &mut hasher);
                buf.clear();
                let termloc = terminator_location(*bb, bbdat);
                ExternalDependencyHasher::new(tcx, &mut hasher, hctx)
                    .visit_terminator(term, termloc);
            }
        });
    hasher.finish()
}

struct ExternalDependencyHasher<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    hasher: &'a mut StableHasher,
    hctx: &'a mut StableHashingContext<'tcx>,
}

impl<'tcx, 'a> ExternalDependencyHasher<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        hasher: &'a mut StableHasher,
        hctx: &'a mut StableHashingContext<'tcx>,
    ) -> Self {
        Self { tcx, hasher, hctx }
    }
}

impl<'tcx, 'a> ty::TypeVisitor<'tcx> for ExternalDependencyHasher<'tcx, 'a> {
    fn visit_ty(&mut self, t: ty::Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        use ty::{TyKind::*, TypeFoldable};
        match t.kind() {
            Foreign(did)
            | FnDef(did, _)
            | Closure(did, _)
            | Generator(did, _, _)
            | Opaque(did, _) => {
                if let Some(ldid) = did.as_local() {
                    flowistry::mir::borrowck_facts::get_body_with_borrowck_facts(self.tcx, ldid)
                        .body
                        .hash_stable(self.hctx, self.hasher);
                } else {
                    use crate::rust::rustc_middle::dep_graph::DepContext;
                    self.tcx.dep_graph().with_query(|_g| 
                        // ???
                        ());
                }
            }
            _ => (),
        }
        t.super_visit_with(self)
    }
}

impl<'tcx, 'a> mir::visit::Visitor<'tcx> for ExternalDependencyHasher<'tcx, 'a> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>, _ctx: mir::visit::TyContext) {
        <Self as ty::TypeVisitor>::visit_ty(self, ty);
    }
}

#[allow(dead_code)]
fn quick_hash<CTX, T: HashStable<CTX>>(dat: &T, hctx: &mut CTX) -> VerificationHash {
    let mut h = StableHasher::new();
    dat.hash_stable(hctx, &mut h);
    h.finish()
}
