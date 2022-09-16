/// Semantics aware hashing for MIR slices.
extern crate either;
extern crate dot;

use either::Either;

use crate::desc::*;
use crate::rust::*;
use crate::{HashMap, HashSet};
use rustc_middle::{
    hir::nested_filter::OnlyBodies,
    ty::{self, TyCtxt},
};
use std::cell::RefCell;

use flowistry::indexed::{impls::LocationDomain, IndexedDomain};

/// A struct that can be used to apply a `FnMut` to every `Place` in a MIR
/// object via the `visit::MutVisitor` trait. Crucial difference to
/// `PlaceVisitor` is that this function can alter the place itself.
struct RePlacer<'tcx, F>(TyCtxt<'tcx>, F);

impl<'tcx, F: FnMut(&mut mir::Place<'tcx>)> mir::visit::MutVisitor<'tcx> for RePlacer<'tcx, F> {
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.0
    }
    fn visit_place(
        &mut self,
        place: &mut mir::Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        self.1(place)
    }
}

#[derive(Clone)]
struct Reindexer<I> {
    mapper: HashMap<I, I>,
    source: I,
    is_fixed: bool,
}

impl<I> Reindexer<I> {
    fn new(base_val: I) -> Self {
        Self {
            mapper: HashMap::new(),
            source: base_val,
            is_fixed: false,
        }
    }

    fn reindex(&mut self, old: I) -> I
    where
        I: Eq + std::hash::Hash + std::ops::Add<usize, Output = I> + Copy,
    {
        if self.is_fixed {
            *self.mapper.get(&old).unwrap_or(&self.source)
        } else {
            let ref mut src = self.source;
            *self.mapper.entry(old).or_insert_with(|| {
                let entry = *src;
                *src = entry + 1;
                entry
            })
        }
    }

    fn seal(&mut self) {
        self.is_fixed = true;
    }

    fn unseal(&mut self) {
        self.is_fixed = false;
    }

    fn make_fixed<It: Iterator<Item = I>>(src: It, mut base: I, default: Option<I>) -> Self
    where
        I: Eq + std::hash::Hash + std::ops::Add<usize, Output = I> + Copy,
    {
        let mapper = src
            .zip(std::iter::repeat_with(|| {
                let ret = base;
                base = base + 1;
                ret
            }))
            .collect();
        Self {
            mapper,
            source: default.unwrap_or(base),
            is_fixed: true,
        }
    }

    fn set_reindex(&mut self, from: I, to: I)
    where
        I: Eq + std::hash::Hash,
    {
        assert!(self.mapper.insert(from, to).is_none())
    }
}

impl Default for Reindexer<mir::BasicBlock> {
    fn default() -> Self {
        Reindexer::new(mir::BasicBlock::from_usize(1000))
    }
}

/// A struct with the task of renaming/repayloading all MIR values of numerical
/// nature to create consistent code slices. Currently only `mir::Place` and
/// basic block indices, e.g. `mir::BasicBlock` are renamed.
struct MirReindexer<'tcx> {
    local_reindexer: Reindexer<mir::Local>,
    bb_reindexer: Reindexer<mir::BasicBlock>,
    promotion_reindexer: Reindexer<mir::Promoted>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MirReindexer<'tcx> {
    fn derived(&self) -> Self {
        MirReindexer {
            local_reindexer: self.local_reindexer.clone(),
            bb_reindexer: Reindexer::default(),
            promotion_reindexer: self.promotion_reindexer.clone(),
            tcx: self.tcx,
        }
    }
}

impl<'tcx> MirReindexer<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        MirReindexer {
            tcx,
            local_reindexer: Reindexer::new(mir::Local::from_usize(0)),
            bb_reindexer: Reindexer::default(),
            promotion_reindexer: Reindexer::new(mir::Promoted::from_usize(10)),
        }
    }
}

impl<'tcx> mir::visit::MutVisitor<'tcx> for MirReindexer<'tcx> {
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
            .for_each(|suc| *suc = self.bb_reindexer.reindex(*suc));
        terminator
            .unwind_mut()
            .and_then(Option::as_mut)
            .map(|s| *s = self.bb_reindexer.reindex(*s));
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
}

enum MemoEntry<'tcx> {
    Computing,
    Dropped,
    Consolidated,
    Processed {
        slice: mir::BasicBlockData<'tcx>,
        hash: VerificationHash,
        self_idx: mir::BasicBlock,
    },
}

impl<'tcx> MemoEntry<'tcx> {
    fn into_processed(self) -> Option<(mir::BasicBlock, mir::BasicBlockData<'tcx>)> {
        match self {
            MemoEntry::Processed { slice, self_idx, .. } => Some((self_idx, slice)),
            MemoEntry::Computing => unreachable!(),
            _ => None,
        }
    }
}

struct BasicBlockSlicingAwareReindexer<'tcx, 'a> {
    generic_reindexer: &'a mut MirReindexer<'tcx>,
    bb_map: &'a HashMap<mir::BasicBlock, MemoEntry<'tcx>>,
}

const DROPPED_BB: mir::BasicBlock = mir::BasicBlock::from_usize(1337);

impl<'tcx, 'a> BasicBlockSlicingAwareReindexer<'tcx, 'a> {
    fn new(
        generic_reindexer: &'a mut MirReindexer<'tcx>,
        bb_map: &'a HashMap<mir::BasicBlock, MemoEntry<'tcx>>,
    ) -> Self {
        Self {
            generic_reindexer,
            bb_map,
        }
    }
    fn reindex_basic_block(&mut self, bb: mir::BasicBlock) -> mir::BasicBlock {
        // TODO(hazard): THIS IS NOT CORRECT. If the return is `None`, we are
        // looking at a back edge that COULD go to a block that is contained in
        // the slice and thus might have a valid renaming!!!. But I am lazy
        // right now and don't want to split this into the multiple passes
        // required to do this properly.
        match self.bb_map.get(&bb) {
            Some(MemoEntry::Dropped) | None => DROPPED_BB,
            _ => self.generic_reindexer.bb_reindexer.reindex(bb),
        }
    }
}

impl<'tcx, 'a> mir::visit::MutVisitor<'tcx> for BasicBlockSlicingAwareReindexer<'tcx, 'a> {
    fn tcx<'b>(&'b self) -> TyCtxt<'tcx> {
        self.generic_reindexer.tcx
    }
    fn visit_place(
        &mut self,
        place: &mut mir::Place<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        self.generic_reindexer.visit_place(place, context, location)
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
        self.generic_reindexer.visit_operand(operand, location);
    }
}

use crate::rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_query_system::ich::StableHashingContext;

fn order_independent_hash<CTX, T: HashStable<CTX>, I: Iterator<Item = T>>(
    mut i: I,
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

fn slice_basic_block<'tcx, F: FnMut(mir::Location) -> bool>(
    mut is_contained: F,
    idx: mir::BasicBlock,
    body: &mir::BasicBlockData<'tcx>,
) -> Either<Vec<mir::Statement<'tcx>>, mir::BasicBlockData<'tcx>> {
    let termidx = body.statements.len();
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
    let termloc = mir::Location {
        block: idx,
        statement_index: termidx,
    };
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

pub fn compute_verification_hash_for_stmt_2<'tcx>(
    tcx: TyCtxt<'tcx>,
    t: &mir::Terminator<'tcx>,
    loc: mir::Location,
    body: &mir::Body<'tcx>,
    loc_dom: &LocationDomain,
    matrix: &<flowistry::infoflow::FlowAnalysis<'_, 'tcx> as rustc_mir_dataflow::AnalysisDomain<
        'tcx,
    >>::Domain,
) -> VerificationHash {
    use mir::visit::Visitor;
    use std::io::Write;

    let mut hasher = StableHasher::new();
    let out_prefix = std::env::var("DBG_FILE_PREFIX").unwrap_or("".to_string());
    let mut out = std::fs::OpenOptions::new()
        .write(true)
        .truncate(true)
        .create(true)
        .open(out_prefix.clone() + "sliced.txt")
        .unwrap();
    let mut hash_out = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(out_prefix.clone() + "hashes.txt")
        .unwrap();
    tcx.create_stable_hashing_context()
        .while_hashing_spans(false, |hctx| {
            use mir::visit::MutVisitor;
            let mut loc_set = HashSet::<mir::Location>::new();
            crate::ana::PlaceVisitor(|pl: &mir::Place<'tcx>| {
                loc_set.extend(
                    matrix
                        .row(*pl)
                        .filter(|l| crate::ana::is_real_location(loc_dom, body, **l)),
                );
            })
            .visit_terminator(t, loc);

            struct DotGraph<'a, 'tcx> {
                body: &'a mir::Body<'tcx>,
                loc_set: &'a HashSet<mir::Location>,
            }
            type N = mir::BasicBlock;
            type E = (mir::BasicBlock, usize, mir::BasicBlock);
            impl <'tcx, 'a> dot::GraphWalk<'a, N, E> for DotGraph<'a, 'tcx> {
                fn nodes(&'a self) -> dot::Nodes<'a, N> {
                    self.body.basic_blocks().indices().collect::<Vec<_>>().into()
                }
                fn edges(&'a self) -> dot::Edges<'a, E> {
                    self.body.basic_blocks().iter_enumerated().flat_map(|(bb, bbdat)| bbdat.terminator().successors().enumerate().map(move |(i, s)| (bb, i, s))).collect::<Vec<_>>().into()
                }
                fn source(&'a self, edge: &E) -> N {
                    edge.0
                }
                fn target(&'a self, edge: &E) -> N {
                    edge.2
                }
            }
            impl <'tcx, 'a> dot::Labeller<'a, N, E> for DotGraph<'a, 'tcx> {
                fn graph_id(&'a self) -> dot::Id<'a> {
                    dot::Id::new("g").unwrap()
                }
                fn node_id(&'a self, n: &N) -> dot::Id<'a> {
                    dot::Id::new(format!("{:?}", n)).unwrap()
                }
                fn node_label(&'a self, bb: &N) -> dot::LabelText<'a> {
                    use std::fmt::Write;
                    let bbdat = &self.body.basic_blocks()[*bb];
                    let (stmts, term) = match slice_basic_block(|l| self.loc_set.contains(&l), *bb, &bbdat) {
                        Either::Left(stmts) => (stmts, None),
                        Either::Right(bbdat) => (bbdat.statements, bbdat.terminator),
                    };
                    let mut label = String::new();
                    for s in stmts.iter() {
                        writeln!(label, "{:?}", s.kind);
                    }
                    if let Some(t) = term {
                        writeln!(label, "{:?}", t.kind);
                    }
                    dot::LabelText::LabelStr(label.into())
                }
                fn edge_label(&'a self, e: &E) -> dot::LabelText<'a> {
                    dot::LabelText::LabelStr(format!("{:?}", e.1).into())
                }
            }

            dot::render(
                &DotGraph {
                    body, loc_set: &loc_set
                },
                &mut std::fs::OpenOptions::new().write(true).create(true).truncate(true).open(out_prefix + "slice.gv").unwrap(),
            ).unwrap();

            let mut memoization = HashMap::new();
            let mut basic_renamer = MirReindexer::new(tcx);
            mir::traversal::postorder(body).for_each(|(bb, bbdat)| {
                memoization.insert(bb, MemoEntry::Computing);
                let new_entry = if let Some(slice) =
                    match slice_basic_block(|l| loc_set.contains(&l), bb, bbdat) {
                        Either::Left(consolidate) => {
                            let its = bbdat
                                .terminator()
                                .successors()
                                .filter_map(|s| memoization.get(&s).map(|v| (s, v)))
                                .filter_map(|(s, entry)| match entry {
                                    MemoEntry::Processed { .. } => Some(s),
                                    MemoEntry::Computing | MemoEntry::Consolidated => {
                                        unreachable!()
                                    }
                                    _ => None,
                                }).collect::<Vec<_>>();
                            if let Some(s) = its.first() {
                                let (_, mut slice) = std::mem::replace(
                                    memoization.get_mut(&s).unwrap(),
                                    MemoEntry::Consolidated,
                                ).into_processed().unwrap();
                                assert_eq!(its.len(), 1);
                                if !consolidate.is_empty() {
                                    slice.statements = consolidate
                                        .into_iter()
                                        .chain(slice.statements.iter().cloned())
                                        .collect();
                                }
                                Some(slice)
                            } else {
                                assert!(consolidate.is_empty());
                                None
                            }
                        }
                        Either::Right(done) => Some(done),
                    } {
                    // Otherwise we're double renaming it on consolidation
                    let mut for_hashing = slice.clone();
                    let self_idx = basic_renamer.bb_reindexer.reindex(bb);
                    BasicBlockSlicingAwareReindexer::new(&mut basic_renamer, &mut memoization)
                        .visit_basic_block_data(bb, &mut for_hashing);
                    writeln!(out, "{bb:?}");
                    for stmt in for_hashing.statements.iter() {
                        writeln!(out, "{:?}", stmt.kind).unwrap();
                    }

                    writeln!(out, "{:?}", for_hashing.terminator().kind).unwrap();
                    let mut hasher = StableHasher::new();
                    for_hashing.hash_stable(hctx, &mut hasher);
                    slice.terminator().successors().for_each(|s| {
                        if let Some(entry) = memoization.get(&s) {
                            match entry {
                                MemoEntry::Processed { hash, .. } => {
                                    hash.hash_stable(hctx, &mut hasher)
                                }
                                _ => (),
                            }
                        }
                    });
                    let hash = hasher.finish();
                    writeln!(hash_out, "{bb:?} {hash:?}").unwrap();
                    MemoEntry::Processed {
                        self_idx,
                        slice,
                        hash,
                    }
                } else {
                    MemoEntry::Dropped
                };

                memoization.insert(bb, new_entry);
            });

            let mut complete_slice = memoization
                .into_iter()
                .filter_map(|(_, v)| v.into_processed())
                .collect::<Vec<_>>();
            complete_slice.sort_by_key(|p| p.0);
            complete_slice.hash_stable(hctx, &mut hasher)
        });
    hasher.finish()
}

// pub fn compute_verification_hash_for_stmt<'tcx>(
//     tcx: TyCtxt<'tcx>,
//     t: &mir::Terminator<'tcx>,
//     loc: mir::Location,
//     body: &mir::Body<'tcx>,
//     loc_dom: &LocationDomain,
//     matrix: &<flowistry::infoflow::FlowAnalysis<'_, 'tcx> as rustc_mir_dataflow::AnalysisDomain<
//         'tcx,
//     >>::Domain,
// ) -> VerificationHash {
//     use mir::visit::Visitor;
//     use std::io::Write;
//     let mut final_hash = 0;
//     tcx.create_stable_hashing_context().while_hashing_spans(false, |mut hctx|{

//         use mir::visit::MutVisitor;
//         let mut loc_set = HashSet::<mir::Location>::new();
//         let mut vis = crate::ana::PlaceVisitor(|pl: &mir::Place<'tcx>| {
//             loc_set.extend(matrix.row(*pl).filter(|l| crate::ana::is_real_location(loc_dom, body, **l)));
//         });

//         vis.visit_terminator(t, loc);
//         let mut replacer = MirReindexer::new(tcx);
//         let out_prefix = std::env::var("DBG_FILE_PREFIX").unwrap_or("".to_string());
//         let mut out = RefCell::new(std::fs::OpenOptions::new().write(true).truncate(true).create(true).open(out_prefix.clone() + "sliced.txt").unwrap());

//         let global_renamer = RefCell::new(MirReindexer::new(tcx));

//         // This computation does two things at one. It takes all basic
//         // blocks, creating a slice over each with respect to the program
//         // location of interest. Then it immediately hashes all interesting
//         // locations. As a result it never needs to materialize the actual
//         // slice but only its hash.
//         //
//         // Read the Notion to know more about this https://www.notion.so/justus-adam/Attestation-Hash-shouldn-t-change-if-unrelated-statements-change-19f4b036d85643b4ae6a9b8358e3cb70#7c35960849524580b720d3207c70004f
//         type Slices<'a, 'tcx> = LazyTree<'a, mir::BasicBlock, SliceResult<'tcx>>;
//         let slice_maker = |bbidx: &mir::BasicBlock, tree: &mut Slices<'_, 'tcx>| {
//             let bbdat = &body.basic_blocks()[*bbidx];
//             let termidx = bbdat.statements.len();
//             let mut new_stmts : Vec<mir::Statement> = bbdat.statements.iter().enumerate().filter_map(|(stmtidx, stmt)| {
//                 let loc = mir::Location {block: *bbidx, statement_index: stmtidx};
//                 if loc_set.contains(&loc) {
//                     Some(stmt.clone())
//                 } else {
//                     None
//                 }
//             }).collect();
//             let termloc = mir::Location {block: *bbidx, statement_index: termidx};
//             if loc_set.contains(&termloc) {
//                 let mut renamer_may = None;
//                 let mut dom = *bbidx;
//                 let mut parents = None;
//                 while renamer_may.is_none() {
//                     dom = body.dominators().immediate_dominator(dom);
//                     renamer_may = if dom == *bbidx {
//                         Some(MirReindexer::new(tcx))
//                     } else {
//                         match tree.get(&dom) {
//                             SliceResult::Dropped => None,
//                             SliceResult::Sliced{ renamer, .. } => Some(renamer.derived()),
//                             SliceResult::Consolidate(stmts, p) => {
//                                 assert!(!stmts.is_empty());
//                                 new_stmts = stmts.drain(..).chain(new_stmts.into_iter()).collect();
//                                 (*global_renamer.borrow_mut()).set_renaming(p, *bbidx);
//                                 None
//                             }
//                         }
//                     };
//                 }
//                 let mut renamer = renamer_may.unwrap();
//                 let mut new_block = mir::BasicBlockData {
//                     statements: new_stmts,
//                     terminator: bbdat.terminator.clone(),
//                     is_cleanup: bbdat.is_cleanup,
//                 };
//                 let self_idx = global_renamer.borrow_mut().bb_reindexer.reindex(*bbidx);
//                 let mut out = out.borrow_mut();
//                 for stmt in new_block.statements.iter() {
//                     writeln!(out, "{:?}", stmt.kind).unwrap();
//                 }

//                 writeln!(out, "{:?}", new_block.terminator().kind).unwrap();
//                 SliceResult::Sliced{ slice: new_block, renamer }
//             } else if !new_stmts.is_empty() {
//                 SliceResult::Consolidate(new_stmts, bbidx)
//             } else {
//                 SliceResult::Dropped
//             }
//         };
//         let hash_out = RefCell::new(std::fs::OpenOptions::new().create(true).write(true).truncate(true).open(out_prefix + "hashes.txt").unwrap());
//         let mut slice : RefCell<Slices> = RefCell::new(LazyTree::new(&slice_maker));
//         let hctx_cell = RefCell::new(hctx);
//         global_renamer.borrow_mut().seal();
//         type Hashes<'a, 'tcx> = LazyTree<'a, mir::BasicBlock, Option<VerificationHash>>;
//         let hashes_maker = |bb : &mir::BasicBlock, tree: &mut Hashes<'_, 'tcx>| {
//             /* This is a bit dangerous. I've added this filter because it is possible you are transitively in your own successors. However there could be other things wrong with the code that could also cause that situation which this would ignore. */
//             /* This encodes the order of successors so we preserve it. I use an addition of the index after filtering non-hashed successors because this just so happens to propagate the successor hash unchanged in the case where we are a consolidated basic block with only one successor.  */
//             let h = (&body.basic_blocks()[*bb]).terminator().successors().filter(|b| b != bb).filter_map(|b| tree.get_may(&b).and_then(|o| o.as_ref()).map(|b| *b)).enumerate().map(|(i, h)| h.wrapping_add(i as u128)).reduce(|a, b| a.wrapping_add(b));
//             let hash = slice.borrow_mut().get(bb).slice_may().map_or(h, |b| {
//                 let mut g_renamer = global_renamer.borrow_mut();
//                 g_renamer.visit_basic_block_data(*bb, &mut b);
//                 let mut hasher = StableHasher::new();
//                 b.hash_stable(&mut hctx_cell.borrow_mut(), &mut hasher);
//                 h.map(|h| h.hash_stable(&mut hctx_cell.borrow_mut(), &mut hasher));
//                 let hash = hasher.finish();
//                 writeln!(hash_out.borrow_mut(), "{hash:?}").unwrap();
//                 Some(hash)
//             });
//             hash
//         };
//         let mut hashes : Hashes<'_, 'tcx> = LazyTree::new(&hashes_maker);

//         final_hash = hashes.get(&mir::START_BLOCK).unwrap();
//     });
//     final_hash
// }

enum SliceResult<'tcx> {
    Dropped,
    Sliced {
        slice: mir::BasicBlockData<'tcx>,
        renamer: MirReindexer<'tcx>,
    },
    Consolidate(Vec<mir::Statement<'tcx>>, mir::BasicBlock),
}

impl<'tcx> SliceResult<'tcx> {
    fn slice_may(&self) -> Option<&mir::BasicBlockData<'tcx>> {
        match self {
            SliceResult::Sliced { slice, .. } => Some(slice),
            _ => None,
        }
    }
}

/// This structure allows you to use knot-tying to compute values that depend on
/// each other. The laziness is quite convenient, because it means you can focus
/// on just one element at a time and assume that all others have already been
/// computed. This is done by invoking `get` in the `make` function to recurse.
/// However there is a caveat, you have to ensure that you traverse this
/// hierarchy in only one direction at a time or that you early initialize a
/// value (using `init`), otherwise you will create an infinite loop.
struct LazyTree<'a, I, P> {
    tree: HashMap<I, Option<P>>,
    make: &'a dyn Fn(&I, &mut Self) -> P,
}

impl<'a, I: Eq + std::hash::Hash + Clone, P> LazyTree<'a, I, P> {
    fn new<F: Fn(&I, &mut Self) -> P>(make: &'a F) -> Self {
        Self {
            tree: HashMap::new(),
            make,
        }
    }

    fn get_may<'b>(&'b mut self, i: &I) -> Option<&'b mut P> {
        if !self.tree.contains_key(&i) {
            let f = self.make;
            self.tree.insert(i.clone(), None);
            let v = f(i, self);
            assert!(self
                .tree
                .insert(i.clone(), Some(v))
                .as_ref()
                .map_or(false, Option::is_none));
        };
        self.tree.get_mut(i).unwrap().as_mut()
    }

    fn get(&mut self, i: &I) -> &mut P {
        self.get_may(i).expect("Still initializing")
    }
}
