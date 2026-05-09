//! Helpers that compile per-`DefId` metadata for the SPDG output
//! ([`DefInfo`], spans, paths) and for the per-instruction sanity checks.
//!
//! Pure metadata extraction — no PDG construction logic lives here.

use crate::{
    MarkerCtx,
    desc::*,
    utils::{identifier_for_item, ty_of_const, type_as_fn},
};

use rustc_hir::{self as hir, def, def_id::DefId};
use rustc_middle::{mir as rustc_mir, ty::TyCtxt};
use rustc_span::Span as RustSpan;

pub(super) fn src_loc_for_span(span: RustSpan, tcx: TyCtxt) -> Span {
    let (source_file, start_line, start_col, end_line, end_col) =
        tcx.sess.source_map().span_to_location_info(span);
    let file_path = source_file.map_or_else(
        || "<unknown>".to_string(),
        |f| f.name.prefer_local_unconditionally().to_string(),
    );
    let abs_file_path = if !file_path.starts_with('/') {
        std::env::current_dir()
            .expect("failed to obtain current working directory")
            .join(&file_path)
    } else {
        std::path::PathBuf::from(&file_path)
    };
    let src_info = SourceFileInfo {
        file_path,
        abs_file_path,
    };
    Span {
        source_file: src_info.intern(),
        start: SpanCoord {
            line: start_line as u32,
            col: start_col as u32,
        },
        end: SpanCoord {
            line: end_line as u32,
            col: end_col as u32,
        },
    }
}

/// Checks the invariant that [`super::driver::SPDGGenerator::collect_type_info`]
/// should produce a map that is a superset of the types found in all the
/// `types` maps on [`SPDG`].
pub(super) fn type_info_sanity_check(controllers: &ControllerMap, types: &TypeInfoMap) {
    controllers
        .values()
        .flat_map(|spdg| spdg.type_assigns.values())
        .flat_map(|types| types.0.iter())
        .for_each(|t| {
            assert!(
                types.contains_key(t),
                "Invariant broken: Type {t:?} is not present in type map"
            );
        })
}

pub(super) fn def_kind_for_item(id: DefId, tcx: TyCtxt) -> DefKind {
    #[allow(deprecated)]
    match tcx.def_kind(id) {
        _ if tcx.is_coroutine(id) => DefKind::Generator,
        def::DefKind::Closure => DefKind::Closure,
        kind if kind.is_fn_like() => DefKind::Fn,
        def::DefKind::Struct
        | def::DefKind::AssocTy
        | def::DefKind::OpaqueTy
        | def::DefKind::TyAlias
        | def::DefKind::Enum => DefKind::Type,
        def::DefKind::Ctor { .. } => DefKind::Ctor,
        kind => unreachable!("{} ({:?})", tcx.def_path_debug_str(id), kind),
    }
}

pub(super) fn path_for_item(id: DefId, tcx: TyCtxt) -> Box<[Identifier]> {
    let def_path = tcx.def_path(id);
    std::iter::once(Identifier::new(tcx.crate_name(def_path.krate)))
        .chain(def_path.data.iter().filter_map(|segment| {
            use hir::definitions::DefPathDataName::*;
            match segment.data.name() {
                Named(sym) => Some(Identifier::new(sym)),
                Anon { .. } => None,
            }
        }))
        .collect()
}

pub(super) fn def_info_for_item(id: DefId, markers: &MarkerCtx, tcx: TyCtxt) -> DefInfo {
    let name = identifier_for_item(tcx, id);
    let kind = def_kind_for_item(id, tcx);
    DefInfo {
        name,
        path: path_for_item(id, tcx),
        kind,
        src_info: src_loc_for_span(tcx.def_span(id), tcx),
        markers: markers
            .all_markers_on_item(id)
            .map(|ann| paralegal_pdg::MarkerAnnotation {
                marker: ann.marker,
                on_return: ann.refinement.on_return(),
                on_argument: ann.refinement.on_argument(),
            })
            .collect(),
    }
}

/// Best-effort resolution of the [`DefId`] of a function being called by a
/// [`Terminator`]. "Dirty" because it does not consider trait dispatch — only
/// constants resolved at the call site.
pub(super) fn dirty_try_resolve_func_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    term: &rustc_mir::Terminator<'tcx>,
) -> Option<DefId> {
    let rustc_mir::TerminatorKind::Call { func, .. } = &term.kind else {
        return None;
    };
    let c = func.constant()?;
    let (id, _) = type_as_fn(tcx, ty_of_const(c)).to_option()?;
    Some(id)
}
