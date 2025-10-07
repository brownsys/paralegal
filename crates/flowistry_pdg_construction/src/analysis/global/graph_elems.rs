//! The representation of the PDG.

use std::{
    fmt::{self, Display},
    hash::Hash,
};

use internment::Intern;

use flowistry_pdg::{Constant, RichLocation};
pub use flowistry_pdg::{SourceUse, TargetUse};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Location, Place},
    ty::TyCtxt,
};
use rustc_span::Span;
use rustc_utils::PlaceExt;

pub use super::partial_graph::PartialGraph;
use crate::constants::PlaceOrConst;

/// Usually a location in a MIR body but can also cross "one hop" into a called function.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct OneHopLocation {
    /// The point in the execution of the program.
    pub location: RichLocation,
    /// If this is actually a place in a called function, then this refes to the
    /// function that was called and whether it refers to the start or end
    /// location in that function. In that case `at` refers to the location at
    /// which the function call occurs in the parent.
    pub in_child: Option<(DefId, bool)>,
}

impl fmt::Display for OneHopLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.location)?;
        if let Some((_, is_start)) = self.in_child {
            write!(f, " -> {}", if is_start { "start" } else { "end" })?;
        }
        Ok(())
    }
}

impl From<RichLocation> for OneHopLocation {
    fn from(location: RichLocation) -> Self {
        OneHopLocation {
            location,
            in_child: None,
        }
    }
}

impl From<Location> for OneHopLocation {
    fn from(at: Location) -> Self {
        OneHopLocation {
            location: RichLocation::Location(at),
            in_child: None,
        }
    }
}

impl<T: Copy> From<&'_ T> for OneHopLocation
where
    OneHopLocation: From<T>,
{
    fn from(at: &'_ T) -> Self {
        OneHopLocation::from(*at)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DepNodePlaceKind<'tcx> {
    pub place: Place<'tcx>,
    /// Pretty representation of the place.
    /// This is cached as an interned string on [`DepNode`] because to compute it later,
    /// we would have to regenerate the entire monomorphized body for a given place.
    pub(crate) place_pretty: Option<Intern<String>>,
    /// Does the PDG track subplaces of this place?
    pub is_split: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DepNodeKind<'tcx> {
    Place(DepNodePlaceKind<'tcx>),
    Const(Constant),
}

/// A node in the program dependency graph.
///
/// Represents a place at a particular call-string.
/// The place is in the body of the root of the call-string.
#[derive(Clone, Debug)]
pub struct DepNode<'tcx, Loc> {
    pub kind: DepNodeKind<'tcx>,

    /// Location of the place in the program.
    pub at: Loc,
    pub span: Span,
}

impl<Loc: PartialEq> PartialEq for DepNode<'_, Loc> {
    fn eq(&self, other: &Self) -> bool {
        // Using an explicit match here with all fields, so that should new
        // fields be added we remember to check whether they need to be included
        // here.
        let Self { at, kind, span } = self;
        let eq = match (kind, &other.kind) {
            (
                DepNodeKind::Place(DepNodePlaceKind {
                    place,
                    place_pretty: _,
                    is_split,
                }),
                DepNodeKind::Place(other_kind),
            ) => {
                let eq = (place, at).eq(&(&other_kind.place, &other.at));
                if eq {
                    debug_assert_eq!(is_split, &other_kind.is_split);
                }
                eq
            }
            (k1, k2) => at == &other.at && k1 == k2,
        };
        if eq {
            debug_assert_eq!(span, &other.span);
        }
        eq
    }
}

impl<Loc: Eq> Eq for DepNode<'_, Loc> {}

impl<Loc: Hash> Hash for DepNode<'_, Loc> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Using an explicit match here with all fields, so that should new
        // fields be added we remember to check whether they need to be included
        // here.
        let place_or_const = match &self.kind {
            DepNodeKind::Const(c) => Ok(c),
            DepNodeKind::Place(p) => Err(p.place),
        };
        (place_or_const, &self.at).hash(state)
    }
}

impl<'tcx> DepNode<'tcx, OneHopLocation> {
    /// Constructs a new [`DepNode`].
    ///
    /// The `tcx` and `body` arguments are used to precompute a pretty string
    /// representation of the [`DepNode`].
    pub fn for_place(
        place: Place<'tcx>,
        at: OneHopLocation,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        context: DefId,
        is_split: bool,
    ) -> Self {
        let span = match at.location {
            RichLocation::Location(loc) => {
                let expanded_span = body
                    .stmt_at(loc)
                    .either(|s| s.source_info.span, |t| t.source_info.span);
                tcx.sess.source_map().stmt_span(expanded_span, body.span)
            }
            RichLocation::Start | RichLocation::End => tcx.def_span(context),
        };
        DepNode {
            kind: DepNodeKind::Place(DepNodePlaceKind {
                place,
                place_pretty: place.to_string(tcx, body).map(Intern::new),
                is_split,
            }),
            at,
            span,
        }
    }
}

impl<'a, Loc> DepNode<'a, Loc> {
    /// Returns a pretty string representation of the place, if one exists.
    pub fn place_pretty(&self) -> Option<&str> {
        if let DepNodeKind::Place(p) = &self.kind {
            p.place_pretty.map(|s| s.as_ref().as_str())
        } else {
            None
        }
    }

    pub fn map_at<'b, Loc2, F: FnOnce(&'b Loc) -> Loc2>(&'b self, f: F) -> DepNode<'a, Loc2> {
        DepNode {
            kind: self.kind.clone(),
            at: f(&self.at),
            span: self.span,
        }
    }

    pub fn make_descriptor(&self) -> PlaceOrConst<'a> {
        match &self.kind {
            DepNodeKind::Const(c) => PlaceOrConst::Const(*c),
            DepNodeKind::Place(p) => PlaceOrConst::Place(p.place),
        }
    }

    pub fn display_place(&self) -> DisplayNodeKind<'a> {
        DisplayNodeKind(self.make_descriptor())
    }

    pub fn place(&self) -> Option<Place<'a>> {
        if let DepNodeKind::Place(DepNodePlaceKind { place, .. }) = self.kind {
            Some(place)
        } else {
            None
        }
    }
}

impl<Loc: fmt::Display> fmt::Display for DepNode<'_, Loc> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            DepNodeKind::Place(p) => match self.place_pretty() {
                Some(s) => s.fmt(f)?,
                None => write!(f, "{:?}", p.place)?,
            },
            DepNodeKind::Const(c) => write!(f, "{c}")?,
        }
        write!(f, " @ {}", self.at)
    }
}

pub struct DisplayNodeKind<'tcx>(PlaceOrConst<'tcx>);

impl std::fmt::Display for DisplayNodeKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            PlaceOrConst::Place(p) => write!(f, "{:?}", p),
            PlaceOrConst::Const(c) => write!(f, "{c}"),
        }
    }
}

impl std::fmt::Debug for DisplayNodeKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

/// A kind of edge in the program dependence graph.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum DepEdgeKind {
    /// X is control-dependent on Y if the value of Y influences the execution
    /// of statements that affect the value of X.
    Control,

    /// X is data-dependent on Y if the value of Y is an input to statements that affect
    /// the value of X.
    Data,
}

/// An edge in the program dependence graph.
///
/// Represents an operation that induces a dependency between places.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DepEdge<Loc> {
    /// Either data or control.
    pub kind: DepEdgeKind,

    /// The location of the operation.
    pub at: Loc,

    pub source_use: SourceUse,

    pub target_use: TargetUse,
}

impl<Loc> DepEdge<Loc> {
    /// Constructs a data edge.
    pub fn data(at: Loc, source_use: SourceUse, target_use: TargetUse) -> Self {
        DepEdge {
            kind: DepEdgeKind::Data,
            at,
            source_use,
            target_use,
        }
    }

    /// Constructs a control edge.
    pub fn control(at: Loc, source_use: SourceUse, target_use: TargetUse) -> Self {
        DepEdge {
            kind: DepEdgeKind::Control,
            at,
            source_use,
            target_use,
        }
    }

    pub fn is_control(&self) -> bool {
        self.kind == DepEdgeKind::Control
    }
    pub fn is_data(&self) -> bool {
        self.kind == DepEdgeKind::Data
    }
}

impl<Loc> DepEdge<Loc> {
    pub fn map_at<'a, Loc2, F: FnOnce(&'a Loc) -> Loc2>(&'a self, f: F) -> DepEdge<Loc2> {
        DepEdge {
            kind: self.kind,
            at: f(&self.at),
            source_use: self.source_use,
            target_use: self.target_use,
        }
    }
}

impl<Loc: fmt::Display> fmt::Display for DepEdge<Loc> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}\n@ {}", self.kind, self.at)
    }
}
