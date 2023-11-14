//! Structs related to MIR [`Local`](mir::Local)s

use std::marker::PhantomData;

use super::{GlobalLocation, GlobalLocationS};
use crate::{
    mir, ty,
    utils::{FnResolution, TyCtxtExt},
    DefId, TyCtxt,
};

/// We wrap [`mir::Local`] to pair it with a type for debug assertions and also
/// we can have it implement [`Display`](std::fmt::Display).
///
/// All trait impls ignore the type field, with the exception of
/// [`Display`](std::fmt::Display), which prints the type in `debug` mode.
#[derive(Debug, Clone, Copy)]
pub struct TypedLocal<'tcx> {
    pub local: mir::Local,
    #[cfg(debug_assertions)]
    ty: ty::Ty<'tcx>,
    _ty_phantom: PhantomData<&'tcx ()>,
}

impl std::fmt::Display for TypedLocal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.local)?;
        #[cfg(debug_assertions)]
        write!(f, ": {:?}", self.ty)?;
        Ok(())
    }
}

impl PartialEq for TypedLocal<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.local == other.local
    }
}

impl Ord for TypedLocal<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.local.cmp(&other.local)
    }
}

impl PartialOrd for TypedLocal<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::hash::Hash for TypedLocal<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.local.hash(state)
    }
}

impl Eq for TypedLocal<'_> {}

impl<'tcx> TypedLocal<'tcx> {
    /// Create a new typed local, fetching the type from the provided local
    /// declarations.
    pub fn new(local: mir::Local, local_decls: &(impl mir::HasLocalDecls<'tcx> + ?Sized)) -> Self {
        Self {
            local,
            #[cfg(debug_assertions)]
            ty: local_decls.local_decls()[local].ty,
            _ty_phantom: PhantomData,
        }
    }

    /// Create a new typed local with the type provided.
    pub fn new_with_type(local: mir::Local, ty: ty::Ty<'tcx>) -> Self {
        Self {
            local,
            #[cfg(debug_assertions)]
            ty,
            _ty_phantom: PhantomData,
        }
    }

    #[cfg(debug_assertions)]
    pub fn ty(self) -> ty::Ty<'tcx> {
        self.ty
    }
}

/// A [`mir::Local`] but also tracks the precise call chain it is reachable
/// from.
///
/// All trait implementations ignore the type field.
#[derive(Clone, Copy, Debug)]
pub struct GlobalLocal<'tcx> {
    local: mir::Local,
    location: Option<GlobalLocation>,
    #[cfg(debug_assertions)]
    ty: ty::Ty<'tcx>,
    _ty_phantom: PhantomData<&'tcx ()>,
}

impl<'tcx> std::cmp::PartialEq for GlobalLocal<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.location == other.location && self.local == other.local
    }
}

impl<'tcx> std::cmp::PartialOrd for GlobalLocal<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(
            self.location
                .partial_cmp(&other.location())?
                .then(self.local.partial_cmp(&other.local)?),
        )
    }
}

impl<'tcx> std::cmp::Eq for GlobalLocal<'tcx> {}

impl<'tcx> std::cmp::Ord for GlobalLocal<'tcx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.location
            .cmp(&other.location)
            .then(self.local.cmp(&other.local))
    }
}

impl<'tcx> std::hash::Hash for GlobalLocal<'tcx> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.local.hash(state);
        self.location.hash(state);
    }
}

impl<'tcx> GlobalLocal<'tcx> {
    /// Construct a new global local in a root function (no call chain)
    pub fn at_root(tcx: TyCtxt<'tcx>, local: mir::Local, context: FnResolution<'tcx>) -> Self {
        Self {
            local,
            location: None,
            #[cfg(debug_assertions)]
            ty: context.local_ty(local, tcx),
            _ty_phantom: PhantomData,
        }
    }

    /// Construct a new global local relative to this call chain.
    pub fn relative(
        tcx: TyCtxt<'tcx>,
        local: mir::Local,
        location: GlobalLocation,
        context: FnResolution<'tcx>,
    ) -> Self {
        Self {
            local,
            location: Some(location),
            #[cfg(debug_assertions)]
            ty: context.local_ty(local, tcx),
            _ty_phantom: PhantomData,
        }
    }

    /// Convert a typed local to a global local. Propagates the type forward.
    pub fn from_typed_local(
        tcx: TyCtxt<'tcx>,
        local: TypedLocal<'tcx>,
        context: FnResolution<'tcx>,
    ) -> Self {
        Self {
            local: local.local,
            location: None,
            #[cfg(debug_assertions)]
            ty: context.best_effort_normalize(tcx, local.ty()),
            _ty_phantom: PhantomData,
        }
    }

    /// Guarantees that `result.location().is_some()`
    pub fn add_location_frame(self, frame: GlobalLocationS) -> Self {
        let Self {
            local, location, ..
        } = self;
        let location = location.map_or_else(
            || GlobalLocation::single(frame.location, frame.function),
            |prior| frame.relativize(prior),
        );
        Self {
            #[cfg(debug_assertions)]
            ty: self.ty,
            local,
            location: Some(location),
            _ty_phantom: PhantomData,
        }
    }

    /// Access to the variable name.
    #[inline]
    pub fn local(self) -> mir::Local {
        self.local
    }

    /// Access to the call chain.
    #[inline]
    pub fn location(self) -> Option<GlobalLocation> {
        self.location
    }

    pub fn ty(self) -> ty::Ty<'tcx> {
        self.ty
    }

    /// Retrieve a reasonable span for this location.
    pub fn span(self, tcx: TyCtxt<'tcx>, context: DefId) -> crate::rustc_span::Span {
        let body = tcx
            .body_for_def_id_default_policy(
                self.location().map_or(context, |l| l.innermost_function()),
            )
            .unwrap()
            .simplified_body();
        body.local_decls[self.local].source_info.span
    }
}

impl<'tcx> std::fmt::Display for GlobalLocal<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} @ ", self.local)?;
        if let Some(loc) = self.location {
            write!(f, "{}", loc)
        } else {
            f.write_str("root")
        }?;
        #[cfg(debug_assertions)]
        write!(f, ": {:?}", self.ty)?;
        Ok(())
    }
}
