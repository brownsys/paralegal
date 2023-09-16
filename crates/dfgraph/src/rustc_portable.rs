//! Exports either rustc identifiers or their proxies depending on whether the
//! `rustc` feature is enabled.
//!
//! The idea is that you can then define your data structure over this
//! (including serialization) like so, using `cfg_attr:
//!
//! ```
//! pub struct GlobalLocationS {
//!     #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::BodyId"))]
//!     pub function: BodyId,
//!
//!     #[cfg_attr(feature = "rustc", serde(with = "rustc_proxies::Location"))]
//!     pub location: Location,
//! }
//! ```

cfg_if::cfg_if! {
    if #[cfg(feature = "rustc")] {
        use crate::rustc::{hir, mir, def_id};
        pub use mir::{Location, BasicBlock};
        pub use hir::{BodyId, ItemLocalId, hir_id::OwnerId, HirId};
        pub use def_id::{DefIndex, LocalDefId};
    } else {
        pub use crate::rustc_proxies::*;
    }
}
