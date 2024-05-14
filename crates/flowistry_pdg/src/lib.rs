#![cfg_attr(feature = "rustc", feature(rustc_private))]

#[cfg(feature = "rustc")]
pub(crate) mod rustc {
    extern crate rustc_driver;
    pub extern crate rustc_hir as hir;
    pub extern crate rustc_index as index;
    pub extern crate rustc_middle as middle;
    pub extern crate rustc_span as span;
    pub use hir::def_id;
    pub use middle::mir;
}

#[cfg(feature = "rustc")]
extern crate rustc_macros;
#[cfg(feature = "rustc")]
extern crate rustc_serialize;

mod pdg;
#[cfg(feature = "rustc")]
mod rustc_impls;
pub mod rustc_portable;
pub mod rustc_proxies;

pub use pdg::*;
