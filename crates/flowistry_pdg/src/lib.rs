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

mod pdg;
#[cfg(feature = "rustc")]
mod rustc_impls;
pub mod rustc_portable;
pub mod rustc_proxies;

pub use pdg::*;

pub mod utils {
    use std::fmt;

    /// Write all elements from `it` into the formatter `fmt` using `f`, separating
    /// them with `sep`
    pub fn write_sep<
        E,
        I: IntoIterator<Item = E>,
        F: FnMut(E, &mut fmt::Formatter<'_>) -> fmt::Result,
    >(
        fmt: &mut fmt::Formatter<'_>,
        sep: &str,
        it: I,
        mut f: F,
    ) -> fmt::Result {
        let mut first = true;
        for e in it {
            if first {
                first = false;
            } else {
                fmt.write_str(sep)?;
            }
            f(e, fmt)?;
        }
        Ok(())
    }
}
