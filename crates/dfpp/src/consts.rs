//! Constants used globally.
//!
//! Many of these are lazyily initialized using [`lazy_static!`] which creates
//! structs with a `Deref` implementation that creates and memoizes the constant
//! on first call. This is why many of the constants here are not categorized as
//! constants, but instead as structs.

use crate::discover::AttrMatchT;
use crate::Symbol;

pub use dfgraph::FLOW_GRAPH_OUT_NAME;

lazy_static! {
    /// The symbol `arguments` which we use for refinement in a `#[dfpp::label(...)]`
    /// annotation.
    pub static ref ARG_SYM: Symbol = Symbol::intern("arguments");
    /// The symbol `return` which we use for refinement in a `#[dfpp::label(...)]`
    /// annotation.
    pub static ref RETURN_SYM: Symbol = Symbol::intern("return");
    /// The symbol `verification_hash` which we use for refinement in a
    /// `#[dfpp::exception(...)]` annotation.
    pub static ref VERIFICATION_HASH_SYM: Symbol = Symbol::intern("verification_hash");
    /// This will match the annotation `#[dfpp::label(...)]` when using
    /// [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract)
    pub static ref LABEL_MARKER: AttrMatchT = sym_vec!["dfpp", "label"];
    pub static ref MARKER_MARKER: AttrMatchT = sym_vec!["dfpp", "marker"];
    /// This will match the annotation `#[dfpp::analyze]` when using
    /// [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract)
    pub static ref ANALYZE_MARKER: AttrMatchT = sym_vec!["dfpp", "analyze"];
    /// This will match the annotation `#[dfpp::output_types(...)]` when using
    /// [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract)
    pub static ref OTYPE_MARKER: AttrMatchT = sym_vec!["dfpp", "output_types"];
    /// This will match the annotation `#[dfpp::exception(...)]` when using
    /// [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract)
    pub static ref EXCEPTION_MARKER: AttrMatchT = sym_vec!["dfpp", "exception"];
}
