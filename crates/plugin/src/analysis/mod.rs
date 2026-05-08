//! Data-and control flow analyzer and inliner.
//!
//! Analysis starts with the construction of [`SPDGGenerator`] from a
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) and then calling
//! [`analyze`](SPDGGenerator::analyze).

pub mod async_support;
mod calling_convention;
mod callback_adapter;
mod def_info;
mod driver;
pub mod global;
pub mod graph_converter;
pub mod inline_judge;
pub mod local;
mod mutation;

pub use self::inline_judge::InlineJudge;
pub use async_support::{determine_async, is_async_trait_fn};
pub use calling_convention::CallingConvention;
pub use driver::SPDGGenerator;
pub use global::call_tree_visit::{VisitDriver, Visitor};
pub use global::{
    DepEdge, DepEdgeKind, DepNode, DepNodeKind, MemoPdgConstructor, Node, OneHopLocation,
    PartialGraph, Use,
};
pub use graph_converter::assemble_pdg;
