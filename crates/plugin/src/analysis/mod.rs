//! Data-and control flow analyzer and inliner.
//!
//! Analysis starts with the construction of [`SPDGGenerator`] from a
//! [`CollectingVisitor`](crate::discover::CollectingVisitor) and then calling
//! [`analyze`](SPDGGenerator::analyze).

pub mod async_support;
mod callback_adapter;
mod calling_convention;
mod def_info;
mod driver;
pub mod graph_converter;
pub mod inline_judge;
mod mutation;
pub mod pdg;

pub use self::inline_judge::InlineJudge;
pub use async_support::{determine_async, is_async_trait_fn};
pub use calling_convention::CallingConvention;
pub use driver::SPDGGenerator;
