//! Library of intermediate representations used in this tool.

pub use paralegal_spdg::global_location::*;
pub mod flows;
pub use flows::*;
pub mod local;
pub mod regal;
pub use local::*;
