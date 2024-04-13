//! Canonical serialziation to use. This is so that `paralegal-flow` and
//! `paralegal-policy` agree on the format to use.
//!
use anyhow::{Context, Ok, Result};
use cfg_if::cfg_if;
use std::{fs::File, path::Path};

use crate::ProgramDescription;

cfg_if! {
    if #[cfg(feature = "binenc")] {
        const CODEC: &str = "bincode";
    } else {
        const CODEC: &str = "json";
    }
}

impl ProgramDescription {
    /// Write `self` using the configured serialization format
    pub fn canonical_write(&self, path: &Path) -> Result<()> {
        let mut out_file = File::create(path)?;
        cfg_if! {
            if #[cfg(feature = "binenc")] {
                let write = bincode::serialize_into(
                    &mut out_file,
                    self
                );
            } else {
                let write = serde_json::to_writer(
                    &mut out_file,
                    self,
                );
            }
        }
        write.with_context(|| {
            format!(
                "Writing SPDG with codec {CODEC} to {}",
                path.canonicalize()
                    .unwrap_or_else(|_| path.to_owned())
                    .display()
            )
        })?;
        Ok(())
    }

    /// Read `self` using the configured serialization format
    pub fn canonical_read(path: &Path) -> Result<Self> {
        let in_file = File::open(path)?;
        cfg_if! {
            if #[cfg(feature = "binenc")] {
                let read = bincode::deserialize_from(
                    &in_file,
                );
            } else  {
                let read = serde_json::from_reader(
                    &in_file,
                );
            }
        };
        read.with_context(|| {
            format!(
                "Reading SPDG with codec {CODEC} from {}",
                path.canonicalize()
                    .unwrap_or_else(|_| path.to_owned())
                    .display()
            )
        })
    }
}
