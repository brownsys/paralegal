//! Canonical serialziation to use. This is so that `paralegal-flow` and
//! `paralegal-policy` agree on the format to use.
//!
use anyhow::{Context, Ok, Result};
use cfg_if::cfg_if;
use std::{
    fs::File,
    io::{BufReader, BufWriter},
    path::Path,
};

use crate::{AnalyzerStats, ProgramDescription};

cfg_if! {
    if #[cfg(feature = "binenc")] {
        const CODEC: &str = "bincode";
    } else {
        const CODEC: &str = "json";
    }
}

impl ProgramDescription {
    /// Write `self` using the configured serialization format
    pub fn canonical_write(&self, path: impl AsRef<Path>) -> Result<()> {
        let path = path.as_ref();
        let mut out_file = BufWriter::new(File::create(path)?);
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
    pub fn canonical_read(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let in_file = BufReader::new(File::open(path)?);
        cfg_if! {
            if #[cfg(feature = "binenc")] {
                let read = bincode::deserialize_from(
                    in_file,
                );
            } else  {
                let read = serde_json::from_reader(
                    in_file,
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

impl AnalyzerStats {
    /// Read the stats from a file using the default encoding (json)
    pub fn canonical_read(path: impl AsRef<Path>) -> Result<Self> {
        let reader = BufReader::new(File::open(path.as_ref())?);
        Ok(serde_json::from_reader(reader)?)
    }

    /// Write the stats to a file using the default encoding (json)
    pub fn canonical_write(&self, path: impl AsRef<Path>) -> Result<()> {
        let file = BufWriter::new(File::create(path)?);
        Ok(serde_json::to_writer(file, self)?)
    }
}
