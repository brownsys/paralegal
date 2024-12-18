//! Canonical serialziation to use. This is so that `paralegal-flow` and
//! `paralegal-policy` agree on the format to use.
//!
use anyhow::{Context, Ok, Result};
use cfg_if::cfg_if;
use std::{
    fs::File,
    io::{Read, Write},
    path::Path,
};

use crate::ProgramDescription;

cfg_if! {
    if #[cfg(feature = "binenc")] {
        const CODEC: &str = "bincode";
    } else {
        const CODEC: &str = "json";
    }
}

/// A magic hash number used to verify version compatibility of output
/// artifacts. Used in reading and writing the [`ProgramDescription`] See
/// build.rs for how this number is created.
fn ser_magic() -> u64 {
    const SER_MAGIC: &str = env!("SER_MAGIC");
    SER_MAGIC.parse().unwrap()
}

impl ProgramDescription {
    /// Write `self` using the configured serialization format
    pub fn canonical_write(&self, path: impl AsRef<Path>) -> Result<()> {
        let path = path.as_ref();
        let mut out_file = File::create(path)?;
        out_file.write_all(&ser_magic().to_le_bytes())?;
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
        let mut in_file = File::open(path)?;
        let magic = {
            let mut buf = [0u8; 8];
            in_file.read_exact(&mut buf).context("Reading magic")?;
            u64::from_le_bytes(buf)
        };
        let ser_magic = ser_magic();
        if magic != ser_magic {
            anyhow::bail!("Magic number mismatch: Expected {ser_magic:x}, got {magic:x}. Likely this application was compiled against a different version of the paralegal-spdg library then used by the flow analyzer.");
        }
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
