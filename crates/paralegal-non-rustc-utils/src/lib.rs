use std::ffi::OsString;
use std::fmt;
use std::fmt::{Display, Formatter, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use tracing::Level;
use tracing_subscriber::filter::Targets;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

/// Name of the file used for emitting the serialized
/// [`ProgramDescription`].
pub const FLOW_GRAPH_OUT_NAME: &str = "flow-graph.o";

pub const FLOW_GRAPH_EXT: &str = "fgo";

pub const ARTIFACT_NAME: &str = "paralegal-artifact.json";

/// Extension for output files containing statistics of the analzyer run.
pub const STAT_FILE_EXT: &str = "stat.json";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParalegalArtifact {
    pub targets: Vec<PathBuf>,
}

pub trait FileSystemStorable: Sized {
    fn load(path: impl AsRef<Path>) -> Result<Self>;
    fn store(&self, path: impl AsRef<Path>) -> Result<()>;
}

#[macro_export]
macro_rules! fs_storable_default {
    ($t:ty) => {
        impl $crate::FileSystemStorable for $t {
            fn load(path: impl AsRef<std::path::Path>) -> anyhow::Result<Self> {
                let reader = std::io::BufReader::new(std::fs::File::open(path.as_ref())?);
                Ok(serde_json::from_reader(reader)?)
            }

            fn store(&self, path: impl AsRef<std::path::Path>) -> anyhow::Result<()> {
                let file = std::io::BufWriter::new(std::fs::File::create(path)?);
                Ok(serde_json::to_writer(file, self)?)
            }
        }
    };
}

fs_storable_default!(ParalegalArtifact);

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

/// Has a [`Display`] implementation if the elements of the iterator inside have
/// one. This will render them surrounded by `[` brackets and separated by `, `
/// comma and space
#[derive(Clone)]
pub struct DisplayList<I> {
    iter: I,
}

/// Display this iterator as a list
pub fn display_list<I: IntoIterator>(iter: I) -> DisplayList<<I as IntoIterator>::IntoIter> {
    DisplayList {
        iter: iter.into_iter(),
    }
}

impl<E: Display, I: IntoIterator<Item = E> + Clone> Display for DisplayList<I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_char('[')?;
        write_sep(f, ", ", self.iter.clone(), |e, f| e.fmt(f))?;
        f.write_char(']')
    }
}

pub mod serde_map_via_vec {
    //! Serialize a [`HashMap`] by converting it to a [`Vec`], lifting
    //! restrictions on the types of permissible keys.
    //!
    //! The JSON serializer for [`HashMap`] needs the keys to serialize to a
    //! JSON string object, but sometimes that is not the case. Since the
    //! [`HashMap`] struct only requires its keys be [`Eq`] and [`Hash`] other
    //! non-string values may have been used as key. Unfortunately you can still
    //! use the [`Serialize`] trait on [`HashMap`], even if the keys do not
    //! serialize to strings. Instead a runtime error will be thrown when a
    //! non-string key is encountered.
    //!
    //! This module converts the [`HashMap`] into a [`Vec`] of tuples and
    //! (de)serializes that, which permits arbitrary types to be used for the
    //! keys.
    //!
    //! You are meant to use both [`serialize`] and [`deserialize`], because the
    //! [`Serialize`] and [`Deserialize`] instances of [`HashMap`] do not work
    //! together with these functions.

    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::HashMap;

    /// Serialize a [`HashMap`] by first converting to a [`Vec`] of tuples and
    /// then serializing the vector.
    ///
    /// See module level documentation for usage information.
    pub fn serialize<S: Serializer, K: Serialize, V: Serialize>(
        map: &HashMap<K, V>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter().collect::<Vec<_>>().serialize(serializer)
    }

    /// Deserialize a [`HashMap`] by first deserializing a [`Vec`] of tuples and
    /// then converting.
    ///
    /// See module level documentation for usage information.
    pub fn deserialize<
        'de,
        D: Deserializer<'de>,
        K: Deserialize<'de> + std::cmp::Eq + std::hash::Hash,
        V: Deserialize<'de>,
    >(
        deserializer: D,
    ) -> Result<HashMap<K, V>, D::Error> {
        Ok(Vec::deserialize(deserializer)?.into_iter().collect())
    }
}

/// A struct with a [`Display`] implementation taht renders a
/// [`std::time::Duration`] in human readable form, similar to the `humantime`
/// crate, but instead of rendering with arbitrary precision it only renders two
/// "significant sections", e.g. "2h 5min" or "2d 20h". The sections are days
/// (d), hours (h), minutes (min), seconds (s), miliseconds (ms), microseconds
/// (μs) and nanoseconds (ns).
pub struct TruncatedHumanTime(std::time::Duration);

impl From<std::time::Duration> for TruncatedHumanTime {
    fn from(value: std::time::Duration) -> Self {
        Self(value)
    }
}

impl std::fmt::Display for TruncatedHumanTime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const SECS_PER_MIN: u64 = 60;
        const MINS_PER_H: u64 = 60;
        const H_PER_D: u64 = 24;
        const MILLIS_PER_SEC: u128 = 1000;
        const MICROS_PER_MILLIS: u128 = 1000;
        const NANOS_PER_MICRO: u128 = 1000;
        let secs = self.0.as_secs();
        let mins = secs / SECS_PER_MIN;
        let hs = mins / MINS_PER_H;
        let days = hs / H_PER_D;
        macro_rules! try_two {
            ($larger:expr, $letter1:expr, $smaller:expr, $letter2:expr, $multiplier:expr $(,)?) => {
                if $larger != 0 {
                    let small = $smaller - ($larger * $multiplier);
                    return write!(f, "{}{} {small}{}", $larger, $letter1, $letter2);
                }
            };
        }
        try_two!(days, 'd', hs, 'h', H_PER_D);
        try_two!(hs, 'h', mins, "min", MINS_PER_H);
        try_two!(mins, "min", secs, 's', SECS_PER_MIN);
        try_two!(secs as u128, 's', self.0.as_millis(), "ms", MILLIS_PER_SEC);
        try_two!(
            self.0.as_millis(),
            "ms",
            self.0.as_micros(),
            "μs",
            MICROS_PER_MILLIS,
        );
        try_two!(
            self.0.as_micros(),
            "μs",
            self.0.as_nanos(),
            "ns",
            NANOS_PER_MICRO,
        );
        write!(f, "{}ns", self.0.as_nanos())
    }
}

pub fn setup_logging() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::layer()
                .with_timer(tracing_subscriber::fmt::time::ChronoLocal::new(
                    "%H:%M:%S".to_string(),
                ))
                .with_writer(std::io::stderr),
        )
        .with(
            tracing_subscriber::filter::EnvFilter::builder()
                .with_default_directive(tracing::level_filters::LevelFilter::INFO.into())
                .from_env()?,
        )
        .with(
            Targets::new()
                .with_target("flowistry", Level::ERROR)
                .with_target("rustc_utils", Level::ERROR)
                .with_default(Level::TRACE),
        )
        .try_init()?;
    Ok(())
}

pub struct CommandFactory {
    path: OsString,
    bin: PathBuf,
}

impl CommandFactory {
    pub fn make(&self) -> Command {
        let mut cmd = Command::new(&self.bin);
        cmd.arg("paralegal-flow").env("PATH", &self.path);
        cmd
    }
}

/// Makes sure `paralegal-flow` and `cargo-paralegal-flow` have been built, then returns
/// a factory for [`Command`]s that invoke them properly
pub fn prepare_analyzer_command(paralegal_root: &Path) -> anyhow::Result<CommandFactory> {
    let paralegal_root = paralegal_root.canonicalize()?;
    let success = Command::new("cargo")
        .args([
            "build",
            "--bin",
            "paralegal-flow",
            "--bin",
            "cargo-paralegal-flow",
        ])
        .current_dir(&paralegal_root)
        .status()
        .unwrap()
        .success();
    ensure!(success, "cargo command failed");
    let path = std::env::var_os("PATH").unwrap_or_default();
    let bin_dir = paralegal_root.join("target").join("debug");
    let cargo_paralegal_flow_path = bin_dir.join("cargo-paralegal-flow");
    ensure!(cargo_paralegal_flow_path.exists());
    let mut new_path = std::ffi::OsString::with_capacity(
        path.len() + cargo_paralegal_flow_path.as_os_str().len() + 1,
    );
    // We then append the parent (e.g. its directory) to the search path. That
    // directory (we presume) contains both `paralegal-flow` and `cargo-paralegal-flow`.
    new_path.push(bin_dir);
    if !path.is_empty() {
        new_path.push(":");
        new_path.push(path);
    }
    Ok(CommandFactory {
        path: new_path,
        bin: cargo_paralegal_flow_path,
    })
}
