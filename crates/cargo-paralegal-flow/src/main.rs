use std::hash::{DefaultHasher, Hasher};
use std::path::Path;
use std::process::{Command, Stdio};

use cargo_metadata::Message;
use clap::Parser;
use tracing::debug;

use cargo_paralegal_flow::{ClapArgs, EXEC_HASH_ARG, PARALEGAL_ARGS};
use paralegal_non_rustc_utils::{
    setup_logging, FileSystemStorable, ParalegalArtifact, ARTIFACT_NAME, FLOW_GRAPH_EXT,
};

pub const CARGO_ENCODED_RUSTFLAGS: &str = "CARGO_ENCODED_RUSTFLAGS";

fn get_rustflags() -> Result<Vec<String>, std::env::VarError> {
    use std::env::{var, VarError};
    let prior = var(CARGO_ENCODED_RUSTFLAGS)
        .map(|flags| flags.split('\x1f').map(str::to_string).collect())
        .or_else(|err| {
            if matches!(err, VarError::NotPresent) {
                var("RUSTFLAGS").map(|flags| flags.split_whitespace().map(str::to_string).collect())
            } else {
                Err(err)
            }
        })
        .or_else(|err| {
            matches!(err, VarError::NotPresent)
                .then(Vec::new)
                .ok_or(err)
        })?;
    Ok(prior)
}

fn main() -> anyhow::Result<()> {
    let mut args = std::env::args().collect::<Vec<_>>();
    setup_logging()?;
    debug!(?args, "In cargo");
    let slf = args.remove(0);
    let rustc_wrapper_bin = Path::new(&slf)
        .parent()
        .map_or(Path::new("paralegal-flow").to_path_buf(), |p| {
            p.join("paralegal-flow")
        });
    let args = ClapArgs::parse();

    let mut hasher = DefaultHasher::new();
    args.hash_config(&mut hasher);
    let exec_hash = hasher.finish();

    let mut rustflags = get_rustflags()?;

    rustflags.push(EXEC_HASH_ARG.into());
    rustflags.push(format!("{exec_hash:1x}"));

    let mut cmd = Command::new("cargo");
    cmd.args(&["check", "--message-format=json"]) // or "build"
        .stdout(Stdio::piped())
        .env("RUSTC_WRAPPER", rustc_wrapper_bin)
        .env(PARALEGAL_ARGS, serde_json::to_string(&args)?)
        .env(CARGO_ENCODED_RUSTFLAGS, rustflags.join("\x1f"));

    if args.anactrl.include_std {
        cmd.arg("-Zbuild-std=std,core,alloc,proc_macro");
    }

    let mut child = cmd.spawn()?;

    let reader = std::io::BufReader::new(child.stdout.take().unwrap());

    let mut targets = vec![];

    for message in Message::parse_stream(reader) {
        match message.unwrap() {
            Message::CompilerArtifact(artifact) => {
                if let Some(p) = artifact
                    .filenames
                    .iter()
                    .find(|f| f.ends_with("rmeta"))
                    .filter(|p| p.exists())
                {
                    targets.push(p.with_extension(FLOW_GRAPH_EXT).into_std_path_buf());
                }
            }
            _ => (),
        }
    }

    ParalegalArtifact { targets }.store(ARTIFACT_NAME)?;

    Ok(())
}
