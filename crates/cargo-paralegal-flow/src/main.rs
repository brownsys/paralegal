#![feature(exit_status_error)]
use std::hash::{DefaultHasher, Hasher};
use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::{ensure, Context};
use cargo_metadata::Message;
use clap::Parser;
use tracing::{debug, error};

use cargo_paralegal_flow::{ClapArgs, EXEC_HASH_ARG, PARALEGAL_ARGS};
use paralegal_non_rustc_utils::{
    setup_logging, FileSystemStorable, ParalegalArtifact, ARTIFACT_NAME, FLOW_GRAPH_EXT,
};
use tracing::field::debug;

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
    if args.get(1).is_some_and(|p| p == "paralegal-flow") {
        args.remove(1);
    }
    let slf = &args[0];
    let rustc_wrapper_bin = Path::new(&slf)
        .parent()
        .map_or(Path::new("paralegal-flow").to_path_buf(), |p| {
            p.join("paralegal-flow")
        });
    let args = ClapArgs::parse_from(args);

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
                let mut applicable = false;
                match artifact
                    .filenames
                    .iter()
                    .filter(|f| f.extension() == Some("rmeta"))
                    .flat_map(|p| {
                        let with_ext = p.with_extension(FLOW_GRAPH_EXT).into_std_path_buf();
                        let basename = with_ext.file_name();
                        let without_lib = with_ext
                            .parent()
                            .zip(
                                basename
                                    .and_then(|b| b.to_str())
                                    .and_then(|b| b.strip_prefix("lib")),
                            )
                            .map(|(p, name)| p.join(name));
                        [with_ext].into_iter().chain(without_lib)
                    })
                    .filter(|p| p.exists())
                    .collect::<Box<[_]>>()
                    .as_mut()
                {
                    [p] => {
                        targets.push(p.clone());
                        applicable = true;
                    }
                    [] => (),
                    other => error!(?other, "Too many applicable paths"),
                }
                debug!(?artifact, applicable, "Found artifact");
            }
            _ => (),
        }
    }

    ParalegalArtifact { targets }.store(ARTIFACT_NAME)?;

    child.wait()?.exit_ok().context("Cargo check command")?;

    Ok(())
}
