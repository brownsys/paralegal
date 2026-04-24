#![feature(exit_status_error)]
use std::collections::HashMap;
use std::process::{Command, Stdio};

use anyhow::Context;
use cargo_metadata::diagnostic::DiagnosticLevel;
use cargo_metadata::{CompilerMessage, Message};
use clap::Parser;
use tracing::{debug, error, trace};

use cargo_paralegal_flow::{ClapArgs, PARALEGAL_ARGS};
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
    if args.get(1).is_some_and(|p| p == "paralegal-flow") {
        args.remove(1);
    }
    let rustc_wrapper_bin = std::env::current_exe()?.with_file_name("paralegal-flow");
    let mut args = ClapArgs::parse_from(args);

    args.anactrl.include_std |= args.marker_control.mark_side_effects();

    let metadata = cargo_metadata::MetadataCommand::new()
        // At the moment this is fine, because we only use this for info about
        // workspace members and the target directory
        .no_deps()
        .other_options(["--offline".into()])
        .exec()?;

    let mut cmd = Command::new("cargo");
    cmd.args(["check", "--message-format=json"]) // or "build"
        .arg("--target-dir")
        .arg(metadata.target_directory.join("paralegal"))
        .args(args.cargo_args.iter())
        .stdout(Stdio::piped())
        .env("RUSTC_WRAPPER", rustc_wrapper_bin)
        .env(PARALEGAL_ARGS, serde_json::to_string(&args)?);

    // HACK: if running on the rustc codebase, this env var needs to exist
    // for the code to compile
    if metadata
        .packages
        .iter()
        .any(|p| p.name == "rustc-main" && metadata.workspace_members.contains(&p.id))
    {
        cmd.env("CFG_RELEASE", "");
    }

    let packages = metadata
        .packages
        .iter()
        .map(|p| (&p.id, p))
        .collect::<HashMap<_, _>>();

    if args.anactrl.include_std {
        cmd.arg("-Zbuild-std=std,core,alloc,proc_macro");
    }

    trace!(cargo_cmd=?cmd);

    let mut child = cmd.spawn()?;

    let reader = std::io::BufReader::new(child.stdout.take().unwrap());

    let mut targets = vec![];

    for message in Message::parse_stream(reader) {
        match message? {
            Message::CompilerArtifact(artifact) => {
                let mut applicable = false;
                if let Some(target) = &args.target {
                    if packages
                        .get(&artifact.package_id)
                        .is_none_or(|p| &p.name != target)
                    {
                        continue;
                    }
                }
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
            Message::TextLine(l) => println!("{l}"),
            Message::CompilerMessage(CompilerMessage { message, .. })
                if matches!(
                    message.level,
                    DiagnosticLevel::Error | DiagnosticLevel::Ice | DiagnosticLevel::FailureNote
                ) =>
            {
                println!("{}", message)
            }
            _ => (),
        }
    }

    ParalegalArtifact { targets }.store(ARTIFACT_NAME)?;

    child.wait()?.exit_ok().context("Cargo check command")?;

    Ok(())
}
