#![feature(exit_status_error)]
use std::collections::HashMap;
use std::hash::{DefaultHasher, Hasher};
use std::io::BufRead;
use std::process::{Command, Stdio};

use anyhow::Context;
use cargo_metadata::diagnostic::DiagnosticLevel;
use cargo_metadata::{CompilerMessage, Message};
use clap::Parser;
use tracing::{debug, error, trace};

use cargo_paralegal_flow::{config_hash_for_file, ClapArgs, EXEC_HASH_ARG, PARALEGAL_ARGS};
use paralegal_utils::{
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
    let cargo = std::path::Path::new(env!("SYSROOT_PATH"))
        .join("bin")
        .join("cargo");
    let mut args = std::env::args().collect::<Vec<_>>();
    setup_logging()?;
    debug!(?args, "In cargo");
    if args.get(1).is_some_and(|p| p == "paralegal-flow") {
        args.remove(1);
    }
    let rustc_wrapper_bin = std::env::current_exe()?.with_file_name("paralegal-flow");
    let mut args = ClapArgs::parse_from(args);

    args.anactrl.include_std |= args.marker_control.mark_side_effects();

    let mut hasher = DefaultHasher::new();
    args.hash_config(&mut hasher);
    config_hash_for_file(std::env::current_exe().ok(), &mut hasher);
    config_hash_for_file(Some(&rustc_wrapper_bin), &mut hasher);

    let exec_hash = hasher.finish();

    let mut rustflags = get_rustflags()?;

    rustflags.push(EXEC_HASH_ARG.into());
    rustflags.push(format!("{exec_hash:1x}"));

    let metadata = cargo_metadata::MetadataCommand::new()
        .cargo_path(&cargo)
        // At the moment this is fine, because we only use this for info about
        // workspace members and the target directory
        .no_deps()
        .other_options(["--offline".into()])
        .exec()?;

    let mut cmd = Command::new(&cargo);
    cmd.args(["check", "--message-format=json"]) // or "build"
        .arg("--target-dir")
        .arg(metadata.target_directory.join("paralegal"))
        .args(args.cargo_args.iter())
        .stdout(Stdio::piped())
        .env("RUSTC_WRAPPER", rustc_wrapper_bin)
        .env(PARALEGAL_ARGS, serde_json::to_string(&args)?)
        .env(CARGO_ENCODED_RUSTFLAGS, rustflags.join("\x1f"));

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

    // Read raw lines from cargo's stdout, echo them so callers expecting
    // `--message-format=json` can parse them, and also parse them into
    // `cargo_metadata::Message` for internal handling.
    for line_res in reader.lines() {
        let line = match line_res {
            Ok(l) => l,
            Err(e) => {
                error!(?e, "failed to read cargo stdout line");
                continue;
            }
        };

        // Forward the raw JSON/text line to stdout so tools that expect the
        // original cargo JSON stream can consume it (e.g. `collect_extern_args`).
        if args.forward_json {
            println!("{}", line);
        }

        // Try to parse it as a cargo Message; if it parses, handle it.
        match serde_json::from_str::<Message>(&line) {
            Ok(Message::CompilerArtifact(artifact)) => {
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
            Ok(Message::TextLine(l)) => println!("{l}"),
            Ok(Message::CompilerMessage(CompilerMessage { message, .. }))
                if matches!(
                    message.level,
                    DiagnosticLevel::Error | DiagnosticLevel::Ice | DiagnosticLevel::FailureNote
                ) =>
            {
                println!("{}", message)
            }
            // Non-JSON lines (e.g. build script stdout) that fail to parse
            // should be forwarded so callers don't silently lose output.
            Err(_) if !args.forward_json => println!("{line}"),
            _ => (),
        }
    }

    ParalegalArtifact { targets }.store(ARTIFACT_NAME)?;

    child.wait()?.exit_ok().context("Cargo check command")?;

    Ok(())
}
