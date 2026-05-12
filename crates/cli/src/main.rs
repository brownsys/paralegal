#![feature(exit_status_error)]
use std::collections::HashMap;
use std::ffi::OsString;
use std::hash::{DefaultHasher, Hasher};
use std::io::BufRead;
use std::path::{Path, PathBuf};
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

/// File-name (no extension) of the symlink that fronts the rustc_driver-linked
/// binary. Cargo's `RUSTC_WRAPPER` is set to this path; the binary it points to
/// is `cargo-paralegal-flow` itself, which dispatches on argv[0] (see [`main`]).
const WRAPPER_SHIM_NAME: &str = "paralegal-flow";

/// File-name of the actual rustc_driver-linked analyzer binary that the shim
/// hands real compile invocations to.
const ANALYZER_IMPL_NAME: &str = "paralegal-flow-impl";

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
    // Dispatch on argv[0] file name. The user-facing `paralegal-flow` is a
    // symlink to this same binary, used as cargo's `RUSTC_WRAPPER`; running
    // through the symlink lets us intercept trivial rustc invocations
    // (`-vV`, `--print …`) before `librustc_driver` → `libLLVM` is resolved
    // via DT_NEEDED. The actual analyzer lives in the sibling
    // `paralegal-flow-impl` binary which only the launcher hands real
    // compile invocations to.
    let argv0 = std::env::args_os().next().unwrap_or_default();
    if Path::new(&argv0)
        .file_stem()
        .is_some_and(|s| s == WRAPPER_SHIM_NAME)
    {
        return launcher_main();
    }
    cargo_orchestrator_main()
}

fn cargo_orchestrator_main() -> anyhow::Result<()> {
    let cargo = std::path::Path::new(env!("SYSROOT_PATH"))
        .join("bin")
        .join("cargo");
    let mut args = std::env::args().collect::<Vec<_>>();
    setup_logging()?;
    debug!(?args, "In cargo");
    if args.get(1).is_some_and(|p| p == "paralegal-flow") {
        args.remove(1);
    }
    let rustc_wrapper_bin = ensure_wrapper_symlink()?;
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

/// Ensure `<exe_dir>/paralegal-flow` exists and points at this binary
/// (`cargo-paralegal-flow`). Self-heals stale symlinks left over from
/// older builds (or a real `paralegal-flow` binary from a pre-shim build).
/// Returns the symlink path so callers can use it as `RUSTC_WRAPPER`.
fn ensure_wrapper_symlink() -> anyhow::Result<PathBuf> {
    let exe = std::env::current_exe().context("locating current executable")?;
    let shim = exe.with_file_name(WRAPPER_SHIM_NAME);

    let needs_create = match std::fs::symlink_metadata(&shim) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => true,
        Err(e) => return Err(e).context("stat-ing wrapper shim"),
        Ok(meta) if meta.file_type().is_symlink() => {
            // Verify the symlink resolves to the same canonical path as us.
            let same = std::fs::canonicalize(&shim)
                .ok()
                .zip(std::fs::canonicalize(&exe).ok())
                .is_some_and(|(a, b)| a == b);
            if !same {
                std::fs::remove_file(&shim).context("removing stale wrapper symlink")?;
            }
            !same
        }
        Ok(_) => {
            // Pre-shim leftover (or someone else's file) — replace it.
            std::fs::remove_file(&shim).context("removing pre-shim wrapper file")?;
            true
        }
    };

    if needs_create {
        create_shim(&exe, &shim)
            .with_context(|| format!("creating wrapper shim at {}", shim.display()))?;
    }
    Ok(shim)
}

#[cfg(unix)]
fn create_shim(target: &Path, link: &Path) -> std::io::Result<()> {
    std::os::unix::fs::symlink(target, link)
}

#[cfg(not(unix))]
fn create_shim(target: &Path, link: &Path) -> std::io::Result<()> {
    // No POSIX symlinks; copy instead. Worse for self-heal across rebuilds
    // (the copy can go stale), but keeps the dispatch working.
    std::fs::copy(target, link).map(|_| ())
}

/// Launcher path: invoked when this binary runs through the
/// `paralegal-flow` symlink as `RUSTC_WRAPPER`. Cargo passes argv as
/// `<wrapper> <rustc_path> <rustc_args…>`. We dispatch trivial calls
/// (anything that doesn't need codegen — version probes, `--print …`,
/// help) directly to stock rustc; everything else is exec'd into the real
/// `paralegal-flow-impl` binary.
fn launcher_main() -> anyhow::Result<()> {
    let mut argv = std::env::args_os();
    let _self_path = argv.next();
    let rustc_path = argv
        .next()
        .context("paralegal-flow shim invoked without a rustc-path argument")?;
    let rest: Vec<OsString> = argv.collect();

    if is_trivial_rustc_invocation(&rest) {
        // Exec stock rustc as cargo intended. Never load librustc_driver,
        // so the libLLVM DT_NEEDED resolution doesn't have to succeed.
        let err = exec_replace(&rustc_path, &rest);
        return Err(err)
            .with_context(|| format!("exec stock rustc at {}", Path::new(&rustc_path).display()));
    }

    // Real compile: hand off to the analyzer. Preserve cargo's wrapper
    // convention so paralegal-flow-impl's own argv-parsing (`wrapper_mode`
    // detection in crates/plugin/src/main.rs) still strips the rustc-path
    // arg before invoking rustc_driver.
    let exe = std::env::current_exe().context("locating current executable")?;
    let impl_path = exe.with_file_name(ANALYZER_IMPL_NAME);
    let mut impl_argv: Vec<OsString> = Vec::with_capacity(rest.len() + 1);
    impl_argv.push(rustc_path);
    impl_argv.extend(rest);
    let err = exec_replace(impl_path.as_os_str(), &impl_argv);
    Err(err).with_context(|| format!("exec analyzer at {}", impl_path.display()))
}

/// Conservatively decide whether a rustc invocation is "trivial" — i.e.
/// produces no codegen and so doesn't need the analyzer (or even
/// librustc_driver) loaded. False negatives are harmless (fall through to
/// the real analyzer); false positives skip analysis on a real compile,
/// so this stays strict: every arg must be on the allow-list.
fn is_trivial_rustc_invocation(args: &[OsString]) -> bool {
    if args.is_empty() {
        return false;
    }
    let mut seen_marker = false;
    let mut i = 0;
    while i < args.len() {
        let Some(s) = args[i].to_str() else {
            return false;
        };
        match s {
            "-V" | "-v" | "-vV" | "-Vv" | "--version" | "--verbose" | "-h" | "--help" => {
                seen_marker = true;
                i += 1;
            }
            "--print" | "--explain" => {
                seen_marker = true;
                if i + 1 >= args.len() {
                    return false;
                }
                i += 2;
            }
            _ if s.starts_with("--print=") || s.starts_with("--explain=") => {
                seen_marker = true;
                i += 1;
            }
            _ => return false,
        }
    }
    seen_marker
}

/// On Unix, replace the current process; on other platforms, spawn-and-wait
/// then exit with the child's status. Returns the underlying I/O error only
/// when exec/spawn itself fails.
#[cfg(unix)]
fn exec_replace(prog: &std::ffi::OsStr, args: &[OsString]) -> std::io::Error {
    use std::os::unix::process::CommandExt;
    Command::new(prog).args(args).exec()
}

#[cfg(not(unix))]
fn exec_replace(prog: &std::ffi::OsStr, args: &[OsString]) -> std::io::Error {
    match Command::new(prog).args(args).status() {
        Ok(status) => std::process::exit(status.code().unwrap_or(1)),
        Err(e) => e,
    }
}
