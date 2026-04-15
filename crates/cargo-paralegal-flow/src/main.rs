use cargo_metadata::Message;
use paralegal_non_rustc_utils::{
    setup_logging, FileSystemStorable, ParalegalArtifact, ARTIFACT_NAME, FLOW_GRAPH_EXT,
};
use std::path::Path;
use std::process::{Command, Stdio};
use tracing::debug;

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

    let mut child = Command::new("cargo")
        .args(&["check", "--message-format=json"]) // or "build"
        .stdout(Stdio::piped())
        .env("RUSTC_WRAPPER", rustc_wrapper_bin)
        .env("SYSROOT", env!("SYSROOT_PATH"))
        .spawn()?;

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
