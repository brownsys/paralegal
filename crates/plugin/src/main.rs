#![feature(rustc_private)]

use cargo_paralegal_flow::{ClapArgs, PARALEGAL_ARGS, prepare_compiler_args};
use paralegal_pdg::utils::setup_logging;
use rustc_session::{EarlyDiagCtxt, config::ErrorOutputType};

extern crate rustc_driver;
extern crate rustc_session;

const REAL_LONG_VERSION: &str = env!("RUSTC_LONG_VERSION");
const HOST: &str = env!("HOST");

fn main() -> anyhow::Result<()> {
    setup_logging()?;
    let args = prepare_compiler_args(REAL_LONG_VERSION, HOST, env!("SYSROOT_PATH"));

    let parsed_plugin_args: ClapArgs = serde_json::from_str(&std::env::var(PARALEGAL_ARGS)?)?;
    let plugin_args: paralegal_flow::Args = parsed_plugin_args.try_into()?;

    let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&early_dcx);

    let code = rustc_driver::catch_with_exit_code(move || paralegal_flow::run(args, plugin_args));
    std::process::exit(if code == std::process::ExitCode::SUCCESS {
        0
    } else {
        1
    })
}
