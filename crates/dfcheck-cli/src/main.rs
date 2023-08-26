#![feature(rustc_private)]

extern crate rustc_span;

use anyhow::Result;
use dfcheck::context::Context;
use dfgraph::ProgramDescription;
use dlopen::wrapper::{Container, WrapperApi};
use dlopen_derive::WrapperApi;
use std::env;
use std::fs::File;
use std::sync::Arc;

#[derive(WrapperApi)]
struct CheckerApi {
    run: extern "C" fn(cx: Arc<Context>),
}

fn main() -> Result<()> {
    simple_logger::init_with_env().unwrap();

    rustc_span::create_default_session_if_not_set_then(|_| {
        let mut args = env::args().skip(1);
        let dl_path = args.next().unwrap();
        let graph_path = args.next().unwrap();

        let desc = {
            let mut f = File::open(graph_path)?;
            serde_json::from_reader::<_, ProgramDescription>(&mut f)?
        };
        let cx = Arc::new(Context::new(desc));

        let checker_api: Container<CheckerApi> = unsafe { Container::load(dl_path)? };
        checker_api.run(cx);

        Ok(())
    })
}
