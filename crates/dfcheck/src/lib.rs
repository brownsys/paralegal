use self::context::Context;
use anyhow::Result;
use dfgraph::ProgramDescription;
use std::env;
use std::fs::File;
use std::sync::Arc;

pub use dfgraph;

pub mod context;
pub mod flows_to;

pub fn cli(cb: impl FnOnce(Arc<Context>)) {
    let inner = move || -> Result<()> {
        simple_logger::init_with_env().unwrap();

        let mut args = env::args().skip(1);
        let graph_path = args.next().unwrap();

        let desc = {
            let mut f = File::open(graph_path)?;
            serde_json::from_reader::<_, ProgramDescription>(&mut f)?
        };
        let cx = Arc::new(Context::new(desc));
        cb(cx);

        Ok(())
    };
    inner().unwrap();
}
