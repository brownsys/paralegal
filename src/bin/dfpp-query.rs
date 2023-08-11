#![feature(rustc_private)]

use anyhow::Result;
use dfpp::desc::ProgramDescription;
use dfpp::query::{context::Context, props::websubmit::DeletionProp};
use std::env;
use std::fs::File;
use std::sync::Arc;

fn main() -> Result<()> {
    dfpp::rust::rustc_span::create_default_session_if_not_set_then(|_| {
        let desc = {
            let path = env::args().skip(1).next().unwrap();
            let mut f = File::open(path)?;
            serde_json::from_reader::<_, ProgramDescription>(&mut f)?
        };
        let cx = Arc::new(Context::new(desc));
        // CommunityProp { cx }.check();
        DeletionProp::new(cx).check();
        Ok(())
    })
}
