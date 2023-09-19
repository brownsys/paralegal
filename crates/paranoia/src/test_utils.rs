use crate::Context;
use parable::test_utils::PreFrg;
use std::sync::OnceLock;

static TEST_CTX: OnceLock<Context> = OnceLock::new();

pub fn test_ctx() -> &'static Context {
    TEST_CTX.get_or_init(|| {
        parable::test_utils::run_parable_with_flow_graph_dump("tests/test-crate");
        let desc = PreFrg::from_file_at("tests/test-crate").0;
        Context::new(desc)
    })
}
