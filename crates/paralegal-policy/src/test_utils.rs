use crate::Context;
use paralegal_flow::test_utils::PreFrg;
use std::sync::OnceLock;

static TEST_CTX: OnceLock<Context> = OnceLock::new();

pub fn test_ctx() -> &'static Context {
    TEST_CTX.get_or_init(|| {
        paralegal_flow::test_utils::run_paralegal_flow_with_flow_graph_dump("tests/test-crate");
        let desc = PreFrg::from_file_at("tests/test-crate").0;
        Context::new(desc)
    })
}
