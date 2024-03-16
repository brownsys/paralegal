mod helpers;

use anyhow::Result;
use helpers::Test;
use paralegal_policy::{assert_error, EdgeSelection};
use paralegal_spdg::Identifier;

#[test]
fn return_markers_on_no_arg_functions() -> Result<()> {
    let test = Test::new(stringify!(
        #[paralegal::marker(target, arguments = [0])]
        fn target<T>(t: T) {}

        #[paralegal::marker(source, return)]
        fn source() -> std::path::PathBuf {
            "buf".into()
        }

        #[paralegal::analyze]
        fn main() {
            target(source())
        }
    ))?;

    test.run(|ctx| {
        let sources: Box<[_]> = ctx.marked_nodes(Identifier::new_intern("source")).collect();
        let targets: Box<[_]> = ctx.marked_nodes(Identifier::new_intern("target")).collect();
        assert_error!(ctx, !sources.is_empty(), "No sources");
        assert_error!(ctx, !targets.is_empty(), "No targets");
        assert_error!(
            ctx,
            ctx.any_flows(&sources, &targets, EdgeSelection::Data)
                .is_some()
        );
        Ok(())
    })
}
