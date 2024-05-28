#![feature(rustc_private)]
#[macro_use]
extern crate lazy_static;

use paralegal_flow::test_utils::*;
use paralegal_spdg::Identifier;

const CRATE_DIR: &str = "tests/cross-crate";

lazy_static! {
    static ref TEST_CRATE_ANALYZED: bool = run_paralegal_flow_with_flow_graph_dump(CRATE_DIR);
}

macro_rules! define_test {
    ($name:ident: $ctrl:ident -> $block:block) => {
        define_test!($name: $ctrl, $name -> $block);
    };
    ($name:ident: $ctrl:ident, $ctrl_name:ident -> $block:block) => {
        paralegal_flow::define_flow_test_template!(TEST_CRATE_ANALYZED, CRATE_DIR, $name: $ctrl, $ctrl_name -> $block);
    };
}

define_test!(basic : graph -> {
    let src_fn = graph.function("src");
    let src = graph.call_site(&src_fn);
    let not_src_fn = graph.function("not_src");
    let not_src = graph.call_site(&not_src_fn);
    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    assert!(src.output().flows_to_data(&target.input()));
    assert!(!not_src.output().flows_to_data(&target.input()));
});

define_test!(basic_marker: graph -> {

    let marker = Identifier::new_intern("mark");
    assert!(dbg!(&graph.spdg().markers).iter().any(|(_, markers)| markers.contains(&marker)))
});

define_test!(assigns_marker: graph -> {
    let sources = graph.marked(Identifier::new_intern("source"));
    let mark = graph.marked(Identifier::new_intern("mark"));
    let target = graph.marked(Identifier::new_intern("target"));
    assert!(!sources.is_empty());
    assert!(!mark.is_empty());
    assert!(!target.is_empty());
    assert!(sources.flows_to_data(&mark));
    assert!(mark.flows_to_data(&target));
});

define_test!(basic_generic : graph -> {
    let src_fn = graph.function("src");
    let src = graph.call_site(&src_fn);
    let not_src_fn = graph.function("not_src");
    let not_src = graph.call_site(&not_src_fn);
    let target_fn = graph.function("target");
    let target = graph.call_site(&target_fn);
    assert!(src.output().flows_to_data(&target.input()));
    assert!(!not_src.output().flows_to_data(&target.input()));
});

define_test!(assigns_marker_generic: graph -> {
    let sources = graph.marked(Identifier::new_intern("source"));
    let mark = graph.marked(Identifier::new_intern("mark"));
    let target = graph.marked(Identifier::new_intern("target"));
    assert!(!sources.is_empty());
    assert!(!mark.is_empty());
    assert!(!target.is_empty());
    assert!(sources.flows_to_data(&mark));
    assert!(mark.flows_to_data(&target));
});
