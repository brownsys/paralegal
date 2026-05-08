use paralegal_flow::{inline_test, test_utils::*};

fn stdlib_environment() -> &'static DependencyEnvironment {
    super::stdlib_environment()
}

#[test]
fn fs() {
    inline_test! {
        fn main() {
            std::fs::write("test", "Content").unwrap();
        }
    }
    .with_dependency_environment(stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.show_side_effects(true);
        assert!(!ctrl.marked("side-effect:fs:write").is_empty());
    });
}

#[test]
fn path_eq() {
    inline_test! {
        fn main() {
            let _ = std::path::Path::new("test") == std::path::Path::new("test");
        }
    }
    .with_dependency_environment(stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.show_side_effects(true);
        ctrl.assert_purity(true);
    });
}

#[test]
fn os_str_from_bytes() {
    inline_test! {
        fn main() {
            use std::os::unix::prelude::OsStrExt;
            std::ffi::OsStr::from_bytes(b"test");
        }
    }
    .with_dependency_environment(stdlib_environment())
    .check_ctrl(|ctrl| {
        ctrl.assert_purity(true);
    });
}
