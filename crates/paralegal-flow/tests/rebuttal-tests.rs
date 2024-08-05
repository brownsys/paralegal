use paralegal_flow::test_utils::{CtrlRef, FlowsTo, HasGraph, InlineTestBuilder, NodeRefs};
use paralegal_spdg::Identifier;

fn policy(ctx: CtrlRef, quantifier: impl Fn(&NodeRefs, &NodeRefs) -> bool) -> Result<(), String> {
    let user_data_types = (&ctx).marked_types(Identifier::new_intern("user_data"));

    assert!(!user_data_types.is_empty());

    let delete_sinks = ctx.marked(Identifier::new_intern("deletes"));
    assert!(!delete_sinks.is_empty());
    for t in user_data_types {
        let srcs = ctx.nodes_for_type(t);
        if srcs.is_empty() {
            return Err(format!("No sources for {t:?}"));
        }
        if !quantifier(&srcs, &delete_sinks) {
            return Err(format!("failed for {t:?}"));
        }
    }
    Ok(())
}

const SIMPLE_BUG: &str = stringify!(
    #[paralegal_flow::marker(deletes, arguments = [0])]
    fn delete<T>(t: T) {}

    #[paralegal_flow::marker(user_data)]
    struct User {}

    #[paralegal_flow::marker(user_data)]
    struct Post {}

    #[paralegal_flow::marker(user_data)]
    struct Comment {}

    fn main() {
        for post in vec![Post {}] {
            delete(post)
        }
        delete(User {});
    }
);

const CORRECT: &str = stringify!(
    #[paralegal_flow::marker(deletes, arguments = [0])]
    fn delete<T>(t: T) {}

    #[paralegal_flow::marker(user_data)]
    struct User {}

    #[paralegal_flow::marker(user_data)]
    struct Post {}

    #[paralegal_flow::marker(user_data)]
    struct Comment {}

    fn main() {
        for post in vec![Post {}] {
            delete(post)
        }
        for comment in vec![Comment {}] {
            delete(comment)
        }
        delete(User {});
    }
);

const FORALL_FAIL: &str = stringify!(
    #[paralegal_flow::marker(deletes, arguments = [0])]
    fn delete<T>(t: T) {}

    #[paralegal_flow::marker(user_data)]
    #[derive(PartialEq)]
    struct User {}

    fn main() {
        let current_user = User {};
        let stored_users = vec![User {}];
        if stored_users.contains(&current_user) {
            delete(current_user);
        }
    }
);

const EXISTENTIAL_MISS: &str = stringify!(
    #[paralegal_flow::marker(deletes, arguments = [0])]
    fn delete<T>(t: T) {}

    #[paralegal_flow::marker(user_data)]
    struct Post {}

    fn main() {
        let first_half_of_user_posts = vec![Post {}];
        let second_half_of_user_posts = vec![Post {}];
        delete(first_half_of_user_posts);
    }
);

#[test]
fn plume_policy_exists_quantifier() {
    let policy = |expect_success, msg| {
        move |ctrl: CtrlRef<'_>| {
            let result = policy(ctrl, |srcs, snks| srcs.flows_to_data(snks));
            if expect_success {
                if let Err(e) = result {
                    panic!("Failed {e} {msg}")
                }
            } else {
                assert!(result.is_err(), "Expected fail on {msg}");
            }
        }
    };
    InlineTestBuilder::new(SIMPLE_BUG).check_ctrl(policy(false, "simple bug"));
    InlineTestBuilder::new(CORRECT).check_ctrl(policy(true, "correct"));
    InlineTestBuilder::new(EXISTENTIAL_MISS).check_ctrl(policy(true, "existential fail"));
    InlineTestBuilder::new(FORALL_FAIL).check_ctrl(policy(true, "Forall false-positive"));
}

#[test]
fn plume_policy_forall_quantifier() {
    let policy = |expect_success, msg| {
        move |ctrl: CtrlRef<'_>| {
            let result = policy(ctrl, |srcs, snks| {
                srcs.as_singles().all(|n| n.flows_to_data(snks))
            });
            if expect_success {
                if let Err(e) = result {
                    panic!("Failed {e} {msg}")
                }
            } else {
                assert!(result.is_err(), "Expected fail {msg}");
            }
        }
    };
    InlineTestBuilder::new(SIMPLE_BUG).check_ctrl(policy(false, "bug"));
    InlineTestBuilder::new(CORRECT).check_ctrl(policy(true, "correct"));
    InlineTestBuilder::new(EXISTENTIAL_MISS).check_ctrl(policy(false, "existential bug"));
    InlineTestBuilder::new(FORALL_FAIL).check_ctrl(policy(false, "forall false-positive"));
}
