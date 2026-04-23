// extern crate async_std;
// use async_std::prelude::*;

use async_trait::async_trait;

#[paralegal::marker(source)]
fn get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[paralegal::marker(source)]
fn get_user_data2() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[paralegal::marker(
    yey_paralegal_flow_now_needs_this_label_or_it_will_recurse_into_this_function,
    return
)]
fn dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

#[paralegal::marker{ sink, arguments = [0] }]
fn send_user_data(user_data: &UserData) {}

#[paralegal::marker{ sink, arguments = [0] }]
fn send_user_data2(user_data: &UserData) {}

#[paralegal::marker(source)]
async fn async_get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}

#[paralegal::marker{ sink, arguments = [0] }]
async fn async_send_user_data(user_data: &UserData) {}

#[paralegal::marker(sensitive)]
struct UserData {
    pub data: Vec<i64>,
}
#[paralegal::analyze]
async fn top_level_inlining_happens() {
    let mut user_data = get_user_data();
    dp_user_data(&mut user_data);
    send_user_data(&user_data);
}

#[paralegal::analyze]
async fn two_data_over_boundary() {
    let user_data1 = get_user_data();
    let user_data2 = get_user_data2();
    let _ = async_get_user_data().await;
    send_user_data(&user_data1);
    send_user_data2(&user_data2);
}

#[paralegal::analyze]
async fn markers() {
    #[paralegal::marker(source, return)]
    async fn src() -> usize {
        0
    }

    #[paralegal::marker(sink, arguments = [0])]
    async fn snk(snk: usize) {}

    snk(src().await).await
}

#[paralegal::analyze]
async fn arguments_work(d: UserData) {
    send_user_data(&d);
}

async fn move_send_both(ud1: UserData, ud2: UserData) {
    send_user_data(&ud1);
    send_user_data2(&ud2);
}

#[paralegal::analyze]
async fn no_value_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get_user_data2();
    move_send_both(ud1, ud2).await;
}

#[paralegal::marker(noinline)]
async fn f() -> usize {
    0
}

#[paralegal::marker(noinline)]
fn some_input() -> usize {
    0
}

async fn id_fun<T>(t: T) -> T {
    let _ = f();
    t
}

#[paralegal::analyze]
async fn return_from_async() -> usize {
    some_input()
}

#[paralegal::analyze]
async fn async_return_from_async() -> usize {
    id_fun(some_input()).await
}

#[paralegal::marker(is_check, return)]
async fn perform_check(data: usize) -> Result<(), ()> {
    if data != 0 { Ok(()) } else { Err(()) }
}

#[paralegal::marker(is_sensitive1, return)]
async fn sensitive_action1(data: usize) {}

#[paralegal::marker(is_sensitive2, return)]
async fn sensitive_action2(data: usize) {}

#[paralegal::analyze]
#[tracing::instrument(skip_all)]
async fn control_flow_overtaint_tracing(condition: bool, data: usize) -> Result<(), ()> {
    if condition {
        perform_check(data).await?;

        sensitive_action1(data).await;
    } else {
        sensitive_action2(data).await;
    }
    Ok(())
}

#[paralegal::marker(is_check, return)]
fn perform_check_unasync(data: usize) -> Result<(), ()> {
    if data != 0 { Ok(()) } else { Err(()) }
}

#[paralegal::marker(is_sensitive1, return)]
fn sensitive_action1_unasync(data: usize) {}

#[paralegal::marker(is_sensitive2, return)]
fn sensitive_action2_unasync(data: usize) {}

#[paralegal::analyze]
#[tracing::instrument(skip_all)]
fn control_flow_overtaint_tracing_unasync(condition: bool, data: usize) -> Result<(), ()> {
    if condition {
        perform_check_unasync(data)?;

        sensitive_action1_unasync(data);
    } else {
        sensitive_action2_unasync(data);
    }
    Ok(())
}

#[async_trait]
trait ControlFlowOvertaintAsyncTrait {
    async fn control_flow_overtaint_async_trait(
        &self,
        condition: bool,
        data: usize,
    ) -> Result<(), ()>;
}

struct ControlFlowOvertaintAsyncTraitTestStruct;

#[async_trait]
impl ControlFlowOvertaintAsyncTrait for ControlFlowOvertaintAsyncTraitTestStruct {
    #[paralegal::analyze]
    async fn control_flow_overtaint_async_trait(
        &self,
        condition: bool,
        data: usize,
    ) -> Result<(), ()> {
        if condition {
            perform_check(data).await?;

            sensitive_action1(data).await;
        } else {
            sensitive_action2(data).await;
        }
        Ok(())
    }
}

#[async_trait]
trait ControlFlowOvertaintAsyncTraitTracing {
    async fn control_flow_overtaint_async_trait_tracing(
        &self,
        condition: bool,
        data: usize,
    ) -> Result<(), ()>;
}

#[async_trait]
impl ControlFlowOvertaintAsyncTraitTracing for ControlFlowOvertaintAsyncTraitTestStruct {
    #[paralegal::analyze]
    #[tracing::instrument(skip_all)]
    async fn control_flow_overtaint_async_trait_tracing(
        &self,
        condition: bool,
        data: usize,
    ) -> Result<(), ()> {
        if condition {
            perform_check(data).await?;

            sensitive_action1(data).await;
        } else {
            sensitive_action2(data).await;
        }
        Ok(())
    }
}

fn main() {}
