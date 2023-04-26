#![feature(register_tool)]
#![register_tool(dfpp)]

#[dfpp::label(noinline)]
fn input() -> i32 {
    0
}

#[dfpp::label(noinline)]
fn output(i : i32) -> i32 {
    i
}

#[dfpp::analyze]
fn return_is_tracked() -> i32 {
    output(input())
}

#[dfpp::label(sensitive)]
struct UserData {
    pub data: Vec<i64>,
}

#[dfpp::analyze]
fn simple_happens_before_has_connections() {
    let mut user_data = get_user_data();
    dp_user_data(&mut user_data);
    send_user_data(&user_data);
}

#[dfpp::analyze]
fn happens_before_if_has_connections(cond: bool) {
    let mut user_data = get_user_data();
    if cond {
        dp_user_data(&mut user_data);
    }
    send_user_data(&user_data);
}

#[dfpp::label(dont_recurse, arguments=[0])]
fn data_contains_3(d: &UserData) -> bool {
    d.data.iter().any(|i| *i == 3)
}

#[dfpp::analyze]
fn data_influenced_conditional_happens_before() {
    let mut user_data = get_user_data();
    if data_contains_3(&user_data) {
        dp_user_data(&mut user_data);
    }
    send_user_data(&user_data);
}

#[dfpp::analyze]
fn conditional_happens_before_with_two_parents_before_if(mut d: Vec<i64>, cond: bool) {
    d.push(6);
    let mut user_data = get_user_data_with(d);
    if cond {
        dp_user_data(&mut user_data);
    }
    send_user_data(&user_data);
}

#[dfpp::analyze]
fn loops(mut x: i32) {
    let mut user_data = get_user_data();
    while x < 10 {
        dp_user_data(&mut user_data);
        x -= 1;
    }
    send_user_data(&user_data);
}

#[dfpp::analyze]
fn loop_retains_dependency(mut x: i32) {
    let mut user_data = get_user_data();
    let mut other_data = get_other_data();
    while x < 10 {
        dp_user_data_with(&mut user_data, &other_data);
        modify_other_data(&mut other_data);
        x -= 1;
    }
    send_user_data(&user_data);
}

#[dfpp::analyze]
fn arguments(mut x: i32) {
    let mut user_data = get_user_data();
    while x < 10 {
        dp_user_data(&mut user_data);
        x -= 1;
    }
    send_user_data(&user_data);
}

#[dfpp::label(source)]
fn get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}

#[dfpp::label(source)]
fn get_user_data_with(data: Vec<i64>) -> UserData {
    return UserData { data };
}

#[dfpp::label(noinline)]
fn get_other_data() -> Vec<i64> {
    return vec![1, 2, 3]
}

#[dfpp::label(yey_dfpp_now_needs_this_label_or_it_will_recurse_into_this_function, return)]
fn dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

#[dfpp::label(noinline, return)]
fn modify_vec(v: &mut [i64]) {
}

#[dfpp::analyze]
fn modify_pointer() {
    let ref mut p = get_user_data();
    modify_vec(&mut p.data);
    send_user_data(p);
}

#[dfpp::label(noinline, return)]
fn modify_it(x: &mut i32) {}

#[dfpp::analyze]
fn on_mut_var() {
    let mut x = source();
    modify_it(&mut x);
    receiver(x)
}

#[dfpp::label(hello, return)]
fn source() -> i32 {
    0
}

struct S {}

#[dfpp::label(noinline, return)]
fn new_s() -> S { S {} }

impl std::ops::Deref for S {
    type Target = T;
    #[dfpp::label(noinline, return)]
    fn deref(&self) -> &T {
        unimplemented!()
    }
}

struct T {}

#[dfpp::label(noinline, return)]
fn read_t(t: &T) {
}

#[dfpp::analyze]
fn spurious_connections_in_deref() {
    let s = new_s();
    let t : &T = &*s;
    read_t(t);
}


#[dfpp::label(there, arguments = [0])]
fn receiver(x: i32) {}

fn dp_user_data_with(user_data: &mut UserData, other_data: &Vec<i64>) {
    for i in 0..user_data.data.len() {
        user_data.data[i] = other_data[i];
    }
}

fn modify_other_data(other_data: &mut Vec<i64>) {
}

#[dfpp::label{ sink, arguments = [0] }]
fn send_user_data(user_data: &UserData) {}

fn main() {
    println!("Hello, world!");
}

#[dfpp::analyze]
fn control_flow_tracking_for_non_fn_compound_conditions() {
    let a_val = new_s();
    let another_thing = input();
    // This also works with a simpler condition (e.g. `false`) after the `&&`,
    // but I want to avoid the potential of a compiler optimization getting
    // clever and making this pass, hence the complexity.
    if source() > 8 && another_thing < 9 {
        read_t(&a_val);
    }
}

#[dfpp::analyze]
fn control_flow_tracking_for_compound_cond_with_fun() {
    let a_val = new_s();
    // This also works with a simpler condition (e.g. `false`) after the `&&`,
    // but I want to avoid the potential of a compiler optimization getting
    // clever and making this pass, hence the complexity.
    if source() > 8 && input() < 9 {
        read_t(&a_val);
    }
}



#[dfpp::analyze]
fn control_flow_tracking_overtaint() {
    let early_val = input();
    let late_val = source();
    let a_val = new_s();
    if early_val > 9 {
        if late_val < 70 {
            read_t(&a_val);
        }
    }
}