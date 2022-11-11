#![feature(register_tool)]
#![register_tool(dfpp)]

#[dfpp::label(sensitive)]
struct UserData {
    pub data: Vec<i64>,
}

#[dfpp::analyze]
fn basic_happens_before() {
    let mut user_data = get_user_data();
    dp_user_data(&mut user_data);
    send_user_data(&user_data);
}

#[dfpp::analyze]
fn conditional_happens_before(cond: bool) {
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
fn args(mut x: i32) {
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



#[dfpp::label(there, arguments = [0])]
fn receiver(x: i32) {}

#[dfpp::label{ sink, arguments = [0] }]
fn send_user_data(user_data: &UserData) {}

fn main() {
    println!("Hello, world!");
}
