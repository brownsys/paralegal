#![feature(register_tool)]
#![register_tool(dfpp)]

#[dfpp::label(sensitive)]
struct UserData {
    pub data: Vec<i64>,
}

#[dfpp::analyze]
fn process_if() {
    let user_data = get_user_data();
    if check_user_data(&user_data) {
        send_user_data(&user_data);
    }
}

#[dfpp::analyze]
fn process_basic() {
    let user_data = get_user_data();
    check_user_data(&user_data);
    send_user_data(&user_data);
}

#[dfpp::analyze]
fn process_if_after() {
    let mut user_data = get_user_data();
    if check_user_data(&user_data) {
        modify(&mut user_data);
    }
    send_user_data(&user_data);
}

#[dfpp::label{source, return}]
fn get_user_data() -> UserData {
    return UserData{data: vec![1, 2, 3]}
}

#[dfpp::label{checks, arguments = [0]}]
fn check_user_data(user_data: &UserData) -> bool {
    for i in &user_data.data {
        if i < &0 {
            return false
        }
    }
    return true
}

#[dfpp::label{ sink, arguments = [0] }]
fn send_user_data(_user_data: &UserData) {
}

fn modify(_user_data: &mut UserData) {
}

fn main() {}
