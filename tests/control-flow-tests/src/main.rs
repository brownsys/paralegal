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

#[dfpp::analyze]
fn process_nested_if() {
    let user_data = get_user_data();
    if check_user_data(&user_data) {
		if check2(&user_data) {
			send_user_data(&user_data);
		}
    }
}

#[dfpp::analyze]
fn process_if_multiple_statements() {
    let mut user_data = get_user_data();
    if check_user_data(&user_data) {
		modify(&mut user_data);
		send_user_data(&user_data);
    }
}

#[dfpp::analyze]
fn process_if_not_function_call() {
	let x = get_x();
	let mut user_data = get_user_data();
    if x > 5 {
		modify(&mut user_data);
    }
	send_user_data(&user_data);
}

#[dfpp::analyze]
fn process_no_args() {
	let x = get_x();
	let mut user_data = UserData{data: vec![]};
    if x > 5 {
		user_data = get_user_data();
    }
	send_user_data(&user_data);
}

#[dfpp::label{ noinline, return }]
fn get_x() -> i64 {
    return 5;
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

#[dfpp::label{checks, arguments = [0]}]
fn check2(user_data: &UserData) -> bool {
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

#[dfpp::label{ noinline, return }] // TODO: After call-chain-analysis is fixed this label can be removed.
fn modify(_user_data: &mut UserData) {
}

fn main() {}
