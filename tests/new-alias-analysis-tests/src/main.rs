#![feature(register_tool)]
#![register_tool(dfpp)]

#[dfpp::label(sensitive)]
struct UserData {
    pub data: Vec<i64>,
}

#[dfpp::label(source)]
fn get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[dfpp::label(source)]
fn get_user_data2() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}

#[dfpp::label(yey_dfpp_now_needs_this_label_or_it_will_recurse_into_this_function, return)]
fn dp_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

#[dfpp::label{ sink, arguments = [0] }]
fn send_user_data(user_data: &UserData) {}

#[dfpp::label{ sink, arguments = [0] }]
fn send_user_data2(user_data: &UserData) {}

#[dfpp::label(noinline, return)]
fn modify_it(x: &mut u32) {}

#[dfpp::analyze]
fn track_mutable_modify() {
    let mut x = new_s();
    modify_it(&mut x.field);
    read(&x)
}

struct S {
    field: u32,
    field2: u32,
}

#[dfpp::label(noinline, return)]
fn new_s() -> S { S {field: 0, field2: 1} }

#[dfpp::label(noinline)]
fn deref_t(s: &S) -> &String {
    unimplemented!();
}

#[dfpp::analyze]
fn eliminate_return_connection() {
    let s = new_s();
    // 'a : 'b
    let t  = deref_t(&s);
    read(t);
}

#[dfpp::label(noinline)]
fn read<T>(t: &T) {}

#[dfpp::analyze]
fn eliminate_mut_input_connection() {
    let mut s : S = new_s();
    let mut v = Vec::new();
    v.push(&s);
    read(&v);
}

fn insert_ref<'v, 't: 'v, T>(v : &mut Vec<&'v T>, t: &'t T) {}
fn insert_ref_2<'v, 't: 'v, T>(v : &mut Vec<&'v T>, t: &'t T) {
    v.push(t)
}

#[dfpp::analyze]
fn input_elimination_isnt_a_problem_empty() {
    let x = new_s();
    let mut v = Vec::new();
    insert_ref(& mut v, &x);
    read(&v);
}

#[dfpp::analyze]
fn input_elimination_isnt_a_problem_vec_push() {
    let x = new_s();
    let mut v = Vec::new();
    v.insert(0, &x);
    insert_ref_2( & mut v, &x);
    read(&v);
}

struct T<'a> {
    field: &'a S
}

#[dfpp::label(noinline)]
fn new_t<'a>() -> T<'a> {
    unimplemented!()
}

#[dfpp::label(noinline)]
fn another_s() -> S {
    unimplemented!()
}


#[dfpp::label(noinline)]
fn assoc<'a, 'b : 'a>(x: &mut T<'a>, s: &'b S) {

}

#[dfpp::analyze]
fn input_elimination_isnt_a_problem_statement() {
    let ref r = new_s();
    let ref r2 = another_s();

    let mut x = new_t();

    assoc(&mut x, r);

    x.field = r2;

    read(&x);
}

fn arity2_inlineable_async_dp_user_data(ud: &(&mut UserData, &mut UserData)) {
    dp_user_data(ud.1)
}

#[dfpp::analyze]
fn no_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get_user_data2();
    arity2_inlineable_async_dp_user_data(&(&mut ud1, &mut ud2));
    send_user_data(&ud1);
    send_user_data2(&ud2);
}