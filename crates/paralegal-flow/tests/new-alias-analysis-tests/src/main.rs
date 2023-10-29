#[paralegal::marker(sensitive)]
struct UserData {
    pub data: Vec<i64>,
}

#[paralegal::marker(source)]
fn get_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}
#[paralegal::marker(source)]
fn get2_user_data() -> UserData {
    return UserData {
        data: vec![1, 2, 3],
    };
}

#[paralegal::marker(yey_paralegal_flow_now_needs_this_label_or_it_will_recurse_into_this_function, return)]
fn dp1_user_data(user_data: &mut UserData) {
    for i in &mut user_data.data {
        *i = 2;
    }
}

#[paralegal::marker{ sink, arguments = [0] }]
fn send_user_data(user_data: &UserData) {}

#[paralegal::marker{ sink, arguments = [0] }]
fn send2_user_data(user_data: &UserData) {}

#[paralegal::marker(noinline, return)]
fn modify_it(x: &mut u32) {}

#[paralegal::analyze]
fn track_mutable_modify() {
    let mut x = new_s();
    modify_it(&mut x.field);
    read(&x)
}

struct S {
    field: u32,
    field2: u32,
}

#[paralegal::marker(noinline, return)]
fn new_s() -> S { S {field: 0, field2: 1} }

#[paralegal::marker(noinline)]
fn deref_t(s: &S) -> &String {
    unimplemented!();
}

#[paralegal::analyze]
fn eliminate_return_connection() {
    let s = new_s();
    // 'a : 'b
    let t  = deref_t(&s);
    read(t);
}

#[paralegal::marker(noinline)]
fn read<T>(t: &T) {}

#[paralegal::analyze]
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

#[paralegal::analyze]
fn input_elimination_isnt_a_problem_empty() {
    let x = new_s();
    let mut v = Vec::new();
    insert_ref(& mut v, &x);
    read(&v);
}

#[paralegal::analyze]
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

#[paralegal::marker(noinline)]
fn new_t<'a>() -> T<'a> {
    unimplemented!()
}

#[paralegal::marker(noinline)]
fn another_s() -> S {
    unimplemented!()
}


#[paralegal::marker(noinline)]
fn assoc<'a, 'b : 'a>(x: &mut T<'a>, s: &'b S) {

}

#[paralegal::analyze]
fn input_elimination_isnt_a_problem_statement() {
    let ref r = new_s();
    let ref r2 = another_s();

    let mut x = new_t();

    assoc(&mut x, r);

    x.field = r2;

    read(&x);
}

fn arity2_inlineable_async_dp_user_data(ud: &mut (&mut UserData, &mut UserData)) {
    dp1_user_data(ud.1)
}

#[paralegal::analyze]
fn no_inlining_overtaint() {
    let mut ud1 = get_user_data();
    let mut ud2 = get2_user_data();
    arity2_inlineable_async_dp_user_data(&mut (&mut ud1, &mut ud2));
    send_user_data(&ud1);
    send2_user_data(&ud2);
}