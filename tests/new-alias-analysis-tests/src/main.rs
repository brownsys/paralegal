#![feature(register_tool)]
#![register_tool(dfpp)]

#[dfpp::label(noinline, return)]
fn modify_it(x: &mut u32) {}

#[dfpp::analyze]
fn track_mutable_modify() {
    let mut x = new_s();
    modify_it(&mut x.field);
    read(&x)
}

struct S {
    field: u32
}

#[dfpp::label(noinline, return)]
fn new_s() -> S { S {} }

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
    v.push(v)
}

#[dfpp::analyze]
fn input_collection_elimination_isnt_a_problem_empty() {
    let x = new_s();
    let mut v = Vec::new();
    insert_ref(& mut v, &x);
    read(&v);
}

#[dfpp::analyze]
fn input_collection_elimination_isnt_a_problem_vec_push() {
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
fn another_s() -> S {
    unimplemented!()
}


#[dfpp::label(noinline)]
fn assoc<'a, 'b : 'a>(x: &mut T<'a>, s: &'b S) {

}

fn input_elimination_isnt_a_problem_statement() {
    let ref r = new_s();
    let ref r2 = another_s();

    let mut x = new_s();

    assoc(&mut x, r);

    x.field = r2;

    read(&x);
}