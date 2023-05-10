#![feature(register_tool)]
#![register_tool(dfpp)]


#[dfpp::label(noinline)]
async fn f() -> usize {
    0
}

#[dfpp::label(noinline)]
fn some_input() -> usize {
    0
}

#[dfpp::label(target)]
fn target(i: usize) {

}

#[dfpp::analyze]
async fn remove_poll_match() {
    let p = some_input();
    let x = f().await;
    let y = target(p);
    ()
}


