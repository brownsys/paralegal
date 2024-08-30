#[paralegal::marker(source, return)]
fn source() -> usize {
    0
}

#[paralegal::marker(pass, arguments = [0])]
fn pass<T>(t: T) -> T {
    t
}

#[paralegal::marker(target, arguments = [0])]
fn target(i: usize) {}

#[paralegal::analyze]
fn thread_spawn() {
    let src = source();
    let next = std::thread::spawn(move || pass(src)).join().unwrap();
    target(next);
}

fn main() {}

#[paralegal::analyze]
async fn async_spawn() {
    let src = source();
    let next = tokio::spawn(async move { pass(src) }).await.unwrap();
    target(next);
}

fn to_block() -> Result<usize, actix_web::error::BlockingError> {
    Ok(source())
}

#[paralegal::analyze]
async fn block_fn() -> Result<(), actix_web::error::BlockingError> {
    Ok(target(actix_web::web::block(to_block).await?? + 1))
}

#[paralegal::analyze]
async fn block_closure(to_close_over: usize) -> Result<(), actix_web::error::BlockingError> {
    Ok(target(
        actix_web::web::block(move || Ok(source() + to_close_over)).await?? + 1,
    ))
}

#[paralegal::analyze]
async fn strategic_overtaint(to_close_over: usize) -> Result<(), actix_web::error::BlockingError> {
    Ok(target(
        actix_web::web::block(move || Ok((source(), to_close_over)))
            .await??
            .0,
    ))
}

#[paralegal::analyze]
async fn strategic_overtaint_2(
    to_close_over: usize,
) -> Result<(), actix_web::error::BlockingError> {
    Ok(target(
        actix_web::web::block(move || Ok((source(), to_close_over)))
            .await??
            .1,
    ))
}

#[paralegal::analyze]
async fn no_taint_without_connection(
    to_close_over: usize,
) -> Result<(), actix_web::error::BlockingError> {
    Ok(target(
        actix_web::web::block(move || {
            let _no_use = source();
            Ok(to_close_over)
        })
        .await??,
    ))
}
