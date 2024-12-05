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

#[allow(dead_code)]
#[paralegal::analyze]
fn thread_spawn() {
    let src = source();
    let next = std::thread::spawn(move || pass(src)).join().unwrap();
    target(next);
}

#[allow(dead_code)]
#[paralegal::analyze]
fn marked_thread_spawn() {
    let next = std::thread::spawn(source).join().unwrap();
    target(next);
}

#[allow(dead_code)]
#[paralegal::analyze]
fn marked_blocking_like(to_close_over: &str) {
    let next = blocking_like(to_close_over, second_source);
    target(next);
}

#[allow(dead_code)]
#[paralegal::analyze]
fn test_blocking_like(to_close_over: &str) {
    let next = blocking_like(to_close_over, |_| second_source(0_usize));
    target(next);
}

pub fn blocking_like<F, T>(pool: &str, f: F) -> T
where
    F: FnOnce(usize) -> T + 'static + Send,
    T: 'static + Send,
{
    let pool = pool.parse().unwrap();
    let res = std::thread::spawn(move || (f)(pool)).join().unwrap();

    res
}

fn main() {}

#[allow(dead_code)]
#[paralegal::analyze]
async fn async_spawn() {
    let src = source();
    let next = tokio::spawn(async move { pass(src) }).await.unwrap();
    target(next);
}

#[paralegal::marker(source, return)]
async fn async_source() -> usize {
    0
}

#[allow(dead_code)]
#[paralegal::analyze]
async fn marked_async_spawn() {
    let next = tokio::spawn(async_source()).await.unwrap();
    target(next);
}

fn to_block() -> Result<usize, actix_web::error::BlockingError> {
    Ok(source())
}

#[allow(dead_code)]
#[paralegal::analyze]
async fn block_fn() -> Result<(), actix_web::error::BlockingError> {
    Ok(target(actix_web::web::block(to_block).await?? + 1))
}

#[allow(dead_code)]
#[paralegal::analyze]
async fn block_closure(to_close_over: usize) -> Result<(), actix_web::error::BlockingError> {
    Ok(target(
        actix_web::web::block(move || Ok(source() + to_close_over)).await?? + 1,
    ))
}

pub async fn blocking<F, T>(pool: &str, f: F) -> T
where
    F: FnOnce(usize) -> T + 'static + Send,
    T: 'static + Send,
{
    let pool = pool.parse().unwrap();
    let res = actix_web::web::block(move || (f)(pool)).await.unwrap();

    res
}

#[paralegal::marker(source, return)]
fn second_source<T>(_: T) -> usize {
    0
}

#[allow(dead_code)]
#[paralegal::analyze]
async fn blocking_with_marker(to_close_over: &str) {
    target(blocking(to_close_over, second_source).await)
}

#[allow(dead_code)]
#[paralegal::analyze]
async fn test_blocking_with_let_bound_closure(to_close_over: &str) {
    let from_scope = 10;
    let the_closure = move |u| u + source() + from_scope;
    target(blocking(to_close_over, the_closure).await);
}

#[allow(dead_code)]
#[paralegal::analyze]
async fn strategic_overtaint(to_close_over: usize) -> Result<(), actix_web::error::BlockingError> {
    Ok(target(
        actix_web::web::block(move || Ok((source(), to_close_over)))
            .await??
            .0,
    ))
}

#[allow(dead_code)]
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

#[allow(dead_code)]
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
