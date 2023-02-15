
extern crate async_std;
use async_std::prelude::*;



async fn a_fn() {
    async_std::path::Path::new("test").is_file().await
}

fn main() {}