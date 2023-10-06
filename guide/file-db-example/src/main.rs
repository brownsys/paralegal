//! Stores
//!
//! db/
//!  |-- img/
//!  |    |-- username.filename.jpg
//!  |-- doc/
//!       |-- username.docname.txt

#![feature(register_tool)]
#![register_tool(paralegal_flow)]

struct User {
    name: String,
}

#[paralegal_flow::marker(user_data)]
struct Image {
    user: User,
    name: String,
}

impl Image {
    fn for_user(user: &User) -> Vec<Self> {
        todo!()
    }

    fn delete(self) {
        std::fs::remove_file(
            std::path::Path::new("db")
                .join("img")
                .join(format!("{}-{}.jpg", self.user.name, self.name)),
        ).unwrap()
    }
}

#[paralegal_flow::marker(user_data)]
struct Document {
    user: User,
    name: String,
}

impl Document {
    fn for_user(user: &User) -> Vec<Self> {
        todo!()
    }

    fn delete(self) {
        std::fs::remove_file(
            std::path::Path::new("db")
                .join("doc")
                .join(format!("{}-{}.txt", self.user.name, self.name)),
        ).unwrap()
    }
}

#[paralegal_flow::analyze]
fn delete(user: User) {
    for doc in Document::for_user(&user) {
        doc.delete()
    }
}

fn main() {
    let mut args = std::env::args().skip(1);

    match args.next().unwrap().as_str() {
        "delete" => delete(User {
            name: args.next().unwrap(),
        }),
        other => panic!("Command not implemented {other}"),
    }
}
