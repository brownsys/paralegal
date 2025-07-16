//! Stores
//!
//! db/
//!  |-- img/
//!  |    |-- username.filename.jpg
//!  |-- doc/
//!       |-- username.docname.txt

#![allow(dead_code, unused_variables)]

struct User {
    name: String,
}

#[paralegal::marker(user_data)]
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
        )
        .unwrap()
    }
}

#[paralegal::marker(user_data)]
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
        )
        .unwrap()
    }
}

#[paralegal::analyze]
fn delete(user: User) {
    for doc in Document::for_user(&user) {
        doc.delete()
    }

    // Comment this back in to make the policy pass
    // for img in Image::for_user(&user) {
    //     img.delete()
    // }
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
