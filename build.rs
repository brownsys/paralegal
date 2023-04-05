use std::process::Command;

fn main() {
    println!(
        "cargo:rustc-env=COMMIT_HASH={}",
        Command::new("git")
            .args(&["log", "-n", "1", "--pretty=format:\"%H\""])
            .output()
            .ok()
            .and_then(|o| String::from_utf8(o.stdout).ok())
            .unwrap_or("unknown".to_owned())
    );
}
