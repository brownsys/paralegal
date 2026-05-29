#[paralegal::marker(bin_marker)]
fn marked_in_bin() {}

#[paralegal::analyze]
fn entrypoint() {
    marked_in_bin();
}

fn main() {
    entrypoint();
}
