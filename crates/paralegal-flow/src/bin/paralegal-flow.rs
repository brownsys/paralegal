#![feature(rustc_private)]

extern crate rustc_plugin;

#[derive(Default)]
struct VersionArgs {
    verbose: bool,
    version: bool,
}

impl VersionArgs {
    pub fn parse_args(args: impl IntoIterator<Item = impl AsRef<str>>) -> Self {
        let mut version_args = Self::default();
        version_args.handle_args(args);
        version_args
    }

    fn handle_args(&mut self, a: impl IntoIterator<Item = impl AsRef<str>>) {
        for i in a {
            self.handle_arg(i.as_ref());
        }
    }

    fn handle_arg(&mut self, a: &str) {
        let mut chars = a.chars();
        if chars.next() != Some('-') {
            return;
        }
        let second = chars.next();
        if second == Some('-') {
            self.handle_long_arg(&a[2..])
        }
        for c in second.into_iter().chain(chars) {
            self.handle_short_arg(c);
        }
    }

    fn handle_short_arg(&mut self, c: char) {
        match c {
            'V' => self.version = true,
            'v' => self.verbose = true,
            _ => (),
        }
    }

    fn handle_long_arg(&mut self, s: &str) {
        match s {
            "verbose" => self.verbose = true,
            "version" => self.version = true,
            _ => (),
        }
    }
}

const REAL_LONG_VERSION: &str = env!("RUSTC_LONG_VERSION");
const LONG_VERSION: &str = "rustc 1.84.1 (e71f9a9a9 2025-01-27)
binary: rustc
commit-hash: e71f9a9a98b0faf423844bf0ba7438f29dc27d58
commit-date: 2025-01-27
host: no-host-defined
release: 1.84.1
LLVM version: 19.1.5
";

const HOST: &str = env!("HOST");

fn unescape_version(s: &str) -> String {
    s.replace("\\n", "\n")
}

fn main() {
    let use_real_version = matches!(std::env::var("PARALEGAL_USE_REAL_RUSTC_VERSION"), Ok(v) if v == "1" || v.eq_ignore_ascii_case("true"));
    let args = std::env::args();
    let version_args = VersionArgs::parse_args(args);
    let long_version = if use_real_version {
        REAL_LONG_VERSION
    } else {
        LONG_VERSION
    };
    let unescaped = unescape_version(long_version);
    if version_args.version {
        if version_args.verbose {
            print!("{}", unescaped.replace("no-host-defined", HOST));
        } else {
            let short_version = &unescaped
                .lines()
                .next()
                .expect("Expected at least one line in version string");
            println!("{}", unescape_version(short_version));
        }
        std::process::exit(0);
    }
    rustc_plugin::driver_main(paralegal_flow::DfppPlugin);
}
