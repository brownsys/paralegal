extern crate rustc_plugin;

struct VersionArgs {
    verbose: bool,
    version: bool,
}

impl Default for VersionArgs {
    fn default() -> Self {
        Self {
            verbose: false,
            version: false,
        }
    }
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

const REAL_SHORT_VERSION: &str = env!("RUSTC_SHORT_VERSION");
const REAL_LONG_VERSION: &str = env!("RUSTC_LONG_VERSION");

#[cfg(not(feature = "real-rustc-version"))]
const SHORT_VERSION: &str = "rustc 1.73.0 (cc66ad468 2023-10-03)
";
#[cfg(not(feature = "real-rustc-version"))]
const LONG_VERSION: &str = "rustc 1.73.0 (cc66ad468 2023-10-03)
binary: rustc
commit-hash: cc66ad468955717ab92600c770da8c1601a4ff33
commit-date: 2023-10-03
host: no-host-defined
release: 1.73.0
LLVM version: 17.0.2
";

const HOST: &str = env!("HOST");

fn unescape_version(s: &str) -> String {
    s.replace("\\n", "\n")
}

fn main() {
    let use_real_version = matches!(std::env::var("PARALEGAL_USE_REAL_RUSTC_VERSION"), Ok(v) if v == "1" || v.to_ascii_lowercase() == "true");
    let args = std::env::args();
    let version_args = VersionArgs::parse_args(args);
    let long_version = if use_real_version {
        REAL_LONG_VERSION
    } else {
        LONG_VERSION
    };
    let short_version = if use_real_version {
        REAL_SHORT_VERSION
    } else {
        SHORT_VERSION
    };
    if version_args.version {
        if version_args.verbose {
            print!(
                "{}",
                unescape_version(&long_version.replace("no-host-defined", HOST))
            );
        } else {
            print!("{}", unescape_version(short_version));
        }
        std::process::exit(0);
    }
    rustc_plugin::driver_main(paralegal_flow::DfppPlugin);
}
