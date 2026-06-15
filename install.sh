#!/bin/sh
# Paralegal installer.
#
# Paralegal's analysis binary (`paralegal-flow-impl`) is a rustc *driver*: it
# links `librustc_driver`/`libLLVM` from a specific nightly toolchain, pinned in
# this repo's `rust-toolchain.toml`. There are two install paths:
#
#   prebuilt  — download binaries built against the pinned toolchain, then point
#               them at a locally-installed copy of that toolchain (a `toolchain`
#               symlink the binaries' rpath resolves). Avoids the local compile.
#   source    — build from a checkout against the pinned toolchain.
#
# Either way `rustup` must provision the pinned nightly (with `rustc-dev`/
# `rust-src`); prebuilt only saves the compile, not the toolchain download.
# Default is `auto`: prebuilt when a binary exists for this platform, else source.
#
# Usage:
#   curl -fsSL https://raw.githubusercontent.com/brownsys/paralegal/main/install.sh | sh
#   curl -fsSL .../install.sh | sh -s -- --version v0.1.0
#
# Options:
#   --version <ref>      release tag to install (default: latest, or `main` for
#                        --from-source when there are no releases yet)
#   --from-source        always build from source
#   --prebuilt           require a prebuilt binary (fail if none for this platform)
#   --root <dir>         install prefix. Prebuilt: binaries in <dir>/bin and a
#                        <dir>/toolchain symlink (default ~/.paralegal). Source:
#                        passed to `cargo install --root` (default ~/.cargo).
#   --source-dir <d>     build from an existing local checkout (implies source)
#   --prebuilt-tarball <f>  install from a local prebuilt tarball (testing)
#   -h, --help

set -eu

REPO="brownsys/paralegal"
REPO_URL="https://github.com/$REPO"
VERSION="latest"
MODE="auto" # auto | prebuilt | source
SOURCE_DIR=""
INSTALL_ROOT=""
PREBUILT_TARBALL=""

# Workspace crates providing installable binaries:
#   cli      -> cargo-paralegal-flow (the `cargo paralegal-flow` subcommand)
#   plugin   -> paralegal-flow-impl  (the rustc driver; toolchain-bound)
#   compiler -> paralegal-compiler   (the policy / CNL compiler)
CRATES="cli plugin compiler"

usage() {
    cat <<'EOF'
Paralegal installer.

Installs Paralegal either from a prebuilt binary (downloaded + pointed at a
locally-installed copy of the pinned nightly toolchain) or by building from
source. Both need rustup; see --help options below.

Options:
  --version <ref>         release tag to install (default: latest)
  --from-source           always build from source
  --prebuilt              require a prebuilt binary (fail if none for platform)
  --root <dir>            install prefix (prebuilt: <dir>/bin + <dir>/toolchain,
                          default ~/.paralegal; source: cargo --root, ~/.cargo)
  --source-dir <d>        build from an existing local checkout (implies source)
  --prebuilt-tarball <f>  install from a local prebuilt tarball (testing)
  -h, --help              show this help
EOF
}

while [ $# -gt 0 ]; do
    case "$1" in
        --version) VERSION="$2"; shift 2 ;;
        --version=*) VERSION="${1#--version=}"; shift ;;
        --from-source) MODE="source"; shift ;;
        --prebuilt) MODE="prebuilt"; shift ;;
        --source-dir) SOURCE_DIR="$2"; MODE="source"; shift 2 ;;
        --source-dir=*) SOURCE_DIR="${1#--source-dir=}"; MODE="source"; shift ;;
        --root) INSTALL_ROOT="$2"; shift 2 ;;
        --root=*) INSTALL_ROOT="${1#--root=}"; shift ;;
        --prebuilt-tarball) PREBUILT_TARBALL="$2"; MODE="prebuilt"; shift 2 ;;
        --prebuilt-tarball=*) PREBUILT_TARBALL="${1#--prebuilt-tarball=}"; MODE="prebuilt"; shift ;;
        -h|--help) usage; exit 0 ;;
        *) echo "paralegal: unknown argument: $1" >&2; exit 2 ;;
    esac
done

# rustup specifically (not just any cargo): the pinned nightly and its
# rustc-dev/rust-src components are provisioned from rust-toolchain.toml (source)
# or installed by name (prebuilt) — both via rustup.
need_rustup() {
    command -v rustup >/dev/null 2>&1 || {
        echo "paralegal: rustup is required — it provisions the pinned nightly toolchain." >&2
        echo "Install it from https://rustup.rs and re-run this script." >&2
        exit 1
    }
}

cleanup=""
trap 'test -n "$cleanup" && rm -rf "$cleanup"' EXIT

# Map uname to the release asset triple. Empty => no prebuilt for this platform.
detect_triple() {
    os=$(uname -s)
    arch=$(uname -m)
    case "$os/$arch" in
        Linux/x86_64) echo "x86_64-unknown-linux-gnu" ;;
        Linux/aarch64|Linux/arm64) echo "aarch64-unknown-linux-gnu" ;;
        Darwin/arm64) echo "aarch64-apple-darwin" ;;
        *) echo "" ;;
    esac
}

verify_sha256() {
    # $1 = file, $2 = expected hex
    if command -v sha256sum >/dev/null 2>&1; then
        actual=$(sha256sum "$1" | awk '{print $1}')
    elif command -v shasum >/dev/null 2>&1; then
        actual=$(shasum -a 256 "$1" | awk '{print $1}')
    else
        echo "paralegal: neither sha256sum nor shasum found; cannot verify download." >&2
        exit 1
    fi
    [ "$actual" = "$2" ] || {
        echo "paralegal: checksum mismatch (expected $2, got $actual)." >&2
        exit 1
    }
}

install_prebuilt() {
    need_rustup
    tmp=$(mktemp -d); cleanup="$tmp"

    if [ -n "$PREBUILT_TARBALL" ]; then
        tarball="$PREBUILT_TARBALL"
        echo "paralegal: using local prebuilt tarball $tarball" >&2
    else
        triple=$(detect_triple)
        [ -n "$triple" ] || { echo "paralegal: no prebuilt binary for $(uname -s)/$(uname -m)." >&2; return 1; }
        if [ "$VERSION" = "latest" ]; then
            base="$REPO_URL/releases/latest/download"
        else
            base="$REPO_URL/releases/download/$VERSION"
        fi
        asset="paralegal-$triple.tar.gz"
        echo "paralegal: downloading $asset ($VERSION)" >&2
        # -f so a missing asset (404) is an error we can fall back on.
        curl -fsSL "$base/$asset" -o "$tmp/p.tar.gz" || return 1
        curl -fsSL "$base/$asset.sha256" -o "$tmp/p.tar.gz.sha256" || return 1
        verify_sha256 "$tmp/p.tar.gz" "$(awk '{print $1}' "$tmp/p.tar.gz.sha256")"
        tarball="$tmp/p.tar.gz"
    fi

    mkdir -p "$tmp/x"
    tar xzf "$tarball" -C "$tmp/x"
    [ -d "$tmp/x/bin" ] || { echo "paralegal: malformed tarball (no bin/)." >&2; exit 1; }
    toolchain=$(cat "$tmp/x/paralegal-toolchain.txt" 2>/dev/null || true)
    [ -n "$toolchain" ] || { echo "paralegal: tarball missing paralegal-toolchain.txt." >&2; exit 1; }

    echo "paralegal: installing toolchain $toolchain (rustc-dev, rust-src)…" >&2
    # Must succeed: the binaries link against this toolchain's libs at runtime,
    # so a failure here would otherwise leave a dangling `toolchain` symlink.
    rustup toolchain install "$toolchain" -c rustc-dev -c rust-src >&2 || {
        echo "paralegal: failed to install toolchain $toolchain." >&2
        exit 1
    }

    prefix="${INSTALL_ROOT:-$HOME/.paralegal}"
    mkdir -p "$prefix/bin"
    cp "$tmp/x/bin/"* "$prefix/bin/"
    chmod +x "$prefix/bin/"*
    # The binaries' rpath ($ORIGIN/../toolchain/lib) and the cli's runtime
    # toolchain lookup both resolve through this symlink.
    tc_root=$(rustup run "$toolchain" rustc --print sysroot)
    rm -f "$prefix/toolchain"
    ln -s "$tc_root" "$prefix/toolchain"

    bindir="$prefix/bin"
    report_done "$bindir"
}

install_source() {
    need_rustup
    command -v cargo >/dev/null 2>&1 || { echo "paralegal: cargo not found (expected via rustup)." >&2; exit 1; }

    if [ -n "$SOURCE_DIR" ]; then
        srcdir="$SOURCE_DIR"
        [ -f "$srcdir/rust-toolchain.toml" ] || { echo "paralegal: $srcdir is not a paralegal checkout." >&2; exit 1; }
        echo "paralegal: building from local checkout $srcdir" >&2
    else
        command -v curl >/dev/null 2>&1 || { echo "paralegal: curl is required to fetch the source (or pass --source-dir)." >&2; exit 1; }
        ref="$VERSION"
        if [ "$ref" = "latest" ]; then
            # Resolve the latest release tag via the releases/latest redirect
            # (no git, no JSON parsing). The effective URL ends in /tag/<tag>;
            # with no releases it lands on /releases, so we fall back to main.
            latest_url=$(curl -fsSL -o /dev/null -w '%{url_effective}' "$REPO_URL/releases/latest" 2>/dev/null || true)
            case "$latest_url" in
                */releases/tag/*) ref="${latest_url##*/tag/}"; echo "paralegal: latest release is $ref" >&2 ;;
                *) echo "paralegal: no release tags found yet; installing from 'main'." >&2; ref="main" ;;
            esac
        fi
        tmp=$(mktemp -d); cleanup="$tmp"
        echo "paralegal: downloading source for $ref" >&2
        # Pull GitHub's source archive — same artifact as a release's "Source
        # code" asset, no git needed. Try the tag archive, then the branch
        # archive, so a tag or a branch name both work.
        if ! curl -fsSL "$REPO_URL/archive/refs/tags/$ref.tar.gz" -o "$tmp/src.tar.gz" 2>/dev/null; then
            curl -fsSL "$REPO_URL/archive/refs/heads/$ref.tar.gz" -o "$tmp/src.tar.gz" || {
                echo "paralegal: could not download source for '$ref'." >&2
                exit 1
            }
        fi
        mkdir -p "$tmp/src"
        tar xzf "$tmp/src.tar.gz" -C "$tmp/src"
        # The archive expands to a single top-level dir whose name varies (the
        # leading `v` is stripped from tags), so glob for it rather than guess.
        srcdir=""
        for d in "$tmp/src"/*/; do
            [ -d "$d" ] && srcdir="${d%/}" && break
        done
        { [ -n "$srcdir" ] && [ -f "$srcdir/rust-toolchain.toml" ]; } || {
            echo "paralegal: extracted source archive doesn't look like a paralegal checkout." >&2
            exit 1
        }
    fi

    echo "paralegal: building and installing — the first build compiles the rustc driver" >&2
    echo "           and may provision the pinned toolchain; this can take several minutes." >&2
    for crate in $CRATES; do
        echo "paralegal: installing crates/$crate" >&2
        if [ -n "$INSTALL_ROOT" ]; then
            ( cd "$srcdir" && cargo install --locked -f --root "$INSTALL_ROOT" --path "crates/$crate" )
        else
            ( cd "$srcdir" && cargo install --locked -f --path "crates/$crate" )
        fi
    done

    if [ -n "$INSTALL_ROOT" ]; then
        report_done "$INSTALL_ROOT/bin"
    else
        report_done "${CARGO_HOME:-$HOME/.cargo}/bin"
    fi
}

report_done() {
    bindir="$1"
    echo ""
    echo "paralegal: installed cargo-paralegal-flow, paralegal-flow-impl and paralegal-compiler"
    echo "           to $bindir"
    case ":$PATH:" in
        *":$bindir:"*) ;;
        *)
            echo ""
            echo "Note: $bindir is not on your PATH. Add this to your shell rc:" >&2
            echo "  export PATH=\"$bindir:\$PATH\"" >&2
            ;;
    esac
    echo ""
    echo "Verify with:  cargo paralegal-flow --help"
}

case "$MODE" in
    source)
        install_source
        ;;
    prebuilt)
        install_prebuilt || { echo "paralegal: prebuilt install failed." >&2; exit 1; }
        ;;
    auto)
        # Prefer prebuilt when one exists for this platform; otherwise build.
        if [ -n "$(detect_triple)" ] && install_prebuilt; then
            :
        else
            echo "paralegal: falling back to a source build." >&2
            PREBUILT_TARBALL=""
            install_source
        fi
        ;;
esac
