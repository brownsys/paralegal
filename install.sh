#!/bin/sh
# Paralegal from-source installer.
#
# Why from-source: Paralegal's analysis binary (`paralegal-flow-impl`) is a
# rustc *driver* — it links `librustc_driver`/`libLLVM` from one specific nightly
# toolchain, pinned in this repo's `rust-toolchain.toml`. A single portable
# prebuilt binary is therefore impractical, so this installer builds against the
# pinned toolchain, which `rustup` provisions automatically from
# `rust-toolchain.toml` (including the `rustc-dev`/`rust-src` components). A
# faster prebuilt-binary path is planned separately; see RELEASE_PLAN.md.
#
# Usage:
#   curl -fsSL https://raw.githubusercontent.com/brownsys/paralegal/main/install.sh | sh
#   curl -fsSL .../install.sh | sh -s -- --version v0.1.0
#
# Options:
#   --version <ref>   git tag or branch to install (default: latest release tag,
#                     or `main` when there are no releases yet)
#   --source-dir <d>  build from an existing local checkout instead of cloning
#                     (also handy for offline / development installs)
#   --root <dir>      install into <dir>/bin instead of cargo's default
#                     (~/.cargo/bin). Mirrors `cargo install --root`.
#   -h, --help        show this help

set -eu

REPO="brownsys/paralegal"
REPO_URL="https://github.com/$REPO"
VERSION="latest"
SOURCE_DIR=""
INSTALL_ROOT=""

# Workspace crates that provide installable binaries:
#   cli      -> cargo-paralegal-flow (the `cargo paralegal-flow` subcommand; it
#               self-creates the `paralegal-flow` rustc-wrapper shim at runtime)
#   plugin   -> paralegal-flow-impl  (the rustc driver; the toolchain-bound part)
#   compiler -> paralegal-compiler   (the policy / CNL compiler)
CRATES="cli plugin compiler"

usage() {
    cat <<'EOF'
Paralegal from-source installer.

Builds Paralegal against the nightly toolchain pinned in rust-toolchain.toml
(provisioned automatically by rustup) and installs the binaries with cargo.

Usage:
  curl -fsSL https://raw.githubusercontent.com/brownsys/paralegal/main/install.sh | sh
  curl -fsSL .../install.sh | sh -s -- --version v0.1.0

Options:
  --version <ref>   git tag or branch to install (default: latest release tag,
                    or 'main' when there are no releases yet)
  --source-dir <d>  build from an existing local checkout instead of cloning
  --root <dir>      install into <dir>/bin instead of cargo's default ~/.cargo/bin
  -h, --help        show this help
EOF
}

while [ $# -gt 0 ]; do
    case "$1" in
        --version) VERSION="$2"; shift 2 ;;
        --version=*) VERSION="${1#--version=}"; shift ;;
        --source-dir) SOURCE_DIR="$2"; shift 2 ;;
        --source-dir=*) SOURCE_DIR="${1#--source-dir=}"; shift ;;
        --root) INSTALL_ROOT="$2"; shift 2 ;;
        --root=*) INSTALL_ROOT="${1#--root=}"; shift ;;
        -h|--help) usage; exit 0 ;;
        *) echo "paralegal: unknown argument: $1" >&2; exit 2 ;;
    esac
done

# --- prerequisites -------------------------------------------------------
# rustup specifically (not just any cargo): the pinned nightly and its
# rustc-dev/rust-src components are provisioned from rust-toolchain.toml, which
# only rustup honors. A distro cargo would ignore the pin and fail to build the
# rustc-driver crate.
if ! command -v rustup >/dev/null 2>&1; then
    echo "paralegal: rustup is required — it provisions the pinned nightly toolchain." >&2
    echo "Install it from https://rustup.rs and re-run this script." >&2
    exit 1
fi
if ! command -v cargo >/dev/null 2>&1; then
    echo "paralegal: cargo not found on PATH (expected alongside rustup)." >&2
    exit 1
fi

# --- obtain the source ---------------------------------------------------
cleanup=""
trap 'test -n "$cleanup" && rm -rf "$cleanup"' EXIT

if [ -n "$SOURCE_DIR" ]; then
    srcdir="$SOURCE_DIR"
    [ -f "$srcdir/rust-toolchain.toml" ] || {
        echo "paralegal: $srcdir does not look like a paralegal checkout." >&2
        exit 1
    }
    echo "paralegal: building from local checkout $srcdir" >&2
else
    command -v git >/dev/null 2>&1 || {
        echo "paralegal: git is required to fetch the source (or pass --source-dir)." >&2
        exit 1
    }
    ref="$VERSION"
    if [ "$ref" = "latest" ]; then
        # Resolve the highest `v*` tag without hitting the API (avoids rate
        # limits and a JSON dependency). Empty result => no releases yet.
        ref=$(git ls-remote --tags --refs --sort=-v:refname "$REPO_URL" 'v*' 2>/dev/null \
              | sed 's#.*refs/tags/##' | head -n1)
        if [ -z "$ref" ]; then
            echo "paralegal: no release tags found yet; installing from 'main'." >&2
            ref="main"
        else
            echo "paralegal: latest release is $ref" >&2
        fi
    fi
    tmp=$(mktemp -d)
    cleanup="$tmp"
    echo "paralegal: cloning $REPO at $ref" >&2
    git clone --depth 1 --branch "$ref" "$REPO_URL" "$tmp/paralegal"
    srcdir="$tmp/paralegal"
fi

# --- build & install -----------------------------------------------------
# Run cargo from inside the checkout so rust-toolchain.toml selects the pinned
# nightly. The first build provisions that toolchain and compiles the
# rustc-driver crate, which takes a few minutes.
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

# --- report --------------------------------------------------------------
if [ -n "$INSTALL_ROOT" ]; then
    bindir="$INSTALL_ROOT/bin"
else
    bindir="${CARGO_HOME:-$HOME/.cargo}/bin"
fi
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
