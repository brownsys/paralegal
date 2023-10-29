# Before editing this script ensure you have read and understood the
# relationship of the scripts with one another and with the CI as alid out in
# the README.md in this directory.

set -e

ARGS=

case $1 in
    clippy-check)
        CMD="clippy --all"
        ARGS="-D warnings"
        PREFIX=Checking
        ;;
    clipp-yfix)
        CMD="clippy --fix --all"
        ARGS="-D warnings"
        PREFIX=Fixing
        ;;
    fmt-check)
        CMD="fmt --check"
        INCLUDE_TESTS=
        PREFIX=Checking
        ;;
    fmt-fix)
        CMD=fmt
        INCLUDE_TESTS=
        PREFIX=Fixing
        ;;
    *)
        echo "Unknown command '$1'"
        exit 1
        ;;
esac

function run() {
    cargo $@ $CMD  -- $ARGS
}

echo "$PREFIX main repo"
run

echo "$PREFIX properties"
run -C props

echo "$PREFIX Guide Project"
run -C guide/file-db-example

echo "$PREFIX Guide Policy"
run -C guide/deletion-policy

echo "$PREFIX Test Crates"

TEST_DIR=crates/paralegal-flow/tests

if [ -n "${INCLUDE_TESTS+x}" ]
then
    for dir in $(ls $TEST_DIR)
    do

        if [ -a "$TEST_DIR/$dir/Cargo.toml" ]
        then
            echo $PREFIX $dir
            run -C "$TEST_DIR/$dir"
        fi
    done
fi