# Before editing this script ensure you have read and understood the
# relationship of the scripts with one another and with the CI as laid out in
# the README.md in this directory.

set -e

SCRIPT_DIR="$( cd "$( dirname "$0" )" &> /dev/null && pwd )"

# cd into root directory of the repo
cd $SCRIPT_DIR/..

ARGS=

case $1 in
    clippy-check)
        CMD="clippy --all"
        ARGS="-D warnings"
        PREFIX=Checking
        ;;
    clippy-fix)
        CMD="clippy --fix --allow-staged --all"
        ARGS="-D warnings"
        PREFIX=Fixing
        echo "
Note: You are using the clippy-fix command. Because this can introduce breaking changes this script only passes \`--allow-staged\` to the fix command. What this means for you is that you need to stage (or commit) your changes in git for the fix command to work. This is a precaution that allows you to inspect, test and potentially reject clippy's changes before accepting them.

Because we invoke the fix command multiple separate time it may fail again because of unstaged changes after applying the first fix. Inspect the changes, stage them and rerun the script until no more errors occur.
" | fmt -w 80
        ;;
    fmt-check | format-check)
        CMD="fmt --check"
        INCLUDE_TESTS=
        PREFIX=Checking
        ;;
    fmt-fix | format-fix)
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

    run -C "crates/paralegal-policy/tests/test-crate"
fi