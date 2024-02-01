# Before editing this script ensure you have read and understood the
# relationship of the scripts with one another and with the CI as laid out in
# the README.md in this directory.

set -e

SCRIPT_DIR="$( cd "$( dirname "$0" )" &> /dev/null && pwd )"

# cd into root directory of the repo
cd $SCRIPT_DIR/..

cargo test -p paralegal-flow --test non_transitive_graph_tests
cargo test -p paralegal-flow --test call_chain_analysis_tests
cargo test -p paralegal-flow --test control_flow_tests
cargo test -p paralegal-flow --test new_alias_analysis_tests
cargo test -p paralegal-flow --test async_tests
#cargo test -p paralegal-flow --test inline_elision_tests
cargo test -p paralegal-policy --lib

echo "Build Test Policies"

cargo -C props build --verbose

echo "Test Guide Project"

cargo -C guide/deletion-policy run
