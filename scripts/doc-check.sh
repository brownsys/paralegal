# Before editing this script ensure you have read and understood the
# relationship of the scripts with one another and with the CI as laid out in
# the README.md in this directory.

set -e

SCRIPT_DIR="$( cd "$( dirname "$0" )" &> /dev/null && pwd )"

# cd into root directory of the repo
cd $SCRIPT_DIR/..

cargo rustdoc -p paralegal-spdg -- -Drustdoc::all
cargo rustdoc -p paralegal-policy -- -Drustdoc::all
cargo rustdoc -p paralegal -- -Drustdoc::all