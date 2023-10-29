# Before editing this script ensure you have read and understood the
# relationship of the scripts with one another and with the CI as alid out in
# the README.md in this directory.

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

echo "Formatting Check"
$SCRIPT_DIR/format.sh fmt-check

echo "Clippy Check"
$SCRIPT_DIR/format.sh clippy-check

echo "Documentation Check"
$SCRIPT_DIR/doc-check.sh
