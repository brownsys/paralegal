# Before editing this script ensure you have read and understood the
# relationship of the scripts with one another and with the CI as laid out in
# the README.md in this directory.

set -e

SCRIPT_DIR="$( cd "$( dirname "$0" )" &> /dev/null && pwd )"

$SCRIPT_DIR/format.sh fmt-fix
$SCRIPT_DIR/format.sh clippy-fix
