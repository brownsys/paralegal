# Before editing this script ensure you have read and understood the
# relationship of the scripts with one another and with the CI as alid out in
# the README.md in this directory.

set -e

cargo rustdoc -p paralegal-spdg -- -Drustdoc::all
cargo rustdoc -p paralegal-policy -- -Drustdoc::all
cargo rustdoc -p paralegal -- -Drustdoc::all