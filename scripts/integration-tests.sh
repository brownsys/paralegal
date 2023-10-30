# Before editing this script ensure you have read and understood the
# relationship of the scripts with one another and with the CI as alid out in
# the README.md in this directory.

set -x

cargo test -p paralegal-flow --test external_annotation_tests