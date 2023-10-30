# The CI in script form.

This directory contains the scripts that run our CI activity and checks. The
idea is that these scripts let you easily replicate CI steps locally.

`integration-tests.sh` and `compiler-tests.sh` are for testing.
`dock-check.sh` lints the documentation of the public-facing crates.
`format.sh` is responsible for `clippy` and `rustfmt` checks.
To run all doc and format checks use `check-all.sh`.

In addition there are the "companion scripts" for `clippy` and `rustfmt` which
apply the suggested fixes by passing `clippy-fix` and `fmt-fix` to `format.sh`
respectively. Most of the time you'll want to use `fix-all.sh` which invokes
both in series, to get your code in the shape the CI expects.