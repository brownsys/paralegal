## What Changed?

<!-- 
A summary of what you are proposing to change.
-->

## Why Does It Need To?

<!-- 
Describe the concern this change addresses. 

Reference any issues that are related and use closing words such as "fixes" or
"closes" if those issues would be fully addressed by this PR. 

You can find out more about closing words here:
https://docs.github.com/en/get-started/writing-on-github/working-with-advanced-formatting/using-keywords-in-issues-and-pull-requests

Try to make your PR about one single concern or issue, unless they are mutually dependent.
-->

## Checklist

- [ ] Above description has been filled out so that upon quash merge we have a
  good record of what changed.
- [ ] New functions, methods, types are documented. Old documentation is updated
  if necessary
- [ ] Documentation in Notion has been updated
- [ ] Tests for new behaviors are provided
  - [ ] New test suites (if any) ave been added to the CI tests (in
    `.github/workflows/rust.yml`) either as compiler test or integration test.
    *Or* justification for their omission from CI has been provided in this PR
    description.