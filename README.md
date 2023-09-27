# Paralegal

A tool for enforcing privacy policies on Rust code.

See our [Notion pages](https://www.notion.so/justus-adam/Dataflow-973fca6c36ca42a3ac8bc6be58edb909)
for details on [getting started](https://www.notion.so/justus-adam/Getting-Started-40541156c25d48f8b6ad79a0e1b09b91)

For your convenience during development the documentation for the code and rustc
(which we use as a library) are hosted on our [github pages][docs]

[docs]: https://brownsys.github.io/paralegal

## Repository Structure

- `crates`: The source code of the various parts and tools that comprise
  Paralegal
  - `paralegal-spdg`: Definition of the Semantic Program Dependence Graph
  - `paralegal-flow`: Rustc plugin that extracts an SPDG by means of control and
    data flow analysis
  - `paralegal-policy`: Framework for defining policies as graph queries
  - `paralegal-explore`: Query and visualize parts of an SPDG
- `prop`: Sample policies we wrote for Open Source Rust applications
  - `websubmit`: Policy for <https://github.com/ms705/websubmit-rs>
  - `lemmy`: Policy for <https://github.com/LemmyNet/lemmy>
- `scripts`: Helper scripts for auxillary tasks. Currently only holds a script
  for counting lines in Forge files
- `doc-src`: Sources for building the documentation. that is hosted on [GitHub pages][docs]
