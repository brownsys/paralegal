# Paralegal: The most practical static analysis tool for enforcing privacy policies on Rust code.

Paralegal is a static analyzer for Rust code that enforces custom privacy and security policies on programs.
Paralegal ships with an expressive policy language that checks for problematic, semantic
code patters by reasoning about dependencies between program values.

For example, a policy checking for the deletion of stored user data may look like this:

```
Somewhere:
1. For each "data type" marked user_data:
  A. There is a "source" that produces "data type" where:
    a. There is a "delete query" marked deletes:
      i) "source" goes to "delete query"

```

And a policy for checking whether correct authorization checks are applied may look like this:

```
Scope:
Everywhere

Policy:
1. For each "write" marked community_write:
	A. There is a "delete check" marked community_delete_check where:
		a. "delete check" affects whether "write" happens
	and
	B. There is a "ban check" marked community_ban_check where:
		a. "ban check" affects whether "write" happens
```

Paralegal enforces these policies on the code base with the help of *markers*,
user-defined, high-level concepts, such as *deletes*, *community_write* and *user_data*.
Developers apply markers to types or function arguments using lightweight annotations.

```rust
#[paralegal::marker(user_data)]
struct Blogpost { ... }

impl Database {
    #[paralegal::marker(deletes, argument = [1])]
    fn delete_row(&mut self, id: u32, table: &str) { ... }
}
```

The tool itself is a fast cargo and rustc plugin that developers can run frequently
(in CI for example) to find potential bugs as they develop their application.

![](misc/ci_plot-3.png)

Once policy and markers have been applied, running the tool is as easy as

```bash
cargo paralegal-flow
```

## Installation

Paralegal has been tested on Linux (Ubuntu), MacOS and WSL. It should also work on Windows though.

Download the
