(Functionality - Immediate Concerns)
- unbound variable errors (variables referenced in bodies that weren't declared)
- not allowed to mix operators within a given level
- write robust parser tests

(Functionality - Future Improvements)
- look through policy api again -- there are new primitives (e.g., more fine-grained always happens before) we can support
- Arbitrary filters on clause intros--instead of "For each a... if a flows to b," allow "For each a that flows to b"
- Allow joining clauses and relations in any order. Right now all of the clauses must come first. It's semantically equivalent, so not an expressivity problem, but the parser should support equivalent expressions. I also think this would simplify some of the parsing logic.
- Shouldn't need separate templates for the negation cases--e.g., flows to and does not flow to should be able to use a single template with an additional layer of indirection to add the ! beforehand
- Plume policy -- should be able to say that there is a retrieval and there is a deletes on the same level (for efficiency)

(Good Practice / User Experience / Nits)
- better error handling
- pass template file paths as arguments instead of string literals
- cargo new for the policy and write a template Cargo.toml for it as well