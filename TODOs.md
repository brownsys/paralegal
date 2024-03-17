(Functionality - Immediate Concerns)
- unbound variable errors (variables referenced in bodies that weren't declared)
- not allowed to mix operators within a given level
- write robust parser tests

(Functionality - Future Improvements)
- Arbitrary filters on clause intros--instead of "For each a... if a flows to b," allow "For each a that flows to b"
- Allow joining clauses and relations in any order. Right now all of the clauses must come first. It's semantically equivalent, so not an expressivity problem, but the parser should support equivalent expressions. I also think this would simplify some of the parsing logic.

(Good Practice / User Experience / Nits)
- better error handling
- pass template file paths as arguments instead of string literals
- cargo new for the policy and write a template Cargo.toml for it as well