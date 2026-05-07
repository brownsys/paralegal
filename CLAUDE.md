Don't infer beyond what the code and repo make explicit—ask when uncertain. Never modify abstractions or architecture without explicit instruction.

## Documentation policy

Document **why**, not what. Comments must add information not visible locally.

**Add** docs for: non-obvious contracts (preconditions, invariants, ownership, thread-safety, error/ordering semantics); rationale for non-obvious design choices; missing module/file headers when purpose isn't self-evident; **anything you had to dig to figure out** — your friction is the signal, leave a breadcrumb where the knowledge belongs.

**Skip** docs that restate code, duplicate what a good name or signature already conveys (improve those first), or assert things you aren't confident will stay true. Stale docs are worse than none.

Use idiomatic doc-comment syntax. Be terse; link out (issue, commit, design doc) rather than inline long explanations. Fix or remove drifted docs you encounter.