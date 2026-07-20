# Natural-Language Proof Analysis

Natural-language analysis judges provability and group boundaries and belongs in `agent_output.md`. The controller does not parse a fixed schema from it. Machine acceptance still comes from the current version, v3 group plan, group checks, parent verification, and final-check.

## Reading order

1. `agent_input.md`: version, target witnesses, group bound, and output paths.
2. Cleaned `*_proof_manual.v`: obligation source and order.
3. Goal/auto/check files: read-only theorem expansion.
4. Current `formal_case_lib`.
5. Diagnostics/snapshot: planning hints only.

Prefer references in `SeparationLogic/examples/LLM_bench` and `QCP_demos_LLM`. Human cases are only non-authoritative idea sources.

## Questions for every witness

- Is `P |-- Q` semantically valid?
- What are the pre/post spatial, pure, and existential components?
- Which value instantiates each right-side witness?
- Which resources cancel directly, and which segments/lists require transformation?
- Which bounds, guards, length facts, and equalities does arithmetic use? Do not write only “lia.”
- What are the refinement hypothesis and goal states, and which unfold/choice steps connect them?
- If a helper is needed, what is its statement, which premises does it require, where does each premise come from, and where will the helper live?
- On failure, is the gap in C annotations, `formal_case_lib`, stale files, or a malformed VC?

Use concise Markdown sections instead of filling a legacy JSON template. The content must be concrete enough to guide a group worker or annotation repair.

## Helpers

For `needs-helper`, state the helper shape, witnesses using it, how every premise is discharged from the current VC, and its destination: `group_worker_lib` with the current group suffix. A premise that cannot be discharged reveals an annotation/specification gap. A cross-group helper returns to annotation.

## Group analysis

After witness analysis, list proposed groups, their shared proof patterns, dependencies, and the reason for each split. The final `group_plan.json` retains only group ids, witnesses, dependencies, and short hints; do not copy long analysis into it.

If any witness is `annotation-bug` or genuinely blocked, do not emit a complete plan that can enter proving. Put the corresponding status/blocker in the terminal report, while retaining concrete witness analysis in `agent_output.md`. The main agent later reads it with the JSON report, completes the blocker summary and reflection in the next annotation `agent_input.md`, and appends the summary plus original paths to the one annotation session.
