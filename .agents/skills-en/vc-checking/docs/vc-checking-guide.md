# VC Checking

The goal is to decide whether each cleaned manual VC is semantically provable before writing proofs and to form a small number of coherent proof groups.

## Analysis

For each `P |-- Q`:

1. List pre/post spatial resources, pure facts, and existentials separately.
2. Explain whether each right-side witness instance comes from an old logical value, `replace_Znth`, `sublist`, `app`, a loop variable, or abstract state.
3. Explain spatial cancellation/split/merge, the sources of pure premises, and refinement transitions.
4. If a helper is needed, give its statement shape, every premise, and how current `P` discharges each premise.
5. If `P` cannot imply `Q`, return to annotations/specifications; do not force a group worker to prove it.

Judgments:

- `proofable`: existing facts and lemmas suffice.
- `needs-helper`: the semantics hold, and a group worker can prove a current-suffix helper in `group_worker_lib`.
- `annotation-bug`: an annotation or `formal_case_lib` specification is missing or wrong.
- `blocked`: a required file/parser has a major failure, or a semantic gap cannot be repaired through annotation or a group-local helper.

Use `stale` for an invalidated version and `compact-error` for compaction. An uncertain proof route, unproved helper, or difficult VC is not a blocker.

## Grouping

Group witnesses by shared invariant unfolding, helper family, array/frame transformation, refinement transition, or similar context. Split only for a real dependency, clearly different strategy, or a group exceeding the handoff limit. Assign every target witness exactly once and keep the dependency graph acyclic.

A mathematical fact that must be shared across groups returns to annotation for promotion into a `formal_case_lib` declaration. Never let a group edit the formal library.

## Output

- `agent_output.md`: natural-language analysis in manual order. Every witness includes at least a judgment, P/Q shape, instantiation, spatial/pure/refinement plan, helper premise, or failure signal. This file supports humans and retries; it is not controller acceptance evidence.
- `group_plan.json`: only the machine-minimal v3 plan:

```json
{
  "schema_version": "qcp-vc-checking-group-plan/v3",
  "source_goal_version": "<digest>",
  "groups": [
    {
      "id": "array-frame",
      "witnesses": ["proof_of_x"],
      "depends_on": [],
      "strategy": "split array, instantiate EX, cancel",
      "helpers": ["optional short helper hint"]
    }
  ]
}
```

Do not copy the complete target-witness set, grouping policy, long per-witness analysis, or controller metadata into the plan. Those live respectively in the current version, handoff, `agent_output.md`, and controller state.

- `agent_report.json`: terminal status, current version, and blockers.

If terminal status is `blocked` or a blocker is an `annotation-bug`, the main agent reads this round's `agent_output.md` and `agent_report.json`, then uses the fixed template in the next annotation `agent_input.md` to summarize failure cause, evidence, reflection on the previous attempt, required repair, and scope decision. It appends the summary plus both original paths to the one annotation agent. Therefore VC Markdown must contain the concrete failure shape and repair location, while JSON keeps only the compact blocker. The vc-checking owner does not write the main agent's summary or recommend another annotation agent.

## Signals to return to annotation

- `Q` requires ownership/resources absent from `P`.
- A guard, invariant, or local assertion lacks a necessary pure fact.
- An array/list observation or `@pre` bridge is missing.
- The `safeExec` abstract states do not match.
- A helper needs an additional premise unavailable from current `P`.
- The proof would need to modify a generated file, witness statement, or formal specification.
