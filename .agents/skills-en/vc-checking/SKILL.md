---
name: vc-checking
description: Used by a vc-checking subagent to read the cleaned manual/generated/formal_case_lib files directly from the main root, judge semantic provability of manual VCs, and emit a group_plan.json bound to source_goal_version.
---

# VC Checking

Read the `agent_input.md` named by the startup message in full. Current main-root files and the handoff version are the only context. A parent transcript is forbidden.

## Documentation

- `docs/vc-checking-guide.md`: provability, per-witness plans, and the group plan.
- `docs/natural-language-analysis.md`: natural-language analysis of `P |-- Q`.
- `../verification-orchestrator/docs/path-configuration.md`: root/group path roles.

## Allowed work

- Read only the main-root manual, goal, auto, diagnostics, snapshot, and `formal_case_lib`.
- Write only the declared `agent_report.json`, `group_plan.json`, and `agent_output.md`.
- Do not modify formal files, witness statements, or generated files.

## Judgments and grouping

For each target witness, analyze pre/post spatial resources, pure facts, existentials, refinement state, witness instantiation, and helper premises.

- `proofable`: existing facts and lemmas suffice.
- `needs-helper`: the semantics hold, and a group worker can prove a current-suffix helper in `group_worker_lib`.
- `annotation-bug`: the current C annotations or `formal_case_lib` specification are missing or wrong and must return to annotation.
- `blocked`: the VC is genuinely semantically unprovable, or a required read/parse tool has a major failure.

On `annotation-bug` or `blocked`, `agent_output.md` must identify the concrete witness, missing premise/resource, corresponding C function/loop/assertion, and specification boundary to reconsider—enough for the main agent to analyze the failure and the annotation owner to repair it. Keep the blocker in `agent_report.json` machine-minimal. The main agent reads both original files, uses the blocker-summary template for its cause and reflection, and appends the summary plus original paths to the run's one annotation agent. It never respawns annotation.

Minimize the number of groups. Put witnesses from the same function, pattern, or helper family in one group when one worker can process them in sequence. Split only for a real dependency, substantially different strategy, or excessive context. Assign every target witness exactly once, keep the dependency graph acyclic, and obey the grouping bound.

If a helper truly must be shared across groups, recommend returning to annotation and promoting the mathematical fact into a `formal_case_lib` specification declaration. Never let a group edit the formal library.

## Output

Write detailed per-witness judgments and natural-language proof analysis in `agent_output.md`. `group_plan.json` keeps only the current version and `groups[{id,witnesses,depends_on,strategy?,helpers?}]`. `agent_report.json` keeps only terminal status, version, and blockers. Only the controller adds `verified: true` to the plan and records acceptance in state.

An uncertain proof route, unproved helper, missing diagnostics hint, or difficult witness is not blocked. Use `stale` for an invalidated version. For compaction, record only the `compact-error` fact. Do not modify annotations directly and do not request a new annotation agent.
