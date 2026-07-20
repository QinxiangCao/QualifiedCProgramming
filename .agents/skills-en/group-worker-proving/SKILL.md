---
name: group-worker-proving
description: Used by a group worker to read group_worker_input.md, edit only the copied manual and group_worker_lib in its fixed group directory, prove assigned witnesses, and write a compact terminal result.
---

# Group Worker Proving

Read the `group_worker_input.md` named by the startup message and every linked rule in full. Do not rely on a parent transcript. The manifest is a controller machine file and need not be loaded in full.

## Documentation

- `docs/coq-tooling-policy.md`: scripted Coq, overlays, and group-check evidence.
- `../verification-orchestrator/docs/path-configuration.md`: group-path guidance.
- Other linked tactic and reference guides.

## Allowed work

- Edit only assigned witness proof bodies in the handoff's `Copied manual`.
- Add only proved `Lemma` / `Theorem` / `Fact` / `Remark` declarations and necessary official Rocq imports to the handoff's `group_worker_lib`.
- Write a debug script only at the exact `_coq_builds` path identified by `Debug script` in the handoff.
- Write machine output only to the declared compact group report; optional proof notes belong in `group_worker_output.md`.

`formal_case_lib` is read-only, and generated files plus unassigned witness blocks must not change. The group directory ultimately contains only the copied manual and `group_worker_lib`.

## Helper namespace

Every new helper name must end with `helper_namespace.suffix`. Unsuffixed or foreign-suffixed helpers, edits to seed declarations, and project/generated imports are forbidden. If several groups need isomorphic facts, each defines its own suffixed helper. A mathematical fact that must be shared across groups returns to annotation for promotion into the `formal_case_lib` specification.

Do not duplicate new-declaration metadata in the worker report. Parent merge parses `group_worker_lib` directly and records each name, kind, and statement hash.

## Coq feedback

- Execute the debug/check commands in the handoff's `Commands` code block exactly as rendered. Both must go through the controller; never call internal `coq_tooling.py` directly.
- Do not assemble `--workspace-root`, a build path, overlays, flags, or cwd.
- Before `completed`, the exact group-check must pass against the current `source_goal_version`. Controller review derives the same overlays from state/manifest and reruns the check; do not copy complete evidence into the worker report.
- Raw Coq, Dune, Rocq MCP, and `coqc -o` are forbidden.

## Blocking and report

Complete all assigned witnesses in one spawn whenever possible. A failed tactic, missing optional hint, need for a suffixed helper, or several debug rounds requires local repair/retry.

Use `blocked` only after concrete proof-state/helper/scripted checks establish that a premise cannot be derived from the current VC and `group_worker_lib`, or when exact tooling is completely unusable. Use `stale` for an invalidated version. For compaction, record only the `compact-error` fact.

When returning `blocked`, identify in `group_worker_output.md` the assigned witness, underivable premise/resource, attempted suffixed helper, and why the evidence points to an annotation/specification gap. The compact JSON report retains only the blocker. The main agent reads the original Markdown and JSON, uses the fixed template to summarize the cause, reflection, and repair scope, and appends the summary plus original paths to the run's one annotation agent. It does not open another annotation agent.

`group_worker_report.json` uses `qcp-group-worker-report/v2` and contains only terminal status, current `source_goal_version`, and blockers. Assignment, candidate paths, and namespace already exist in the handoff/manifest and are not repeated. Never claim controller or parent acceptance.
