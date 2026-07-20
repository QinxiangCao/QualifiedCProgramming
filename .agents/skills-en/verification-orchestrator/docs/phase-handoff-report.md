# Phases, Handoffs, and Reports

`AGENTS.md` is the complete contract. This document lists only the minimal runtime interface.

## File responsibilities

| File | Reader/writer | Stores only |
|---|---|---|
| `reports/<run>/annotation-attempts/annotation-attemptN/agent_input.md` | Attempt 1: controller; later: controller template + main-agent summary → the one annotation owner | Initial context; later blocker causal summary/reflection, original evidence paths, version, exact commands, linked rules, and annotation-checking timing boundaries |
| `reports/<run>/annotation-attempts/annotation-attemptN/agent_report.json` | Annotation owner | This attempt's terminal status, check summary, changed files, or blockers |
| `reports/<run>/annotation-attempts/annotation-attemptN/agent_output.md` | Annotation owner | Human analysis and repair notes for this attempt; not acceptance evidence |
| `rounds/<round>/agent_input.md` | Controller → vc-checking owner | Current task, paths, version, and linked rules |
| `rounds/<round>/agent_report.json` | vc-checking owner | Terminal status, version, and blockers |
| `rounds/<round>/agent_output.md` | vc-checking owner | Human-readable analysis and retry/annotation feedback; not acceptance evidence |
| `group_plan.json` | vc-checking/controller | Group ids, witnesses, dependencies, and short strategy/helper hints |
| `base_manifest.json` | Preparing | Formal paths, seed/witness hashes, and version |
| `group_workers_manifest.json` | Preparing/controller | Group copies, assignments, namespaces, commands, and order |
| `group_worker_input.md` | Controller → group worker | One group task and exact commands |
| `group_worker_report.json` | Group worker | Terminal status, version, and blockers |
| `group_worker_output.md` | Group worker | Optional human proof notes |
| `proving_merged_result.json` | Parent verification | Compact candidate/check/merge trace |

Do not duplicate Markdown rules, full plans/manifests, a parent transcript, command argv/cwd/flags, pending-evidence templates, or controller state in JSON.

## Sequence

`intake → annotation → annotation-check-round → vc-checking → vc-checking-check-round → vc-proving-preparing → group-worker/review → vc-proving-verify → final-apply → final-check`. When the annotation main check fails, or vc-checking/group work returns an annotation/specification blocker, the controller/review first queues a main-owned `retry-round` transition in `next_actions`. After the main agent executes it, the controller makes downstream work stale, creates the next `annotation-attempts/annotation-attemptN` and blocker-summary template, and stops at `awaiting-main-summary`. The main agent reads original Markdown/JSON and controller main-check evidence and completes all five template sections. Only after `annotation-summary-ready` validates and seals the input does the controller produce an append action for the original annotation target, followed by another annotation-check-round. If final-check fails and rollback succeeds, return to `final-candidate-apply`; `step` returns only `final-apply`, and final-check may run again only after reapplying. Failed rollback produces no next action.

Each annotation iteration's three files live directly in a separate, non-overwriting `reports/<run>/annotation-attempts/annotation-attemptN/` directory. The input digest is recorded before delivery, while report/output digests are recorded by `mark-attempt-returned`; review and feedback reject later modifications to sealed files. `verification_runs/<run>/annotation_history/<attempt-id>/` stores only formal `before/after`; agents do not write history. Acceptance of a new annotation makes old downstream plans, groups, and merges stale.

Every owner executes `mark-attempt-started` / `mark-attempt-returned` at real delivery/return boundaries. The annotation owner executes the paired handoff `timing-stage` start/finish commands before and after the complete annotation-checking review/repair/recheck. The controller writes `timing_summary.json` as `qcp-timing-summary/v4`: every item in `annotation_attempts` and `rounds` binds explicitly to its attempt/round, gives the overall created-to-finished interval first, then a few important stages. All vc-checking witness analysis is one `witness-analysis` stage. Parallel vc-proving groups contribute only one wall-clock interval and aggregate Coq/review time, never per-witness timing or legacy global command counts.

## Main-agent blocker summary

In later `agent_input.md` files, controller-owned sections fix the assignment, target, original blocker Markdown/JSON, controller evidence, skills, writable paths, and exact commands. The main agent replaces only five `MAIN_AGENT` comments:

1. `Main-agent blocker conclusion`: the primary failure, blocked witness/check, and why the task returns to annotation.
2. `Evidence and causal analysis`: decisive evidence and the causal chain through the specification, contract, invariant, assertion, or call instantiation.
3. `Reflection on the previous annotation attempt`: the previous mistaken assumption, what should be preserved, and which strategy must not be repeated.
4. `Required annotation repair`: repair target/location, preserved constraints, and success criteria for the three checks.
5. `Scope decision`: local repair or broad redesign and why; iteration 3+ must address the broader-redesign requirement.

Every section must be concrete. Do not merely copy the original report, write “keep trying,” or remove controller facts. `annotation-summary-ready` checks template markers, required sections, original sources, skill paths, commands, and repeated-repair instructions, then records the input digest. Modifying a sealed input prevents agent delivery/review.

## Acceptance

- An owner report marked `completed` says only that owner work ended; a separate controller main-owned check decides acceptance.
- For annotation, the controller reruns canonical symbolic execution, diagnostics splitting, and the fixed `formal_case_lib` check.
- For vc-checking, the controller validates the v3 plan's current version, exact witness coverage, unique assignment, group bound, and acyclic dependencies, then adds `verified: true`.
- For a group, the controller revalidates the base/worker manifest digests pinned during preparing and rederives current versions. It then checks assigned/unassigned blocks and statements in the copied manual, `Admitted` / `Abort`, seed library, helper namespaces/imports/declarations, and forbidden lemmas. Finally it derives overlays from state/manifest and reruns group-check; it does not read evidence pasted by the worker.
- Parent verification rechecks group directories, assigned/unassigned blocks, helper suffixes, seed library, and forbidden lemmas, then runs the full goal check. Coq builds reuse base `.vo` files from the prerequisite full make but remove and rebuild the current target's five modules. A missing required base `.vo` fails rather than falling back to recompiling base source.
- A passed merge still requires final-apply and final-check. Final freshness diagnostics-splits the raw refreshed manual before comparing cleaned witness names/statements. Controller cleanup removes old side products only for the current target and non-build run areas, rescans the same boundaries afterward, preserves base `.vo` files, and stores only deletion/error/residual counts plus first-failure information.

## Retry

Retry is based only on a terminal report, explicit cancellation, version mismatch, machine-check failure, or compact error. For annotation, `--previous-attempt` identifies the feedback source: it may be annotation, vc-checking, or `<vc-proving-round>:<group-id>`. The controller extracts the corresponding original Markdown/JSON paths and creates a new attempt/template. Old files are read-only. After the main agent passes the summary gate, it must append the controller message to the initially saved annotation target; spawning another agent is forbidden. A long run is not retry evidence.

Every annotation append explicitly requires rereading annotation-filling and annotation-checking in full. Iteration 3 and later also explicitly require considering a complete redesign of the mathematical specification, function contracts, and invariants. Compact error is not proof failure: annotation continues by appending to the same agent while retry capacity remains; only vc-checking/group-worker restarts the same role, and exhaustion records `compact-error-retry-exhausted`.
