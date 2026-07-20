---
name: verification-orchestrator
description: Used to control the controller state machine for one verification case, its one persistent annotation agent, per-attempt annotation reports, main-root annotation/vc-checking, the three library roles, copied group directories, deterministic proving_merged output, and final-check.
---

# Verification Orchestrator

Only the main agent uses this skill. `AGENTS.md` is the complete contract. Read as needed:

- `docs/phase-handoff-report.md`: phases, lightweight Markdown/JSON files, and acceptance.
- `docs/path-configuration.md`: controller-owned symbolic-execution and Coq paths.
- `docs/forbidden-lemma.md`: lemmas forbidden in the manual and all three library roles.

## Boundaries

- Use only `scripts/controller.py`; internal modules do not expose an agent CLI.
- The controller writes state, events, acceptance, retry/stale status, and handoffs. It does not start agents or write proofs. The main agent spawns exactly one annotation agent per run, then appends only to the saved target.
- Annotation edits target C/`formal_case_lib` directly in the main root. vc-checking treats formal files in the main root as read-only.
- A group worker edits only the copied manual/`group_worker_lib` in its fixed group. Only mechanical merge creates `proving_merged_lib`.
- Agent-facing handoffs are Markdown. Terminal JSON stays flat and does not copy rules, manifests, tooling evidence, or controller state.
- Preparing and parent verification are not agent rounds and do not create phase-agent files.

## Controller sequence

1. `init-run` / `step`: create a run; the first round uses `reports/<run>/annotation-attempts/annotation-attempt1/` and establishes state for the one annotation session.
2. `spawn-instructions`: initially returns a spawn message. A later annotation retry creates a new `annotation-attempts/annotation-attemptN/agent_input.md` main-summary template and stops at `awaiting-main-summary`. Only after the main agent reads original blockers, completes the template, and calls `annotation-summary-ready` does the controller return an append message. The main agent retains and reuses the initial annotation target. The controller records the ordinary attempt lifecycle and `review-attempt`.
3. `annotation-check-round`: rerun symbolic execution, diagnostics splitting, and the `formal_case_lib` check; accept the current version.
4. `vc-checking-check-round`: validate exact coverage, dependencies, and version of the v3 group plan.
5. `vc-proving-preparing`: write compact base/worker manifests, copy group files, and create Markdown group handoffs.
6. Group lifecycle/review: accept a group only after the controller reruns its fixed group-check.
7. `vc-proving-verify`: mechanically merge, run the parent full check, and write compact `proving_merged_result.json`.
8. `final-apply` / `final-check`: back up and write back files. The controller removes old Coq side products only for the current target and non-build run areas, preserving base `.vo` files from the prerequisite full make. After fresh symbolic execution it diagnostics-splits the raw manual inside the refresh directory, runs the full check, checks structure/libraries, and rescans cleanup boundaries before writing `done`. On failure with successful rollback, return to `final-candidate-apply` and apply again before checking again.

Every agent delivery/return uses `mark-attempt-started` / `mark-attempt-returned` to establish real wall-clock boundaries. The annotation handoff also includes paired `timing-stage` commands, executed around the complete annotation-checking review/repair loop. The controller uses these data to generate `qcp-timing-summary/v4`, organized by annotation attempt and vc-checking/vc-proving round. The summary emphasizes whole lifecycles and a few important stages, not per-witness timing or global command totals.

## Operating rules

- The main agent executes only controller-returned actions/commands and never assembles paths, flags, overlays, or build directories.
- The first annotation action spawns one agent. Every later `append-annotation-agent` action goes to that same target. For each retry, the main agent fills the five-part blocker cause, evidence, previous-attempt reflection, required repair, and scope decision in `agent_input.md`, preserving original Markdown/JSON paths. The controller refuses an incomplete template. Every append requires rereading both annotation skills, the main summary, and original evidence in full. The third and later iterations also require broader redesign of specifications, contracts, and invariants.
- vc-checking and group workers use independent sessions without the parent transcript. Handoff Markdown and current files are authoritative.
- A long run is not retry evidence. Annotation compaction repair still appends to the same target; another agent with compact error may restart according to the bounded state policy. A version change makes downstream work stale.
- Recover from final-check failure only through controller state: after successful rollback, `step` returns `final-apply`; after failed rollback, there is no next action. Cleanup evidence remains compact and never stores every side-product path.
- Acceptance reads only `controller_state.json`, the event log, current files, and controller-generated merge results. The controller does not rewrite owner reports.
