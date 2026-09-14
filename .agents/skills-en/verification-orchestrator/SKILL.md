---
name: verification-orchestrator
description: Use when the main agent controls a complete run for one C verification case in this repository; starting at init-run, follow controller actions to manage the sole annotation agent, vc-checking and every group-worker when needed, aggregated annotation-gap feedback, mechanical merge, final-apply, and final-check until done or an explicit blocker.
---

# Verification Orchestrator

Use only as the main agent. Treat `controller_state.json` and the action returned by the controller as authoritative; do not call an internal module directly, implement a state transition yourself, or modify owner files on an owner's behalf.

Main executes every invocation carried by an action verbatim, maintains the mapping from controller owners to agent targets, and sends each claim response's fixed `handoff.prompt` verbatim to the corresponding agent. Spawn the annotation agent only once per run and append every later repair to the same target; each vc-checking attempt and each group's first group-worker claim uses an independent session.

If the annotation agent returns a proposal to change a user-provided specification without running `finalize-delivery`, main pauses the run and asks the user. After approval, resume the run, execute `unfreeze` for the current annotation round, and return the approved proposal to the same annotation agent. Do not create an attempt or replace the owner.

When the user explicitly requests stop/pause, immediately run `cancel-action` for the exact active action id (or `pause-run` when no exact active action exists), wait for controller-owned process-group cleanup, and cease advancement. A paused `step` reports state only. Never invoke `resume-run` without a later explicit user request; then resume the same suspended action.

Main's proactive read boundary consists only of:

- this skill and every workflow/doc listed below;
- the current blocker, state summary, and handoff files explicitly provided by controller actions;
- when the controller reaches `final-check`, [`final-check/SKILL.md`](../final-check/SKILL.md) and its workflow;
- on Windows, the [Windows adaptation guide](docs/windows.md).

Main does not read, summarize, or reinterpret owner skills such as `annotation-designing`, `vc-checking`, or `group-worker-proving`. Each owner reads only its own skill and the current handoff files according to the verbatim claim message; main orchestrates and does not learn role-specific knowledge on an owner's behalf. `vc-proving` is not a phase subagent: the controller drives group preparation, aggregation, merge, and parent verification.

These read boundaries keep roles focused and reduce context; they are not controller delivery gates. Accidentally reading an extra file does not fail or reopen an attempt by itself. The controller advances from actual writes, fixed inputs, reports, plans, formal bytes, and machine checks.

When there is no manual VC, skip vc-checking and group-workers but still perform the controller-selected dependency preparation (whose public action name remains `dune-build`), parent verification, writeback, and final checks. The first proving round dispatches all groups normally. After an annotation retry, dispatch comparison-related priority groups first; if one reports another annotation gap, return immediately to annotation without dispatching the remaining groups. Statement, proof-mode, case-library, dependency-snapshot, and public-helper-snapshot changes do not gate cross-round reuse. When a previous proving round exists, every actually claimed group worker searches that round's group manuals/libraries by current witness/helper names, reads only candidate proof blocks, and may write a short `proof_reuse.md`. A missing or empty note does not block finalize; the current round's full group check always validates any reused or rewritten proof.

## Required reading

- [Overall workflow](workflows/verification-workflow.md)
- [State and handoffs](workflows/state-handoffs-and-reports.md)
- [Paths and commands](workflows/paths-and-commands.md)
- [Controller public interface](docs/controller-cli.md)

`SKILL.md` provides only the entry point and reading route; state transitions and write boundaries belong in `workflows/`, while the public interface and stable knowledge belong in `docs/`. This repository does not track skill regression tests; do not add test scripts under `.agents/skills/**/scripts/test/` or a language mirror.
