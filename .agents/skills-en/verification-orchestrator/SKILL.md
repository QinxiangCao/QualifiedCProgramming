---
name: verification-orchestrator
description: Use when the main agent controls a complete run for one C verification case in this repository; starting at init-run, follow controller actions to manage the sole annotation agent, vc-checking and every group-worker when needed, aggregated annotation-gap feedback, mechanical merge, final-apply, and final-check until done or an explicit blocker.
---

# Verification Orchestrator

Use only as the main agent. Treat `controller_state.json` and the action returned by the controller as authoritative; do not call an internal module directly, implement a state transition yourself, or modify owner files on an owner's behalf.

Main executes every invocation carried by an action verbatim, maintains the mapping from controller owners to agent targets, and sends each claim response's fixed `handoff.prompt` verbatim to the corresponding agent. Spawn the annotation agent only once per run and append every later repair to the same target; each vc-checking attempt and each group's first group-worker claim uses an independent session.

Main's proactive read boundary consists only of:

- this skill and every workflow/doc listed below;
- the current blocker, state summary, and handoff files explicitly provided by controller actions;
- when the controller reaches `final-check`, [`final-check/SKILL.md`](../final-check/SKILL.md) and its workflow;
- on Windows, the repository-root [`AGENTS_WIN.md`](../../../AGENTS_WIN.md) and the [Windows adaptation guide](docs/windows.md) to which it routes.

Main does not read, summarize, or reinterpret owner skills such as `annotation-filling`, `annotation-checking`, `vc-checking`, or `group-worker-proving`. Each owner reads only its own skill and the current handoff files according to the verbatim claim message; main orchestrates and does not learn role-specific knowledge on an owner's behalf. `vc-proving` is not a phase subagent: the controller drives group preparation, aggregation, merge, and parent verification.

When there is no manual VC, skip vc-checking and group-workers but still perform the controller-selected dependency preparation (whose public action name remains `dune-build`), parent verification, writeback, and final checks. When groups exist, keep dispatching every group in the round even after a group reports an annotation gap; enter one aggregated annotation retry only after every group reaches a terminal state, and do not merge or verify that round.

## Required reading

- [Overall workflow](workflows/verification-workflow.md)
- [State and handoffs](workflows/state-handoffs-and-reports.md)
- [Paths and commands](workflows/paths-and-commands.md)
- [Controller public interface](docs/controller-cli.md)

`SKILL.md` provides only the entry point and reading route; state transitions and write boundaries belong in `workflows/`, while the public interface and stable knowledge belong in `docs/`. This repository does not track skill regression tests; do not add test scripts under `.agents/skills/**/scripts/test/` or a language mirror.
