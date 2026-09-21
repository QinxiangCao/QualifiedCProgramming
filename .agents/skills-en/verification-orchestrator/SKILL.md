---
name: verification-orchestrator
description: Use when the main agent controls one C verification case in this repository; start at init-run, follow current controller actions to manage annotation, VC-checking, and group owners, and complete acceptance, merge, publication, and final-check until done or an explicit blocker.
---

# Verification Orchestrator

For main only. Read all four documents before executing a case:

- [Overall workflow](workflows/verification-workflow.md)
- [State, handoffs, and reports](workflows/state-handoffs-and-reports.md)
- [Paths and commands](workflows/paths-and-commands.md)
- [Public CLI](docs/controller-cli.md)

On Windows, also read the [Windows runtime rules](docs/windows.md). At `final-check`, read
[`final-check/SKILL.md`](../final-check/SKILL.md) and its required workflow.

Main maps controller owners to actual agent targets and executes the returned structured invocations.
Claim each owner action first, then send the claim response's `handoff.prompt` verbatim to that agent.
Create only one annotation agent per run; send repairs and later annotation attempts to that same agent.
Use an independent owner for each VC-checking attempt and each group's first claim; repairs of the same
task retain its owner. Main executes controller actions for `vc-proving` preparation, dispatch, merge,
and parent checks; there is no separate phase agent.

After an owner writes its terminal report and stops editing, main executes `finalize-delivery`. This
command performs all acceptance checks for that role directly; a `completed` report alone is not
acceptance. Derive the next step from current task facts. Continue until `phase: done`, wait while
owners are running, and report an explicit blocker when no action can proceed.

Main does not edit annotations, plans, or proofs on an owner's behalf, or proactively read, summarize,
or restate owner skills. Owners read their role knowledge from their own handoffs. This division
controls context; acceptance depends on current files, reports, and actual checks, not accidental
extra reading.

If a frozen user specification must change, the owner records the proposal and stops. Main pauses
the run and asks the user to approve it. After explicit approval, resume the run, execute `unfreeze`
for the current annotation round, and return the work to the same owner. An unfrozen model-written
specification may be repaired within the current annotation attempt.

When the user requests pause or stop, execute `cancel-action` for the current action, or `pause-run`
if its exact id is unavailable. Wait for running tools to clean up their processes, then stop advancing.
Call `resume-run` only after the user explicitly requests resumption, then run `step`. Tasks and owners
remain unchanged; actions are recomputed from current state.
