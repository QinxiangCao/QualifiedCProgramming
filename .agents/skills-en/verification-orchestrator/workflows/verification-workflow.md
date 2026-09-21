# Workflow for One C Case

## Main execution loop

```text
init-run → step → annotation owner → finalize-delivery
→ dune-build → VC-checking owner → finalize-delivery
→ vc-proving-preparing → group owners → finalize-delivery
→ vc-proving-verify → final-apply → final-check → done
```

If the manual has no top-level VCs, dependency preparation leads directly to proving with no groups;
parent checks, publication, and final checks still run. `dune-build` is the public command name; the
selected workspace backend may be Dune or Make.

After each command actually exits, inspect its final JSON. Execute current `next_actions`, or wait
for owners listed in `waiting_for`. Once an owner has finished its report and stopped writing, use
the `finalize_invocation` from the claim response or waiting entry. If a command returns no further
actions, call `step` once; do not construct the next phase's command yourself. An unfinished task
with no action, running owner, or explicit blocker produces `controller-no-progress`; do not poll
indefinitely.

## Initialization

`init-run` fixes the C file, independent formal case stem, `target_files`, case-library policy,
problem statement, symexec profile, and group limits. The current mapping is
`QCP_examples/<collection>/.../<input>.c` → `Rocq/examples/<collection>/.../<case>_*.v`.

Library policies are `present` (existing library), `create` (create a seed), and `absent` (keep it
absent). When omitted, select the first or second according to whether the canonical library exists.
`--freeze-spec` identifies user-provided function specifications; without it, the annotation owner
writes the specifications. Clarify ambiguous problem requirements or specification authority before
initialization.

## Annotation

Following its role skill, the annotation owner derives mathematical specifications, necessary
predicates, minimal function contracts, and loop invariants from the problem, and repairs symexec
findings within the same attempt. It edits only the C annotations, active case library, and reports
or plan permitted by the handoff. It does not hand-edit generated files or the proof manual.

Development checks run in this order: `formal-case-lib-design` → `symexec` → `formal-case-lib`;
run the last check only when the library exists. The controller generates and validates outputs in
a temporary directory before publishing them. A symexec command starts at most one driver. Its
failure diagnostics go to the owner; zero-byte output does not trigger an automatic rerun.

After the owner reports `completed` and stops, main's `finalize-delivery` directly performs annotation
acceptance: validate the plan and frozen specifications, regenerate once from current inputs, check
failed-VC/current-VC comparisons, compile the active library, and save after-history. Only success
marks the task `accepted` and advances to dependency preparation.

To change a frozen specification, the owner records the function, old and proposed meanings, reason,
and impact in its notes, stops editing, and asks main to obtain user approval. After approval,
`unfreeze` applies to the same attempt; successful acceptance records the new baseline. Keep the
same owner throughout.

## VC checking

When the manual has VCs, the controller creates an independent VC-checking owner. Its mathematical
work still follows the role skill: first perform the cheap top-level structural blocker scan, then
complete exhaustive split-first analysis, proof-mode selection, and the group plan for inputs
without a definite blocker. Review annotation comparisons independently; `resolved` is not proof.

Canonical files are read-only. To inspect goals, add `Show.` only to the handoff's debug manual copy
and run the provided `coq-debug`. Main's `finalize-delivery` validates debug edit boundaries, plan
coverage of the current manual, and group limits. Success creates the proving task. Acceptance does
not rerun symexec to remove `Show.`.

## Group proving

`vc-proving-preparing` creates independent group copies and handoffs from the current plan and
canonical manual/library. Assignments, paths, and candidates derive from current inputs. Owners may
read historical proofs listed in their handoffs and decide what to reuse; scripts do not prefill
proofs/helpers or rename them automatically.

Dispatch in plan-array order under the concurrency limit. After an annotation retry, groups covering
comparison `current` VCs run first; dispatch the remaining groups only after all priority groups are
accepted. If the priority batch finds an annotation gap, stop expanding dispatch, wait until running
or returned deliveries have been handled, then aggregate actual blockers for an annotation retry.

A group owner edits only assigned proof spans and permitted suffixed helpers. `group-development`
and `coq-debug` provide development feedback. `finalize-delivery` must check current structure, proof
modes, helper suffixes, forbidden assumptions/commands, and compile the assigned-witness wrapper.
Unfinished witnesses assigned to other groups do not prevent this group's acceptance.

After every required group is accepted, `vc-proving-verify` mechanically merges current copies and
runs the full parent check. Follow controller repair/retry actions for merge or parent failures;
main does not repair owner proofs or plans.

## Repairs and retries

A repairable report or check failure returns the same task to `prepared`, retains its owner, and
increments `repair_index`. Main claims the append action and sends it to the original agent. Do not
turn a repair of the same task into a new round.

| Confirmed cause | Next behavior |
|---|---|
| Annotation owner finds an annotation/specification/dependency gap | Repair within the same attempt and owner |
| VC-checking annotation/specification/dependency gap | Create an annotation retry from structured VC feedback |
| VC-checking plan/report defect | Create a VC-checking retry |
| Group annotation gap | Let the current batch finish safely, aggregate exact VCs, then retry annotation |
| Group plan defect | Derive a VC-checking retry from current groups' terminal states |
| Tool or infrastructure blocker | Preserve diagnostics; do not infer mathematical gaps from error prose or switch rounds without an action |
| Unreadable current inputs, parent failure, or another mechanical problem | Execute only the controller's explicit recovery/retry action |

`retry-round` must match the current action, with all running/returned owners already handled. A new
annotation attempt carries historical `failed_vcs`, copies necessary design notes, and requires new
comparisons. Delivery requires every actual old gap to be resolved. Model-written specifications
remain directly editable; frozen user specifications still require the approval described above.

## Publication and final checks

After parent success, `final_candidate` records only the proving round. `final-apply` rereads that
round's current candidate, validates write boundaries, compiles the latest candidate, then saves
original/candidate bytes and publishes. `final-check` checks actual main-root files, frozen
specifications, an independent symexec replay, manual/VC and library boundaries, Rocq compilation,
and exact side-product cleanup. Enter `done` only after every check passes.

On failure or interruption, recover using the current publication record. If external new content
appears, preserve backups and report the conflict; never overwrite it silently. A user pause changes
only control and the signal, retaining task facts. Explicit resumption derives actions again. A
`returned` task left by interrupted acceptance can be finalized again without requiring its owner
to prove again that writing has stopped.
