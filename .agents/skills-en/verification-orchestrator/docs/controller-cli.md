# Controller Public Interface

The public parser exposes 20 subcommands. `public_command_schema()` is authoritative; main uses action invocations instead of composing commands.

```text
<python> .agents/scripts/verification-orchestrator/controller.py --main-root <root> <subcommand> ...
```

## Command Table

| Command | Required arguments | Purpose |
|---|---|---|
| `init-run` | `--case --target-c-file` | Create fixed run/topology/state; problem, policy, profile, group limits, and hard-spec inputs are optional |
| `step` | `--run` | Publish actions or waiting/done/blocker |
| `pause-run` | `--run --reason` | Cooperative pause |
| `cancel-action` | `--run --action --reason` | Cancel exact active action and pause |
| `resume-run` | `--run` | Resume only after explicit user request |
| `claim-attempt` | `--run --next-action --owner` | Atomically claim a delivery and return handoff/finalize invocation |
| `finalize-delivery` | `--run --attempt --owner` | Seal owner delivery and enter controller validation |
| `retry-round` | `--run --phase --reason --previous-attempt` | Create an authorized annotation/vc-checking retry |
| `unfreeze` | `--run --round` | Allow the current attempt to revise a user-provided specification |
| `annotation-check-round` | `--run --round` | Annotation acceptance, clean replay, and comparison revalidation |
| `vc-checking-check-round` | `--run --round` | Seal group plan and restore clean manual; optional `--group-plan` must be fixed |
| `dune-build` | `--run` | Prepare exact goal-check dependency snapshot with selected backend |
| `vc-proving-preparing` | `--run --round` | Create groups, hand off the previous proving round, and compute priority batch |
| `vc-proving-verify` | `--run --round` | Merge accepted groups and run parent full check |
| `symexec` | `--run --round` | Transactional generated refresh for a claimed annotation attempt |
| `coq-check` | `--run --round --target-kind` | Check case library or group; group targets also use `--group` |
| `coq-debug` | `--run --round` | Inspect VC manual/group debug; group mode uses `--group` |
| `final-apply` | `--run` | Transactionally apply accepted merged candidate |
| `final-check` | `--run` | Final freshness/Rocq/structure/seal/cleanup checks |
| `validate-artifact` | `--kind --path` | Validate public JSON, including annotation plan version 2 |

## Init

`--case` is the authoritative Rocq/generated stem. Common options select library policy, a user-provided specification, symexec profile, group limits, and problem/spec hints. Presence of the existing `--freeze-spec` option means the formal specification is user-provided; every name must exactly match a C function with an extracted specification or init fails. Omission means the annotation owner generates it. Init never takes over an existing same-named run/report directory.

## Claim and Finalize

`claim-attempt` accepts only the current delivery action and returns stable owner, role/CWD, verbatim claim/handoff prompt, and finalize invocation. Main retains the owner-to-target mapping. Annotation retry and group repair reuse their existing targets; each vc-checking retry is independent.

`finalize-delivery` seals report/plan/formal copies and immediately performs phase/group validation. `report-repair-required` keeps the same owner and attempt.

## Retry

`retry-round` must exactly match the current action. A new annotation attempt accepts only an annotation gap from VC checking or VC proving. It revalidates feedback sources, derives failed VCs from structured blocker entries and sealed manuals, carries unresolved failed VCs, renders related comparison history, copies function specifications, loop invariants, and new predicates, clears comparisons, and directly publishes a prepared append delivery. An identical repeat returns `already-retried`.

## Annotation and unfreeze

Without `--freeze-spec`, the annotation owner edits function specifications, internal annotations, and the case library together in the current attempt. `formal-case-lib-design` checks only the current C and case library.

With `--freeze-spec`, the annotation owner does not change the user-provided specification. When a change is needed, the owner stops, writes the proposal in `agent_output.md`, and main asks the user. After approval, main resumes the run and executes `unfreeze --run <run> --round <round>`. The command preserves functions, sets baseline to `null`, and keeps the round, attempt, and owner unchanged.

`annotation-check-round` validates plan version 2, the user-spec baseline, case-library checks, transactional symexec, comparisons, and clean replay. When baseline is `null`, successful acceptance records the current specification surface as the new baseline. An unresolved result, missing source, or nonexistent current VC returns to the same annotation owner in the current attempt.

## VC Checking and Proving

`vc-checking-check-round` requires a clean-equivalent manual and complete group plan.

`vc-proving-preparing` seals base/group-plan/public-helper/dependency-snapshot digests, group ids/order, and previous round. It never decides or copies old proofs: every current group stays `prepared` and is published in priority/remaining order. With a previous round, an actual worker searches candidate proof blocks by current witness/helper names without reading every full manual; an optional `proof_reuse.md` may be missing or empty without affecting finalize. `vc-proving-verify` runs only after every required group is accepted.

## Artifact Validation

Kinds are `agent-report`, `group-worker-report`, `annotation-plan`, `manifest`, `group-plan`, `merge-result`, `controller-state`, and `run-log`. Blockers use `vcs`; annotation plans accept only version 2 exact fields.

## Errors and Idempotency

Action mismatch, wrong owner, topology/seal drift, current-file drift, or schema errors are rejected or become explicit controller blockers. Repair at the returned boundary; never edit state/seals or respawn to bypass an error.
