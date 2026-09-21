---
name: group-worker-proving
description: Use after a group-worker receives a controller-claimed group_worker_input.md or an append-group-worker for the same owner; when the handoff names a previous proving round, first search for relevant old proofs/helpers and optionally record a short proof_reuse.md, then prove assigned witnesses in the fixed group directory and deliver completed or one blocker with structured vcs.
---

# Group Worker Proving

## Role boundary

Use only the current claim/handoff, this skill, and its linked documents. Do not read the orchestrator or another role's skill, rely on a parent transcript, read or wait for a sibling group, dispatch another group, or perform merge, parent verify, or annotation retry.

These read rules prevent non-current content from becoming proof input; an accidental extra read is not itself a blocker. Continue the delivery when there is no out-of-bound write, no dependence on current-round sibling output, and the final proof still passes this group's controller validation.

Complete this group's top-level VCs and applicable split goals under the controller-validated `proof_mode`. Maintain proofs/helpers only in the fixed copies named by the handoff, use the handoff-rendered commands for optional preflight checks, then stop writing and deliver the report so main can invoke `finalize-delivery` for complete current report, structure, and group Rocq acceptance. Assignments and paths derive from the current plan; owners maintain no controller files.

When history exists, search the earlier proving round and annotation history paths listed in the handoff for relevant proof/helper blocks. Decide whether to copy, adapt, or redo them. The controller does not search, seed, or rename historical proofs. The optional proof_reuse.md is a human note. Do not read current siblings; copied helpers use the current suffix and all reused proofs still require current Coq validation.

When an annotation/spec gap is diagnosed, that gap is this group's terminal result: stop adding out-of-bound repairs to this group's copies and write a complete blocker. Its `vcs` entries give exact current-manual `name`, `parent`, and `annotation_location`; `message` only explains the existing premises and missing conclusion. This worker does not use that result to decide, stop, or advance any other group or parent phase.

## Required reading

- Always read [Proof flow](workflows/group-worker-proving.md), [Commands and checks](workflows/commands-and-checks.md), and [Mandatory forbidden-lemma rules](docs/forbidden-lemma.md) in full.
- Before proving a manual VC, read [Whole separation-logic proof tactics](docs/separation-logic-whole-proof-tactics.md).
- When this group contains a refinement target, read [Refinement proof tactics](docs/refinement-proof-tactics.md).
- When this group uses ordering, bounds, sum, or another pure-proposition predicate, read [Pure proposition proof patterns](docs/pure-proposition-proof-patterns.md).
- Read [Reference cases](docs/reference-cases.md) only when an analogous proof is genuinely needed.
