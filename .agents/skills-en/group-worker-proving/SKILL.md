---
name: group-worker-proving
description: Use after a group-worker receives a controller-claimed group_worker_input.md or an append-group-worker for the same owner; prove assigned witnesses only in the fixed group directory, modify the handoff-provided copied manual and optional group_worker_lib, and deliver a terminal completed report or a report with a complete blocker.
---

# Group Worker Proving

## Role boundary

Use only the current claim/handoff, this skill, and its linked documents. Do not read the orchestrator or another role's skill, rely on a parent transcript, read or wait for a sibling group, dispatch another group, or perform merge, parent verify, or annotation retry.

Complete this group's top-level VCs and applicable split goals under the controller-validated `proof_mode`. Maintain proofs/helpers only in the fixed copies named by the handoff, use the handoff-rendered commands for optional preflight checks, then stop writing and deliver the report so the main agent can invoke `finalize-delivery` for sealing and validation.

When an annotation/spec gap is diagnosed, that gap is this group's terminal result: stop adding out-of-bound repairs to this group's copies, write a complete traceable blocker, and deliver normally. This worker does not use that result to decide, stop, or advance any other group or parent phase.

## Required reading

- Always read [Proof flow](workflows/group-worker-proving.md), [Commands and checks](workflows/commands-and-checks.md), and [Mandatory forbidden-lemma rules](docs/forbidden-lemma.md) in full.
- Before proving a manual VC, read [Whole separation-logic proof tactics](docs/separation-logic-whole-proof-tactics.md).
- When this group contains a refinement target, read [Refinement proof tactics](docs/refinement-proof-tactics.md).
- When this group uses ordering, bounds, sum, or another pure-proposition predicate, read [Pure proposition proof patterns](docs/pure-proposition-proof-patterns.md).
- Read [Reference cases](docs/reference-cases.md) only when an analogous proof is genuinely needed.
