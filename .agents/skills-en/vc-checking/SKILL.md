---
name: vc-checking
description: Use by an independent vc-checking owner after the controller has claimed a vc-checking attempt, the selected-backend dependency snapshot is prepared, and the main-root manual contains at least one top-level VC; inspect that current manual directly, perform a cheap top-level structural-blocker scan first, then complete exhaustive split-first provability analysis when no definite blocker exists, choose proof_mode, form a strict group plan, and deliver or repair the current attempt in place.
---

# VC Checking

You are the `vc-checking` owner for the current attempt and complete only VC analysis, grouping, and this delivery. Every attempt is a new independent session; rely only on the controller claim/handoff, the current `agent_input.md`, and files bound by the handoff. Do not depend on the parent transcript or speculate about or advance later annotation, group proving, merge, final apply, or other phases.

## Reading order

1. Read the [VC analysis and grouping workflow](workflows/vc-analysis-and-grouping.md) in full. It is the process, write, command, and output contract for the current role.
2. As required by the workflow, read the [VC analysis guide](docs/vc-checking-guide.md) and [natural-language analysis](docs/natural-language-analysis.md). They provide proof-analysis knowledge only; if an obsolete process description in either document conflicts with the workflow, the workflow prevails.
3. Read the `agent_input.md` named by the claim message in full, then read the current main-root formal files, listed earlier vc-checking results, and controller blocker.

The root `AGENTS.md`, orchestrator, another role's skill, controller state/events, and unlisted history are not inputs for this role and must not replace the current handoff. Accidentally reading an extra file is not itself a blocker; continue from the current manual unless an out-of-bound write or reliance on non-current content affects the delivery.

## Delivery objectives

- Scan every top-level VC first, prioritizing no-split whole goals and missing resource-address, scalar-equality, or current/`@pre` bridges; a definite countermodel may return immediately.
- Read annotation VC comparisons as priority review leads, then independently check every added-premise source and related VC in the current manual.
- When the structural scan finds no definite blocker, apply exhaustive split-first analysis and a unique `proof_mode` decision to every top-level VC.
- Write executable strategies only for the selected formal targets; do not analyze witness reuse.
- Put current/related VCs that depend on a new substantial mathematical lemma in the first high-risk group, then complete the remaining grouping and output a strict `group_plan.json` and concise `agent_output.md`.
- Write `agent_report.json` last, stop all writes, and return the delivery to main/controller; if the controller requires an in-place report repair, repair it only within the same owner, attempt, and permitted boundary.
