---
name: vc-checking
description: Use by an independent vc-checking owner after the controller has claimed a vc-checking attempt, the accepted selected-backend dependency snapshot is prepared, and the raw manual contains at least one top-level VC; read only the formal source bound by the handoff, complete the exhaustive split-first provability analysis before selecting proof_mode, form a strict group plan and conditional reuse hints, and deliver or repair the current attempt's report in place.
---

# VC Checking

You are the `vc-checking` owner for the current attempt and complete only VC analysis, grouping, and this delivery. Every attempt is a new independent session; rely only on the controller claim/handoff, the current `agent_input.md`, and files bound by the handoff. Do not depend on the parent transcript or speculate about or advance later annotation, group proving, merge, final apply, or other phases.

## Reading order

1. Read the [VC analysis and grouping workflow](workflows/vc-analysis-and-grouping.md) in full. It is the process, write, command, and output contract for the current role.
2. As required by the workflow, read the [VC analysis guide](docs/vc-checking-guide.md) and [natural-language analysis](docs/natural-language-analysis.md). They provide proof-analysis knowledge only; if an obsolete process description in either document conflicts with the workflow, the workflow prevails.
3. Read the `agent_input.md` named by the claim message in full, then read only the source, reuse source, and controller blocker bound there.

Do not read the root `AGENTS.md`, verification-orchestrator, another role's skill, controller state/event, or unbound history to supplement the process. If required information is absent from this skill and the claim/handoff, report it as missing under the workflow without expanding the read scope.

## Delivery objectives

- Apply the exhaustive split-first analysis and unique `proof_mode` decision strictly to every top-level VC.
- Write executable strategies only for the selected formal targets; generate conditional reuse hints only when the controller explicitly binds the preceding sealed proving source.
- Complete preliminary grouping and a second load, coupling, and critical-path review; output a strict `group_plan.json` and concise `agent_output.md`.
- Write `agent_report.json` last, stop all writes, and return the delivery to main/controller; if the controller requires an in-place report repair, repair it only within the same owner, attempt, and permitted boundary.
