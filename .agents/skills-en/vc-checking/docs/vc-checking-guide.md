# VC Checking Guide

The goal is to scan every top-level VC for fatal structural gaps first, then judge every split goal when no definite blocker exists, select `aggressive_pre_process` or `LLM_pre_process`, explain only the targets selected by that mode, and form a small number of coherent proof groups.

## Analysis

Use this exact order:

1. Scan every top-level VC, checking no-split whole goals first for missing resources, scalar/current-to-`@pre` equalities, and impossible existentials. A concrete countermodel returns immediately to annotation/specification.
2. Independently review added-premise/resource sources for annotation-comparison current/related VCs. Return to annotation for a missing source; mark a new substantial mathematical obligation high-risk.
3. After that scan passes, visit every split goal and record only provable or unprovable. Ignore whole top-level goals and do not plan helpers.
4. If a VC has at least one split goal and all are provable, choose `aggressive_pre_process` without analyzing whole-goal provability.
5. If any split is unprovable or no split exists, judge the whole top-level VC. Choose `LLM_pre_process` when it is provable; otherwise return to annotation/specification.
6. After all modes are fixed, analyze proof ideas: aggressive routes analyze split goals only; LLM routes analyze the whole top-level goal only.
7. Group only after all strategies are complete. Put comparison-related high-risk witnesses in the first group; other split goals follow their parent top-level VC.

For each analyzed target, identify the pre/post spatial resources, pure facts, existentials, right-side witness, cancellation/frame/list transformation, source of pure premises, refinement transition, and any helper's exact premises and use site.

A failed split alone is not a blocker; it causes whole-goal analysis. An unprovable whole goal is a blocker. A hard VC, uncertain tactic search, or an unproved helper is not by itself a blocker.

When goal expansion helps, add `Show.` inside the relevant proof body of the current main-root manual and run the handoff's controller command. Change no other manual token and do not create a debug script. The controller later deletes and regenerates the manual.

## Grouping

Group by invariant, proof pattern, resource transformation, refinement transition, helper family, and sustained context, then perform a separate load/coupling/critical-path review.

Consider top-level witness count, aggressive split count, helper complexity, library context, proof-mode differences, program phase, and likely tail work. Independent final-result and transition/safety work should be split unless they share an indivisible helper/context. A group usually has two to six top-level VCs.

Groups are independent and contain no dependency field. Planned helpers are only helpers newly proved or materially changed in the current round. They use the owner suffix and `local` or `public` visibility. A frozen public helper copied unchanged is not a new plan item.

## Output

`agent_output.md` records split decisions, modes, concrete proof patterns and deltas, helper premises, grouping review, and blockers. On later attempts it may cite earlier vc-checking results, but every decision is checked against the current manual.

`group_plan.json` contains only the minimal plan. Every top-level VC appears in exactly one group. An aggressive witness contains `name`, `proof_mode`, and ordered `split_strategies`; an LLM witness contains `name`, `proof_mode`, and one `strategy`. Each group has `id`, `estimated_difficulty`, `witnesses`, and optional `helpers`.

Do not add digests, acceptance, dependency, or reuse metadata.

A successful report contains only `status: completed`. A blocked report adds one complete blocker whose `vcs` list exact failed top-level/split goals and annotation locations. The controller writes the sealed manual, report, and comparison history directly into the next annotation handoff; main writes no replacement summary.

## Signals to return to annotation

- A required ownership/resource is absent from the antecedent.
- A guard, invariant, or local assertion omits a necessary pure fact.
- An array/list observation or `@pre` bridge is missing.
- The abstract state does not match the refinement target.
- A helper needs a premise the current VC cannot provide.
- Proving would require changing a generated statement or formal specification.
