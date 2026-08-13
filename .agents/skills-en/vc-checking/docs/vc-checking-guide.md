# VC Checking

Before writing proofs, first judge all split goals and analyze a whole top-level VC only when necessary. Select `aggressive_pre_process` or `LLM_pre_process` from that result, then analyze strategies for the applicable goals and form a small number of coherent proof groups. `<vc>_split_goal_*` declarations are part of the raw obligation source and are neither preprocessed away nor deleted.

## Analysis

Use this strict order:

1. Traverse all split goals of all top-level VCs, recording only whether each is provable; ignore top-level VCs and do not plan helpers, proof routes, or reuse.
2. If a top-level VC has at least one split goal and all are provable, select `aggressive_pre_process` and do not analyze that top-level VC's provability.
3. If any split goal is unprovable, or there is no split goal, judge only the whole top-level VC's provability. Select `LLM_pre_process` if the whole goal is provable; otherwise return to annotations/specifications.
4. After every mode is fixed, analyze proof strategy and reuse: aggressive analyzes only split goals, while `LLM_pre_process` analyzes only the whole top-level VC.
5. Group only after all strategies are complete. Assign top-level VCs, never split goals independently; every split goal follows its top-level VC into the same group.

For every split goal or whole top-level VC that is actually analyzed:

1. List pre/post spatial resources, pure facts, and existentials separately.
2. Explain whether each right-side witness instance comes from an old logical value, `replace_Znth`, `sublist`, `app`, a loop variable, or abstract state.
3. Explain spatial cancellation/split/merge, the source of each pure premise, and refinement transitions.
4. If a helper is needed, give its statement shape, every premise, and how current `P` discharges each premise.
5. If a split goal fails, proceed to whole-top-level analysis. If the whole top-level VC still fails, return to annotations/specifications; do not force a group worker to prove it.

The first split-goal pass uses only:

- Provable: the conclusion is semantically valid.
- Unprovable: the current premises of this split goal do not imply its conclusion.

Only the detailed analysis after mode selection distinguishes whether existing facts and lemmas suffice, whether a current-suffix helper is needed in `group_worker_lib`, and whether a failed whole top-level VC is an annotation/specification gap or a tool blocker. An unprovable split goal is not itself a blocker.

Use `stale` for an invalidated version and `compact-error` for compaction. An uncertain proof route, unproved helper, or difficult VC is not a blocker.

## Grouping

After proof-strategy analysis, group top-level VCs by shared invariant unfolding, proof pattern, array/frame transformation, refinement transition, helper family, and nearby context. Never group a split goal independently. Group an aggressive top-level VC by the combined burden and shared structure of all its split-goal strategies. Then review load, coupling, and predicted critical path:

- Consider top-level witness count, aggressive split-goal count, expected helper-family count, mathematical libraries, proof-mode differences, program phase, and sustained proof context. `max_witnesses_per_group` is only a hard upper bound.
- Usually form a small number of coherent groups with roughly two to six top-level witnesses each. A single-witness group needs a real boundary such as final result, independent special route, or independent helper family. Explain in `agent_output.md` why any group above six cannot reasonably be split.
- Within one function, split initialization, core semantic transformation, simple control-flow projection, and final result unless an indivisible helper family connects them. For a likely tail, split final-result from transition/safety work whenever they are independently provable. Otherwise explain the helper/context coupling in `agent_output.md` and plan permutation, sum/length, mask-clear, or similar formal/public helpers that can be prepared early.
- Manual seed order controls only final manual witness-declaration order. Accepted plan order controls group numbering and helper merge order. Program phase, actual load, and helper ownership determine group boundaries first.

All groups are mechanically independent, and the plan has no dependency field. Keep witnesses in one group when they require the same tightly coupled, proof-specific helper family, maintained with current-suffix helpers in one `group_worker_lib`. Structured `helpers` lists only helpers newly proved or adapted by this group and bearing the owner suffix; historical snapshot/reuse helpers are not new plan items. Use `visibility: local` for a helper used only by this group. Use `visibility: public` for a stable mathematical property expected to be reusable by later groups or rounds, and list likely consumers in notes. Once the owner passes validation, the controller appends that public candidate and its required local-helper dependency closure to the run-root durable pool. Every group in the current round sees only the same `public_helper_snapshot.txt` frozen at preparing, so promotion serves future rounds only and cannot affect current dispatch. Neither snapshot nor pool may be imported, become a fourth library, or create a group dependency. Never read/import sibling `group_worker_lib` output or make multiple groups duplicate the same large helper family.

When helper ownership permits, a case like `sieve_of_euler` may use this natural-language grouping example; controller code must never hard-code concrete witness names:

- `initialization`: prefix initialization, the `replace_Znth` step, and initialization-loop exit.
- `semantic-transitions`: current composite/prime classification, prime append, and product marking, sharing the heavy prime/least-factor/flag-state helper family.
- `control-and-exits`: projection/rewriting/arithmetic witnesses for inner divide/non-divide, index normalization, stored exit implication, and outer exit.
- `final-result`: derive the public result specification from the final outer state.

Split `semantic-transitions` further into outer-entry and inner-product groups only after their shared mathematical facts have legally entered `formal_case_lib`.

## Sealed-source proof reuse

Run this only when the handoff explicitly binds the immediately previous sealed vc-proving source, in the same step as detailed strategy analysis after all modes are fixed. A source may be a failed round or a verified round made stale by annotation/freshness retry. The controller pins its manifest, base, reuse local build, and accepted dependency artifact digest and, when a parent merge result exists, also seals the corresponding failed/passed result. Without a binding, never scan historical directories, run comparisons, or create hint files.

Analyze reuse in three phases: all helpers, all aggressive split goals, all `LLM_pre_process` top-level VCs. Do not create rows for aggressive top-level VCs or `LLM_pre_process` split goals. The controller excludes structurally invalid failed groups. Only an accepted group that passed controller group validation can provide `direct copy`; an unaccepted failed/blocked proof provides at most a partial idea, and its helper is from scratch. Helper decisions are binary. Use the handoff current/reference debug scripts and exact commands to print generated goals in their respective builds:

- When current and previous routes are both `aggressive_pre_process`, compare only corresponding split goals.
- When both are `LLM_pre_process`, compare only top-level whole goals.
- When modes differ, names/goals are insufficiently similar, or proof state does not support reuse, choose from scratch.

When a split goal changes from `P |-- Q` to `P' |-- Q'`, do not compare only text. If `P |-- P'` and `Q' |-- Q` are provable, wrap the old proof in before/after adapters. If the change adds or reorders a common spatial frame, such as `P ** F |-- Q ** F`, it may be `partial proof-idea reuse`. `direct copy` requires an accepted source, a complete compatible proof span/route, and matching current/previous generated-goal semantic fingerprints. The fingerprint binds the transitive local Definition closure and `formal_case_lib`, ignoring only a rename of the generated declaration itself. Adapter/frame analysis in Reason guides the worker but is not controller proof.

Debug is mandatory evidence, not an optional reference. The handoff lists raw targets for selection. The final current script must exactly cover every aggressive split proof row and every `LLM_pre_process` top-level proof row; the final reference script must exactly cover every previous goal cited by a direct/partial row. Each comparison unit is `Goal <active_case_theory>.<case>_goal.<symbol>.`, immediately followed by `Show.`, then optional proof tactics/additional `Show.`, and ending in `Abort.`. When every row is from scratch, do not create or run a reference script. The controller seals script/build/round/version receipts. The existing build digest is a combined seal mechanically binding the local tree and reachable-base aggregate; the receipt gains no base fields. The controller rechecks the sealed `reuse-source` combined seal. Extra unselected targets, missing coverage, or seal drift fails acceptance.

Write one `reuse_hints/<group-id>.md` per proposed group. Its table has five fixed columns and orders all helpers, all aggressive split goals, then all `LLM_pre_process` top-level VCs. A helper direct row cites the complete proved declaration in an accepted source `group_worker_lib`; a split/top-level direct or partial row cites a compatible complete proof declaration in the copied manual. Every non-from-scratch range must start and end at the complete parser-recognized declaration boundaries; it cannot cite only the statement, `Proof` section, or a few tactics. From-scratch file/lines are `—`. Helper reuse is expressed only by its own row; do not invent a dependency from it to every witness. The controller validates row order, mode, semantic fingerprint, path/range, source kind, completion, and receipts and seals bytes from the same read. A hint never replaces the current group check.

## Output

- `agent_output.md`: first record the binary provability judgment for every split goal in manual order. Then, for each goal actually analyzed after mode selection, record the P/Q shape, instantiation, spatial/pure/refinement plan, helper premise or failure signal, and its top-level VC's mode. This file supports humans and retries; it is not controller acceptance evidence.
- `group_plan.json`: the minimal plan:

```json
{
  "groups": [
    {
      "id": "array-frame",
      "witnesses": [
        {
          "name": "proof_of_x",
          "proof_mode": "aggressive_pre_process",
          "split_strategies": {
            "proof_of_x_split_goal_1": "instantiate the old list and discharge the length fact",
            "proof_of_x_split_goal_2": "rewrite the update and cancel the unchanged segment"
          }
        }
      ],
      "helpers": [
        {
          "name": "decimal_comparator_transitive__array_frame",
          "strategy": "prove the comparator order is transitive independently of C locals",
          "visibility": "public"
        }
      ],
      "estimated_difficulty": 5
    }
  ]
}
```

Each top-level VC appears in exactly one group, and its split goals follow it into that group. The top level allows only `groups`; a group object allows only `id`, `witnesses`, `helpers`, and `estimated_difficulty`, with no version, verified, or dependency field. Difficulty is an integer from 1 through 5, used to produce dispatch order without changing plan/merge order. An aggressive witness contains only `name`, `proof_mode`, and `split_strategies`; those keys exactly match raw-manual names/order and every value is nonempty. An `LLM_pre_process` witness contains only `name`, `proof_mode`, and one whole-goal `strategy`. `helpers` lists only helpers newly proved or adapted by this group in the current round. Each helper has exactly `name`, `strategy`, and `visibility`; names are globally unique, and visibility is `local` or `public`. A public candidate enters the pool after owner validation. Historical snapshot/reuse helpers are opportunistic copies and are not redeclared as new unsuffixed planned helpers. Do not copy the complete target-witness set, grouping policy, long analysis, reused proof content, or controller metadata into the plan; they belong in accepted current inputs, `agent_output.md`, `reuse_hints`, and controller state respectively.

- `agent_report.json`: success contains only the completed status, while `blocked` adds one complete `blocker`. Do not copy the current version or checks.

An unprovable split goal first triggers analysis of its whole top-level VC and does not directly create a blocker. Only if the whole top-level VC remains unprovable does terminal status become `blocked` or `annotation-bug`. The main agent then reads this round's `agent_output.md` and `agent_report.json`, uses the fixed template in the next annotation `agent_input.md` to summarize failure cause, evidence, previous-attempt reflection, required repair, and scope decision, and appends the summary plus original paths to the one annotation agent. VC Markdown therefore gives a concrete failure shape and repair location while JSON stays compact. The vc-checking owner never writes the main-agent summary or recommends another annotation agent.

## Signals to return to annotation

- `Q` requires ownership/resources absent from `P`.
- A guard, invariant, or local assertion lacks a necessary pure fact.
- An array/list observation or `@pre` bridge is missing.
- The `safeExec` abstract states do not match.
- A helper needs an extra premise unavailable from current `P`.
- The proof would need to modify a generated file, witness statement, or formal specification.
