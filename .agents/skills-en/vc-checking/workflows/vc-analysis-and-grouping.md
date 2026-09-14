# VC Analysis and Grouping Workflow

Only a claimed `vc-checking` owner runs this workflow. Current formal files in the main root are the sole working copy. If the manual is absent or has no top-level VC, the controller accepts an empty plan without creating this role.

## 1. Start

1. Check the claimed role, owner, and CWD.
2. Read this skill, the current `agent_input.md`, and its listed current formal files in full.
3. Read the handoff's annotation VC comparisons and record each source, current/related VCs, fact sources, and judgement; they are priority review leads only.
4. On the second and later attempts, read the earlier vc-checking `agent_output.md`, `group_plan.json`, and blocker listed by the handoff. They prevent repeated analysis, but the current main-root manual remains authoritative.
5. Do not read controller state/events, another role's skill, or unlisted history.

Each attempt is an independent session. Do not claim work yourself, advance phases, start another owner, or edit controller artifacts.

## 2. File boundary

You may read:

- the current main-root `*_proof_manual.v`, `*_goal.v`, and `*_proof_auto.v`;
- the current `formal_case_lib` when present;
- earlier vc-checking results and controller blockers explicitly listed by the handoff.

You may write:

- the current main-root `*_proof_manual.v`, only to insert temporary `Show.` commands inside proof bodies while inspecting raw goals;
- this attempt's `group_plan.json`;
- `agent_output.md`;
- `agent_report.json`.

Other than inserting `Show.`, do not modify any proof or non-proof manual token, C file, goal, auto, goal-check, library, or history. Do not create a debug script, reuse hint, parser output, or line-number list.

After vc-checking is accepted, the controller deletes the main-root manual and reruns symbolic execution. Group workers therefore receive a clean generated manual, and this owner need not clean temporary `Show.` commands manually.

## 3. Inspecting a goal

When Rocq expansion is useful, insert `Show.` directly in the target proof body and run the handoff's exact `coq-debug --round <current-round>` command. It reads the current manual itself. Do not create another script, copy the goal, change any other manual token, or assemble a raw Coq command.

Keep the controller argv, cwd, interpreter, arguments, and order unchanged. A check passes only with exit code 0 and JSON `status: passed`. Preserve the first diagnostic on failure; do not bypass it with raw Coq, Dune, Make, `coqdep`, or a custom script.

## 4. Structural-blocker scan, then exhaustive split-first analysis

First perform a cheap scan of every top-level VC, prioritizing whole goals with no split goals. Look only for structural facts that make the entailment definitely false: missing equalities from current pointer/scalar values to consequent `@pre` parameters, absent resource addresses, or existentials that cannot be instantiated from current resources. Do not plan tactics/helpers here, and do not treat difficulty as a blocker.

Fill the four exact `Structural Blocker Scan` fields in `agent_output.md`: status, number of top-level VCs scanned, number of no-split VCs checked first, and number of definite blockers. A concrete countermodel must explain how P can hold while Q fails and may immediately return an annotation/specification/dependency blocker; exhaustive split analysis is unnecessary in that blocked attempt. If no definite blocker exists, continue with the strict exhaustive split-first pass below.

After that scan passes, two ordering boundaries are mandatory:

1. Do not analyze any top-level VC until every split goal has a provable/unprovable decision.
2. Do not write detailed strategies, helpers, or groups until every top-level VC has a mode or blocker.

List every top-level VC and its `<vc>_split_goal_*` declarations in manual order. Report a name or mapping problem instead of guessing or changing a statement.

For each split goal, record only:

- provable: the current antecedent entails the conclusion;
- unprovable: the current antecedent does not entail the conclusion.

Do not analyze the parent top-level goal during this pass, write a strategy, or stop after the first failed split.

Then decide each top-level VC in manual order:

- if it has split goals and all are provable, choose `aggressive_pre_process` and do not analyze whole-goal provability;
- if it has no split goal or any split is unprovable, analyze the whole top-level VC and choose `LLM_pre_process` when it is provable;
- if the whole goal remains unprovable, report an annotation/specification/dependency blocker instead of assigning it to proving.

The formal targets for an aggressive route are all of its split goals. An LLM route proves only the top-level VC and leaves its generated split blocks unchanged.

After the structural scan, independently review annotation comparisons in the current manual. Check the actual source of every added premise/resource and whether a related VC carries its establishment. `provable` is not proof evidence. Return a structured annotation blocker for a missing source. Mark a VC high-risk when it needs a new substantial mathematical lemma but has no definite counterexample or missing premise.

## 5. Strategies and helpers

Write strategies only after every mode is fixed:

- aggressive: one strategy for each split goal;
- LLM: one strategy for the whole top-level goal.

Explain the pre/post spatial resources, pure facts, existentials, right-side witnesses, cancellation/frame/list transformations, the sources of bounds and equalities, refinement states, and any helper's statement, premises, use site, and proof route.

Define a repeated proof pattern once; individual VCs should record only the real differences.

No helper is legal when `formal_case_lib` is absent. Otherwise, `helpers` lists only helpers newly proved or materially changed by the owning group in this round. Names use the group suffix and visibility is `local` or `public`. Every premise must follow from the current VC; a missing premise is an annotation/specification signal.

## 6. Grouping

Assign only top-level VCs; split goals always follow their parent.

Form preliminary groups by invariant, proof pattern, resource transformation, refinement transition, helper family, and sustained context. Then independently review load, coupling, and the critical path:

- top-level witness count;
- aggressive split count;
- helper count and complexity;
- proof mode, program stage, and library context;
- likely tail groups;
- whether independent final-result, transition, or safety work can be split.

A group usually has two to six top-level VCs. A truly independent result, route, or helper family may have one. Give each group an integer `estimated_difficulty` from 1 through 5. The handoff's size limit is only a hard cap. Groups are independent, do not read sibling output, and never contain `depends_on`.

Put high-risk witnesses containing comparison current/related VCs in a separate first group; do not mix them with many light projection/lia witnesses. The controller dispatches remaining groups only after this priority group passes.

## 7. Output contract

### `group_plan.json`

The top level contains only `groups`. A successful plan is nonempty and covers every current top-level VC exactly once.

Each group contains only `id`, `estimated_difficulty`, `witnesses`, and optional `helpers`.

An aggressive witness contains only `name`, `proof_mode`, and `split_strategies`, whose keys match manual names and order. An LLM witness contains only `name`, `proof_mode`, and `strategy`. A helper contains only `name`, `strategy`, and `visibility`.

Do not add digests, acceptance, dispatch, dependency, or reuse fields.

### `agent_output.md`

Keep these concise sections:

1. Outcome;
2. Structural Blocker Scan (the four machine-read fields);
3. Annotation Comparison Review;
4. Proof-Mode Decisions;
5. Common Proof Patterns;
6. VC Deltas;
7. Grouping Decisions;
8. Risks or Blockers.

Define each common pattern once. On a retry, state briefly what was retained or changed from the earlier vc-checking result.

### `agent_report.json`

Success is exactly:

```json
{"status": "completed"}
```

A blocked result adds one blocker with `failure_class`, `kind`, `vcs`, `message`, and `repair_boundary`. Annotation/specification/dependency blockers use nonempty `vcs` entries with exact current-manual `name`, `parent`, and `annotation_location`; plan/report/infrastructure blockers use an empty list. Legal failure classes are `annotation-gap`, `specification-gap`, `dependency-gap`, `plan-defect`, `report-defect`, and `infrastructure`. The first three return to annotation; the others retry vc-checking.

Do not copy command output, digests, or controller checks into the report.

## 8. Delivery

Write the plan and `agent_output.md` first. Write the report last, stop all writes, and tell main the owner has stopped. Main then runs `finalize-delivery`.

For `report-repair-required`, keep the same owner and attempt and repair only the named plan, explanation, manual inspection, or report. Do not create another round. After acceptance, the controller deletes the temporary manual and regenerates it; do not modify files again.
