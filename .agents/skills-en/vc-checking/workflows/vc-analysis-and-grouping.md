# VC Analysis and Grouping Workflow

This workflow is performed only by the controller-claimed `vc-checking` owner, and only when the raw manual contains at least one top-level VC. Zero manual VCs (the manual is missing, or contains only generated imports and scope commands) are accepted directly by the controller as `{"groups": []}`; the owner must not invent a witness, manual, plan, or group for them.

This file is the process and machine contract for vc-checking. The files under `docs/` provide proof-analysis knowledge only; text there that describes an obsolete read scope, report layout, or handoff method does not broaden this workflow's permissions.

## 1. Start from the claim/handoff

Main has executed the controller-provided `claim_invocation` and then sends the current owner the prompt from the claim response verbatim. The prompt always contains `Role`, `Owner`, `CWD`, and the verbatim `Claim message`. At the start of work:

1. Confirm that the role is the current `vc-checking` work, that the owner agrees with the claim message, and work in the given `CWD`.
2. Read the current `agent_input.md` named by the claim message in full. Do not guess paths, versions, commands, or output locations from a directory name, case stem, or old attempt.
3. Use only the current attempt, source version, target witnesses, group limit, input paths, output paths, optional reuse binding, and exact controller commands provided by the handoff.
4. If the prompt lacks a section, role/owner conflict, a required path is unbound, or a required file's state conflicts with the handoff, stop expanding the read scope and report a blocker or stale condition under Section 9.

Do not run or reclaim `claim-attempt` yourself and do not change owner. Every new attempt uses an independent session; continue in this owner target only when the controller explicitly requests an in-place repair of the same delivery.

## 2. Read and write boundaries

Apart from this skill's workflow/docs and the current claim/handoff, read only the following items precisely bound by the handoff:

- raw `*_proof_manual.v`;
- `*_goal.v`;
- `*_proof_auto.v`;
- a present `formal_case_lib`;
- when reuse is enabled, the sealed source, frozen helper snapshot, existing group seal/result, and controller blocker;
- current-attempt receipts or diagnostics returned by controller commands.

Write only the following paths precisely provided by the handoff:

- `group_plan.json`;
- `agent_output.md`;
- `agent_report.json`;
- when reuse is enabled, `reuse_hints/<group-id>.md`;
- the current/reference debug script paths provided by the handoff.

Always observe these boundaries:

- Every main-root formal file is read-only; do not modify C annotations, generated files, raw manual, goal, auto, proof bodies, or any lib.
- Do not create a missing manual, `formal_case_lib`, helper lib, or placeholder file.
- Do not read the root `AGENTS.md`, verification-orchestrator, another role's skill, controller state/event, sibling-owner output, an unbound run, or repository examples.
- Do not scan history for reuse opportunities; only the exactly preceding sealed proving source explicitly bound by the handoff is readable.
- Do not perform a phase transition for main/controller or start an annotation owner, group-worker, merge, verify, final apply, or final check.

## 3. Controller command boundary

Run every `coq-debug` or other controller command in the handoff unchanged: do not change argv, `argv[0]`, cwd, flags, paths, or order. Prefer a direct system-terminal call. If the runtime exposes terminal operations only through `functions.exec`, use a transparent bridge: each cell may await exactly one `tools.exec_command` to launch, or call exactly one `tools.write_stdin` to continue the same live session (or use the runtime-documented normalized name for that same terminal operation), and may only forward its result. When launching, pass the complete command/argv, every argument, and cwd unchanged; when continuing, preserve the same session id. Do not serialize argv into shell text, reparse the command, or add quoting.

Forbidden actions:

- calling a second tool in a bridge cell, or constructing, altering, sequencing, parallelizing, or interpreting commands;
- using other JavaScript/Python orchestration, a generated shell/PowerShell/Python script, or another layer of `uv run`;
- using `sh -c`, a pipeline, command substitution, a background process, or a self-constructed environment;
- directly invoking an internal controller module, raw Coq/Rocq, symexec, Dune, Make, or a similar substitute command.

Preserve and continue every outer cell and inner session/process id until the actual command exits. If a transparent bridge returns a running `functions.exec` cell, resume only that cell with `functions.wait` until its one terminal operation returns. Empty output, the initial yield, and `Script completed` do not mean the check passed. A controller check passes only when the final exit code is `0` and the controller JSON has `status` equal to `passed`; otherwise preserve the exact failure evidence and handle it under Section 9 rather than bypassing it with a substitute command.

## 4. Exhaustive split-first analysis and `proof_mode`

The analysis has two global ordering barriers: do not analyze any top-level VC before completing the binary judgment for every split goal; do not write a detailed strategy, helper, reuse judgment, or group before determining a mode or failure conclusion for every VC.

### 1. Verify the formal targets

List every top-level VC and its `<vc>_split_goal_*` declarations in raw-manual declaration order, and compare them with the handoff's target witnesses and mapping. A mismatch in name, order, statement, or target coverage is stale/malformed input; do not edit the manual or guess a mapping.

A split declaration is a formal subgoal of `aggressive_pre_process`, not preprocessing noise. Explicitly mark a top-level VC with no split declaration as "no split," but do not invent a split for it.

### 2. Complete the binary judgment for all split goals first

Visit every split goal of every top-level VC, traversing the entire raw manual before proceeding. At this stage, record exactly one conclusion for each actual split goal:

- **Provable**: the current premises semantically imply the conclusion.
- **Unprovable**: the current split goal's premises do not imply the conclusion.

At this stage, do not:

- judge, expand, or record the overall provability of any top-level VC;
- diagnose one unprovable split directly as an annotation/spec gap;
- write a proof strategy, helper, reuse decision, or grouping;
- stop before judging later split goals because an earlier split was unprovable.

`aggressive_pre_process` may discard information needed by the whole proof, so an unprovable split means only that its top-level VC must next receive an overall judgment.

### 3. Determine one unique mode for every top-level VC

After completing every split binary judgment, process each top-level VC in raw-manual order:

- If it has at least one split goal and all its split goals are provable, select `aggressive_pre_process` and do not analyze the top-level VC's overall provability.
- If any split goal is unprovable, or the VC has no split goal, judge only the whole top-level VC. Select `LLM_pre_process` if the whole goal is provable; if it remains unprovable, record an annotation/spec gap or a genuine infrastructure blocker.

Complete every required overall judgment so that `agent_output.md` gives complete feedback for the attempt. If any whole top-level VC is unprovable, this attempt must not output a complete plan eligible for proving or send that VC to a group-worker to be forced through; write one terminal report under Section 9.

`LLM_pre_process` proves only the top-level VC and leaves its original split proof tokens unchanged. The formal proving targets of `aggressive_pre_process` are all split goals belonging to that VC; the top level is combined later by the established preprocessing route.

## 5. Detailed strategies and helper planning

Write detailed strategies only after every top-level VC has a `proof_mode` eligible for proving. The analysis object must correspond exactly to the mode:

- `aggressive_pre_process`: analyze only all split goals of that VC; do not analyze or compare the top-level VC's proof idea, and do not create a reuse row for the top level.
- `LLM_pre_process`: analyze only the whole top-level VC; do not analyze its split-goal proof ideas, and do not create a reuse row for a split.

For every actual analysis target, explain specifically:

- the pre/post spatial resources, pure facts, and existentials in `P |-- Q`;
- the instantiations and sources of right-hand witnesses;
- resource cancellation, split/merge, frame, and array/list/permutation transformations;
- the sources of pure premises such as bounds, guards, length facts, and equalities;
- the source/target state and transition of a refinement;
- a helper's statement shape, every premise, how the current VC discharges each premise, where it is used, and its proof route.

First extract repeated routes into common proof patterns and define each pattern only once; for each VC, reference the pattern and record only real differences such as binders, bounds, branches, witnesses, rewrites, or helpers. Use this skill's two `docs/` files for detailed domain methods, but do not follow examples in those docs to read unbound repository files.

Plan in `helpers` only helpers that the owning group will newly prove or materially modify in this round:

- When `formal_case_lib` is missing, do not plan any helper; the controller will not create `group_worker_lib`, and a shared or differently named lib cannot be treated as the current case's editable lib.
- A name must carry that owner group suffix and be globally unique within the plan.
- `visibility` may only be `local` or `public`.
- `local` is for this group only; use `public` only for stable, pure mathematics expected to serve a future group or round.
- A helper whose declaration/proof tokens match the frozen snapshot or accepted reuse is not a new planned helper.
- A helper premise that cannot be discharged from the current `P` is an annotation/spec signal; do not hide it by placing the premise into a helper or public pool.

All groups are independent for scheduling in this round. Do not plan to read/import a sibling `group_worker_lib`, wait for a public helper to be promoted during this round, or use `depends_on`; keep a tightly coupled proof-specific helper family in the same group as its consumers.

## 6. Conditional sealed-source reuse

Perform reuse only when `agent_input.md` explicitly binds the "exactly preceding sealed vc-proving source." When it does not:

- do not scan `verification_runs/`, reports, Git history, or another directory;
- do not create `reuse_hints`;
- do not run a reference comparison;
- plan the strategy from scratch against the current targets.

When reuse is enabled, complete unit comparisons after determining modes and current detailed strategies, then write exactly one hint for every group after the final grouping is determined. The comparison order is fixed:

1. all planned helpers;
2. all `aggressive_pre_process` split goals;
3. all `LLM_pre_process` top-level VCs.

Within every mixed-mode group, `group_plan.json` must also place all `aggressive_pre_process` witnesses before all `LLM_pre_process` witnesses while preserving relative order within each segment. This makes plan traversal, the fixed category order, and the actual hint rows identical; reordering only the hint table is insufficient.

Do not create comparison units for aggressive top-level VCs or `LLM_pre_process` split goals. The controller may bind a source from a round whose parent check failed, a failed round containing a structurally valid blocked group, or a round that was once verified but became stale due to an annotation/freshness retry.

Reuse decisions:

- Only an accepted group that passed controller group validation can provide `direct copy`.
- A proof that was not accepted can provide at most `partial proof-idea reuse`; every helper from it is `from scratch`.
- A helper permits only `direct copy` or `from scratch`.
- A proof permits `direct copy`, `partial proof-idea reuse`, or `from scratch`.
- A proof `direct copy` also requires compatibility of the complete proof declaration/route and equality of the current/previous generated-goal semantic fingerprint; changing only a generated declaration name permits direct reuse.
- When `P |-- Q` becomes `P' |-- Q'`, only an explainable pre/post adapter or shared frame idea permits partial reuse; an explanation in a hint is not a machine proof.

Compare a helper's complete declaration/proof tokens only against the frozen snapshot or sealed source bound by the handoff, and do not put a helper in a goal debug script. Use the current/reference debug script paths and exact commands from the handoff; every proof comparison unit uses the complete target supplied by the handoff:

```coq
Goal <active_case_theory>.<case>_goal.<symbol>.
Show.
Abort.
```

You may add actual debugging tactics and additional `Show.` commands within that goal, but do not add local declarations, `Load`, load-path commands, or wrappers. The current script exactly covers all proof comparison units—that is, aggressive split goals and `LLM_pre_process` top-level VCs. The reference script covers only previous proof goals actually cited for direct/partial reuse. If every proof is `from scratch`, do not create or run a reference script.

Each final group's `reuse_hints/<group-id>.md` contains only the fixed five-column table:

```text
Current goal | Decision | Previous file | Lines | Reason
```

Rows remain in the relative order "all helpers → all aggressive split goals → all LLM top-level VCs" and contain only items belonging to that group. For a non-`from scratch` item, file/path and start/end lines must exactly cover one complete helper or proof declaration recognized by the parser; they cannot cite only a statement, internal tactic, or `Proof` subsection. Write `—` for the file/lines of `from scratch`. Express helper reuse only in the helper's own row; do not invent its dependency on every witness.

## 7. Preliminary grouping and second review

After every strategy is complete, form preliminary groups by shared invariants, proof patterns, array/frame transformations, refinement transitions, helper families, and similar sustained contexts. Assign only top-level VCs; every split goal of an aggressive VC always follows it into the same group.

After preliminary grouping, perform an independent review of load, coupling, and the expected critical path. Recheck every group for:

- the number of top-level witnesses;
- the number of aggressive split goals;
- the number and complexity of helper families;
- mathematical-library and sustained-proof-context burden;
- whether it mixes different `proof_mode` values or unrelated program stages;
- which group is expected to become the tail critical path and whether it can still be split.

Separate initialization, core semantic transitions, simple control-flow projections, and final results when they do not share an inseparable helper/context. Independently provable final-result and transition/safety work must be separated; if separation is impossible, explain the concrete helper/context coupling in `agent_output.md` and plan stable helpers such as permutation, sum/length, or mask-clear in advance.

Usually put about 2 to 6 top-level witnesses in each group. Use a single-witness group only for an independent final result, special route, or independent helper family. Do not create a large tail group by combining heavy aggressive/helper work with many light VCs needing only projection, rewriting, or arithmetic. Explain any group with more than 6 witnesses or any expected tail that still cannot be split.

Give each group an integer `estimated_difficulty` from `1` to `5`. The handoff's `max_witnesses_per_group` is a hard upper bound, not a substitute for this load judgment. Accepted-plan order determines fixed group numbering and helper merge order; the dispatch order computed separately by the controller affects only concurrent scheduling.

## 8. Strict output contract

For a successful attempt eligible for proving, complete `group_plan.json`, optional reuse/debug artifacts, and `agent_output.md` first. After confirming that they will no longer be modified, write `agent_report.json` last. On a terminal blocked/stale/compact-error path, do not invent a plan, hint, or debug artifact to satisfy the success contract; retain only diagnostic materials permitted by the handoff and formed before failure, preserve complete evidence in `agent_output.md` first, and write the corresponding terminal report last. On every path, do not continue modifying owner files after writing the report.

### `group_plan.json`

The top level of a successful plan contains only `groups`. Under this workflow, `groups` must be nonempty and exactly cover every top-level VC in the raw manual; only the controller generates an empty plan for zero manual VCs.

```json
{
  "groups": [
    {
      "id": "array-frame",
      "estimated_difficulty": 4,
      "witnesses": [
        {
          "name": "proof_of_x",
          "proof_mode": "aggressive_pre_process",
          "split_strategies": {
            "proof_of_x_split_goal_1": "instantiate the old list and discharge the bound",
            "proof_of_x_split_goal_2": "rewrite the update and cancel the unchanged frame"
          }
        }
      ],
      "helpers": [
        {
          "name": "list_update_frame__array_frame",
          "strategy": "prove the unchanged prefix and suffix frame from the index bounds",
          "visibility": "local"
        }
      ]
    }
  ]
}
```

Machine fields must satisfy all of the following exactly:

- A group contains only `id`, `estimated_difficulty`, `witnesses`, and optional `helpers`; group ids are unique.
- Every top-level VC appears exactly once; each witness name exactly matches the raw manual.
- An aggressive witness contains only `name`, `proof_mode`, and `split_strategies`. Split keys exactly match raw-manual names/order and every strategy is nonempty; do not write a top-level `strategy`.
- An `LLM_pre_process` witness contains only `name`, `proof_mode`, and a nonempty whole-top-level `strategy`; do not write `split_strategies`.
- When reuse is enabled, a mixed-mode group's witnesses list all aggressive witnesses before all LLM witnesses while preserving relative order within each segment.
- A helper contains only `name`, a nonempty `strategy`, and `visibility`; its name has the owner group suffix and is globally unique, and visibility is only `local` or `public`.
- `estimated_difficulty` is an integer in `1..5`; the witness count in every group does not exceed the handoff limit.
- Do not add source/version, digest, `verified`, `depends_on`, dispatch order, load statistics, notes, or any other field.

### `agent_output.md`

Retain only six decision sections:

1. `Outcome`: whether the attempt can enter proving, witness/group counts, and the expected critical path.
2. `Proof-Mode Decisions`: in manual order, concisely record every split binary result for each VC, whether an overall judgment was required, and the final mode and reason.
3. `Common Proof Patterns`: common proof patterns, each defined only once.
4. `VC Deltas`: for each VC, the pattern reference, actual differences for the selected formal targets, helper premises/ownership, and optional reuse conclusion.
5. `Grouping Decisions`: preliminary sharing relationships, the second load/coupling/critical-path review, and why groups were split or cannot be split further.
6. `Risks or Blockers`: genuine risks; on failure, complete evidence for the annotation/spec or tool blocker.

This Markdown is for people and later repair and does not control machine acceptance. Do not repeat the handoff contract, skill text, complete plan/schema, controller commands, complete reuse table, previous proof, or steps identical for every VC. New evidence may be written fully; write a common route only once.

### `agent_report.json`

On success it contains only:

```json
{
  "status": "completed"
}
```

Do not copy a version, digest, changed files, checks, command output, receipt, or "verified" declaration; the controller computes and accepts those facts itself.

## 9. Boundaries for blocked, stale, and annotation feedback

None of the following is a blocker: a difficult proof, an as-yet-unproved helper, a strategy requiring group-worker exploration, reuse being `from scratch`, or one unprovable split goal when the whole top-level VC is provable.

Write a terminal report only when the whole top-level VC remains unprovable, an input/command is genuinely damaged, or a required file or authorized path is missing such that work cannot continue within this role's boundary. A `blocked` report has only `status` and one complete `blocker` at the top level:

```json
{
  "status": "blocked",
  "blocker": {
    "failure_class": "<classification allowed by handoff/controller>",
    "kind": "<specific problem type>",
    "location": "<witness, formal symbol, or file location>",
    "message": "<complete and concise explanation of why the current premises do not imply the target>",
    "repair_boundary": "<exact boundary that must be repaired>"
  }
}
```

No field may be omitted or added. `failure_class` must be exactly `annotation-gap`, `specification-gap`,
`dependency-gap`, `source-version`, `plan-defect`, `report-defect`, or `infrastructure`. Use the current enums
supplied by the handoff/controller for `kind` and `repair_boundary`; do not invent synonyms. The controller selects
the recovery phase only from `failure_class`: the first four return to annotation, while the last three preserve the
accepted source and selected dependency snapshot and retry vc-checking after repairing the corresponding controller/plan/report
boundary. It never guesses from `kind`, `message`, or prose. If multiple top-level VCs expose annotation gaps, JSON
still contains one complete blocker: aggregate the affected witnesses in `location/message` and preserve evidence
for each item in `agent_output.md`.

Annotation/spec-gap feedback must specifically state:

- the failing witness and the whole-goal shape actually analyzed;
- the ownership/resource, pure fact, array/list observation, `@pre` bridge, refinement state, or helper premise required by `Q` but absent from `P`;
- when locatable, the corresponding C function, function contract, loop invariant, assertion, call instantiation, or mathematical specification in the present `formal_case_lib`;
- why the repair boundary lies outside vc-checking or group proof.

Do not modify annotation/spec, force an unprovable target into a plan, contact or start an annotation agent, or write an annotation summary for main. Main/controller will cite this attempt's original Markdown/JSON blocker when it later creates one formal annotation feedback delivery; this owner's work stops at report delivery.

If the source version or seal becomes invalid during work, use the `stale` terminal status required by the handoff and do not read a new version into the same attempt. If context is compacted and you can no longer guarantee that the exhaustive analysis was completed, use the required `compact-error` rather than guessing the remainder. The exact JSON shapes of both statuses come from the claim message; do not disguise either as `completed` or advance an old plan.

## 10. Stop writing, finalize, and in-place repair

After completion or blocking, close every owner file and confirm that no formal/report/debug writes remain before returning the result to main. Main uses the complete `finalize_invocation` from the claim response or `step.waiting_for`; the owner does not construct, rewrite, or preemptively execute finalize. Finalize first runs any applicable owner-candidate preflight. Only after that passes does it seal the owner files and directly run `vc-checking-check-round` to mechanically check the current version, exact VC coverage, proof mode, difficulty, helper contract, and conditional reuse hints. If preflight returns a same-attempt repair, follow the boundary below and rerun the same command.

After finalize:

- Acceptance succeeds: this role's work ends. Do not read state to guess the next step or run proving preparing or another phase.
- The controller returns `report-repair-required` or a repairable handoff for the same attempt: the delivery remains `running`; continue only after receiving the controller repair prompt appended verbatim by main to the same owner target. Read only the blocker/files explicitly given by that handoff, and modify permitted owner outputs according to the repair boundary; do not create a new round, change owner, or redo formal analysis that was not rejected.
- If only report repair is permitted, keep `group_plan.json`, reuse hints, debug scripts, and all formal source unchanged; repair only the contract error identified by the controller in `agent_report.json`/`agent_output.md`. If the handoff opens a plan/hint output, modify only the listed path.
- After repair, stop all writes again and return to main, which reruns the same delivery's `finalize_invocation` verbatim.
- If the controller determines that source/seal drifted, repair crossed its boundary, or the result cannot be accepted, report according to its terminal handoff; do not bypass the check or independently enter annotation or a later phase.

Before delivery, verify one final time:

- Every split goal received a binary judgment before any top-level analysis.
- Every top-level VC's mode follows the unique decision rule.
- Each strategy covers only the formal targets for that mode.
- On success, the plan exactly covers the targets with no extension fields and the second load/coupling/critical-path review is complete; a terminal path did not fabricate a plan.
- When reuse is enabled, the source is the explicitly bound source and hint/debug coverage and ordering are correct.
- The report was written last and follows the minimal JSON contract.
- No formal source was modified, no other role's process was read, and no later phase was advanced.
