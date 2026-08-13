# Overall Flow for One Verification Case

The main agent controls this flow. The only public program entry is:

```text
.agents/scripts/verification-orchestrator/controller.py
```

A human performs the initial repository-root bootstrap with:

```text
uv sync --frozen --python 3.12
uv run --frozen --python 3.12 python .agents/scripts/verification-orchestrator/controller.py ...
```

The public entry rejects any interpreter other than Python 3.12 before parsing or writing files. Subsequent actions use the validated absolute `sys.executable` from that uv environment. Main executes it unchanged and does not nest uv around it.

The authoritative C, generated files, and Rocq formal files always use the repository root as their current state. Stages do not create Git isolation directories; the run root stores only history, builds, group copies, and merge candidates. The main agent does not call controller internals, implement state transitions, or edit owner files on an owner's behalf.

## 1. Roles and fixed boundaries

| Role | Primary responsibility | Writable scope |
|---|---|---|
| main agent | Execute controller actions, retain agent targets, summarize blockers, perform writeback and final-check | Controller-designated main-summary sections |
| annotation-subagent | Design and repair annotations and mathematical specifications | Main-root target C, `formal_case_lib` when present, and current-attempt report; only `symexec` refreshes generated files |
| vc-checking-subagent | Analyze current VC, choose `proof_mode`, group work, and perform conditional reuse comparison | Current-round plan, analysis, hints, and debug scripts |
| group-worker | Prove this group's witnesses | Fixed-group copied manual, `group_worker_lib`, report, and debug script |
| controller | Own state, seals, versions, checks, scheduling, mechanical merge, writeback transaction, and final-check | `verification_runs/`, `reports/`, and controller-owned builds/output |

Each run has exactly one persistent annotation agent. Every later annotation repair appends to that same target. When manual VCs exist, each vc-checking attempt and each group's first worker claim uses an independent conversation without a parent transcript. When no manual VC exists, neither kind of agent is created.

Main proactively reads only the orchestrator `SKILL.md` and all its workflows/docs, current material explicitly returned by the controller, and the final-check skill/workflow when entering final checks; on Windows it also reads the root `AGENTS_WIN.md` and the Windows document to which it routes. The corresponding owner reads annotation, VC-analysis, and group-proof skills. Main does not read, summarize, or interpret those role documents or add the parent transcript to a handoff. An owner reads only its own skill and the current handoff files named by the claim message.

The three active library roles exist only when `formal_case_lib` is present:

1. main-root `formal_case_lib`;
2. group-directory `group_worker_lib`;
3. `proving_merged_lib`.

`formal_case_lib` and `proof_manual_file` both retain candidate paths derived from the authoritative formal stem, but either may be missing; the controller neither seeds a library nor creates a placeholder. A shared or differently named library is a dependency of the selected build backend and does not automatically become the current case's editable library. `public_helper_lemma_lib.v` is a controller-owned cross-round candidate pool. It is neither imported nor compiled directly and is not a fourth active library. A proving round reads only its frozen round-start `public_helper_snapshot.txt`.

## 2. Main state transitions

```text
intake
  → annotation
  → annotation-check-round
  → dune-build
  → with manual VCs: vc-checking → vc-checking-check-round
  → without manual VCs: controller accepts groups: []
  → vc-proving-preparing
  → with groups: continuously dispatch every group-worker / finalize-delivery / group validation
  → every group in the accepted plan reaches a terminal state for the round
      ├─ annotation gaps exist: aggregate feedback → one annotation retry
      └─ no annotation gap and every group accepted: vc-proving-verify
  → final-apply
  → final-check
  → done
```

If the current version changes at any stage, downstream conclusions cannot be reused as acceptance evidence. The controller marks affected attempts `stale`, records the mechanical difference, and routes the run back to annotation.

## 3. Stage details

### 3.1 `init-run` and `step`

`init-run` creates the fixed run root, report root, `controller_state.json`, event log, and timing summary. Run and report roots are allocated as an inseparable pair: a same-named leftover directory on either side may not be taken over by a new run. `--case` is both the run-id stem and the sole authoritative Rocq/generated formal stem, and it must be a valid Rocq identifier. The C stem, directory name, and case may differ, and one directory may contain multiple programs. A target C may reside under `QCP_examples/<collection>/**`; its parent is mirrored beneath `Rocq/examples/<collection>/**`. The controller persists `target_files` as exactly nine fields: the C path, mirrored formal directory, five exact artifact candidate paths, case, and active theory. It also creates `reports/<run>/controller_target_topology.json` exactly once with `O_EXCL`; that immutable anchor has exactly the top-level fields `run_id`, `case`, and `target_files`. On each state load the controller recomputes the nine target fields from the fixed C path and authoritative case and requires the state, anchor, and recomputed result to be exactly equal; later actions neither rename formal modules from the C stem/directory nor trust a substituted persisted target path. Each symexec rederives profile and recursive include/strategy search arguments from the sealed C path rather than copying them to state. `--max-parallel-group-workers N` stores a positive concurrency limit in run state; the default is 5. Later proving attempts inherit exactly that value without another hidden cap.

`step` derives the next action only from current state or records `waiting_for` while work is still active. It must not leave a state with neither an action nor a wait reason. Every main-owned action carries complete `invocation.argv` and absolute `invocation.cwd`; main executes them directly instead of inferring parameters from the action name.

For the first annotation attempt it:

- creates the sole annotation session;
- creates `annotation-attempts/annotation-attempt1/`;
- before agent startup, seals the target C, all optional formal/generated files that are actually present, and each candidate role's present/missing state under the attempt's `annotation_history/<attempt-id>/before/`;
- records an aggregate digest and present/missing counts in state.

Each annotation, vc-checking, vc-proving, and group attempt re-derives its directory, report, input, output, manifest, candidate, and reuse paths from the current run root, report root, round, and attempt id. Persisted paths are records to validate, not a new trust root. A cross-run or wrong-round path, absolute alias, symlink/reparse parent, or special directory entry fails before read, write, deletion, reuse, or validation; the controller never touches its target tree.

### 3.2 Agent claim and delivery

Every agent task begins with `claim-attempt`:

- the spawn/append action supplies a stable owner and complete `claim_invocation`;
- main executes that invocation unchanged;
- the controller atomically claims the action;
- binds the owner;
- records start time;
- returns a fixed `handoff.prompt` and complete `finalize_invocation` rendered from current authoritative fields.

Repeating the claim with the same owner is idempotent; another owner is rejected.

When an annotation retry comes from a group aggregate, the controller revalidates every `feedback_sources` fixed path and sealed digest before the first claim, a repeated claim by the same owner, and handoff rerendering. If a source drifts, it does not deliver an old prompt.

Main uses only this four-part prompt for spawn or append, without rewriting the claim message:

```text
Role: <role>
Owner: <owner>
CWD: <cwd>
Claim message (verbatim):
<claim message exactly as returned>
```

Main retains the owner-to-agent-target mapping. Annotation append and group repair use the existing target for that owner. Only after an agent has finished writing and stopped modifying files does main execute the claim response's `finalize_invocation`. If context is lost, it can recover the invocation from the next `step.waiting_for`. Never finalize and then allow further formal or report edits.

### 3.3 Annotation-owner work

The annotation owner:

1. modifies the main-root target C and `formal_case_lib` when present;
2. runs controller `symexec` exactly;
3. runs the `formal-case-lib` check exactly only when `formal_case_lib` is present;
4. performs annotation-checking in the same turn;
5. writes the final report.

Before each owner `symexec`, the controller revalidates the attempt's sealed `before` and creates a persistent temporary transaction for the generated roles named by persisted `target_files`; the transaction protects both file bytes and present/missing state.

The controller may remove and regenerate the manual only when it is:

- absent;
- zero bytes;
- composed entirely of generated `Admitted`/`Abort` seeds for each top-level/split proof;
- byte-identical to the revalidated sealed-before manual for this attempt.

The last case only lets the controller restore temporarily removed old bytes; it does not make annotation history a proof-reuse source. Any other completed/custom manual returns `protected-proof-manual`.

On main-root symexec failure, the transaction restores the pre-call existence and exact bytes of every generated role. Success commits it. A prepared transaction left by interruption is restored before the next invocation.

### 3.4 Annotation delivery and main-owned checking

Annotation `finalize-delivery` first mechanically compares:

- attempt `before`;
- current main root;
- the final report;
- the permitted write boundary.

If it returns `report-repair-required`:

- delivery remains `running`;
- no new attempt is created;
- owner does not change;
- the same annotation agent repairs the report or authorized files;
- the original `finalize-delivery` is rerun.

After the precheck passes, the controller creates and seals `after/`, the report digest, and actual changed files, then completes phase validation directly.

The main agent then performs `annotation-check-round`:

1. rerun canonical symexec in main root using persisted `target_files`;
2. parse the raw manual when present; a missing manual is equivalent to zero witnesses;
3. only when `formal_case_lib` is present, first run the selected backend's exact dependency preparation so dependency resolution and stale-dependency rebuilding finish, then run the fixed local `coqc` check;
4. replay canonical symexec in an attempt-owned clean root;
5. compare generated-role present/missing state and the digests of present files;
6. when the manual is present, compare declaration order and top-level/split names and statements;
7. save `source_version` and `source_goal_version`.

Only stable output is accepted. Owner checks do not replace this gate.

### 3.5 Selected dependency preparation (public action: `dune-build`)

After annotation acceptance and before deciding whether vc-checking is needed,
the controller performs the main-owned `dune-build` action. That historical
action name does not force Dune. Shared `build_mode.py` checks only
`<main-root>/_build`: a directory selects the existing Dune backend; otherwise
the lock-free Makefile backend is selected. Its presence must not change during
a run.

Both modes:

1. use persisted `goal_check_file` and `proof_auto_file` to determine the exact current case family;
2. prepare only the exact goal-check transitive closure, classifying the persisted case family as current and everything else as trusted-base dependencies;
3. seal current edges, dependency source/artifact digests, build configuration, case identity, and `source_goal_version`;
4. enter vc-checking/proving only after the snapshot passes; an accepted annotation retry invalidates the receipt and repeats preparation.

The existing Dune flow remains unchanged: remove ordinary canonical `Rocq/`
side products that conflict with Dune rules, run only
`dune build --root <main-root> --display=short <goal-check.vo>`, extract the
exact closure from theory dependency data, and write
`verification_runs/<run>/dune_dependency_snapshot.json`; dependency `.vo`
files live under `_build/default`.

Makefile mode runs breadth-batched `coqdep` only during temporary annotation
library preparation and this stage, then generates an exact standalone
Makefile whose sole goal is `trusted-base`. The formal action atomically writes
run-root `Makefile` and `makefile_dependency_snapshot.json`. It rejects
repository aggregate goals, removes recursive Make/flag injection, updates
main-root trusted-base `.vo` files sequentially through `.NOTPARALLEL`, and
cleans old side products only for the exact current family. It uses no legacy
global Make target, per-source resolver, or lock.

After proving starts, development, exact, validation, parent, debug, and final
only validate and reuse the selected snapshot and its corresponding `.vo`
files. They invoke neither Dune, Make, nor `coqdep` and never resolve the graph
again. Local `_coq_builds` compile only the current case. A project import
outside the snapshot requires an annotation retry and new accepted snapshot; a
group may not extend the dependency version dynamically.

Within one side-effect-free interval of a controller action, the selected
receipt is fully validated only once. The returned snapshot, dependency
summary, already-read current-source bytes, and debug-build summary are reused
without rereading, rehashing, or reparsing identical input. Validation runs
again after a build/Rocq step that can modify validated input, a state reload,
or an independent post-acceptance boundary. This process-local reuse adds no
persistent cache, freshness database, or handoff field; state field
`dune_preparation` retains its name only for wire compatibility.

### 3.6 VC analysis and acceptance

An empty `source_goal_version.target_witnesses` means symbolic execution has completed every VC. A missing manual, or a present raw manual containing only generated imports and scope commands, is valid. The controller then writes the standard `{"groups": []}` at report root and accepts it directly, without a vc-checking attempt, agent handoff, reuse hint, or debug script, and without manufacturing a manual. Goal-check and later parent/final full Coq checks remain mandatory; if goal-check imports a missing manual, the check must fail.

When at least one top-level VC exists, the controller creates an independent vc-checking attempt. Its subagent reads current main-root formal files and writes:

- `group_plan.json`;
- `agent_output.md`;
- owner report;
- only when a sealed source is bound, reuse hints and debug scripts.

The analysis order is fixed: judge all split goals while ignoring top-level VCs; select `aggressive_pre_process` for a parent whose split goals are all provable, otherwise analyze the whole parent and select `LLM_pre_process`; then analyze strategy and reuse only for aggressive split goals or `LLM_pre_process` top-level VCs; finally group top-level VCs, with every split goal following its parent into the same group.

After every proof mode is determined, vc-checking performs a second load, coupling, and expected-critical-path review. Separate independent final-result and transition/safety work; when separation is genuinely impossible, record the helper/context coupling. `max_witnesses_per_group` is only a hard upper bound and does not replace this review.

Reuse may be compared only when the controller explicitly binds the exactly preceding sealed proving source, in the fixed order of all helpers, all aggressive split goals, then all `LLM_pre_process` top-level VCs. A proof marked `direct` must come from a previous accepted group and have the same current/previous generated-goal semantic fingerprint; every other complete source is at most `partial`, and helpers must be `from scratch`. The controller enforces the helper reuse mode mechanically and rejects `direct` or `partial`; when no source is bound, do not scan other historical rounds.

After `finalize-delivery` seals the owner report, `vc-checking-check-round` mechanically validates:

- current version;
- exact top-level VC coverage;
- every `proof_mode`;
- order of aggressive `split_strategies`;
- `estimated_difficulty` in the range 1 through 5;
- owner-suffixed helpers and `visibility`;
- hard group bound;
- conditional reuse hints, source ranges, semantic fingerprints, and debug results.

The controller stores only plan path, digest, and current version in state; it does not rewrite the owner's plan. Critical-path and grouping rationale remains in `agent_output.md`, without fragile natural-language parsing.

`agent_output.md` is a decision summary: define each common proof pattern once, and give each VC only a pattern reference and its real delta. Preserve proof-mode reasons, grouping, critical path, and blockers. Do not repeat the handoff, full schema, controller commands, or identical proof steps. The controller records byte, line, pattern, and VC-delta counts, but these metrics do not affect acceptance. The complete strict `group_plan.json` remains the machine contract.

### 3.7 `vc-proving-preparing`

The controller revalidates the accepted plan and durable public pool, then creates all groups at once only when a present manual contains witnesses:

- `base_manifest.json`;
- fixed group directories and copied files;
- round-local `public_helper_snapshot.txt`;
- when applicable, `reuse_source_raw/` and the reference debug build;
- compact `group_workers_manifest.json`;
- each group's `group_worker_input.md` and optional `proof_reuse.md`.

The manifest stores only summaries and seals that cannot be derived from fixed directories, base, or accepted plan. Paths, assignment, routes, namespace, and commands are derived uniformly when read.

When the preceding proving round is stale but bound as the reuse source, the controller must parse its manifest using that source round's sealed `reuse_source_raw` seed explicitly. It must not reinterpret the old manifest, witnesses, or semantic fingerprints from main-root raw files modified by annotation.

Accepted plan order defines stable group numbering and mechanical merge. `dispatch_order` only fills concurrency slots and is mechanically ordered by: no reusable units first, decreasing difficulty, decreasing structural load, then plan index. It is not a dependency relation.

An empty plan still creates the base, public snapshot, applicable raw source, `proving_merged/`, and compact manifest. Both `groups` and `dispatch_order` in that manifest are empty arrays. An absent optional manual/library has a `null` digest in base and merged records. The controller immediately publishes `vc-proving-verify` and publishes no group action.

### 3.8 Group scheduling, delivery, and validation

This section applies only to a nonempty plan. All groups are mechanically independent and contain no `depends_on`. The controller fills available slots using `dispatch_order` and the run's concurrency limit.

Before each group delivery claim, the controller rerenders the handoff from current state, accepted plan, base, and manifest. A group prepared before a workflow upgrade but not yet claimed therefore receives current rules.

A worker may run development or exact checks for early feedback; these provide early feedback only. After the worker writes the final report, the main agent runs `finalize-delivery`. The controller always first seals the report, copied manual, and applicable `group_worker_lib`, then revalidates the current version, manifest/seed/public/reuse seals, write boundary, statements, and declaration order. For a `completed` delivery it additionally checks ownership, proof route, helper/import/safety/forbidden rules, runs Rocq, revalidates the seal afterward, and marks the group accepted only on success. For a `blocked` delivery it instead validates the blocker classification and the structure required by that failure class; an incomplete proof cannot be mislabeled accepted, and the write-boundary and structural checks on potentially reusable bytes cannot be skipped.

Validation runs Rocq within one controller command, then reloads fresh state, revalidates the same attempt and seals, and commits the result. It publishes no PID/in-flight marker and does not support concurrent calls of the same action.

A repairable structure, route, proof-completeness, or safety failure creates `append-group-worker` for the same owner in the same directory; other ready/running groups continue. A report-only failure opens only report repair. Drift of sealed formal bytes creates `invalid-report` and is not silently resealed.

If the first group preflight returns `report-repair-required` because of a report or Markdown contract, the controller freezes the copied manual and applicable library in `repair_formal_sha256` before returning. The owner repairs only the report/Markdown, and a subsequent finalize must keep the formal bytes unchanged; after successful finalize the controller clears that temporary seal.

When a group reports an annotation/spec gap with `blocker.failure_class: annotation-gap`, it does not take the in-place proof-repair path. The controller classifies only by that failure class, not by guessing from `kind` or message. Mathematical specifications, function contracts, loop invariants, assertions, and call instances all lie outside the group-worker write boundary. The group continues to use the existing blocker contract:

- In `group_worker_output.md` at the fixed report path, the owner itemizes this group's findings and evidence. The controller requires it to be a nonempty UTF-8 regular file and records its digest in the finalized `artifact_sha256`.
- During group validation, reuse, feedback aggregation, annotation summary, first/repeated claims, and repeated handoffs, the controller continuously revalidates that Markdown and the other feedback-source seals.
- In its own JSON, the owner explains this group's finding and `location` must name the affected witness. The controller checks structure, ownership, route, helpers, imports, and safety with `require_complete=False`, does not run exact/full group Rocq, and does not require an unfinished proof. Only a structurally valid group is retained as a blocked terminal state and reuse source for this round.
- In manifest order, the controller preserves each gap as one flat `current_blockers` record: the owner blocker's `failure_class`, `kind`, `location`, `message`, and `repair_boundary`, plus controller-bound `round`, `group_id`, `witnesses`, `markdown`, and `json`. `witnesses` is the accepted-plan group assignment; `location` still identifies the exact affected witness.
- Do not append annotation-repair work to that group or repeatedly attempt proof in its directory.
- This does not stop siblings: running groups continue, and ready unclaimed groups continue to be published under `dispatch_order` and the concurrency limit until every group in the accepted plan reaches a terminal state for the round. It is insufficient to wait only for deliveries that were already running when the gap appeared.

After every group is either `accepted` or a structurally valid annotation-gap `blocked`, the controller aggregates every annotation gap in manifest order and creates exactly one `retry-round --phase annotation --reason group-worker-annotation-gaps --previous-attempt <vc-proving-round>`. The retry expands those records into `feedback_sources` in plan/source order; the new annotation input must link every original `group_worker_output.md` and `group_worker_report.json` item by item so that main's five-part summary and the annotation agent's repair can cover every root cause. Whenever the aggregate is nonempty, the controller does not publish `vc-proving-verify`, perform mechanical merge, or run the parent check for this round.

Every group's report/manual/library seal enters the existing `reuse_group_artifacts.groups`, and the structural filter is recorded in `structurally_valid_groups`. In the next round, only a proof from a previous accepted group with the same semantic fingerprint may be `direct`; a proof from a structurally valid annotation-gap blocked group is at most `partial`, and its helpers are reproved from scratch. Both kinds of bytes remain sealed; historical sources provide conditional reuse rather than acceptance evidence for the current round.

Other failure classes do not participate in this aggregate and continue to follow the existing same-delivery report repair, in-place proof repair, `compact-error` exhaustion, or termination rules. Annotation gaps change only the timing of continued dispatch and aggregated feedback; they relax no group-report, structure, or sealing check.

An accepted group's planned public helper is appended to the durable pool through a before/after digest transaction and is available only to later rounds. Pool-contract validation, the append baseline, and the round-snapshot copy reuse the same exact bytes read once; the digest gates before and after atomic replacement remain mandatory. Siblings in the current round retain the frozen snapshot.

When `formal_case_lib` is absent, the plan cannot declare a helper, preparing does not create `group_worker_lib`, and a worker cannot modify a shared or differently named library. The same owner executes development, debug, exact, and validation commands sequentially for the same group development workspace.

### 3.9 `vc-proving-verify`

Only when the accepted plan is empty, or when the round has no annotation gap and every group is accepted, does the controller publish and execute `vc-proving-verify` to:

1. revalidate current version and base, manifest, and group seals;
2. mechanically merge assigned proof spans in accepted-plan order;
3. merge `group_worker_lib` files when `formal_case_lib` is present;
4. deduplicate token-identical same-name helpers or deterministically rename variants only in the candidate;
5. revalidate final structure and forbidden rules;
6. run one parent full check;
7. write `proving_merged_result.json`.

Parent verification does not repeat a full Rocq check for each group. Scheduling or completion order cannot affect the candidate.

For same-name helpers with different tokens, a frozen public/reuse canonical block wins; otherwise the first plan group wins. Every other legal variant receives a unique current-group suffix only in the merged candidate. Only exact identifier tokens in that group's new library declarations and assigned proof blocks are rewritten. Sealed group files remain unchanged, and the rewritten candidate must pass the parent full check.

With manual VCs, a parent failure saves the first precise error plus result path and digest so the next vc-checking attempt can read the original blocker. With no manual VC, the failure routes directly to annotation repair. The same failed candidate is not simply rerun.

### 3.10 `final-apply` and `final-check`

Before writing main root, `final-apply` revalidates:

- accepted annotation target C and `after_snapshot`;
- current generated files;
- parent result;
- accepted seals for every group that exists;
- candidate digests.

It then uses a persistent `prepared → backed-up → completed` transaction to back up and atomically replace the formal manual and/or `formal_case_lib` that are actually present. When both optional candidates are absent, a zero-target transaction is valid but still completes source revalidation and the state transition. Before every recovery, re-entry, or rollback, the records must exactly bind the accepted zero-, one-, or two-candidate set: no additional, missing, or duplicate record; source, target, relative path, candidate digest, original presence/digest, transaction id, and backup path must match the current run, accepted seals, and fixed backup topology. A zero-target transaction has only empty records. Injection, cross-run paths, an original digest differing from the accepted annotation seal, or invalid backup topology terminates as `rollback-failed` without rollback.

`final-check` performs:

- independent symbolic-execution freshness;
- main-root full Rocq check;
- `proof_mode` structure of a present manual;
- consistency of the three libraries and public pool when applicable;
- forbidden-lemma checks;
- independent import checking from a present `formal_case_lib` to this run's exact generated artifacts; every other project import must belong to the accepted dependency snapshot;
- before/after cleanup of target by-products.

Successful cleanup records only a deletion count. Failure records only error count, residual count, and the first error or residual path, not the complete path list. An agent does not manually delete by-products.

After a failure and successful rollback, the phase first returns to `final-candidate-apply`; a new `final-apply` must succeed before final-check can run again. If a source seal is still invalid, apply stops `blocked` without touching rolled-back formal files. A rollback failure stops automatic recovery.

## 4. Retry and invalidation

### Annotation repair

A valid blocked vc-checking report must use a fixed `failure_class`. Only `annotation-gap`, `specification-gap`,
`dependency-gap`, and `source-version` route to annotation. `plan-defect`, `report-defect`, and `infrastructure`
route to a same-phase vc-checking retry while preserving the accepted annotation, `source_goal_version`, and selected
dependency snapshot. The controller does not infer the recovery phase from prose in `kind`, `message`, or `repair_boundary`; an
unknown class first becomes an invalid report for vc-checking to repair.

Under one accepted source/source-goal version, when three consecutive `infrastructure` reports have the same
`failure_class`, `kind`, and `location` after replacing the round id with a fixed placeholder, the controller stops
creating no-progress retries. It clears the retry action and publishes
`repeated-vc-checking-infrastructure-blocker`, while preserving the accepted annotation and selected dependency snapshot for
recovery in the VC-checking phase after the framework is repaired. A historical attempt whose report bytes or seal
are invalid does not count toward this consecutive chain.

An annotation retry gets a new independent attempt directory while continuing the same annotation-agent target. The main agent reads the original blocker's Markdown and JSON, then fills five fixed sections in the new `agent_input.md`:

1. blocker conclusion;
2. evidence and causal analysis;
3. reflection on the previous annotation attempt;
4. required repair;
5. scope decision.

When the source is an aggregate of group annotation gaps, main must read every original Markdown/JSON file listed by the controller and make the five-part summary cover every group rather than selecting one. `annotation-summary-ready`, the first/repeated claim, and repeated handoff must revalidate those fixed sources and their digests; only after validating and sealing the input does the controller emit one `append-annotation-agent`. The controller separately maintains `annotation_causal_retry_count`: it increases only when the feedback report's machine `failure_class` is an annotation/specification/dependency gap. Infrastructure, tool/report, version authorization, and other non-annotation causes end and reset that consecutive count; `compact-error` preserves the prior value without increasing it. Only when that count reaches 2—at least the second annotation repair in the same causal lineage—must the owner reassess the overall relationship among the mathematical specification, function contracts, loop invariants, assertions, and call instances. The annotation-attempt directory ordinal alone never triggers broad refactoring.

A group-aggregate retry binds the entire preceding proving round with `retry_previous_attempt`, and its phase, reason, and source must match the current action. On an identical repeated invocation, it returns `already-retried` and reuses the original attempt only after revalidating the feedback sources; it does not create a second annotation attempt.

### `compact-error`

- Annotation: append to the same agent while retries remain.
- VC-checking: create a same-stage retry within the state limit.
- Group: at the limit, seal the failed round's fixed group artifacts and structurally valid set, then write `compact-error-retry-exhausted`; do not create another retry or mislabel it as annotation/plan failure.

### Version change

If vc-checking, preparing, group validation, or parent verification detects current-version drift, the controller records the mechanical difference and routes back to annotation. If another group delivery is still running, it waits for those deliveries to end before emitting unified annotation feedback. Version mismatch is not `failure_class: annotation-gap`; when current source is stale, do not continue dispatching unclaimed groups. The new "dispatch every planned group" contract applies only to a valid annotation-gap blocker, and existing boundaries for other failure classes remain unchanged.

The controller follows the single-run, single-command execution contract. It creates no lock file for state, formal targets, workspaces, or selected build artifacts and uses no operating-system locking API. State still rejects stale whole-state writes through generation compare-and-swap and atomic replacement; formal, report, and build files still obey fixed-path, digest-seal, and atomic-replacement contracts. This document does not define multiple runs modifying the same main root concurrently.

Exactly the previous sealed proving round may be bound as the next vc-checking comparison source when eligible. It may be parent-failed, contain structurally valid blocked groups, or have been verified and then made stale by annotation/freshness retry. Historical proof is a reuse opportunity, never current acceptance evidence.

## 5. Completion criteria

The controller may set the run to `done` only when all of the following hold:

- Independent symbolic-execution freshness passes.
- Every top-level VC and aggressive split goal is complete; only original split blocks belonging to `LLM_pre_process` may retain a valid `Abort.`.
- Fixed goal-check and the main-root full Rocq check pass.
- A present manual has valid declaration and `proof_mode` structure; a present manual and `formal_case_lib` contain no `Admitted.`, additional `Axiom`, or forbidden lemma.
- The digest of a present `formal_case_lib` equals the accepted `proving_merged_lib`; when absent, both digests are `null`; the three library levels and public helper pool agree where applicable.
- Annotation attempts have complete `before/after` history, and all adopted formal content comes from a controller-accepted candidate.
- The independent import audit for `formal_case_lib`, pre/post final-check side-product cleanup, and final-check all pass.
- `controller_state.json` has phase `done`, and the corresponding success event has been committed to the append-only event log.
