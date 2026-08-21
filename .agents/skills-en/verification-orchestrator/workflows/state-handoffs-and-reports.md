# State, Handoffs, and Reports

`controller_state.json` is the sole authority for current state. Markdown explains work to people and agents. JSON stores only state, plans, seals, and terminal results that the controller must parse.

## Core terms and authoritative sources

| Term | Meaning |
|---|---|
| `main root` | Repository root; current state of the authoritative C, generated files, and Rocq formal files |
| `run root` | `verification_runs/<run>/`; builds, annotation history, group copies, and merge candidate |
| `report root` | `reports/<run>/`; state, events, timing, handoffs, and results |
| `round` | One annotation modification iteration, one vc-checking attempt, or one controller-owned proving preparation |
| `split goal` | A `<vc>_split_goal_*` declaration in the raw manual; a formal subgoal of the aggressive route |
| `proof_mode` | Exactly `aggressive_pre_process` or `LLM_pre_process` |
| `source_version` | Binds annotation source files by relative path and digest; stores no absolute path |
| `source_goal_version` | Binds the four raw generated records, targets and split mapping, statement hashes, goal symbols, and relevant semantic fingerprints of `formal_case_lib` |
| `case` | `--case`; the run-id stem and sole authoritative Rocq/generated formal stem, which must be a valid Rocq identifier and cannot be replaced by the C stem or directory name |
| `target_files` | The nine-field C/formal path, case, and active-theory mapping resolved once by `init-run`; also written to the non-rewritable `controller_target_topology.json` anchor and recomputed from the fixed C/case and checked three ways on every load |

`formal_case_lib` and `proof_manual_file` are candidate roles and may be missing; optional-role versions/digests use present/missing and `null`, and no placeholder may be created. The main-root `formal_case_lib`, applicable `group_worker_lib`, and applicable `proving_merged_lib` are the three active library levels; shared or differently named libraries are dependencies of the selected backend. `public_helper_lemma_lib.v` is only the controller-owned, append-only cross-round candidate pool, not a fourth active library.

## 1. Fixed directories

```text
verification_runs/<run>/
  dune_dependency_snapshot.json       # Dune mode: `_build/` present
  makefile_dependency_snapshot.json   # Makefile mode: `_build/` absent
  Makefile                            # Makefile mode only: exact trusted-base plan
  _coq_builds/
    current/
  public_helper_lemma_lib.v
  annotation_history/<attempt-id>/
    before/
    after/
  <case>-vc-proving-rN/
    base_manifest.json
    public_helper_snapshot.txt
    reuse_source_raw/
    groups/group_NN__<group-id>/
      <case>_proof_manual.v
      <case>_lib.v                 # only when formal_case_lib is present
    proving_merged/
      <case>_proof_manual.v        # only when proof_manual_file is present
      <case>_lib.v                 # only when formal_case_lib is present

reports/<run>/
  controller_state.json
  controller_target_topology.json
  run_logs.json
  timing_summary.json
  group_plan.json
  annotation-attempts/annotation-attemptN/
    agent_input.md
    agent_report.json
    agent_output.md
  rounds/<round-id>/
    agent_input.md
    agent_report.json
    agent_output.md
    group_plan.json
    reuse_hints/<group-id>.md
    group_workers_manifest.json
    proving_merged_result.json
    groups/<group>/
      group_worker_input.md
      group_worker_report.json
      group_worker_output.md
      proof_reuse.md
```

The report-root `group_plan.json` exists only when there is no manual VC and the controller writes `{"groups": []}`; a missing manual is also a zero-manual-VC case. Ordinary plans remain in vc-checking round directories. An annotation-attempt directory may also contain controller-owned `clean-output-freshness/`. It is not another stage or formal role.

## 2. File ownership

| File | Owner | Content |
|---|---|---|
| `annotation-attemptN/agent_input.md` | Controller for attempt 1; later controller template plus five main-agent sections | Current task, original blocker paths, write boundary, skills, and exact commands |
| annotation `agent_report.json` | Sole annotation owner | Final status; one complete blocker when `blocked` |
| annotation `agent_output.md` | Annotation owner | Optional analysis, reflection, and repair notes; does not control acceptance |
| `annotation_history/.../before/` | Controller | Immutable pre-agent state of target C and persisted formal/generated roles; optional roles record present/missing |
| `annotation_history/.../after/` | Controller | Result and aggregate seal for that same role set after finalize precheck |
| `dune_dependency_snapshot.json` | Controller `dune-build`; Dune mode | Fixed Dune dependency graph for the exact goal-check, dependency source/artifact digests, Dune configuration, case identity, and `source_goal_version`; read-only afterward |
| `makefile_dependency_snapshot.json` and run-root `Makefile` | Controller `dune-build`; Makefile mode | Exact graph from batched `coqdep`, main-root base source/artifact digests, Make/Coq tool and configuration seals, and the sole `trusted-base` exact plan; later checks neither resolve dependencies nor run Make |
| vc-checking `agent_input.md` | Controller | Current version, raw targets, skills, write boundary, and optional reuse source |
| vc-checking `agent_report.json` | VC-checking owner | Final status |
| vc-checking `agent_output.md` | VC-checking owner | Decision summary: proof modes, common patterns, VC deltas, critical path, grouping, and blockers |
| `group_plan.json` | VC-checking owner; controller when there is no manual VC | Groups, routes, strategies, difficulty, and helper visibility; only empty groups when there is no manual VC |
| `reuse_hints/<group-id>.md` | VC-checking owner | Complete declaration reuse decisions only when the controller binds a source |
| `base_manifest.json` | Controller preparing | Current version plus candidate relative paths, presence, and seed digests for optional manual/library; an absent digest is `null` |
| `group_workers_manifest.json` | Controller preparing | Base/plan/snapshot seals, compact groups, optional reuse seals, and `dispatch_order` |
| `group_worker_input.md` | Controller | Group assignment, write boundary, commands, and appended repairs |
| `group_worker_report.json` | Group-worker | Final status |
| `group_worker_output.md` | Group-worker | Optional proof notes; when the owner delivers them, finalize writes their digest into `artifact_sha256`. An annotation-gap delivery must include them, as a nonempty UTF-8 regular file at the fixed path itemizing affected witnesses and evidence |
| `proof_reuse.md` | Controller copy | Accepted per-group reuse hint; read-only to the worker |
| `public_helper_lemma_lib.v` | Controller | Cross-round helper candidate pool; never imported |
| `public_helper_snapshot.txt` | Controller preparing | Immutable bytes of the pool at round start |
| `reuse_source_raw/` | Controller | Present raw goal/manual/library used for historical structure and semantic fingerprints; a stale source manifest must use this round's sealed bytes as its seed and cannot read an updated main root |
| `proving_merged_result.json` | Controller parent verify | Per-role candidate digests (an absent optional role is `null`), group count, added declarations, optional reuse statistics, or first failure; not created on the annotation-gap aggregation branch |

Store each fact once. A fact derivable from state, fixed directories, the plan, or file contents is not copied into another report or manifest.

When a group is blocked by an annotation gap, each `group_worker_report.json` still describes only its own single blocker and `failure_class` must be exactly `annotation-gap`. The controller classifies only by that field; `kind` may be `missing-annotation-premise` for a missing annotation premise, but neither `kind` nor natural language substitutes for the failure class. From the accepted plan and fixed reports for the round, the controller derives a round-wide aggregate in manifest order, preserving each group, witness, location, message, repair boundary, and original Markdown/JSON path; it neither overwrites those sources back into owner reports nor keeps only the first gap. The annotation-retry input cites original files instead of copying or rewriting them.

JSON does not store:

- complete rule text;
- parent transcript;
- a complete state copy;
- persisted copies of command argv, cwd, or flags;
- prefilled check results;
- another full manifest;
- optional notes;
- a complete list of cleanup paths.

## 3. Machine contracts

Every machine-read JSON is validated directly against its current field set.

### Owner report

A successful report is only:

```json
{
  "status": "completed"
}
```

For `blocked`, add one `blocker` with exactly:

- `failure_class`
- `kind`
- `location`
- `message`
- `repair_boundary`

The controller computes versions, digests, changed files, check results, command output, and receipts; an owner does not repeat them.

For a group, a valid `failure_class: annotation-gap` blocker is that group's terminal state for the round, not a repair action asking its owner to modify annotations in the original directory. Multiple groups may each have one such blocker; "one blocker per owner report" does not conflict with "controller aggregates every blocker in the round."

### Group annotation-gap aggregation

After every planned group reaches a terminal state, state stores flat records in `current_blockers` in manifest `order`. Each record contains only:

- owner fields: `failure_class`, `kind`, `location`, `message`, `repair_boundary`;
- controller source fields: `round`, `group_id`, `witnesses`, `markdown`, `json`.

`witnesses` comes from the complete assignment for that group in the accepted plan; the owner's `location` must name the exact affected witness. `markdown` and `json` point to that group's original reports and cannot be copied into a controller-owned owner report. Retry uses the proving round as the sole `previous_attempt` and expands every record into one annotation attempt's `feedback_sources` in plan/source order.

Finalize treats a delivered `group_worker_output.md` as a source artifact together with the JSON/manual/optional library: the file must be at the fixed report path, must not be a symlink or other special leaf, must be nonempty and UTF-8 decodable, and its digest is written to the finalized `artifact_sha256`. Subsequent group validation, `reuse_group_artifacts`, feedback aggregation, `annotation-summary-ready`, first or repeated annotation claims, repeated handoffs, and `already-retried` responses all revalidate the same path and digest. Any missing file, substitution, or content drift prevents further reuse or delivery.

Every group's report/Markdown/manual/library seal remains in the existing `reuse_group_artifacts.groups`; only groups that pass the `require_complete=False` structure, ownership, route, helper/import/safety checks enter `structurally_valid_groups`. Annotation-gap validation does not run exact/full group Rocq or require an unfinished proof. A previously accepted group is eligible for `direct` only when the generated-goal semantic fingerprint agrees; a structurally valid blocked group is at most `partial`. A helper's reuse mode must be `from scratch`; the controller mechanically rejects helper `direct` or `partial` during reuse-hint acceptance and later consumption rather than relying only on the owner's assertion.

### Group plan

The root contains only `groups`.

When there is no manual VC, including when the manual is absent, the only valid content is:

```json
{
  "groups": []
}
```

The controller writes this file without creating a vc-checking attempt. It is not an owner report. When any VC exists in a present manual, `groups` must exactly cover every top-level VC and an empty array cannot skip proof work. A group exists only when the manual has witnesses; when `formal_case_lib` is absent, the plan cannot declare helpers.

A group contains only:

- `id`
- `estimated_difficulty`
- `witnesses`
- optional `helpers`

Every witness has `name` and `proof_mode`. An `aggressive_pre_process` witness adds only `split_strategies`; an `LLM_pre_process` witness adds only one whole-top-level-VC `strategy`.

A helper contains only `name`, `strategy`, and `visibility`, where `visibility` is `local` or `public`.

Do not add `source_goal_version`, `verified`, `depends_on`, or another extension field.

### Merge result

A successful result stores only:

- `status`;
- `source_goal_version`;
- manual/library candidate digests, with `null` for an absent optional role;
- `group_count`, which is 0 when there is no manual VC;
- `added_declarations`;
- `proof_reuse` when applicable.

A failed result additionally stores `error_count`, `blocker_count`, and the first structured `failure`. Fixed paths are derivable from round and targets and are not repeated.

## 4. Claim and delivery

Actions remain compact in state. The controller hydrates them before output instead of persisting absolute argv in `controller_state.json`.

- A `main-owned-action` gains a complete `invocation`.
- A spawn/append action gains `role`, stable `owner`, absolute `cwd`, and complete `claim_invocation`.
- A claim response gains the fixed `handoff` and complete `finalize_invocation`.
- A running/returned delivery re-exports `finalize_invocation` through `step.waiting_for`.

Main never constructs a command from an action name, state fields, or a documentation example. See the [Controller CLI](../docs/controller-cli.md) for every public field and entry.

`target_files` and every persisted attempt, report, manifest, candidate, or reuse path are not independent authorization. Init creates `reports/<run>/controller_target_topology.json` exactly once with `O_EXCL`; it contains exactly `run_id`, `case`, and the nine-field `target_files` and is never rewritten. On state load, the controller re-derives the exact fixed topology from the current run id, authoritative case, fixed C path, round, and attempt id, and then requires the state, target anchor, and recomputed values to match. A same-content directory from another run or round, an absolute alias, symlink/reparse parent, or special directory entry cannot thereby become readable, writable, deletable, reusable, or validatable.

### `claim-attempt`

A spawn/append action already contains `role`, stable `owner`, absolute `cwd`, and a complete `claim_invocation`. Main executes that invocation directly; it does not choose another owner or reconstruct arguments. In one state commit, the controller:

1. confirms the action remains valid;
2. binds the owner;
3. records start time;
4. updates timing;
5. returns the original claim message, fixed `handoff`, and complete `finalize_invocation`.

State stores only action id/kind, owner, and times. A repeated message is rerendered from the current attempt/manifest rather than copied into state.

Before a first claim, repeated claim by the same owner, or rerendered handoff for an annotation retry produced by group aggregation, the controller revalidates the fixed path and sealed digest of every original Markdown/JSON file in `feedback_sources`. If revalidation fails, it does not return a handoff that can be sent. This requirement also applies when reclaiming an already created retry, not only at `annotation-summary-ready`.

The same owner can repeat the claim idempotently. A different owner is rejected.

Default controller owners are:

```text
annotation/<run-id>
vc-checking/<attempt-id>
group-worker/<round-id>/<group-id>
```

An annotation retry reuses `annotation_session.owner`, a group repair reuses that group's bound owner, and an already claimed owner from an old run is preserved.

Main sends only `handoff.prompt` when spawning or appending:

```text
Role: <role>
Owner: <owner>
CWD: <cwd>
Claim message (verbatim):
<claim message exactly as returned>
```

Main does not summarize, translate, or interpret the claim message, and it does not read a subagent skill to write replacement rules. The owner reads its role skill and the attempt handoff named by the claim message.

### `finalize-delivery`

Run it only after the agent has finished and its report is complete. The controller:

- validates owner;
- validates that files remain in fixed paths;
- seals the report and applicable formal bytes;
- ends owner work timing;
- directly performs phase validation or group validation.

There is no second public command for checking an owner delivery on the normal path.

Main uses the `finalize_invocation` returned by the claim response. If that context is lost, run `step` again; a running/returned delivery includes the same complete invocation in `waiting_for`. Execute it only after the owner has stopped writing.

For annotation report/diff precheck failure, return `report-repair-required` and leave delivery `running`; the same owner repairs it and reruns the original command.

Before a first group preflight returns `report-repair-required` for a report or annotation-gap Markdown contract, the controller freezes the copied manual and applicable library in temporary `repair_formal_sha256`. The same owner may then repair only the JSON report/Markdown; every subsequent finalize first revalidates that seal, and formal drift terminates as `invalid-report` instead of resealing the drifted content. Successful finalize clears `repair_formal_sha256` so the temporary repair seal does not enter the terminal state.

If the report contract is valid and `blocker.failure_class` is exactly `annotation-gap`, the controller seals that group's report, copied manual, and applicable library; checks structure, ownership, route, helper/import/safety with `require_complete=False` without running exact/full group Rocq; and records it as a blocked terminal state. It does not publish `append-group-worker` asking the owner to modify annotations outside its boundary. That terminal state no longer occupies a concurrency slot, and the next `step` continues publishing unclaimed groups from `dispatch_order`.

Repeating finalize with the same owner and unchanged files is idempotent. One controller command performs group validation; the system publishes no in-flight PID marker and does not support concurrent calls of the same action. After a long Rocq check, the command reloads state, revalidates the same attempt and every seal, then commits the incremental result.

## 5. Persistent annotation session

The run's sole `annotation_session` stores the first annotation target. The first action is spawn; all later actions are append.

A later annotation attempt's `agent_input.md` contains controller-fixed sections and five `MAIN_AGENT` sections. The main agent may fill only:

1. `Main-agent blocker conclusion`
2. `Evidence and causal analysis`
3. `Reflection on the previous annotation attempt`
4. `Required annotation repair`
5. `Scope decision`

The content identifies the concrete witness or check, causal chain, prior wrong assumption, material to preserve,
required edit location, and completion standard. It must address whole-design reconsideration only when the action has
`consider_broader_refactor: true`. That value comes from at least two machine-classified annotation/specification/
dependency-gap causal retries, not the `annotation_iteration` directory ordinal. Infrastructure, tool/report, version
authorization, context compaction, and other non-annotation causes cannot turn it on.

`annotation-summary-ready` checks:

- every template marker has been replaced;
- all five sections are concrete;
- every original Markdown/JSON source remains at its fixed path and its bytes/digest agree with the `feedback_sources` seal;
- skill paths, commands, and repeated-repair guidance remain intact;
- current version and fixed facts are unchanged;
- the input digest is sealed.

Changing the input after sealing blocks append delivery.

## 6. Retry sources

Annotation `--previous-attempt` may name:

- a previous annotation attempt;
- a vc-checking attempt;
- one `<vc-proving-round>:<group-id>` blocker;
- an aggregation from a vc-proving round containing multiple annotation-gap blocked groups.

The last source binds all annotation gaps from the same proving round. The controller publishes exactly one `retry-round --phase annotation --reason group-worker-annotation-gaps --previous-attempt <vc-proving-round>` and places each group's original Markdown and JSON paths into the same attempt's `feedback_sources` in plan/source order. Old files remain read-only and are neither copied over nor replaced.

When creating the retry attempt, the controller binds that one complete proving-round source with `retry_previous_attempt`; the invocation's phase, reason, and source must agree field by field with the current action. If the attempt already exists, the same invocation returns only `already-retried` and reuses the original attempt after revalidating every feedback source; a different parameter or drifting source seal prevents an idempotent return.

`report-repair-required`, a repairable group proof, or a repairable group report is not a new round; continue the same delivery. Only a final report, explicit cancellation, version mismatch, main-owned check failure, or `compact-error` enters the corresponding retry rule.

## 7. State, events, and concurrency

`controller_state.json` has monotonically increasing `generation`. Ordinary mutation within one controller command performs this complete sequence:

```text
read → validate → modify → generation CAS write
```

An old snapshot cannot overwrite new state. An event is appended to `run_logs.json` only after the state commit succeeds. The event log is append-only JSONL and never repeats a complete state.

Long Rocq work for group development, exact, and validation does not write back the full pre-check snapshot. Validation:

1. seals and prechecks;
2. runs Rocq;
3. reloads fresh state;
4. revalidates the same attempt and every seal;
5. commits an incremental result.

Group owners may work concurrently, but the main agent executes controller commands serially in action order, and the controller cannot overwrite later state with the stale snapshot from before a long check.

Group scheduling treats both `accepted` and valid annotation-gap `blocked` as terminal states for the round, but does not place the latter in the early-stop set. As long as a group in the manifest/accepted plan has not reached a terminal state and a slot under `max_parallel_group_workers` is available, `step` continues to hydrate the next unclaimed action; an existing annotation blocker cannot hide ready groups behind `waiting_for`. Only after every planned group reaches a terminal state does the controller inspect the round-wide aggregate:

- Nonempty aggregate: publish one annotation retry, retain the sealed bytes of accepted and structurally valid blocked groups, and create no merge/parent-verify action.
- Empty aggregate and every group accepted: publish `vc-proving-verify`.

Report repair, proof repair, retry exhaustion, and termination rules for other blockers remain unchanged; the annotation-aggregation path cannot rewrite them as annotation gaps.

The controller supports only one run command at a time in action order. It creates no synchronization file for state, formal targets, workspaces, or dependencies, stores no PID-occupancy record, and uses no operating-system synchronization primitive. State uses generation compare-and-swap and atomic replacement; reports, formal targets, and builds use fixed paths, digest seals, and atomic replacement. Multiple runs modifying the same main root concurrently are outside this contract.

## 8. Timing summary

`timing_summary.json` supports whole-flow analysis rather than global counting of every controller command. When there is no manual VC, it has no vc-checking or group-work timing item; preparing, parent verify, and finalization are still recorded.

- `run`: wall time from creation to `done`.
- `annotation_attempts`: annotation work, symexec, the selected-backend `formal_case_lib` check when present, clean-output freshness, annotation-checking, controller validation, controller acceptance check, and the post-acceptance `dune-build` action.
- `rounds`: vc-checking `witness-analysis`; vc-proving group-work concurrency interval, development/exact/group validation, and parent verify.
- `finalization`: accepted proving through final-check completion.

It records no per-witness time and no estimated internal agent time. Each item retains only status, creation/completion times, total seconds, and a small set of stages.

## 9. Performance telemetry

Selected dependency preparation and every Coq check expose independently verifiable measurements:

- `dune_preparation.base_artifact_count`, `current_source_count`, `rebuilt_count`, `returncode`, and all four digests;
- `dune_preparation.elapsed_seconds`;
- a Makefile receipt additionally exposes `dependency_metrics` (breadth batches/processes/nodes/sources), `current_cleanup`, and `make_seconds`;
- `coq_check.current_compile_seconds`;
- vc-checking `agent_output_metrics` for bytes, lines, common-pattern count, and VC-delta count.

The `dune-build` action runs once per accepted annotation. Every later Coq check must report `dependency_mode: dune-snapshot` or `makefile-snapshot` according to the selected mode and must start no new Dune, Make, or dependency-resolution child process. Judge performance primarily from the single selected-preparation wall time, the bounded batched-`coqdep` process count in Makefile mode, actual rebuild count, and current-local compile time. State field `dune_preparation` retains its name only for compatibility and does not determine the backend.
