# Controller Public Interface

This document explains every public entry to main agents and controller maintainers. During a normal run, main executes the invocation returned by an action. It does not reconstruct a command from this document or consult `--help` at runtime.

## 1. Common invocation contract

The only public program entry is:

```text
.agents/scripts/verification-orchestrator/controller.py
```

A human syncs and starts the first command from the repository root:

```text
uv sync --frozen --python 3.12
uv run --frozen --python 3.12 python .agents/scripts/verification-orchestrator/controller.py ...
```

The public entry rejects every interpreter other than Python 3.12 before parsing or performing business writes. After that gate, each action keeps the validated absolute `sys.executable` from the uv environment as `argv[0]`. An agent executes the array directly; it neither replaces Python nor nests uv around the returned command.

Every executable controller command has this shape:

```json
{
  "argv": [
    "/workspace/qcp-binary-democases/.venv/bin/python",
    "/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py",
    "--main-root",
    "/workspace/qcp-binary-democases",
    "step",
    "--run",
    "demo-20260729000536"
  ],
  "cwd": "/workspace/qcp-binary-democases"
}
```

Rules:

- `argv` is an array of strings passed directly to a terminal tool, not a shell command.
- `cwd` is absolute and is the required working directory.
- `argv[0]` is the current uv-environment interpreter already validated as Python 3.12.
- Controller path, root, run, round, attempt, owner, and file arguments are fully expanded.
- Do not replace Python, change arguments, use `sh -c`, pipe output, background the command, or wrap it.
- Human-readable action fields explain the operation. `argv` is the execution authority.

A `main-owned-action` carries `invocation`. A spawn/append action carries `claim_invocation`. A successful claim returns `handoff.prompt` and `finalize_invocation`. Main saves the latter and executes it only after the owner has stopped writing. If context is lost, the next `step.waiting_for` re-exports it.

The handoff has exactly four parts:

```text
Role: <controller role>
Owner: <controller owner>
CWD: <controller cwd>
Claim message (verbatim):
<controller claim message exactly as returned>
```

Main does not summarize, translate, or supplement it. The owner reads its own role skill and attempt handoff.

Before any public entry first reads, writes, deletes, reuses, or validates a phase artifact, it re-derives the fixed topology from the current run/report roots, round, attempt id, and exact target mapping, then requires every persisted directory, report, input, output, manifest, candidate, and reuse path to match field by field. A persisted path cannot make another run, the wrong round, an absolute alias, or a symlink/reparse tree a valid source.

Examples below use:

```text
Python: /workspace/qcp-binary-democases/.venv/bin/python
Root: /workspace/qcp-binary-democases
Run: demo-20260729000536
```

They are documentation examples only. Real execution always uses the current action.

## 2. All 18 public commands

### 1. `init-run`

**Caller and timing:** Main, once at the start of a case. The target C file must already exist under main root.

**Arguments:**

| Argument | Required | Meaning |
|---|---:|---|
| `--case` | yes | Run-id stem and sole authoritative Rocq/generated formal stem; must be a valid Rocq identifier |
| `--target-c-file` | yes | Target C under main-root `QCP_examples/**`, relative or absolute; its stem/directory may differ from the case |
| `--timestamp` | no | Fixed run timestamp; generated when omitted |
| `--max-compact-attempts` | no | Positive compact-retry limit, default 3 |
| `--max-witnesses-per-group` | no | Positive hard group bound, default 12 |
| `--max-parallel-group-workers` | no | Positive group concurrency, default 5 |
| `--problem-statement` | no | Problem text |
| `--problem-statement-file` | no | Problem file |
| `--target-function` | no | Target function |
| `--expected-behavior` | no | Expected behavior |
| `--input-output-contract` | no | Input/output contract |
| `--spec-hint` | no, repeatable | Specification hint |
| `--preferred-hidden-property` | no, repeatable | Hidden property to preserve |
| `--forbidden-pattern` | no, repeatable | Forbidden implementation pattern |
| `--reference-case-hint` | no, repeatable | Reference case |

**Result and success:** Exit 0 and JSON containing `run_id`, `run_root`, `report_root`, and `controller_state`. The controller mirrors the target parent beneath `Rocq/examples/<collection>/**`, names generated/formal modules from `--case`, and persists `target_files` as exactly nine fields containing only the C/formal paths, case, and active theory. Multiple programs may coexist in one directory without ambiguity. Run and report roots are allocated as a pair: either same-named leftover directory prevents a new run from taking over. Init also creates `reports/<run>/controller_target_topology.json` exactly once with `O_EXCL`; it contains exactly `run_id`, `case`, and `target_files` and is never rewritten. On every state load, the controller recomputes `target_files` from current run identity, the fixed C path, and the authoritative case and requires the state, anchor, and recomputed fields to match exactly. Include/SLP/profile resolution is recomputed from the sealed C path for each canonical symexec, not persisted as an extra search mapping. Call `step` next.

**Repeat and failure:** This is not a recovery command. An invalid Rocq case identifier, invalid bound, missing/escaping target, or collision on either allocated run/report directory stops initialization. Correct the input and create an explicit new run. Never hand-create state, recompute formal names from the C stem, or reuse another case's run root. Every later action consumes persisted `target_files`.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","init-run","--case","demo","--target-c-file","QCP_examples/LLM_bench/Algorithms/demo/demo.c","--timestamp","20260729000536","--max-compact-attempts","3","--max-witnesses-per-group","12","--max-parallel-group-workers","5"],"cwd":"/workspace/qcp-binary-democases"}
```

### 2. `step`

**Caller and timing:** Main after initialization, after every completed action, and after waiting or context recovery.

**Arguments:** Required `--run`.

**Operation and result:** Advances controller-only transitions from authoritative state and returns `phase`, hydrated `next_actions`, hydrated `waiting_for`, and optional blockers. Main actions include `invocation`; deliveries include role/owner/cwd and `claim_invocation`; running/returned deliveries include `finalize_invocation`. For a nonempty group plan, even after a group reaches a terminal state for the round with `blocker.failure_class: annotation-gap`, the scheduler does not place it in the early-stop set. Whenever a group has not reached a terminal state and a slot under `max_parallel_group_workers` is available, `step` continues hydrating an unclaimed group action; it cannot merely wait for deliveries that were already running.

**Repeat and failure:** Exit 0 means the step completed, not that the run passed. Repeating on unchanged state must not create duplicate attempts. Empty `next_actions` requires a wait reason, blocker, or `phase: done`. Never infer the next phase or construct a command from state.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","step","--run","demo-20260729000536"],"cwd":"/workspace/qcp-binary-democases"}
```

### 3. `claim-attempt`

**Caller and timing:** Main before spawning or appending an agent, using the action's exact `claim_invocation`.

**Arguments:** Required `--run`, `--next-action`, and `--owner`. The last two come directly from the action.

**Result and success:** `status` is `claimed` or idempotent `already-claimed`; JSON also includes attempt, owner, original `message`, fixed `handoff`, and complete `finalize_invocation`. Main sends only `handoff.prompt`. Before a first claim, repeated claim, or rerendered handoff for an annotation retry produced by group aggregation, the controller revalidates every `feedback_sources` fixed path and sealed digest; if a source drifts, it does not return the old handoff.

**Repeat and failure:** The same owner is idempotent; a different owner, stale action, invalid manifest, or non-delivery action is refused. Annotation retry reuses the annotation owner; group repair reuses the group owner. Never change owner, edit the prompt, or spawn before claiming.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","claim-attempt","--run","demo-20260729000536","--next-action","spawn-demo-vc-checking-r1-attempt-1","--owner","vc-checking/demo-vc-checking-r1-attempt-1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 4. `finalize-delivery`

**Caller and timing:** Main after the owner has stopped writing, using the claim response or `step.waiting_for` invocation.

**Arguments:** Required `--run`, `--attempt`, and `--owner`.

**Operation and result:** Validates owner, seals delivery, and directly performs annotation/vc-checking phase validation or group validation. Results may include `ready-for-main-check`, `returned`, `report-repair-required`, `invalid-report`, group-validation output, or an idempotent result. A valid group blocker with `failure_class: annotation-gap` additionally requires the fixed-path `group_worker_output.md` to be a nonempty UTF-8 regular file; its digest enters the finalized `artifact_sha256` and is sealed with the copied formal bytes. The controller checks structure/ownership/route/helper/import/safety with `require_complete=False`, does not run exact/full group Rocq, and makes it a blocked terminal state and reuse source only when structurally valid. It neither asks the owner to modify annotations outside its boundary nor stops sibling scheduling.

**Success, repeat, and failure:** Repeated finalize by the same owner over the same seal is idempotent. One controller command completes group validation; it publishes no in-flight execution and does not support concurrent calls of the same action. Before the first group preflight returns `report-repair-required`, `repair_formal_sha256` freezes the manual/optional library. The same owner may repair only the report/Markdown; formal drift returns `invalid-report`, and successful finalize clears the temporary seal. `failure_class: annotation-gap` is not in-place proof repair; the controller waits until every planned group reaches a terminal state and then handles the aggregate once. Other blockers continue under their existing repair, exhaustion, or terminal actions. Never change owner, continue writing after finalize, or mark acceptance manually.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","finalize-delivery","--run","demo-20260729000536","--attempt","demo-vc-proving-r1:group1","--owner","group-worker/demo-vc-proving-r1/group1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 5. `retry-round`

**Caller and timing:** A main-owned action after the controller explicitly requests annotation or vc-checking retry.

**Arguments:** Required `--run`, `--phase` (`annotation` or `vc-checking`), `--reason`, and `--previous-attempt`, all from the action.

**Operation and result:** Creates the authorized retry and publishes either an annotation-summary action or a new vc-checking delivery. For a blocked vc-checking report, a fixed `failure_class` mapping selects the phase: annotation/specification/dependency/source-version classes return to annotation, while plan/report/infrastructure classes stay in vc-checking; blocker prose is never inspected. When multiple groups report annotation gaps in one round, the controller publishes only once after every group is accepted or structurally valid annotation-gap blocked: `--phase annotation --reason group-worker-annotation-gaps --previous-attempt <vc-proving-round>`. The attempt's `retry_previous_attempt` binds the entire proving round, and phase, reason, and source must agree field by field with the current action. Retry expands every original group Markdown/JSON file into the same input's `feedback_sources` in plan/source order. Annotation attempts also retain a causal retry count; only machine-classified annotation/specification/dependency gaps increase it, while directory ordinals and infrastructure/tool/report/compact causes do not.

**Repeat and failure:** When an identical invocation finds that the attempt already exists, it first revalidates the feedback sources, then returns only `already-retried` and reuses the original attempt; it cannot create a second attempt. An old action, phase/reason/source mismatch, version drift, or source-seal drift is rejected or recorded as a blocker. Never invent parameters, turn same-delivery report repair into a retry, or skip an original blocker.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","retry-round","--run","demo-20260729000536","--phase","annotation","--reason","vc-proving-parent-failed","--previous-attempt","demo-vc-proving-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

For a multi-group annotation-gap aggregate, the same entry's action has this form:

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","retry-round","--run","demo-20260729000536","--phase","annotation","--reason","group-worker-annotation-gaps","--previous-attempt","demo-vc-proving-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 6. `annotation-summary-ready`

**Caller and timing:** A main-owned action after main fills the five annotation-retry blocker-summary sections.

**Arguments:** Required `--run` and `--attempt`.

**Operation and result:** Validates markers, every original blocker path and sealed digest, fixed facts, and input digest; seals the input and publishes `append-annotation-agent`. For an aggregated group source, the five-part summary must cover every listed gap; a missing or drifting feedback Markdown/JSON file rejects summary-ready.

**Repeat and failure:** A sealed input cannot be edited. Incomplete sections, remaining markers, missing sources, or changed fixed text fail. Repair the summary and rerun. Main summarizes only controller-designated current blockers and does not read a subagent skill.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","annotation-summary-ready","--run","demo-20260729000536","--attempt","demo-annotation-r2-attempt-1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 7. `timing-stage`

**Caller and timing:** Annotation owner at the start and finish of manual annotation-checking, exactly as rendered in the handoff.

**Arguments:** Required `--run`, `--round`, `--stage`, and `--event`. `--stage` is only `annotation-checking`; `--event` is `start` or `finish`.

**Operation and result:** Records timing JSON only; it does not accept annotation.

**Repeat and failure:** Wrong phase, missing current attempt, or invalid event order fails. Never use it as a check or invent another stage.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","timing-stage","--run","demo-20260729000536","--round","demo-annotation-r1","--stage","annotation-checking","--event","start"],"cwd":"/workspace/qcp-binary-democases"}
```

### 8. `annotation-check-round`

**Caller and timing:** A main-owned action after the annotation delivery and controller phase validation are sealed.

**Arguments:** Required `--run` and `--round`.

**Operation and result:** Reruns canonical main-root symexec using persisted `target_files` and parses a present raw manual. When `formal_case_lib` is present, it first prepares that exact `.vo` target with the selected backend and then performs local `coqc`. It next performs a clean replay, compares generated-role presence/digest stability, and records source versions. Candidate manual/library paths may be missing; no library seed or placeholder is created. Acceptance publishes `dune-build`.

**Repeat and failure:** Rechecking an unchanged accepted result is stable. Drift routes to retry. Owner self-check is not a substitute. Never enter vc-checking directly or edit accepted state.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","annotation-check-round","--run","demo-20260729000536","--round","demo-annotation-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 9. `vc-checking-check-round`

**Caller and timing:** A main-owned action after the vc-checking delivery is sealed.

**Arguments:** Required `--run` and `--round`; optional `--group-plan`, fully supplied by the action when needed.

**Operation and result:** Strictly validates version, exact witness coverage, proof modes, aggressive split order, strategies, difficulty, helpers, group bound, and conditional reuse/debug evidence. The helper reuse-mode machine gate accepts only `from scratch` and rejects `direct` or `partial`. Acceptance returns plan path, group count, and `agent_output_metrics`.

**Repeat and failure:** A sealed plan is stable to recheck. An invalid plan follows the controller retry. Shorter Markdown never relaxes `group_plan.json`, and main may not point at another plan.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","vc-checking-check-round","--run","demo-20260729000536","--round","demo-vc-checking-r1","--group-plan","/workspace/qcp-binary-democases/reports/demo-20260729000536/rounds/demo-vc-checking-r1/group_plan.json"],"cwd":"/workspace/qcp-binary-democases"}
```

### 10. `dune-build`

**Caller and timing:** A main-owned action after annotation acceptance and before vc-checking/preparing.

**Arguments:** Required `--run`.

**Operation and result:** Constructs the exact goal-check `.vo` from the persisted arbitrary-depth target path. When main-root `_build` is a directory, it runs the unchanged exact Dune build and writes `dune_dependency_snapshot.json`. Otherwise it performs lock-free Makefile preparation: breadth-batched `coqdep` resolves only the exact closure, a run-root `Makefile` exposes only the `trusted-base` goal and rejects aggregate targets, and `makefile_dependency_snapshot.json` is written. Historical state field `dune_preparation` stores `build_mode` for Makefile mode, snapshot path/digest, dependency/source/artifact/configuration digests, current/dependency counts, rebuild count, and elapsed time. Makefile mode additionally reports dependency batch/process/node metrics, current cleanup, and Make time.

**Success:** `status: passed`; snapshot and receipt digests agree; every dependency source/artifact and the selected configuration revalidate; `source_goal_version` equals the accepted annotation; and the exact target agrees with the current case identity. Makefile mode also requires matching run-Makefile digest, tool paths, and batched-resolution metrics.

**Repeat and failure:** The same accepted input may rerun the selected exact preparation and overwrite the same snapshot/Makefile paths; an annotation retry produces a new version and invalidates the old receipt. A side-effect-free interval of one action reuses the snapshot/summary returned by one full validation. Validation runs again after a build/Rocq step that can modify validated input, a state reload, or an independent post-acceptance boundary. No snapshot history, dependency fragment, or additional freshness database is retained. Repair only the first selected-build/Rocq/source/configuration error and rerun the same action. Never widen to a whole-workspace Dune target or repository Make aggregate target or forge a snapshot. Do not add or remove `_build` to switch modes during a run.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","dune-build","--run","demo-20260729000536"],"cwd":"/workspace/qcp-binary-democases"}
```

### 11. `vc-proving-preparing`

**Caller and timing:** A main-owned action after a VC plan, including a controller-owned empty plan, is accepted.

**Arguments:** Required `--run` and `--round`.

**Operation and result:** Revalidates plan/source/the accepted selected dependency snapshot and creates the fixed base manifest, applicable group copies, public snapshot, optional reuse source, compact group manifest, and handoffs. The manifest for a stale proving source is parsed using the source round's sealed `reuse_source_raw` seed explicitly and cannot read main root after annotation updates. A missing manual is equivalent to zero witnesses; groups exist only when a present manual has witnesses. When `formal_case_lib` is absent, no `group_worker_lib` is created and no helper may be declared. An absent optional role has a `null` digest in base/merged records. Returns `groups-ready`, manifest path, and hydrated worker actions; an empty plan publishes verify directly.

**Repeat and failure:** An unchanged prepared round never creates a second workspace. Source/plan/dependency-snapshot drift stops. Never hand-create groups, change assignments, invoke Dune in a preparing-local directory, or compile dependency source there.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","vc-proving-preparing","--run","demo-20260729000536","--round","demo-vc-proving-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 12. `vc-proving-verify`

**Caller and timing:** A main-owned action for an empty plan, or after every group is accepted in a round with no annotation gap.

**Arguments:** Required `--run` and `--round`.

**Operation and result:** Revalidates seals, mechanically merges the manual/library roles that are actually present in accepted-plan order, runs one parent goal-check/full Coq check, and writes `proving_merged_result.json`. If both are absent, the check remains mandatory and no candidate file is manufactured. Success publishes `final-apply`; failure publishes the proper retry. If even one group in the round is a structurally valid annotation-gap blocked group, this entry is neither published nor invoked: the controller creates one aggregated annotation retry and performs no mechanical merge. Every group seal remains in `reuse_group_artifacts.groups`; an accepted proof may be direct when its semantic fingerprint agrees, a structurally valid blocked proof is at most partial, and its helpers are reproved from scratch.

**Repeat and failure:** State and the result seal identify a completed candidate, which is not run again. A failed parent candidate must go through the returned retry, not be rerun directly. Main never merges files by hand.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","vc-proving-verify","--run","demo-20260729000536","--round","demo-vc-proving-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 13. `symexec`

**Caller and timing:** Annotation owner in the current claimed/running annotation round, using the handoff command.

**Arguments:** Required `--run` and `--round`.

**Operation and result:** Revalidates the before seal, then transactionally refreshes generated roles using init's exact persisted `target_files`, dynamic include/SLP/active theory, and quoted-include strategy roots. It restores pre-call presence and exact bytes on failure and never recomputes from the C stem or fixed `QCP_demos_LLM` configuration.

**Success and failure:** Exit 0 plus JSON `status: passed`. Empty output, initial yield, or an outer `Script completed` is not success. Repair authorized annotation/spec content and rerun exactly. Never run raw symexec, edit generated files, change paths/flags, or delete a protected proved manual.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","symexec","--run","demo-20260729000536","--round","demo-annotation-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 14. `coq-check`

**Caller and timing:** Annotation or group owner, only for a target rendered by its handoff.

**Arguments:**

| Argument | Required | Values |
|---|---:|---|
| `--run` | yes | Current run |
| `--round` | yes | Current claimed round |
| `--target-kind` | yes | `formal-case-lib` (only when present), `group-development`, or `group-check` |
| `--group` | conditional | Required by both group target kinds |

**Operation and result:** Uses one local plan to stage and compile the current closure and directly reads dependency `.vo` files named by the accepted selected snapshot (Dune `_build/default` or the Makefile main-root base). Formal-case-lib mode first runs the selected exact library preparation; proving/group modes only revalidate the existing snapshot and never run Dune, Make, or `coqdep`. Returns Rocq status, the mode-specific `dependency_mode`, reuse counts, and `current_compile_seconds`.

**Repeat and failure:** Success requires exit 0 and `status: passed`. Development/exact are early feedback; final group acceptance still occurs in finalize validation. Modify only owner-authorized formal files and rerun exactly. If a group import is outside the snapshot, return to annotation to form a new accepted version; do not extend dependencies in place. Never invoke raw `coqc`, choose another build/group, or copy/compile dependency source.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","coq-check","--run","demo-20260729000536","--round","demo-vc-proving-r1","--target-kind","group-check","--group","group1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 15. `coq-debug`

**Caller and timing:** VC-checking or group owner after writing the one handoff-authorized debug script.

**Arguments:** Required `--run` and `--round`; group context uses optional `--group`.

**Operation and result:** Revalidates script, targets, manifest, version, the accepted selected dependency snapshot, and the build seal, then runs controller-owned Rocq debug. The controller normalizes the sole authorized script to its fixed absolute path inside the build; that same path is used for regular-file/digest validation and as the `coqtop -l` argument, and its digest is revalidated after the child exits. The result includes the authorized path, actual load argument, resolved path, script digest, target coverage, build receipt, and current-compilation timing. A path mismatch fails before launch, and script drift during execution cannot be accepted. Debug reruns neither Dune, Make, nor `coqdep` and never resolves dependencies again.

**Repeat and failure:** The same script may rerun; edits stay within its designated path. Never add targets, `Load`, load-path commands, scan unbound history, or treat `Show.` output as proof acceptance.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","coq-debug","--run","demo-20260729000536","--round","demo-vc-checking-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 16. `final-apply`

**Caller and timing:** A main-owned action after parent verification accepts the candidate.

**Arguments:** Required `--run`.

**Operation and result:** Revalidates annotation, manifest, existing groups, parent result, and candidate, then transactionally backs up and atomically writes the manual and/or `formal_case_lib` that are actually present. When both optional candidates are absent, a zero-target transaction is valid but still completes source revalidation and the phase transition. Fixed paths, backup digests, and atomic replacement constrain each exact target. Success enters final-check.

**Repeat and failure:** The same transaction only continues or rolls back and never replaces its original backup. Every recovery or rollback requires records that match the exact zero-, one-, or two-candidate set, accepted original seals, fixed targets, and `reports/<run>/final-check/backup/<transaction-id>/`; a zero-target transaction has only empty records. Any additional/missing record or injected path/digest stops without rollback. Source drift stops before root modification; partial application recovers from the same backup. Never copy from a group/stale report or create another backup.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","final-apply","--run","demo-20260729000536"],"cwd":"/workspace/qcp-binary-democases"}
```

### 17. `final-check`

**Caller and timing:** A main-owned action after successful `final-apply`.

**Arguments:** Required `--run`.

**Operation and result:** Runs independent symexec freshness, main-root full Rocq, checks for a present manual/applicable three-library chain/forbidden rules, and by-product cleanup. A present `formal_case_lib` is audited as an independent import root even when goal-check does not import it; it may not reach any of this run's four exact generated identities, including a currently missing leaf, and every other project import must belong to the accepted dependency snapshot. This audit reads source and snapshot only and does not run Dune, Make, `coqdep`, `coqc`, or compilation. With no manual, freshness/full Coq remains mandatory and goal-check importing the missing manual must fail. Cleanup covers like-named by-products for every exact current module identity even when the optional source is absent; a broken symlink or non-regular leaf cannot pass as missing. Full success writes `phase: done`.

**Repeat and failure:** State and seals identify an already completed final result. A failure attempts rollback. After successful rollback, main must execute a new `final-apply` action before final-check again. Never clean by hand, invoke Dune, or compile dependency source inside final.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","final-check","--run","demo-20260729000536"],"cwd":"/workspace/qcp-binary-democases"}
```

### 18. `validate-artifact`

**Caller and timing:** Maintainers or diagnostics; validates one public JSON artifact without advancing a run.

**Arguments:** Required `--kind` and `--path`. `--kind` is one of `agent-report`, `group-worker-report`, `manifest`, `group-plan`, `merge-result`, `controller-state`, or `run-log`. This command has no `--run`.

**Result and success:** JSON `status: valid|invalid`, `errors`, and `path`; valid exits 0 and invalid exits 1.

**Repeat and failure:** Pure validation is repeatable. It never substitutes for `finalize-delivery`, a phase check, parent verification, or final-check, and a valid artifact is not automatically written into state.

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","validate-artifact","--kind","group-plan","--path","/workspace/qcp-binary-democases/reports/demo-20260729000536/rounds/demo-vc-checking-r1/group_plan.json"],"cwd":"/workspace/qcp-binary-democases"}
```

## 3. Maintenance and drift prevention

The `controller.py` parser is the code authority for command names, required/optional parameters, choices, and defaults. External regression can export `public_command_schema()` and must verify:

- all 18 parser subcommands appear here;
- required/optional flags and choices agree;
- the builder generates a complete invocation for every main-owned action;
- delivery actions, claim responses, and waiting deliveries generate complete claim/finalize invocations;
- adding or removing a subcommand without updating documentation fails regression.

Normal main execution still does not call the schema or depend on `--help`. A parser change must update the parser, unified invocation builder, this document, and external regression in the same change.
