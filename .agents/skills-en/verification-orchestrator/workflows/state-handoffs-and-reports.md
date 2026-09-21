# State, Handoffs, and Reports

## One set of task facts

`reports/<run>/controller_state.json` uses **schema 4**. Fixed inputs include roots, `target_files`,
library policy, and problem/specification constraints; `attempts` holds task facts. `current` contains
only three current-task pointers: `annotation`, `vc-checking`, and `vc-proving`. Group-owner task
records live in the corresponding proving attempt's `groups`.

Owner tasks share one lifecycle:

```text
prepared → claim → running → finalize begins → returned → accepted / blocked
                                                      ↘ same-owner repair → prepared
```

`returned` means the owner has stopped writing; acceptance may still be incomplete. `finalize-delivery`
can continue from this state. Repairs retain the attempt, owner, and file directory, update feedback
and `repair_index`, and lead to another append-action claim. A phase attempt id is also its CLI round id. A group delivery id is
`<round>:<group_id>`.

The controller derives `next_actions` and `waiting_for` from facts on each call. They appear only in
responses and are not persisted. There is no second `rounds`, `accepted_rounds`, or session state.
`pending_retry` records only a confirmed retry destination, reason, and source; group annotation-gap
batch handling derives directly from current groups' terminal states.

Main submits business state sequentially. Group tool checks do not change that state for timing.
Never hand-edit state to fabricate acceptance. Schema 3 and older runs are not migrated: recover with
the code that created them, or initialize a new run from current formal files.

## Paths and files

```text
verification_runs/<run>/
  dependency_plan.json
  annotation_history/annotation-attemptN/{before,after}/...
  <case>-vc-proving-rN/
    groups/group_NN__<id>/<case>_proof_manual.v
    groups/group_NN__<id>/<case>_lib.v       # when the library is active
    proving_merged/...                    # current candidate
  _coq_builds/...
reports/<run>/
  controller_state.json
  controller_control.json
  run_logs.json                           # JSON Lines
  timing_summary.json
  annotation-attempts/annotation-attemptN/
    agent_input.md / agent_report.json / agent_output.md
    annotation_plan.json
  rounds/<case>-vc-checking-rN/
    agent_input.md / agent_report.json / agent_output.md
    group_plan.json
    <case>_proof_manual.v                  # VC debug copy
  rounds/<case>-vc-proving-rN/
    groups/group_NN__<id>/
      group_worker_input.md / group_worker_report.json / group_worker_output.md
      tool_calls.jsonl
      proof_reuse.md                      # optional
  final-check/backup/...
```

With no manual VCs, the empty `group_plan.json` lives at the run's report root. Group assignments,
directories, and candidates derive from the current plan/manual/library plus round identity; do not
write separate base manifests, worker manifests, or merged-result mirrors. `final_candidate` stores
only the round; consumers reread candidate files.

Annotation before/after history preserves original bytes as read-only references for failed-VC
explanations and model-selected reuse. A `failed_vcs` entry contains `source_attempt`, `name`, `parent`,
`annotation_location`, `manual`, and `message`. Group ids use ASCII letters, digits, and underscores;
new helpers use the exact `__<group_id>` suffix.

## Claim and owner handoff

Main executes the owner action's `claim_invocation`, retains the owner-to-agent-target mapping, and
sends the returned `handoff.prompt` verbatim. Spawn on the first claim; append actions contact the
same target. The annotation owner remains the same throughout a run; same-attempt repairs of other
tasks also retain their owners.

Owners read the handoff's role skill, current assignment, write boundaries, and structured Commands.
Write the terminal report last, then stop editing and notify main. Main uses the returned
`finalize_invocation`; do not construct an acceptance command independently.

## Reports and plans

A successful report is exactly:

```json
{"status": "completed"}
```

A blocked report contains exactly `status` and one `blocker`:

```json
{
  "status": "blocked",
  "blocker": {
    "failure_class": "annotation-gap",
    "kind": "missing-premise",
    "vcs": [{"name": "vc_name", "parent": null, "annotation_location": "function/loop boundary"}],
    "message": "Existing premises, missing conclusion, and the reason",
    "repair_boundary": "C annotation"
  }
}
```

Blocker and VC-entry fields are fixed. Semantic gaps must identify actual VCs; tool/report problems
may use empty `vcs`. VC-checking gap classes are `annotation-gap`, `specification-gap`, and
`dependency-gap`; `plan-defect`, `report-defect`, and `infrastructure` are also allowed. Group semantic
gaps all use `annotation-gap`; each VC must belong to the group, with a nonempty explanation in
`group_worker_output.md`. Scheduling reads structured fields and does not extract VCs from prose.

`annotation_plan.json` is version 2, with `version`, `status`, `function_specs`, `loop_invariants`,
`new_predicates`, and `vc_comparisons`. Owners provide design summaries. Scripts check required
structure, VC identities, and comparison coverage, not mathematical quality inferred from guessed
function/loop counts. The VC owner is responsible for current group-plan coverage and array order.

## Pause, resumption, and diagnostics

Pause updates run control and writes the control signal. Tasks, owners, and files remain unchanged;
no suspended-action list is saved. Tools respond to the signal and clean up their process trees.
After explicit resumption, run `step`: running owners continue their tasks, returned deliveries are
finalized again, and prepared tasks remain available to claim.

Run/group logs record commands, durations, and exits. `timing_summary.json` contains `run`, `commands`,
`annotation_attempts`, and `rounds`; summed durations are not parallel wall-clock time. Logging
failures are diagnostic, not evidence for or against a proof. Symexec progress records only actual
output, elapsed time, and file sizes; it does not guess the current function or mathematical progress.
