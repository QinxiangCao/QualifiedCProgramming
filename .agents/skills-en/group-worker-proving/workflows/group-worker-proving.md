# Group Proof Flow

One group-worker performs this flow. It solves only the witnesses assigned to this group by the controller in the current claim/handoff, does not modify main-root formal files, has no dependency on a sibling group, and is responsible for no parent phase.

## 1. Start and reading order

The main agent has already executed the controller-provided `claim_invocation`. On both the initial claim and a same-owner appended repair, the message must contain `Role`, `Owner`, `CWD`, and the verbatim `Claim message`. First confirm that the role is the current group-worker, that the owner matches the claim message, and that all work remains in the provided `CWD`; do not run or reconstruct claim yourself. If any of the four sections is missing, they conflict, or the referenced current handoff does not exist, stop expanding the read scope and identify the missing item under the already-bound report contract; do not reconstruct context from run state or another role's documents.

Before starting formal work, read the following in full and in this order:

1. `group-worker-proving/SKILL.md`, this flow, the command rules, and the forbidden-lemma rules.
2. The current `group_worker_input.md` specified by `Claim message`.
3. The proof-knowledge documents selected by the target-based navigation in `SKILL.md`.
4. Read the round-start `public_helper_snapshot.txt`.
5. If `proof_reuse.md` exists, read its helper, split-goal, and top-level VC rows in that order.

The current `group_worker_input.md` is this worker's sole scope source. It must provide the owner/group identity, fixed work and report paths, assigned witnesses, each witness's `proof_mode` and applicable split goals, the copied manual, optional `group_worker_lib`, helper suffix, public-snapshot/reuse hints, and executable commands. Use only its exact paths, names, assignments, and argv; do not infer them from a C stem, directory name, or another file.

Do not read the orchestrator or another role's skill, rely on a parent transcript, or read `controller_state.json`, `group_workers_manifest.json`, or sibling output to fill gaps in the handoff. If a handoff field required to perform this group's work is missing or contradictory, report the precise handoff location under the existing blocker contract; do not search outside scope or alter the plan yourself.

When the controller returns `append-group-worker`, the same owner continues in the same group directory. First read the appended category, message, required repair, and write boundary opened for this repair in `group_worker_input.md`: a formal repair changes only the original copied files; a report-only repair changes only the report and optional notes and must not touch formal files again.

## 2. Write boundary

The worker may modify:

- assigned proof spans in this group's copied manual;
- this group's `group_worker_lib`, only when the handoff explicitly provides it;
- the exact debug script named by the handoff;
- `group_worker_report.json`;
- optional `group_worker_output.md`.

These remain read-only:

- statements, manual declaration order, and unassigned proof spans;
- main-root `formal_case_lib`;
- generated files;
- `public_helper_snapshot.txt`;
- previous sources referenced by `proof_reuse.md`;
- all sibling-group files.

Do not modify the main-root formal manual/library, a shared or differently named library, generated files, the durable public pool, a plan/manifest/state file, or a sibling file. If `group_worker_lib` is missing or absent from the handoff, do not create it, add a helper/import, or modify any shared library instead.

The group directory must end with only the copied manual and the optional `group_worker_lib` already provided by the handoff. Reports and debug/build files live at the handoff-designated report path and under `_coq_builds` respectively; do not create another file or directory yourself.

The controller checks semantic write boundaries through Rocq tokens. Comments, whitespace, CRLF/LF, trailing spaces, and EOF-newline differences are not proof-token edits; statement tokens, unassigned proofs, and `LLM_pre_process` split blocks remain strictly protected.

## 3. Complete the manual by `proof_mode`

Treat the assigned top-level witnesses listed by the handoff as a closed scope. For each witness, execute only its accepted `proof_mode`. Do not prove, modify, or depend on an unassigned witness even if another declaration looks similar. If the handoff's mode/split mapping conflicts with the copied manual, do not change the mode or plan yourself; report the precise conflicting location under the blocker contract.

### `aggressive_pre_process`

Edit only:

- the current top-level VC proof span;
- every split-goal proof span listed by the handoff.

Proceed as follows:

1. Prove every split goal first, each opening with `LLM_pre_process ltac:(...)`.
2. Use `aggressive_pre_process` in the top-level VC.
3. For every branch produced by `aggressive_pre_process`, use only `Goal_apply <corresponding split-goal lemma>.` and no other tactic.
4. Apply every split lemma to its corresponding branch. Do not replace `Goal_apply` with `apply`, `eapply`, `exact`, `refine`, a local alias, or another mechanism.

This is a mandatory group-worker proof rule. The controller deliberately does not inspect whether the top-level proof spells `Goal_apply`; it checks the selected `proof_mode`, split-goal completeness, write boundaries, and Rocq result.

### `LLM_pre_process`

Edit only the top-level VC proof span and run `LLM_pre_process ltac:(...)` with an argument appropriate for the current goal. The corresponding split-goal blocks must retain the Rocq tokens of `Proof. Abort.`; only comments, whitespace, and line endings may differ.

### Skeleton and forbidden tactics, both modes

`aggressive_pre_process` appears only in a top-level VC that has split goals, and only `Goal_apply` follows it. Every other proof — split goals, and top-level VCs on the `LLM_pre_process` route — opens with `LLM_pre_process ltac:(...)` and spells out its closer.

Proof text must not contain `entailer!` or the alias `pre_process`. Both are scanned like a forbidden lemma and a match fails the group under `forbidden-lemma`; internal calls from `LLM_pre_process` and `Goal_apply` are unaffected. For rewrites see [Separation-logic proof tactics](../docs/separation-logic-whole-proof-tactics.md).

## 4. Helpers, imports, and `group_worker_lib`

Only when the handoff provides `group_worker_lib` may the worker add proved `Lemma`, `Theorem`, `Fact`, or `Remark` declarations and necessary official Rocq imports to it. A helper must be fully proved in this library and must not be placed in the copied manual.

Naming rules:

- Every new, rewritten, or renamed helper ends with `helper_namespace.suffix`.
- A planned helper uses the exact name in the handoff.
- A historical or other-group suffix may remain only when declaration and proof tokens are identical to a frozen snapshot block or an accepted helper reuse row.
- A material change to an existing helper creates a new current-group helper and therefore uses the current suffix.

Add only project imports genuinely required by the proof and already covered by the accepted dependency snapshot, or imports from the installed Rocq standard library. Do not modify seed declarations; add a generated/current/sibling import; edit the durable pool; or import the snapshot as a `.v` library. A project import outside the snapshot cannot be prepared dynamically for this group; record the exact requirement and return to annotation as directed by the controller. The worker does not inspect the dependency graph, invoke Dune, Make, or `coqdep`, or widen a build target.

`public_helper_snapshot.txt` is the read-only round-start catalog. A token-identical proved helper may be copied from it into `group_worker_lib`. A helper promoted to `public_helper_lemma_lib.v` later by another group in this round is not visible to this group.

For a planned helper with `visibility: local`, the candidate remains local to this group. For `visibility: public`, the controller still appends it and the required local-helper dependency closure to the durable pool only after this group passes validation. The worker neither publishes a file to siblings, treats a public helper as a same-round cross-group dependency, nor waits for a pool update.

If a later merge sees legal helpers with the same name but different tokens, the controller selects a canonical block and renames other variants only in the merged candidate, rewriting this group's references as needed. A worker does not anticipate the merge result or read or edit another group's names.

## 5. Use of reuse hints

`proof_reuse.md` exists only when the controller binds the immediately preceding sealed proving source. Read rows in this fixed order:

1. all helper rows;
2. all aggressive split rows;
3. all `LLM_pre_process` top-level rows.

An aggressive top-level VC has no independent reuse row. Complete it from its current split goals under the `Goal_apply` rule above.

Every non-`from scratch` line range must cover a complete declaration:

- Helper `direct copy` and proof `direct copy` come only from a previously accepted group.
- Direct proof reuse has also passed the generated-goal semantic-fingerprint comparison; a generated declaration rename alone may still be direct.
- `partial proof-idea reuse` conveys only an idea. The worker must prove any `P |-- P'`, `Q' |-- Q` adapter or common-frame transformation.
- A proof from an unaccepted failed or blocked group is at most partial, and its helpers are always from scratch.

All previous files are read-only. A reuse hint cannot change this group's assignment, `proof_mode`, commands, or validation requirements.

## 6. Proof loop

1. Read the current target and available helpers.
2. When useful, write the exact handoff-designated debug script and run the rendered `coq-debug`.
3. Prefer `group-development` for fast feedback; temporary `Abort.` is allowed only in this group's editable proof spans.
4. Repair assigned proofs, and repair `group_worker_lib` only when it exists and a change is needed.
5. Run exact `group-check` when useful; it requires complete proofs and legal routes for this group.
6. Before delivery, check the assignment/mode, helper suffix/import, write boundary, and forbidden rules. Do not leave `Admitted.`, an extra `Axiom`, or a forbidden lemma; a terminal copy blocked by an annotation gap must not fake progress through any of them either.
7. Write the final report. An `annotation-gap` terminal result must also write `group_worker_output.md`; that note is optional for other terminal results. Then stop modifying the report, manual, and library.
8. Return the result to the main agent. The main agent invokes the `finalize-delivery` bound by the claim/handoff verbatim; the controller seals the report, manual, and library when applicable, then performs the single mandatory group validation.

Development and exact checks are optional early feedback, not credentials required in the owner report. Even an exact pass does not replace controller validation over the finalized sealed bytes. The worker does not run claim/finalize itself, invoke controller `step`, or attempt merge, parent verify, or annotation retry.

## 7. Repair and blocking

### Locally repairable findings

Continue repairing locally rather than returning `blocked` for:

- a tactic failure;
- a missing optional reuse hint;
- the need for another suffixed helper;
- multiple debug iterations;
- a controller-reported repairable structure, route, proof-completeness, or safety issue.

Repairable findings arrive through `append-group-worker` for the same owner. Within the exact boundary opened by the handoff, repair the copied manual or `group_worker_lib` when applicable, rewrite the terminal report, stop writing, and deliver again.

### Annotation/spec gaps

Diagnose an annotation/spec gap only when the concrete proof state and every legal helper path jointly establish all of the following:

- The hypotheses of a current assigned witness genuinely lack a semantic premise required to complete the goal.
- That premise cannot be proved from the existing hypotheses through an existing helper, frozen/reuse helper, ordinary proof transformation, or a legal current-suffix helper.
- Repair requires changing a mathematical specification, function contract, loop invariant, assertion, or call instantiation outside the group-worker write boundary.

Once that diagnosis is established:

1. Treat it as the terminal result for this group's current delivery. Do not keep adding proof changes to the copied manual or `group_worker_lib` in an attempt to replace annotation work, and never modify a statement, main root, or unassigned proof.
2. Preserve the existing legal copies. In `group_worker_output.md`, identify the group id from the handoff, every affected assigned witness, its top-level/split location, the exact missing premise, attempted helpers/routes, and the annotation/spec boundary that must change.
3. Write a complete machine report with `status: blocked`. Its `blocker.failure_class` must be exactly `annotation-gap`; use `kind: missing-annotation-premise` for a specifically missing annotation premise. `location` must list the affected declaration/proof state by witness, `message` must state a diagnosable missing fact, and `repair_boundary` must identify the annotation/spec boundary that actually needs repair.
4. Stop all formal/report writes and return the result to the main agent so the current delivery can be sealed through the normal `finalize-delivery` path.

This terminal result describes this group only. The worker does not read or query sibling state, request cancellation of unclaimed groups, wait for other groups to finish, create annotation feedback/retry, or attempt merge or parent verify. The controller/main agent handles other groups and later rounds.

### Other blockers and in-place report repair

For a proof blocker, blocking is justified only when the concrete proof state/helpers show that a necessary premise cannot be derived; ordinary tactic-search failure is not terminal. Tool/resource, handoff, version, and other blockers retain their existing `failure_class`/`kind` meanings and repair boundaries. When the exact tool represented by the handoff command cannot run at all, report the existing tool/resource blocker. Do not misclassify any of these as `annotation-gap` merely to include it in round aggregation. Use the existing `stale` classification for version invalidation and the existing `compact-error` classification for context compaction.

If finalize returns only a final-report field-contract error, the delivery remains the same claimed attempt and the same owner repairs it in place. The repair boundary opens only `group_worker_report.json` and optional `group_worker_output.md`; the controller-sealed copied manual and applicable `group_worker_lib` must remain byte/token identical. After repairing the report, stop writing and return it to the main agent to rerun the original `finalize-delivery`. Formal drift produces non-reusable `invalid-report`; a report-repair window must not reopen a proof. An annotation-gap terminal result likewise permits only this report-only repair.

## 8. Final report

On success, write only:

```json
{
  "status": "completed"
}
```

A `blocked` report still has only `status` and one complete `blocker` at the top level. The `blocker` has exactly these five fields:

```json
{
  "status": "blocked",
  "blocker": {
    "failure_class": "<existing deterministic value selected under this flow and the handoff>",
    "kind": "<specific issue type>",
    "location": "<exact witness/declaration/proof-state location>",
    "message": "<complete diagnosable issue and evidence>",
    "repair_boundary": "<permitted and necessary repair boundary>"
  }
}
```

Do not add `group`, `witness`, version, digests, changed files, command output, receipt, assignment, candidate paths, namespace, or declaration metadata to the JSON. The controller binds the group and assignments through the current delivery/accepted plan/seal. Use `location`/`message` and `group_worker_output.md` to identify affected witnesses; `group_worker_output.md` is required for `annotation-gap` and optional for other terminal results. The owner does not copy controller-derived data or helper declaration metadata.
