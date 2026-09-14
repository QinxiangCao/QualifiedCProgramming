# Verification Workflow for One C Case

The main agent executes controller actions, retains the owner-to-agent-target mapping, and forwards each claimed `handoff.prompt` verbatim. Owners modify their permitted files; the controller owns state, seals, checks, scheduling, merge, writeback, and cleanup.

## 1. Overall Flow

```text
init-run
  -> step
  -> annotation
      -> function specifications + internal predicates + C annotations + case-library lemmas + plan
      -> symexec + failed-VC comparisons
      -> annotation-check-round
  -> dune-build
  -> vc-checking
      -> structural scan + independent comparison review + group plan
      -> vc-checking-check-round
  -> vc-proving-preparing
      -> group reviews previous manual/lib
      -> priority groups
      -> remaining groups
      -> vc-proving-verify
  -> final-apply
  -> final-check
  -> done
```

After each controller command, inspect the final JSON:

- execute a nonempty `next_actions` list;
- wait for nonempty `waiting_for`;
- run one `step` when the consumed action leaves both empty;
- finish only at `phase: done`;
- stop and report a terminal controller blocker.

Never infer a phase, build a command, or edit state.

## 2. Init and Fixed Topology

`init-run` fixes run/report roots, C path, formal case stem, the nine `target_files`, case-library policy, user-provided formal specifications, symexec profile, group limits, and public-helper pool. Specification authority uses only `--freeze-spec`: when present, the formal specification is user-provided; when omitted, the annotation owner writes and revises it in the current attempt. Every later path is re-derived from this topology.

Library policy is `present`, `create`, or `absent`. Windows runs also follow the [Windows guide](../docs/windows.md).

## 3. Annotation

Spawn one annotation agent per run and append every retry to that same target.

The first attempt starts `prepared`. The controller creates annotation plan version 2:

```json
{
  "version": 2,
  "status": "planning",
  "function_specs": [],
  "loop_invariants": [],
  "new_predicates": [],
  "vc_comparisons": []
}
```

Without a user-provided specification, the owner starts with a natural-language specification and writes or revises the Rocq specification, function contracts, necessary predicates, minimal C body annotations, case-library definitions/lemmas, and plan in the same attempt, running:

```text
formal-case-lib-design
symexec
formal-case-lib                 # when the case library is active
```

The annotation owner never edits the proof manual or writes proofs.

With a user-provided specification, the owner preserves `spec_freeze.baseline` and completes internal annotation and case-library work. If that specification must change, the owner stops immediately, does not edit it, and does not run `finalize-delivery`. It records the function, reason, planned `With` / `Require` / `Ensure` changes, meaning before and after, and effect on the requested result in `agent_output.md`. Main pauses the run and asks the user. After approval, main resumes the run, runs `unfreeze` for the current round, and returns the approved proposal to the same owner. The round and attempt remain unchanged.

### Retry

A VC-checking or group blocker uses structured `vcs` entries with exact `name`, `parent`, and `annotation_location`. `retry-round` reads the sealed source manual and writes every target into the new attempt's `failed_vcs`. The attempt is immediately `prepared`; the controller renders the complete handoff and publishes `append-annotation-agent`. Main writes no intermediate summary.

The retry plan copies prior `function_specs`, `loop_invariants`, and `new_predicates` and clears `vc_comparisons`. After symexec, the owner directly compares each sealed old statement with the current manual:

- `resolved`: the current change removes the old gap;
- `unresolved`: continue editing this attempt.

Only `resolved` results for every source permit plan `status: ready` and report `completed`. Agent-written specifications, necessary predicates, internal annotations, and the case library remain editable in the current attempt. A new annotation attempt is created only from an annotation gap found by VC checking or VC proving.

### Acceptance

`annotation-check-round`:

1. revalidates sealed report/plan and current files;
2. validates plan version 2, function and loop summaries, new-predicate records, complete failed-VC coverage, and current VC names;
3. checks the user-provided specification when its baseline is non-null;
4. runs pre-symexec case-library contract/dependency/coqc;
5. reuses an exact owner-generation receipt or reruns transactional symexec;
6. revalidates comparisons;
7. runs the post-symexec case-library check;
8. performs clean replay and revalidates comparisons against the final manual;
9. when baseline is `null`, records the current specification surface as the user baseline; records comparison/resolved counts and source/current VC names, then accepts the C/library/generated files.

## 4. Dependency Preparation

`dune-build` is the public action name; the controller selects the backend. It prepares the exact goal-check target and seals the dependency snapshot used by VC checking, group checks, parent verification, and final check.

## 5. VC Checking

Each vc-checking attempt has an independent owner. The owner reads the current manual and annotation comparisons:

1. cheaply scans every top-level VC, checking no-split whole goals first;
2. returns a structured annotation/specification/dependency blocker for a definite missing premise/resource or countermodel;
3. otherwise performs exhaustive split-first analysis and chooses one proof mode per top-level VC;
4. directly reviews the current VCs named by each comparison; an annotation result is not proof evidence;
5. places current VCs requiring a new substantial mathematical lemma in a first high-risk group;
6. writes `group_plan.json` and concise `agent_output.md`.

`vc-checking-check-round` seals the plan, reruns symexec to remove temporary `Show.`, compares the clean and owner manuals modulo that permitted difference, and accepts the plan.

## 6. Proving Scheduling

`vc-proving-preparing` creates the base manifest, fixed group copies, public-helper snapshot, and compact worker manifest.

### Proof reuse

The controller only gives each actually dispatched group worker the immediately preceding proving-round directory and the optional current `proof_reuse.md` path. It does not match statement/split hashes, proof mode, or group id, and does not compare case-library, dependency, or public-helper digests to permit reuse.

The worker searches the preceding round's group manuals/libraries by current witness/helper/predicate names and reads only candidate declaration/proof blocks; it does not read every duplicated full manual. It performs the actual copy or rewrite in the current group files and may record direct reuse, reuse with changes, or no reuse for each current witness. Missing or empty `proof_reuse.md` does not affect finalize. A blocked old group, a renamed witness, or a changed grouping may still provide useful material, but never replaces the current full Rocq group check. The first proving round and a group that is never dispatched create no note.

### Priority batch

The first proving round has no comparisons and dispatches all groups under normal concurrency.

After an annotation retry, groups containing comparison `current` form the first batch:

- after all priority groups are accepted, dispatch remaining groups;
- if a priority group reports an annotation gap, do not dispatch remaining groups; finish already-running/returned priority work, aggregate available blockers, and create an annotation retry immediately.

Remaining groups use `dispatch_order` and `max_parallel_group_workers`.

### Group terminal results

A completed group passes statement/write-boundary/helper/import/safety/proof-mode and exact Rocq checks. An annotation-gap group may retain incomplete proofs, but every blocker VC exists in its sealed manual and belongs to an assigned top-level witness. `group_worker_output.md` explains existing premises, missing conclusion, and repair boundary.

After all required groups are accepted, `vc-proving-verify` mechanically merges the manual/library, handles helper namespaces and public-helper promotion, and runs full parent verification.

## 7. Retry Routing

- `annotation-gap`, `specification-gap`, `dependency-gap` -> annotation;
- `plan-defect`, `report-defect`, `infrastructure` -> vc-checking;
- group proof/report repair -> same group owner;
- current-file drift -> accepted annotation boundary;
- user-provided specification needs a change -> stop the current attempt, then continue after user approval and `unfreeze`;
- agent-generated specification needs a change -> edit it directly in the current attempt.

The controller consumes structured fields and never parses VC names or retry phases from `message`.

## 8. Final

`final-apply` transactionally writes the accepted merged candidate. Main then reads and uses the `final-check` skill and executes the action's `final-check`. Finish only when the controller returns `done`.

## 9. Pause and Resume

When the user requests stop, run `cancel-action` for the exact active action, or `pause-run` when none is active. Wait for controller-owned process cleanup. Run `resume-run` only after an explicit user request and continue the same action.
