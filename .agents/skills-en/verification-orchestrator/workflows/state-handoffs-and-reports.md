# State, Handoffs, and Reports

## 1. Authoritative Data

`verification_runs/<run>/controller_state.json` is authoritative state; `reports/<run>/controller_target_topology.json` fixes case topology. Owner reports declare only terminal status/blockers.

Key paths include annotation attempt reports/plans, sealed annotation `before`/`after` histories, proving base/group manifests, fixed group manual/library copies, group reports/notes, and optional `proof_reuse.md`. Every persisted path must match the current run/round/attempt layout. Source-byte drift after sealing rejects retry, acceptance, or merge.

## 2. Annotation State

User-spec state:

```json
{
  "spec_freeze": {
    "functions": ["f"],
    "baseline": {}
  }
}
```

Only `init-run --freeze-spec` creates this record; without a user-provided specification, `spec_freeze` is `null`. After the user approves a change, `unfreeze` preserves `functions` and sets `baseline` to `null`. When the current annotation attempt is accepted, the controller records the checked current specification surface as the baseline.

Every annotation attempt contains `failed_vcs`; the first attempt uses an empty list. Exact entry:

```json
{
  "source_attempt": "<round-or-round:group>",
  "name": "<top-level-or-split VC>",
  "parent": null,
  "annotation_location": "<C annotation point>",
  "manual": "/absolute/sealed/manual.v",
  "message": "<old gap>"
}
```

The controller checks that the manual is under the run root and that the VC name and parent exist.

## 3. Annotation Plan Version 2

Exact top-level fields:

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

`function_specs` gives one sentence for each C function contract. `loop_invariants` gives one sentence for each lexical loop. `new_predicates` contains only predicates added by this case and the reason core interfaces are insufficient.

The first attempt requires empty comparisons. A retry covers every failed VC exactly once, and every current VC exists in the current manual. The owner compares the old and current propositions directly and records the old gap, change, and `resolved` or `unresolved`. Ready status requires every result to be `resolved`. Accepted evidence stores the comparison count, resolved count, and source/current VC names.

## 4. Retry Handoff

After VC checking or VC proving supplies an annotation gap, an annotation retry starts directly at `prepared`. The controller renders a complete `agent_input.md` containing assignment, targets/write boundary, original sealed Markdown/JSON sources, `failed_vcs`, related `Previous VC changes`, exact commands, and completion contract.

History comes from prior comparisons in time order and retains records related by exact name, parent, or current VC name. Main and annotation owners maintain no second copy.

The initial attempt uses `spawn-annotation-agent`; every retry immediately uses `append-annotation-agent` with the same owner/target.

## 5. Agent Reports

Success:

```json
{"status": "completed"}
```

Blocked:

```json
{
  "status": "blocked",
  "blocker": {
    "failure_class": "annotation-gap",
    "kind": "missing-annotation-premise",
    "vcs": [
      {
        "name": "proof_of_f_entail_wit_1_split_goal_2",
        "parent": "proof_of_f_entail_wit_1",
        "annotation_location": "outer loop exit"
      }
    ],
    "message": "<existing premises and missing conclusion>",
    "repair_boundary": "<annotation/specification boundary>"
  }
}
```

Blocker fields are exactly `failure_class`, `kind`, `vcs`, `message`, and `repair_boundary`. Group/VC-checking annotation/specification/dependency blockers require nonempty `vcs`; the controller never guesses a VC from `message`. Tool/report blockers may use empty `vcs`.

VC-checking routing:

- to annotation: `annotation-gap`, `specification-gap`, `dependency-gap`;
- stay in VC checking: `plan-defect`, `report-defect`, `infrastructure`.

An agent-written specification changes directly in the current attempt without a report or a new attempt. If a user-provided specification needs a change, the annotation owner does not run `finalize-delivery`; it writes the proposal in `agent_output.md` and returns it to main. After user approval and `unfreeze`, the same owner continues in the same attempt.

## 6. Group Blocker Aggregation

The controller accepts only blocker VCs that exist in the sealed group manual and belong to assigned witnesses. Aggregate records preserve round/group id, assigned witnesses, exact `vcs`, message/repair boundary, and original output/report paths.

The first proving round aggregates after ordinary concurrent groups reach terminal states. If a priority batch finds an annotation gap, no remaining group is dispatched; once already-running/returned priority work finishes, current priority blockers are aggregated immediately.

`retry-round` expands every blocker VC into `failed_vcs` pointing to the group's sealed copied manual.

## 7. Proving Manifest and Previous-Round Material

The compact worker manifest records base/group-plan/public-helper/dependency-snapshot digests, group ids, dispatch order, and the immediately preceding proving round or `null`.

The previous-round id comes directly from the latest proving attempt in controller state. Preparation does not probe the directory and silently clear it, or reread the just-written manifest to recover the same value.

The proving attempt also stores `priority_group_ids`. Every group remains `prepared` after preparation. The controller does not copy old proofs, create a worker report or `proof_reuse.md`, or store reuse results in group state.

When a previous round exists, each actually claimed worker handoff contains that directory and this group's optional `proof_reuse.md` path. The worker searches across old groups by current witness/helper names, reads only candidate proof blocks, and chooses what to reuse. Missing or empty Markdown does not block finalize; the current group check alone determines whether the proof is valid. The first round and groups never dispatched create no file.

Accepted groups seal report, manual, and active group library. An annotation-gap group also seals `group_worker_output.md` as retry evidence.

## 8. Owner, Claim, and Finalize

Controller owners are stable:

- one annotation owner per run;
- one independent owner per vc-checking attempt;
- one owner per round/group, reused for group repair.

Main runs the action's `claim_invocation`, forwards the returned `handoff.prompt` verbatim, then runs the original `finalize_invocation` after owner return. `report-repair-required` keeps the same owner and invocation.

## 9. Timing

Timing separates annotation attempts, owner generation, controller refresh, clean replay, acceptance, VC checking, group work, parent verification, final apply, and final check. Progress is measured by VC comparisons and accepted proofs.
