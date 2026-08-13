# Final-apply and Final-check Flow

Only the main agent performs this flow; it does not start a subagent. The controller accepts a candidate only when `proving_merged_result.json` is `passed` and the parent full check has succeeded.

## 1. Source checks before writeback

Before touching a main-root formal target for the first time, the controller rechecks, in order:

1. the accepted annotation's target C file;
2. the annotation `after_snapshot`;
3. that the current target C plus every formal/generated role in persisted `target_files` still matches the accepted annotation delivery in present/missing state and present bytes;
4. the complete digest of the parent merge result;
5. the report, copied manual, and applicable `group_worker_lib` digest of every accepted group that exists;
6. the per-role candidate manual and `proving_merged_lib` digests, using `null` for an absent optional role.

Optional notes such as `group_worker_output.md` are outside the seal. A missing `after_snapshot`, invalid path, unparseable JSON, or digest drift produces a precise blocker before any formal target is modified.

This prevents an unaccepted optional manual or library from being treated as the rollback original, and prevents replacement of only the present formal files from hiding goal, auto, or check drift.

## 2. `final-apply`

The source must be under:

```text
verification_runs/<run>/<round>/proving_merged/
```

The controller writes back only candidates that are actually present:

- merged manual to the main-root formal manual;
- `proving_merged_lib` to the main-root `formal_case_lib`.

An absent optional role does not create a target or placeholder. When both are absent, a zero-target transaction is valid but still completes source revalidation and the phase transition. The target C file and other generated files remain the accepted annotation's main-root versions; they are not copied from a group or merged directory. Fixed exact paths, backup digests, and atomic replacement constrain apply/rollback.

### Persistent transaction

Apply follows this fixed transition:

```text
prepared → backed-up → completed
```

1. `prepared` records source, target, candidate digest, whether the original existed, and its digest in state.
2. `backed-up` creates one non-overwritable backup at `reports/<run>/final-check/backup/<transaction-id>/`.
3. `completed` atomically replaces each target and records completion.

After interruption, the controller may only verify and continue the same transaction or roll back through that same backup. It must not create a replacement backup that overwrites the original baseline.

Before every recovery, re-entry, or rollback, the controller re-derives the exact zero-, one-, or two-candidate set for the accepted proving and binds it strictly to the transaction. The record set and order may contain neither extra, missing, nor duplicate entries; source, target, relative path, candidate digest, original presence/digest, transaction id, and backup path must exactly match the current run, accepted seals, and fixed backup topology. A zero-target transaction may contain only empty records. If any field has been injected, a path crosses runs, an original digest differs from the accepted annotation seal, or the backup topology is invalid, the controller does not roll back: it terminates as `rollback-failed`, so a corrupt record cannot authorize deletion or restoration of arbitrary main-root files.

When re-entering a `backed-up` or `completed` transaction, each formal target must be either the sealed original or candidate. If an annotation, candidate, manifest, or group seal then fails, the controller first uses the same backup to undo any partial writeback and only then persists `blocked`.

An apply copy failure or final-check failure also uses only the transaction backup. Even if a target leaf has been replaced by a symlink, rollback replaces or removes that directory entry without following the external target.

Never apply files directly from a group directory, annotation history, or a stale report.

## 3. Freshness check

The controller reruns canonical symexec in:

```text
reports/<run>/final-check/symexec-refresh/
```

This check reuses the annotation clean-output implementation but does not overwrite the proved manual.

It compares:

- fresh goal, auto, and goal-check against main root exactly;
- the directly parsed raw fresh manual when present;
- declaration order when both the raw fresh and proved manuals are present;
- top-level VC names and statements when a manual is present;
- split-goal names and statements when a manual is present;
- the current target C digest against the accepted annotation `source_version`;
- goal, auto, goal-check, and other files not replaced by final-apply against sealed annotation history.

When the proved manual is present, its proof bodies intentionally differ from the raw manual, so their digest is not compared and no extra manual artifact is introduced. The acceptance-stage clean replay prevents unstable obligations from reaching proving; it does not replace this final candidate check.

When present, the final applied manual and `formal_case_lib` are expected to differ from the annotation bundle and are compared with the accepted proving candidate. An absent role must have `null` candidate and applied digests and must not gain a placeholder.

When there is no manual VC, the manual may be absent. If present, both raw and proved manuals may contain only generated imports and scope commands and both declaration lists must be empty. Regardless of manual presence, freshness, goal, auto, goal-check, accepted annotation source, and parent/full Coq checks remain mandatory. If goal-check imports a missing manual, the check must fail.

## 4. Main-root Rocq check

The controller uses fixed `coq-check` settings:

- workspace: main root;
- build: `verification_runs/<run>/_coq_builds/final-check/src`;
- target: the root-relative goal check;
- target kind: `check`;
- version: the current `source_goal_version`.

`coqc` and `coqtop` come from explicit environment variables or PATH; accepted dependencies come from selected build output. The main agent does not construct flags, call an internal module, invoke Dune, Make, or `coqdep`, or run raw Coq.

Main executes only the complete `invocation.argv` returned by the `final-check` action, with `invocation.cwd`. It never reconstructs a command from the examples in this document.

A human uses root-level `uv run --frozen --python 3.12 python` only to enter the first public controller command. This stage's action already binds the validated absolute `sys.executable`; main neither substitutes it nor wraps the action in uv again.

### Accepted selected dependency snapshot

After annotation acceptance, the `dune-build` action has selected Dune or Makefile according to the `_build` directory, discovered dependencies, and rebuilt stale files for the exact goal-check target. It writes the fixed version to run-root `dune_dependency_snapshot.json` or `makefile_dependency_snapshot.json`. Final-check:

- stages only the exact snapshot closure of applied current files;
- copies no dependency `.v` or `.vo` into the local build;
- reads dependency `.vo` files through the selected base's absolute load paths: `_build/default` for Dune, main-root `Rocq/` for Makefile;
- derive case identity only from persisted `target_files`, where `--case` is the authoritative formal stem;
- treat only this run's five exact canonical artifact identities as current; only actually reachable generated artifacts and the editable `formal_case_lib` are staged;
- retains fixed broad selected-base mappings unchanged;
- add the build-local exact current mapping last;
- require every current dependency to have a local `.vo` in this build first.

A shared or differently named library does not become editable current merely because it is in the same directory or imported by the current goal; it is a readable dependency only when it belongs to the accepted snapshot. Final validates snapshot, dependency source/artifact, selected configuration, and the run-Makefile digest when applicable and directly reuses the corresponding `.vo` files. It does not run Dune, Make, or `coqdep`, re-resolve the dependency graph, or compile dependency source during final.

A missing or drifting dependency, a project import outside the snapshot, a changed current edge, or an inconsistent current local artifact must return a precise failure. There is no fallback to a whole-workspace Dune target, a repository Make aggregate target, a whole-repository mirror, an old source-tree current artifact, or dependency-source compilation during a check.

## 5. Manual and the three active libraries

All of these must hold:

- A present manual contains no `Admitted.`, additional `Axiom`, helper, or forbidden top-level declaration.
- Present-manual declaration names, order, and statement hashes match `source_goal_version`.
- When `target_witnesses` is empty, either an absent manual or a present manual containing only generated imports and scope commands, together with empty proof routes and `group_count: 0`, is valid. This does not remove the parent full check or any check in this stage.
- Every top-level VC is complete.
- Every split goal for `aggressive_pre_process` is complete, and its top-level proof uses that `proof_mode`.
- Only an original split-goal block whose accepted route is `LLM_pre_process` may retain `Abort.`.
- A present `formal_case_lib` contains no `Admitted.`, additional `Axiom`, or forbidden lemma.
- A present `formal_case_lib` digest equals the accepted `proving_merged_lib`; when absent, both digests are `null`.
- A present `formal_case_lib` is audited as an independent import root even when goal-check does not import it. It must not reach any of this run's exact generated identities from `target_files`, whether that generated leaf is present or missing. Every other project import must belong to the accepted dependency snapshot; a namespace regex must not widen the prohibition. This audit reads only source and snapshot; it does not run Dune, Make, `coqdep`, `coqc`, or compilation.
- When the library is present, every merged helper traces to a `group_worker_lib` and `proving_merged_result.json`; when absent, neither a helper nor `group_worker_lib` may exist.
- A present manual uses no forbidden lemma.

The accepted group manifest binds assignments through the plan digest. Accepted plan order controls mechanical merge; `dispatch_order` controls only scheduling.

Helpers with the same name and the same declaration/proof tokens are deduplicated. If names match but tokens differ, a frozen public or reuse block wins; otherwise the first plan group wins. Other legal variants are renamed only in the merged candidate with a unique current-group suffix, and references are rewritten only in that group's new-helper closure and assigned proofs. Sealed group files remain unchanged, and the rewritten candidate must already have passed the parent full check.

The run-root `public_helper_lemma_lib.v` path, digest, and count must match controller state. It is not imported, compiled as an active case library, or written to main root.

## 6. By-product cleanup

At the start of final-check, the controller removes only:

- stale `.vo/.vos/.vok/.glob/.aux` files for every exact current module identity in persisted `target_files`, including same-named residue when an optional source is absent;
- matching stale files in the current run outside `_coq_builds`.

Only the deletion count is recorded. Accepted dependency `.vo` files are preserved: under `_build/default` in Dune mode and as main-root trusted-base `.vo` files in Makefile mode. A broken symlink, directory, FIFO, or other non-regular side-product leaf cannot masquerade as an absent artifact; inability to remove it safely is a cleanup error.

After freshness, Rocq, and structural checks, the controller scans the same target/run boundary again. A newly produced or undeletable target by-product fails cleanup. State and output retain only:

- deletion count;
- error count;
- residue count;
- the first error or residual path.

Formal deliveries, base `.vo` files, controller state, the run log, annotation attempt files, annotation history, round/group reports, and the merge result must not be deleted. The agent does not clean them manually.

## 7. Single-run execution boundary

Main executes only the one controller action currently returned by `step` and keeps the same terminal session until the process exits. The controller creates no synchronization file for state, formal targets, workspaces, or selected build artifacts. State uses generation compare-and-swap and atomic replacement; final formal mutation uses the persistent backup transaction, digest seals, and atomic replacement. Multiple runs modifying the same main root concurrently are outside this contract.

## 8. Failure and recovery

Any freshness, Rocq, structure, library, forbidden-lemma, or cleanup failure triggers a rollback attempt.

After successful rollback:

1. the phase returns to `final-candidate-apply`;
2. the main agent runs `step`;
3. it runs the controller-provided `final-apply`;
4. only a successful new apply permits another final-check.

Do not rerun final-check directly on a rolled-back main root.

The new `final-apply` revalidates the accepted annotation, parent result, manifest, and group seals before creating a backup or writing main root. If the original failure came from those source files, the entry consumes its action with the existing `blocked` state while preserving the rolled-back formal bytes; it does not re-enter final-check or repeat the same exception indefinitely.

If rollback fails, automatic recovery stops with a precise blocker.

Only after every item passes does the controller set the run to `done`.
