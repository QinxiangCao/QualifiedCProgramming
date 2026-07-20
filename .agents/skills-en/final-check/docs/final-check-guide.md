# Final-Check Guide

This document is for the main agent. Final-check does not start a subagent.

## final-apply

The controller accepts only a candidate whose `proving_merged_result.json.status == passed` and whose parent full scripted check passed.

final-apply:

- The source must be the accepted `verification_runs/<run>/<round>/proving_merged/` directory.
- Copy only the merged manual and `proving_merged_lib` to the formal manual and `formal_case_lib` in the main root.
- The accepted annotation already left target C/generated files in the main root; do not copy them from a group or merged directory.
- Before applying, back up touched files under `reports/<run>/final-check/backup/`; roll back if apply or final-check fails.

Never adopt a file directly from a group directory or stale history/report.

## Symbolic-execution freshness

The controller uses `symexec_tooling.py` internally with this fixed output root:

```text
reports/<run>/final-check/symexec-refresh/
```

The helper assembles the driver, cwd, canonical include/SLP arguments, and logic/generated paths. Fresh goal/auto/check files are compared file-for-file with the main root. The raw fresh manual undergoes the same diagnostics split used during annotation acceptance inside the refresh directory; the cleaned fresh manual contributes only witness names/statements and never overwrites proved bodies. Refresh diagnostics and the snapshot belong only to this freshness evidence and are not written back to the main root.

The current target C digest must still equal the target C recorded in the accepted annotation `source_version`. The finally applied `formal_case_lib` is expected to differ from the annotation seed, so do not incorrectly require whole-source-version equality for it.

## Fixed Coq check

The controller internally runs the fixed check from `coq_tooling.py`: the workspace is the main root, the build directory is `verification_runs/<run>/_coq_builds/final-check/src`, the target is the root-relative goal check, target kind is `check`, and the version is the current `source_goal_version`. The `coqc` path comes from `SeparationLogic/CONFIGURE` and the Makefile's `COQBIN` / `SUF` convention. As in every run and phase, the check reuses prerequisite `.vo` files from the main root's prior full make across every Makefile load path. It does not create a cache keyed by source digest, Coq version, or flags, and it does not recompile base libraries. Old products for the current target's lib/goal/auto/manual/check modules are excluded, and those modules are rebuilt from applied source. The main agent never invokes the internal helper directly.

Do not write Coq flags or raw commands. Controller state keeps only necessary summaries such as status, version, return code, and first failure diagnostic. Rerun the same controller check exactly when full feedback is needed.

## Manual and three-library review

- The manual contains no `Admitted.`, `Abort.`, extra `Axiom`, helper, forbidden top-level declaration, or forbidden lemma.
- The manual witness list exactly matches `source_goal_version.target_witnesses`.
- `formal_case_lib` contains no `Admitted.`, extra `Axiom`, or import of a current generated artifact.
- The `formal_case_lib` digest equals the accepted `proving_merged_lib` digest.
- Merged helpers are traceable to `group_worker_lib` reports and `proving_merged_result.json`.
- Neither the manual nor `formal_case_lib` uses any forbidden lemma.

## Cleanup

At the start of final-check, the controller removes old `.vo/.vos/.vok/.glob/.aux` products only for the current target's five formal modules and in current-run areas outside `_coq_builds`, recording only deletion counts. Base `.vo` files from the prerequisite full make must remain. After freshness, fixed Coq, and structural checks, the controller scans the same target/run boundaries again. New or undeletable target side products make cleanup fail. State/output stores only deletion, error, and residual counts plus the first error or residual path; it does not store a complete path list.

New Coq side products for the current target are allowed only inside the current run's `_coq_builds`. Main-root base-library `.vo` files are allowed and required trusted inputs. The agent does not perform cleanup manually. The controller must not delete formal deliverables, base `.vo` files, controller state, the run log, any `annotation-attempts/annotation-attemptN` handoff/report, formal annotation history, round/group reports, or merge records.

## Failure recovery

Any failed final-check item rolls back final-apply. After successful rollback, the phase returns to `final-candidate-apply`; the main agent invokes `step`, executes the returned `final-apply`, and only then may run final-check again. Never rerun final-check directly against a rolled-back root. If rollback fails, the controller preserves the blocker and returns no new apply/check action.

Write `done` only after every freshness, fixed-check, structure, library, forbidden-content, and cleanup item passes. Otherwise record the blocker and roll back the final apply.
