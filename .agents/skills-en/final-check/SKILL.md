---
name: final-check
description: Used by the main agent after final-apply to confirm that root generated/manual/formal_case_lib files agree with the accepted proving_merged_lib, versions, and reports.
---

# Final Check

Only the main agent uses this skill. It does not start a subagent.

## Documentation

- `docs/final-check-guide.md`: final-apply, freshness, fixed Coq checks, the manual, the three library roles, forbidden content, and cleanup.
- `../verification-orchestrator/docs/path-configuration.md`: freshness and final Coq paths.

## Completion requirements

- The formal manual and `formal_case_lib` come only from the controller-accepted proving-merged directory, and the `formal_case_lib` digest equals the `proving_merged_lib` digest.
- Scripted freshness symbolic execution writes to a temporary report location and does not overwrite the proved manual. The controller performs diagnostics splitting on the raw refreshed manual, then compares only cleaned witness names/statements.
- The scripted full goal check on the main root passed, with build files confined to the run's `_coq_builds`.
- The manual and `formal_case_lib` contain no `Admitted.`, extra `Axiom`, or forbidden lemma; the manual contains only target witness proofs.
- Every helper is traceable to `group_worker_lib` reports and `proving_merged_result.json`.
- The controller removes old Coq side products before checks and rescans afterward. No new or undeletable side product remains on a formal path, and cleanup evidence stays compact.
- If final-check fails and rollback succeeds, return to `final-candidate-apply` and run final-apply again. If rollback fails, stop automatic recovery. Controller state/log records the final result.
