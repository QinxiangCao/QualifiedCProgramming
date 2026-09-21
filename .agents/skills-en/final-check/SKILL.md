---
name: final-check
description: Use from main after final-apply publishes the current proving_merged candidate; check current C obligations, complete Rocq proofs, manual/library boundaries and side-product cleanup, with safe recovery on failure.
---

# Final Check

Only main uses this skill after the controller completes `final-apply`; do not create a subagent. Execute the current action's complete argv/cwd. Actions derive from current task status, so do not reuse commands from old reports.

Read [the workflow](workflows/final-check.md) in full and follow the orchestrator's [paths and commands](../verification-orchestrator/workflows/paths-and-commands.md) and [public interface](../verification-orchestrator/docs/controller-cli.md). Do not edit proofs, clean directories manually, or invoke raw Coq/Dune/Make.

`final-check` verifies current-source obligations, all proof routes, the case library, safety boundaries, and cleanup. Only complete success changes the run to `done`. After a failed check and safe rollback, perform the controller's `final-apply` action before another final check. Publication conflicts preserve current files for the user to resolve.
