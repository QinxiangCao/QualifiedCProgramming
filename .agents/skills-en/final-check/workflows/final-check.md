# Final Publication and Check

Only main executes the current controller action; do not create a subagent. Preserve its interpreter, complete argv, and cwd. Shell-only tools must quote arguments for the actual shell.

## Publish the current candidate

`vc-proving-verify` reads current group files and the accepted plan, merges mechanically, and runs a complete parent check. `final-apply` reads the current manual/library from that proving task's `proving_merged` directory, compiles them through overlays, and checks statements, prelude, proof modes, safety, and new helper suffixes. It publishes the normalized source bytes actually checked in this invocation's staging directory. Owners maintain no base/worker manifests or merge-result file.

Publish only the exact manual and active case library: zero, one, or two files. Absent roles create no placeholders and authorize no unrelated deletion. Annotation generation still owns C/goal/auto/goal-check updates.

After the same import normalization, the case library must retain the complete annotation seed as its token prefix; existing declarations cannot change, while helpers appended after the seed remain editable in the current candidate.

Publication backups are in `reports/<run>/final-check/backup`. After a failed or interrupted replacement, the controller recovers using this publication's original/candidate contents. Third-party changes, unsafe paths, or missing backups preserve current files and report a publication conflict; main must not force an overwrite.

## Check current obligations and proofs

`final-check` independently runs symexec once for current C into `reports/<run>/final-check/symexec-refresh`, without overwriting the proved manual. The controller verifies:

- fresh goal/auto/goal-check match current generated files;
- fresh/proved manual preludes, scopes, declaration order, VC names, statements, and split mappings agree, with imports normalized by the same rules as Coq staging;
- every top-level VC completes the current plan's proof mode; aggressive splits are complete and start with `LLM_pre_process`, while unused LLM-route splits retain generated `Abort`;
- current sources pass the full Rocq check, including a case library not imported by goal-check, whose import closure must not reach current generated artifacts;
- no Admitted, extra axioms, unsafe typing, rollback controls, or forbidden lemmas appear, including unsafe commands inside Proof; new/reused helpers use current group suffixes;
- user-specified contracts retain their text-level freeze.

Dependencies use one plan format and the current native backend. History is reference material; old check results cannot replace current checks. An absent raw manual requires an absent proved manual. Zero VCs still require full parent/final checks. The current publication's original backup identifies newly added helpers.

## Cleanup, recovery, and outcome

The controller removes only exact current-module side-product files and side products in this run outside `_coq_builds`. Preserve sources, base-library artifacts, histories, reports, candidates, backups, and directories whose names resemble side products. Report scan failures and junction/reparse redirections.

A proof, structure, or freshness failure attempts safe rollback of this publication. Successful rollback makes `final-apply` the current action again. Conflicts stop automatic replacement. After pause or another task-status change, read the current action instead of publishing from an old check result. Only complete success returns `done`.
