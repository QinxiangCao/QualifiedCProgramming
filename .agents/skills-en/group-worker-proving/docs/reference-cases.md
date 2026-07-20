# Reference-Case Scope

Reference cases are only for learning proof style, tactic sequences, and helper-lemma shapes.

## Scope

Prefer:

- `SeparationLogic/examples/LLM_bench`
- `QCP_demos_LLM`

Reading `QCP_demos_human` is allowed but not recommended. Read-only inspection of a human case does not itself create a blocker. Acceptability of the current group depends only on assigned witnesses, helper/import boundaries, the fixed group-check bound to the current `source_goal_version`, and later parent verification and final-check. Reject under the contract only when formal files introduce a library, import, generated artifact, or other formal dependency forbidden by the phase contract.

## Useful material

- Similar array split/merge proofs.
- Similar `replace_Znth` / `sublist` / `Zlength` helpers.
- Similar `safeExec` normalization.
- Similar string-memory proofs.
- Similar data-structure predicate unfold/fold proofs.

## Do not copy

- File-handoff names outside the current Markdown handoff / compact JSON result contract.
- The old practice of placing helper lemmas in `*_proof_manual.v`.
- `Admitted.`.
- A new `Axiom`.
- A manual patch to a generated file.

If a reference puts a helper in a location forbidden by the current contract, put the helper in `group_worker_lib` and let parent verification merge it.
