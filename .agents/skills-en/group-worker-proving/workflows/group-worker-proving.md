# Group Worker Proving Workflow

## Current assignment

Use the current claim/handoff, this skill, and its named references. Read group_worker_input.md and relevant proof guidance. Do not read controller state, schedule siblings, or advance parent phases. Accidental extra reading is not itself a blocker; unauthorized writes and dependencies on current sibling output remain forbidden.

The handoff supplies fixed copied files, assigned witnesses, current proof modes, helper suffix, reports, and commands. These derive directly from current canonical files and the accepted plan. Each command reads current inputs; owners create no additional assignment records.

## Reuse history when useful

The handoff lists read-only historical locations in this run. Preparation copies only current canonical manual/library files; it never prefills historical proofs.

1. Search the previous proving round by current witness, proposition, and mode. Earlier proofs may also be in each annotation attempt's `before` directory. Do not scan other runs or read current sibling output.
2. Decide whether to copy, adapt, or redo a proof. Edit only assigned spans. Put needed helpers in the provided group library under the current suffix and update their references yourself.
3. Use the handed-off development/check commands against current definitions, imports, premises, and split routes. Historical `Qed` is not current acceptance.
4. Optionally record the source and decision in `proof_reuse.md`. Missing or empty notes never block delivery.

Changed propositions or modes, unfinished helpers, unsafe assumptions, and forbidden tactics are not ready proofs. Repair ordinary tactic failures in this group. Only a real premise/resource gap becomes an annotation blocker.

## Write boundaries and modes

Write only assigned top-level spans, aggressive-route split spans, the handed-off optional group library, authorized debug script, and reports. Statements, declaration order, prelude, unassigned proofs, canonical files, histories, plans, state, and siblings are read-only. Preserve current library seed declarations.

Aggressive routes prove every split first using LLM_pre_process, then use aggressive_pre_process and Goal_apply for each corresponding split lemma. Controller validation checks mode/completeness/Rocq, not exact Goal_apply spelling. LLM routes prove only the top-level VC with LLM_pre_process and retain generated Proof/Abort tokens in unused splits.

Reject entailer!, its pre_process alias, Admitted, extra Axiom, unsafe typing, rollback commands, and forbidden lemmas. Formatting/comments/line endings are not proof-token changes. The group directory ends with only the handed-off manual and optional library.

## Helpers and dependencies

Only a provided group_worker_lib may receive complete proved helpers and necessary official Rocq imports. Every new, copied, or adapted helper uses this group's suffix. Visibility is a reuse hint, not promotion. Merge concatenates checked proofs/helpers; owners repair naming conflicts. The controller never renames helpers or rewrites references.

Project dependencies come from current canonical inputs and controller preparation. Report new project dependency/spec/seed needs at that boundary; do not run raw Dune/Make/coqdep, alter load paths, import generated/current/sibling modules, or edit main libraries. An absent library stays absent.

## Check and deliver

Use handed-off debug/development/exact commands. The controller uses one dependency-plan format to refresh needed native dependencies and actually compile current source. Group checks cover their wrapper/dependencies; parent/final checks cover the complete combination.

Write explanation before the terminal report, stop writing, and let main finalize. `finalize-delivery` accepts the current report and files in one operation: completed requires structure and group Rocq success; annotation-gap requires exact VC/location data and safe ownership boundaries, without requiring the unprovable target to be complete. Repair keeps the same owner and directory; a report-only repair changes only notes/report, while formal repair remains within assigned spans. Each delivery is checked anew. Repeated tool errors have no automatic attempt-count gate or new round; repair from the diagnostic or report a concrete infrastructure blocker.

Success is exactly `{"status":"completed"}`. A blocker has exactly failure_class, kind, vcs, message, and repair_boundary; each VC has name, parent, and annotation_location.

A concrete annotation gap uses failure_class annotation-gap and nonempty group_worker_output.md explaining existing premises, the missing conclusion, attempted routes, and required annotation/spec changes. Its vcs identify actual assigned VCs in the current manual. This is this group's terminal outcome: stop unauthorized repair, without controlling siblings. Tool/report problems and ordinary tactic-search failures are not annotation gaps.
