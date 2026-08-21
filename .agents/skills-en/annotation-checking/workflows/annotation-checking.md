# Annotation Candidate Checking Workflow

This workflow is performed by the run's sole annotation owner within the same agent work session. It checks the current candidate, sends repairable problems back to `annotation-filling`, and repeats the checks after repair; it does not create a new agent, decide controller acceptance, or require reading the orchestrator or another role's skill.

## 1. Starting conditions and current inputs

All of the following must be true before starting:

- Both annotation skills and their workflows have been reread in full.
- The current attempt's `agent_input.md`, the original materials named by the handoff, and the current main-root target files have been read in full.
- `annotation-filling` has formed a candidate, or has completed one integrated repair according to the current retry's five-part summary.
- The exact `symexec` command for the current attempt, and the checking invocation for a present `formal_case_lib`, come from the handoff's Commands; an invocation is neither needed nor permitted to be invented for a missing optional role.

Use the current main root for both a first attempt and a retry. A retry must not rely on old conversation memory; if its feedback aggregates annotation gaps from multiple groups, first confirm that every evidence path the handoff lists has been read in full, and retain an itemized coverage checklist containing each group, witness, location, message, and repair boundary. The handoff lists only the files an owner delivered and the controller sealed; a file it does not list does not exist, so do not go looking for one.

If required controller-handoff fields, current inputs, or an explicitly cited original blocker are missing, stop checking and report the exact missing item. Do not scan controller state, other reports, group directories, or orchestrator documents to reconstruct the context.

## 2. Shared write and command boundary

During checking, writes remain limited to the target C annotations, mathematical specifications in the `formal_case_lib` that existed at the start, generated roles refreshed by the handoff's `symexec`, and the current attempt's reports/notes. Do not modify the C algorithm, hand-edit generated files, create a missing lib, or modify manual proofs, group files, annotation history, controller files, or another formal/shared lib.

Run the checking timing, `symexec`, and `coq-check` invocations from the handoff unchanged with its `CWD`. Prefer a direct system-terminal call. If the runtime exposes terminal operations only through `functions.exec`, use a transparent bridge. Each cell may await exactly one `tools.exec_command` to launch the command, or call exactly one `tools.write_stdin` to continue the same live session (or use the runtime-documented normalized name for that same terminal operation), and may only forward its result. When launching, pass the complete command/argv, every argument, the bound interpreter, and `CWD` unchanged; when continuing, preserve the same session identifier. Use a normalized equivalent only when its input shape accepts those values unchanged; do not serialize argv into shell text, reparse the command, or add quoting.

Do not call a second tool in a bridge cell, add other JavaScript/Python orchestration, construct, alter, sequence, parallelize, or interpret commands, add another `uv run`, use a generated shell/PowerShell/Python script, `sh -c`, a pipeline, command substitution, background execution, or another wrapper. Do not construct cwd, flags, include paths, SLP options, overlays, build paths, or targets yourself, and do not substitute internal modules, raw symexec, raw Coq, Dune, Make, or Rocq MCP.

Preserve and continue every outer cell and inner process/session identifier until the actual command exits. If a transparent bridge returns a running `functions.exec` cell, resume only that cell with `functions.wait` until its one terminal operation returns. Empty output, an initial yield, or `Script completed` does not by itself mean success. The corresponding check passes only when the exit code is 0 and the controller's final JSON has `status` equal to `passed`.

If the handoff provides annotation-checking timing invocations, run start only when this checking work actually begins and run finish only when it actually ends, executing each verbatim. Timing does not control the candidate conclusion; do not estimate or fill in time, or add an agent round trip merely for timing.

## 3. Checklist

### 1. Mathematical specification quality

If `formal_case_lib` is present, check whether its specification describes the business-level mathematical semantics independently of the current C control flow:

- The input/output relation in a function contract is sufficient to express the real result, not only a range or shape.
- Declarations do not copy loop locals, one-step transitions, or control flow into a Rocq algorithm.
- When a direct proof encounters an algorithm-mirror specification, it must be redesigned; difficulty proving it is not a reason to retain the mirrored specification.
- A refinement proof may retain the `safeExec` or monad specification required by the proof type, but local run-time facts still belong in the annotation.
- It contains no `Admitted.`, additional `Axiom`, forbidden lemma, unsafe shortcut, or import of a current generated artifact.

If `exists f : A -> B, ...` or a similar higher-order witness appears, compare a transparent specification value, a finite list, and a function representation. Retain the function representation only when it has a real advantage for the domain, valid range, or proof interface, and explain the reason in `agent_output.md`.

If `formal_case_lib` is missing, confirm that the candidate did not create a placeholder or differently named replacement; continue checking the existing specification interface and C annotations, and do not treat the missing role itself as failure.

### 2. End-to-end annotation connection

Check each of the following:

- The C function contract references the correct, currently permitted specification declaration.
- A helper/check function's `Ensure` provides the decision property actually needed by the caller, rather than only a return-value range.
- Every loop invariant covers initialization, preservation, and exit, and connects the processed state to the postcondition.
- Branch conditions, loop bounds, call instances, existential witnesses, resource changes, and exit states can be closed.
- After modifying a callee contract, all caller instances, preconditions, and exit bridges have been reviewed in sync.
- Arrays and strings preferentially reuse existing predicates such as `IntArray`, `UIntArray`, `CharArray`, `PtrArray`, `store_string`, `store_stringLit`, and `GlobalStrings`; the choices for writable buffers, read-only literals, and local `char[]` are consistent.

Do not hide a VC by weakening a postcondition, contract, or invariant, and do not move a local fact that belongs in the annotation into a proof body.

When the handoff carries `## Frozen specification`, the listed functions' specs and every existing `Extern Coq`, `Import Coq`, and case-lib declaration must not change; review only confirms they are verbatim unchanged, and any modification is caught by the controller's comparison before acceptance.

### 3. Ordinary `Assert`

Give each ordinary `Assert` that is neither an invariant nor a postcondition an individual `keep`, `remove`, or `revise` decision:

- Retain only assertions that serve a function-call boundary, semantic-stage transition, path merge, or exit bridge.
- Remove assertions that mechanically repeat an invariant, postcondition, or current symbolic state.
- Place an assertion where its semantic fact has just been established and later code still needs it.
- If there is no ordinary `Assert`, record `none` in `agent_output.md`.

### 4. Itemized coverage for an aggregated retry

If the current retry contains one or more annotation blockers, verify the coverage checklist item by item:

1. Every original group/witness/location points to a contract, invariant, assertion, call instance, or mathematical specification reviewed in this repair.
2. A shared root cause may be repaired once, but every original evidence citation still has its own conclusion.
3. The current generated results do not merely eliminate the first blocker while omitting gaps from other groups in the same round.
4. `agent_output.md` concisely explains each source, the shared root cause, the corresponding repair, and the review result.

Check only blockers explicitly cited by the handoff. Do not enter a group copy to extend a proof, edit an original report, scan history for extra sources, or decide proof reuse, next-round grouping, or scheduling.

### 5. Freshness of controller owner checks

When entering this workflow for the first time, confirm that `annotation-filling` ran and passed the following verbatim in handoff order after the latest formal/generated write:

1. the current attempt's `symexec`;
2. its `coq-check --target-kind formal-case-lib` invocation, only when `formal_case_lib` is present.

If both already passed against the current candidate, do not repeat them merely because checking began. If checking modifies the target C annotations or present `formal_case_lib`, return to `annotation-filling`, rerun `symexec` and the applicable lib check, and then restart this checklist from the beginning. `symexec` is the only way to refresh generated roles; on failure, repair only within the permitted boundary and do not hand-edit generated results. Owner checks establish only that the controller can refresh the current candidate stably in main root; they do not mean that the controller has accepted it.

### 6. Write-boundary review

Finally confirm that modifications landed only in the current attempt's permitted target C annotations, present `formal_case_lib`, exact generated roles refreshed by the controller, and report files. Do not declare changed files, digests, versions, check output, or an acceptance conclusion in JSON; the controller computes them mechanically from the sealed before/current states.

## 4. Repair loop and conclusion

When any checklist item finds a repairable problem:

1. Locate the problem in the mathematical-specification or C-annotation layer of `annotation-filling`.
2. Complete the coordinated repair within the shared write boundary.
3. Rerun `symexec` and the applicable `formal_case_lib` check verbatim.
4. Restart this checklist from the beginning, including coverage of every aggregated blocker.

A single tactic failure, a specification that can still be improved, an ordinary tool failure, or a rerunnable controller invocation cannot immediately be reported as `blocked`. Form a real blocker only when the problem truly cannot be resolved within this role's permitted file and command boundaries.

After all items pass, write `agent_report.json` and optional `agent_output.md` according to the `annotation-filling` workflow, finish timing if the handoff provides it, stop modifying formal/generated/report files, and notify the main agent that it can execute the original `finalize_invocation`. Success JSON may only be `{"status":"completed"}`; blocked JSON may add only one complete blocker containing `failure_class`, `kind`, `location`, `message`, and `repair_boundary`.

## 5. When finalize requests report repair

`finalize-delivery` is executed by the main agent, not by the annotation owner. If the controller returns `report-repair-required`:

- The delivery remains `running`; keep the same attempt, owner, agent target, and original finalize invocation.
- Read the exact mismatch appended by the main agent and repair it only within the shared write boundary.
- If the mismatch concerns only the report, leave the formal/generated candidate unchanged; if a permitted file truly requires repair, rerun the affected commands and this checklist.
- Stop writing again and let the main agent rerun the original finalize; do not claim, finalize, create a new round, or run a downstream check yourself.

Passing this workflow means only that the candidate can be returned to the main agent. The controller alone decides whether finalize accepts it and performs every subsequent state transition; this role neither predicts nor performs them.
