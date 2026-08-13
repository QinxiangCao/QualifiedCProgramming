# Annotation Filling and Repair Workflow

This workflow is performed by the sole, persistently reused annotation owner within a run. You modify the current main-root annotation candidate directly and complete `annotation-checking` within the same agent work session. This file already contains the process contract needed by this role; do not read the orchestrator or another role's skill to learn the "next step."

## 1. Role boundary after claim

The main agent has already claimed the delivery using the controller-returned `claim_invocation`. The start or append message you receive must contain `Role`, `Owner`, `CWD`, and the verbatim `Claim message`:

- Always work in the given `CWD`; do not guess the repository, run, or attempt path.
- Treat the `Claim message`, the current `agent_input.md` it identifies, and the original materials listed there as the authoritative input for this attempt.
- The controller has already bound the owner name and attempt; do not run `claim-attempt`, `step`, or `finalize-delivery`, change owner, or create another annotation agent.
- Execute only this role's commands explicitly provided by the handoff. Do not infer a missing command, parameter, interpreter, path, or next-phase action from state.
- The current main-root target C file, optional formal files, and controller-refreshed generated files are the current candidate. Old-session memory, old-attempt snapshots, and group copies are not editing baselines.

If the start message lacks any of those four sections, or a current handoff file cited there does not exist, stop writing and report the missing item to the main agent; do not scan run state or orchestrator documents to reconstruct the handoff.

## 2. Read the current attempt in full

### First attempt

Read in this order:

1. this skill and this workflow;
2. `annotation-checking/SKILL.md` and its workflow;
3. the current `agent_input.md`;
4. the handoff-listed `problem_context`, target C file, present `formal_case_lib`, current generated files, and required original blocker materials;
5. the knowledge documents directly navigated by the two annotation skills, plus examples within this skill explicitly selected by the handoff.

Record from `agent_input.md` the exact target paths, which optional roles are present/missing, the permitted report paths, and Commands. The path, case stem, and C stem may differ; use only the exact paths in the handoff and do not derive another formal file from a filename or directory name.

### Later retries

Every append is still handled by the same agent target. Reread all of the following in full each time:

1. both annotation skills and their workflows;
2. the new attempt's complete `agent_input.md`;
3. its five-part feedback summary: blocker conclusion, causal analysis, previous-attempt reflection, required repair, and scope decision;
4. every original `group_worker_report.json`, `group_worker_output.md`, or other current-attempt Markdown/JSON blocker cited item by item by that summary;
5. the current main-root target files.

Original blockers and current files take precedence over old-session memory. Do not continue modifying from only the
summary or the previous diff. Reassess the overall relationship among the mathematical specification, function
contracts, loop invariants, assertions, and call instances only when the controller handoff explicitly sets
`consider_broader_refactor: true`; do not infer that requirement from the annotation-iteration directory ordinal.

### Handle annotation gaps from multiple groups at once

One retry may aggregate annotation gaps reported by multiple groups in the same proving round. They constitute one complete feedback delivery and must each be closed within this attempt:

1. Build a coverage checklist from the five-part summary; for every item retain the original group, witness, location, message, repair boundary, and corresponding `group_worker_report.json` / `group_worker_output.md` path.
2. Read every original blocker cited by the checklist in full. Do not read only the first item or treat different witnesses with similar wording as already covered.
3. Map each gap to the mathematical specification, function contract, loop invariant, assertion, or call instance that needs review. Multiple gaps may share one root cause and one repair, but retain each source citation independently.
4. Form an integrated repair that covers every item before editing the candidate; do not finish the attempt after repairing the first group.
5. After completing the checking loop, compare the result against every original blocker and confirm which repair covers each one. Concisely record the itemized citations, shared root causes, and dispositions in `agent_output.md`.

These blockers are inputs to annotation repair only. Their original reports, group manual/lib, copies, and sealed proofs are all read-only; do not enter a group directory to continue proving, decide proof reuse, or infer how the controller will next schedule or merge. If the feedback omits an original citation that it claims exists, or the citations contain a conflict that cannot be verified from the current files, stop the affected edit and tell the main agent exactly what is missing or conflicting; do not scan unauthorized reports to fill the gap.

## 3. Write boundary

Writes are allowed only to:

- annotations in the handoff-specified main-root target `.c`; do not modify the C algorithm implementation;
- mathematical specifications paired with the annotations in the main-root `formal_case_lib` that already existed when the handoff began;
- exact generated roles transactionally refreshed by the current attempt's handoff `symexec` command; never hand-edit generated files;
- the current attempt's `agent_report.json` and optional `agent_output.md`.

If `formal_case_lib` is marked missing, keep it missing: do not create a placeholder or same-named/differently named lib, and do not run a check applicable only to that lib. An optional generated role being missing at the start is not a failure; only the controller's `symexec` may determine its refreshed present/missing state.

Everything below is read-only and cannot be modified under the pretext of "repairing annotations":

- `agent_input.md`, annotation history, `before/`, `after/`, controller state/event, and original blockers;
- manual proof bodies, group files, public helpers, `proving_merged`, and other formal/shared libs;
- controller scripts and every skill's scripts, workflows, or knowledge documents.

Do not add `Admitted.`, an additional `Axiom`, a forbidden lemma, an unsafe shortcut, or an import of a current generated artifact for this run. The controller computes changed files, digests, versions, command results, and acceptance decisions; do not copy them into owner JSON.

## 4. Form a complete candidate

### 1. Understand the computational objective

First read `problem_context`, the target C file, existing specifications, and actual call relationships. Determine the inputs, outputs, resources that change, and pure facts that must survive loops, branches, and function calls. A short background, incomplete initial annotation, or missing `formal_case_lib` is not a stopping condition; form the smallest sufficient candidate within the permitted boundary.

### 2. Review the mathematical specification first

If `formal_case_lib` is present, first confirm that its specification can be understood independently of the current C control flow, and then design predicates and annotations:

- Do not disguise a translation of the loop, state machine, or one-step transition as a Rocq algorithm serving as a functional specification.
- For a finite result uniquely determined by the input, prefer a transparent specification value or finite list.
- Before using `exists f : A -> B, ...` or a similar function witness, confirm that it represents a genuine mathematical object or proof interface rather than leaving avoidable search to a proof worker.
- Put stable business-level mathematical facts in the existing `formal_case_lib`; keep local run-time properties in the C annotation.

If `formal_case_lib` is missing, do not create a new lib. Complete the C annotation using the current permitted and existing specification interfaces, and mention the optional role's absence in `agent_output.md` instead of treating it as a blocker.

### 3. Modify the C annotation in coordination

Check and complete, in order:

1. function contracts;
2. loop invariants;
3. pure facts needed by branches, loops, and exits;
4. function-call instances and existential witnesses;
5. necessary ordinary `Assert` statements.

An invariant must connect initialization, preservation, and exit, and express hidden algorithmic properties such as prefixes, suffixes, intervals, candidate optima, feasibility, or shape. Do not weaken a postcondition, contract, or invariant merely to reduce VCs.

Use ordinary `Assert` statements only for function-call boundaries, semantic-stage transitions, path merges, or exit bridges. Review each added, retained, or modified ordinary `Assert` according to the knowledge document and record `keep`, `remove`, or `revise` in `agent_output.md`; record `none` when there is no ordinary `Assert`.

### 4. Integrated review

Confirm that the mathematical specification, function contracts, loop invariants, assertions, and call instances describe the same functional relationship; when repairing one interface, review all callers and exit bridges in sync. For a retry, recheck the current five-part summary and the coverage checklist for every original blocker item by item.

## 5. Controller command contract

The Commands in `agent_input.md` provide complete controller commands with the interpreter, cwd, case, paths, flags, and build/overlay already bound. Every command must be:

- run unchanged with the handoff's `CWD`; prefer a direct system-terminal call; if terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or calls exactly one `tools.write_stdin` to continue the same live session (or uses the runtime-documented normalized name for that same terminal operation), and only forwards the result;
- launched with the complete command/argv, every argument, interpreter, and `CWD` unchanged, or continued with the same session identifier; a normalized equivalent is allowed only when its input shape accepts those values unchanged, and must not serialize argv into shell text, reparse the command, or add quoting;
- executed with the returned argv interpreter and every argument unchanged, without another `uv run` wrapper;
- kept free of a second tool call in the bridge cell, command construction, alteration, sequencing, parallelization, or interpretation, other JavaScript/Python orchestration, generated shell/PowerShell/Python scripts, `sh -c`, pipelines, command substitution, background processes, and other wrappers;
- executed without changing cwd, environment, flags, include paths, SLP options, drivers, overlays, build paths, or output paths;
- left as a controller command rather than replaced with an internal controller module, raw symbolic execution, raw Coq, Dune, Make, Rocq MCP, or a self-constructed equivalent.

Preserve and continue every outer cell and inner process/session identifier until the actual command exits. If a transparent bridge returns a running `functions.exec` cell, resume only that cell with `functions.wait` until its one terminal operation returns. Empty output, the first yield, or `Script completed` does not independently mean success. A command passes only when its exit code is 0 and the controller's final JSON has `status` equal to `passed`.

Work in this order:

1. Run the current attempt's `symexec` verbatim. It is the only way to refresh generated roles; on failure, repair only the permitted annotations/specifications and rerun the same command.
2. Only if `formal_case_lib` is present and the handoff provides the corresponding invocation, run `coq-check --target-kind formal-case-lib` verbatim. Do not invent that invocation yourself.
3. Enter `annotation-checking` and follow its workflow for candidate checks and the checking timing invocations provided by the handoff.

Entering checking does not itself require repeating the same set of commands if they just passed and no formal/generated write has occurred since then. Only after checking finds a problem and modifies the candidate should the affected commands be rerun according to its workflow.

After a command fails, use its complete output to locate a cause within the permitted boundary. A single tactic failure, a repairable specification problem, or a rerunnable controller command is not `blocked`. Do not hand-edit generated files, weaken the functional specification, or modify a proof to make the command pass.

## 6. Annotation-checking repair loop

After forming a candidate and completing the latest owner checks above, invoke `annotation-checking` within the current agent; do not spawn a new agent. If checking finds a repairable problem:

1. Return to the corresponding mathematical-specification or C-annotation layer in this workflow and repair it.
2. Rerun the affected `symexec` and the present `formal_case_lib` check verbatim.
3. Repeat the full annotation-checking checklist.
4. For a retry, recheck all aggregated blockers rather than only confirming that the latest error disappeared.

Repeat until the current candidate satisfies the checking conditions or a real blocker that cannot be repaired within the permitted boundary has been established. The owner's checking conclusion means only that the candidate can be delivered; it does not mean the controller has accepted it.

## 7. Reports, stop-writing boundary, and finalize repair

On success, `agent_report.json` contains only:

```json
{
  "status": "completed"
}
```

When work genuinely cannot continue, write `blocked` and add exactly one complete `blocker` containing only this contract's required `failure_class`, `kind`, `location`, `message`, and `repair_boundary`. Use `stale` for version invalidation and `compact-error` for context compaction. Do not disguise multiple diagnoses as multiple JSON blockers; put detailed sources and itemized analysis in `agent_output.md`, while the one blocker must completely state the boundary that truly prevents this attempt from continuing.

`agent_output.md` may record the problem interpretation, mathematical-specification rationale, higher-order-witness judgment, branch control, ordinary-`Assert` review, repair summary, and, for a retry, citations and coverage conclusions for every original blocker. It is read by people and later repair work and does not control acceptance.

After writing the reports, stop modifying every formal/generated/report file and notify the main agent that it can execute the `finalize_invocation` exactly as given in the claim response or `waiting_for`. The main agent executes that invocation; the owner neither runs nor rewrites it.

If the controller returns `report-repair-required`:

1. The current delivery remains `running`, and the current attempt, owner, and agent target all remain unchanged; do not create a new attempt or claim again.
2. Read the exact mismatch appended by the main agent and the current-attempt materials it cites; do not infer the reason from the orchestrator or state.
3. Repair the mismatch only within this workflow's write boundary. If only report repair is requested, do not touch the formal/generated candidate after the stop-writing boundary; if a permitted file truly needs repair, rerun the affected owner checks before updating the report.
4. Stop writing again and notify the main agent. The main agent reruns the original `finalize_invocation`; the owner still does not execute finalize.

`report-repair-required` does not create `after/`, start a new annotation round, change owner, or justify starting downstream work. This role's work ends when the controller accepts finalize; do not independently run an acceptance check, proof, merge, apply, cleanup, or final check.
