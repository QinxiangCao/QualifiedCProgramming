# Paths and Commands

## 1. Controller Entrypoint

The only public entrypoint is:

```text
<python> .agents/scripts/verification-orchestrator/controller.py --main-root <root> <command> ...
```

Main executes only structured action `invocation` values. Owners execute only handoff `Commands`. Never invoke internal Python modules, raw symexec, raw Coq, Dune, or Make.

Use the exact cwd/argv and continue a live terminal session until real exit. Both exit zero and the final JSON success status are required.

Controller-owned Coq/build processes use one 900-second limit throughout the workflow, including annotation, VC checking, groups, parent verification, final check, and dependency preparation. Each runs in an independent process group. On timeout the controller explicitly terminates the whole group and force-kills anything still running; returning a timeout status alone is not sufficient.

## 2. Fixed Roots

```text
<root>/verification_runs/<run>/
<root>/reports/<run>/
```

`target_files` fixes the C file, formal directory, case library, goal, auto, manual, goal-check, case name, and active theory. The C stem may differ from the case stem; always use exact state/action paths.

Annotation sources live in the main root; `before/after` histories are controller-owned seals. VC checking may edit only temporary `Show.` commands in the main-root manual. Group workers write only fixed group copies. Never copy a group/merged candidate into the main root before final apply.

## 3. Annotation Commands

The handoff order is:

```text
coq-check --target-kind formal-case-lib-design
symexec
coq-check --target-kind formal-case-lib       # active library
```

An agent-written specification may change together with internal annotations and the case library in the current attempt. After changes, rerun `formal-case-lib-design` and symexec as needed. If a user-provided specification needs a change, the owner stops and gives the proposal to main. After user approval, main runs `unfreeze --run <run> --round <round>` and returns the proposal to the same owner. `unfreeze` is not an owner handoff command.

`symexec` transactionally rebuilds exact generated roles. On retry, the owner reads the current manual and fills VC comparisons; the proof manual is always read-only.

## 4. VC-Checking Commands

The owner may insert temporary `Show.` in the current manual and run the handed-off `coq-debug`. On successful delivery the controller runs `vc-checking-check-round`, regenerates a clean manual, and seals the clean manual/group plan.

## 5. Group Commands

Each handoff names a fixed directory, copied manual, optional group library, report paths, and controller commands for `group-development` and exact `group-check`. A worker may use development checks repeatedly; controller acceptance always runs the exact check. Never invoke a sibling command or substitute a main-root path.

If a previous round exists, every actually claimed worker searches it by current witness/helper names and reads only candidate proof blocks; it does not read every full manual. It may write a per-witness `proof_reuse.md`, but a missing or empty note is valid and never gates finalize. The current manual/plan remains authoritative, and the controller does not parse the Markdown.

## 6. Main-Owned Actions

Main uses action invocations for retry, annotation/VC acceptance, dependency preparation, proving preparation/previous-round handoff/scheduling, merge/parent verification, final apply/check, and pause/cancel/resume. After user approval, main runs `unfreeze` for the current annotation round.

## 7. Seals and Deletion Boundary

Before reading, writing, deleting, reusing, or validating, the controller re-derives each target and rejects aliases, symlinks, cross-run paths, and wrong rounds. Agents never delete run/report trees or edit manifests, state, histories, or seals. Final check owns cleanup.
