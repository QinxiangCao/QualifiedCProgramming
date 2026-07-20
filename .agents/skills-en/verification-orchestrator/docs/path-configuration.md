# Path Configuration

Controller-internal repository tooling owns every executable, cwd, include/search mapping, formal relative path, overlay, build directory, and fixed flag. An agent executes only commands already rendered in handoff Markdown.

## General rules

1. Annotation reads its independent `reports/<run>/annotation-attempts/annotation-attemptN/agent_input.md`; vc-checking reads the current round's `agent_input.md`; a group reads `group_worker_input.md`.
2. Execute each controller command exactly as rendered. Do not transcribe it, add flags, or change paths.
3. When a command fails, modify only formal content allowed by the current phase or the declared debug script, then rerun the same command exactly.
4. Report a path mismatch as a controller/handoff problem. Never try a different cwd or flags.

## Annotation

The handoff supplies:

```text
python3 .../controller.py --main-root <root> symexec --run <run> --round <round>
python3 .../controller.py --main-root <root> coq-check --run <run> --round <round> --target-kind formal-case-lib
```

The controller chooses the symbolic-execution driver from the runtime environment: `win-binary/symexec.exe` on Windows, `linux-binary/symexec` on Linux, `mac-arm64-binary/symexec` on Apple Silicon macOS, and `mac-x86-64-binary/symexec` on Intel macOS. It then derives generated paths from target C, adds canonical `-I` / `-slp` arguments, runs in the main root, and confines Coq builds to the current run's `_coq_builds`. An unknown platform or macOS architecture fails explicitly and never defaults to the Ubuntu binary.

The first annotation handoff starts the one agent. Each later handoff lives in a new `annotation-attempts/annotation-attemptN`; the main agent first completes the blocker summary/reflection template and passes `annotation-summary-ready`, then sends the append action to the original target. Old reports are not overwritten. Run-root `annotation_history/<attempt-id>/` stores only formal before/after states; the history command is read-only bookkeeping and does not execute files.

The annotation handoff also supplies two `timing-stage` commands around annotation-checking. The owner wraps its complete review, repair, and recheck in the start/finish pair. Every phase/group owner's delivery and return uses `mark-attempt-started` / `mark-attempt-returned`, allowing the timing summary to derive real boundaries.

Final freshness reuses the symbolic-execution helper with fixed output root `reports/<run>/final-check/symexec-refresh/`; it does not overwrite the proved manual. The controller diagnostics-splits the raw refreshed manual inside that directory just as during annotation acceptance, then compares cleaned witness names/statements. The agent does not manipulate refresh files.

## Group

The group handoff supplies `coq-debug` and `coq-check --target-kind group-check --group <id>`. From current state and the compact manifest, the controller derives:

- A main-root formal-source mirror and base `.vo` files from the prerequisite full make.
- Two overlays mapping the copied manual and `group_worker_lib` to formal relative paths.
- A group-unique `_coq_builds/<round>/<group>/src`.
- A build-only group-check wrapper and assigned witnesses.
- The exact debug-script path.

The group directory itself contains only two copied formal files. A group worker does not manipulate overlay arguments or internal helpers.

## Parent and final

Coq tooling resolves executables through `SeparationLogic/CONFIGURE` and the Makefile's `COQBIN` / `SUF` convention. Reuse of base `.vo` files is a system-wide rule across runs: annotation, group, parent, final, and debug entries read products for every Makefile `-R` / `-Q` load path from the same main-root full make and stage them into each check build. They do not cache by source digest, Coq version, or fixed flags and do not recompile base sources. A missing required base `.vo` is an explicit failure. The current target's lib/goal/auto/manual/check modules always exclude old `.vo` files and rebuild from current source or overlays.

Parent verification overlays the proving-merged manual and `proving_merged_lib` on the main-root mirror and runs the full check in `_coq_builds/<round>/parent/src`. Final-check first has the controller remove old Coq side products for the current target and non-`_coq_builds` current-run areas while preserving base `.vo` files, then checks the applied main-root files in `_coq_builds/final-check/src` and rescans the same target/run boundaries afterward. An agent never deletes or moves these files manually.

## Forbidden

Never call `symexec_tooling.py` / `coq_tooling.py`, raw symexec, raw `coqc` / `coqtop`, Dune, Rocq MCP, `coqc -o`, or an `_CoqProject`-derived command directly. Never construct the driver, `-R`, include/SLP, cwd, overlay, or build path yourself.
