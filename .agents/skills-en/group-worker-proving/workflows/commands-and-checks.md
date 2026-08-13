# Group Commands and Checks

## 1. Only external entries

Use only the exact argv and cwd rendered in the current `group_worker_input.md`; do not derive them from a filename, manifest, repository build metadata, or historical command. The only Rocq external entries the group-worker may execute are:

- `controller.py coq-debug`
- `controller.py coq-check --target-kind group-development`
- `controller.py coq-check --target-kind group-check`

The main agent runs `claim-attempt` before the worker starts and the handoff-bound `finalize-delivery` after the worker stops writing. The group-worker does not run or reconstruct claim/finalize itself and does not invoke `step`, merge, parent verify, annotation feedback/retry, or any other controller action.

Run each line unchanged. Prefer a direct system-terminal call. If the runtime exposes terminal operations only through `functions.exec`, use a transparent bridge: each cell may await exactly one `tools.exec_command` to launch, or call exactly one `tools.write_stdin` to continue the same live session (or use the runtime-documented normalized name for that same terminal operation), and may only forward its result. When launching, pass the complete command/argv, every argument, and cwd unchanged; when continuing, preserve the same session identifier. Do not serialize argv into shell text, reparse the command, or add quoting. Do not use:

- a second tool call in a bridge cell, or command construction, alteration, sequencing, parallelization, or interpretation;
- other JavaScript/Python orchestration;
- a generated shell/PowerShell/Python script;
- another `uv run` layer;
- `sh -c`, a pipeline, command substitution, or a background process;
- direct invocation of `coq_tooling.py`;
- raw `coqc`, `coqtop`, `coqc -o`, Dune, or Rocq MCP;
- a command derived from repository build metadata;
- a hand-built cwd, flag set, overlay, or build path.

Preserve and continue every outer cell and inner process/session identifier until the actual command exits. If a transparent bridge returns a running `functions.exec` cell, resume only that cell with `functions.wait` until its one terminal operation returns. Empty output, an initial yield, and `Script completed` do not mean that the controller or Rocq has finished. A check passes only when the exit code is 0 and the controller JSON contains `status: passed`.

## 2. Directories and overlays

The controller has rendered this group's results from state, the accepted plan, base manifest, and group manifest into the handoff. When it executes a command, it derives:

- the overlay from copied manual to the formal manual relative path;
- when the handoff provides `group_worker_lib`, its overlay to the `formal_case_lib` relative path;
- exact build `_coq_builds/<round>/<group>/src`;
- a separate incremental development build for the same group;
- the group-check wrapper and assigned witnesses;
- one debug-script path.

The group directory contains only the copied manual and the optional `group_worker_lib` already provided by the handoff. When `group_worker_lib` is missing, do not create a library overlay or add a helper/import. `public_helper_snapshot.txt` is not an active library, is not an overlay, and must not be imported.

Before creating, cleaning, or writing a build, the controller rejects symlinks, junctions, reparse points, and non-regular children. Output is written through an unpredictable same-directory temporary file and atomic replacement so it cannot be redirected outside the run.

## 3. Shared checks

Development, exact, and mandatory post-finalize validation use the same structural checker. Every invocation rechecks:

- current version;
- accepted plan;
- base manifest, group manifest, and seed seals;
- the frozen public snapshot and reuse-source digest;
- manual declaration order and statement tokens;
- assigned and unassigned proof tokens;
- `LLM_pre_process` split blocks;
- helper suffix, seed, import, and forbidden rules;
- no `Admitted.`, extra `Axiom`, or forbidden lemma in copied formal files;
- fixed-directory location and lack of formal-file drift.

Comments, whitespace, CRLF/LF, trailing spaces, and EOF-newline differences are excluded from token comparison.

### Development

`group-development` allows temporary `Abort.` only in this group's editable proof spans and skips final proof-completeness and route-connection requirements. It compiles the copied manual incrementally for proof-search feedback. It cannot support `completed` or controller acceptance.

### Exact

Exact `group-check` additionally requires:

- every assigned top-level VC to be complete;
- every aggressive split goal to be complete;
- every `LLM_pre_process` split block to remain `Proof. Abort.`;
- every top-level proof to use its accepted `proof_mode`;
- the fixed group wrapper to pass Rocq.

The group worker uses only `Goal_apply` to apply split lemmas in an aggressive top-level VC, but this proof rule is not a tactic-text check.

### Mandatory validation after finalize

After the worker has stopped writing, the main agent runs `finalize-delivery`. The controller first seals `group_worker_report.json`, the copied manual, and `group_worker_lib` when applicable, then performs mandatory validation matching the reported terminal result over those exact bytes and compares the seals again afterward:

- `status: completed` must pass the full structure, proof-completeness, route, and Rocq checks. Only success marks the group accepted.
- `blocker.failure_class: annotation-gap` must pass the five-field blocker contract, witness/location traceability, fixed write boundary, statement/unassigned/mode protection, helper/import/safety rules, and seal checks. An assigned proof left incomplete because of the gap must not be disguised as `completed`, and this terminal result is not required to pass the complete group Rocq target that the gap makes unprovable. The controller seals it as a structurally legal, traceable blocked terminal result available for conditional reuse in a later round.
- Other blockers retain their existing structural checks, in-place repair, retry-exhaustion, or terminal semantics; the `annotation-gap` aggregation mechanism does not change them.

This is the single mandatory group validation. Worker development or exact results are not written to the final report and do not replace controller acceptance or a blocked-seal conclusion. If validation returns only a report-contract repair, the formal seal remains unchanged; the same owner repairs only the report and reruns the original finalize, without modifying the proof/library.

## 4. Fixed selected dependencies and the current build

After annotation acceptance, the controller has run one `dune-build` action for the exact goal-check target and sealed the Dune or Makefile snapshot according to the `_build` directory. A group-local build only:

1. revalidates snapshot, dependency-source/artifact, selected-configuration, and applicable run-Makefile digests;
2. stages the actually reachable sources among the persisted five current case identities, together with this group's overlay, into the fixed local build;
3. compiles current modules according to the fixed current edges in the snapshot;
4. reads snapshot-bound dependency `.vo` files through absolute `-R/-Q` mappings into the selected base (Dune `_build/default` or Makefile main-root `Rocq/`);
5. binds the dependency artifact digest into the current cache and debug/reuse seal.

The worker neither analyzes dependencies nor supplies a target, and does not invoke Dune, Make, or `coqdep`. Proof-time source may continue to use project imports already in the snapshot and imports from the installed Rocq standard library. A new project import outside the snapshot returns a mode-specific dependency-not-prepared failure; a later annotation retry creates a new accepted source and snapshot. This group cannot dynamically extend the dependency version.

Current ownership comes only from the persisted case identity; it is not inferred from the C stem, a same-directory prefix, a helper name, or an import. Another program or differently named library in the same directory is readable only when it belongs to the snapshot closure. Each current dependency must have a local `.vo` in this build before its consumer compiles or debugs.

Development and mandatory checks share a run-local cache for current prerequisite artifacts. Its key includes source, fixed current edges, tools, configuration, flags, and the accepted dependency digest. A miss, deletion, or corruption recompiles only current prerequisites from source. The mandatory check's final target always runs.

These failures must remain precise and may not fall back to a whole-workspace target, dependency-source compilation during a check, or an old source-tree current `.vo`:

- accepted dependency source, artifact, or configuration drift;
- a project import outside the snapshot;
- an inconsistent current edge, source, or local artifact;
- a dynamic `Load` or load-path command appears;
- a path, mapping, or build-plan conflict exists.

## 5. Time limits and processes

All child processes started by one `coq-check` or `coq-debug` share a 1800-second deadline. Snapshot validation and staging time is deducted from the time remaining before the next child starts.

The controller places tools in an independent process group and terminates the entire group at timeout, with bounded output draining. A worker must not bypass this limit through a raw process or an unbounded substitute command.
