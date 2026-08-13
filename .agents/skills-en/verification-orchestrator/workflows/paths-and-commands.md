# Paths and Commands

The controller owns executable, cwd, include/search mappings, formal relative paths, overlays, build directories, and fixed flags. Main executes the invocation carried by action JSON. A subagent executes commands already rendered into its handoff Markdown. Neither constructs a command.

A human uses uv only to enter the public boundary from the repository root:

```text
uv sync --frozen --python 3.12
uv run --frozen --python 3.12 python .agents/scripts/verification-orchestrator/controller.py ...
```

The public entry rejects non-3.12 interpreters before parsing or writing. Controller-generated invocations then use the validated absolute `sys.executable` from that environment; main and owners do not wrap internal actions in uv.

The root-level `pyproject.toml`, `uv.lock`, and `.python-version` manage only the agent system. `mcp/qcp-mcp` remains an independent uv project and does not share the environment. For Windows first launch and path differences, see the repository-root `AGENTS_WIN.md` and the [Windows adaptation guide](../docs/windows.md); they do not change this file's public command contract.

## 1. General execution rules

1. For a `main-owned-action`, main submits `invocation.argv` unchanged with `invocation.cwd`.
2. For a spawn/append action, main first submits `claim_invocation.argv` unchanged with `claim_invocation.cwd`.
3. Annotation reads its independent `annotation-attempts/annotation-attemptN/agent_input.md`.
4. VC-checking reads the current round's `agent_input.md`.
5. A group-worker reads `group_worker_input.md`.
6. A subagent sends every rendered controller command unchanged to the system terminal.
7. Do not transcribe it, add a flag, change a path or cwd, or substitute an interpreter.

The authoritative invocation shape is:

```json
{
  "argv": ["/absolute/python", "/absolute/controller.py", "--main-root", "/absolute/root", "step", "--run", "case-run"],
  "cwd": "/absolute/root"
}
```

`argv` is an array of strings, not a shell string. Every parameter is expanded; there are no `<run>` or `<owner>` placeholders. Human-readable action names explain the work but are not a source for rebuilding the command. See the [Controller CLI](../docs/controller-cli.md) for the complete public interface.

Prefer a direct system-terminal call. If the runtime exposes terminal tools only through `functions.exec`, use a transparent bridge. Each cell must:

- await exactly one `tools.exec_command` to launch the command, or call exactly one `tools.write_stdin` to continue the same live session; the runtime-documented normalized name for that same terminal operation is also allowed;
- when launching, pass the complete command/argv, every argument, and cwd unchanged; when continuing, preserve the same session identifier; only forward the result;
- use a normalized equivalent only when its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting;
- never call a second tool in the cell or construct, alter, sequence, parallelize, or interpret commands.

Otherwise, do not use:

- other JavaScript/Python orchestration;
- a generated shell/PowerShell/Python script;
- another `uv run` layer;
- `sh -c`;
- a pipeline;
- command substitution;
- a background process;
- another wrapper that invokes a terminal tool again.

Do not imitate controller behavior in a new script.

Preserve and continue every outer cell and inner process/session identifier until the actual command exits. If a transparent bridge returns a running `functions.exec` cell, resume only that cell with `functions.wait` until its one terminal operation returns. Empty output, an initial yield, and `Script completed` only mean that an outer call yielded; they do not mean the controller, symexec, or Rocq has completed.

A check passes only when both conditions hold:

- the terminal process exits with code 0;
- the controller JSON contains `status: passed`.

On failure, modify only formal content authorized for the current stage or the designated debug script and rerun the same command. A path mismatch is a controller/handoff problem; do not probe alternative paths or flags.

## 2. Fixed-path safety

These paths and every existing ancestor or leaf must be fixed non-symlink paths inside main root:

- `verification_runs/`
- `reports/`
- formal target files
- annotation history
- round/group/report directories
- `proving_merged`
- public-helper pool and snapshot
- clean refresh directories
- `_coq_builds`
- the mode-selected run-root `dune_dependency_snapshot.json` or
  `makefile_dependency_snapshot.json`, plus the Makefile mode's run-root `Makefile`
- final backup and apply destinations

The controller rejects:

- POSIX symlinks;
- Windows junctions or reparse points;
- other non-regular special files;
- any path that redirects state, cleanup, candidate, build, or final apply outside its owner.

Before read, deletion, staging, or formal write, the controller checks the lexical fixed path. A temporary file has an unpredictable same-directory name, is followed by `fsync`, and is committed with `os.replace`; no attacker-predictable fixed `.tmp` leaf is reused.

The controller creates no synchronization file for state, formal targets, workspaces, or dependencies and uses no POSIX or Windows file-synchronization API. Commands execute in single-run action order. Generation compare-and-swap, fixed-path checks, digest seals, and atomic replacement continue to protect against stale writes and path escape. Multiple runs modifying the same main root concurrently are outside this contract.

## 3. Annotation commands and paths

A handoff renders commands of this form:

```text
<handoff-python> .../controller.py --main-root <root> symexec --run <run> --round <round>
<handoff-python> .../controller.py --main-root <root> coq-check --run <run> --round <round> --target-kind formal-case-lib  # only when the library is present
```

The controller renders `<handoff-python>` from the current `sys.executable` after its Python 3.12 gate, with platform-correct quoting. The agent must not replace it with a fixed `python3` or another interpreter, and must not add another `uv run` wrapper.

### Symexec driver

The controller selects by host:

| Host | Driver |
|---|---|
| Windows | `win-binary/symexec.exe` |
| Linux | `linux-binary/symexec` |
| Apple Silicon macOS | `mac-arm64-binary/symexec` |
| Intel macOS | `mac-x86-64-binary/symexec` |

An unknown host or macOS architecture fails explicitly; Linux is not a fallback.

`--case` is both the run-id stem and the sole authoritative Rocq/generated formal stem, and must be a valid Rocq identifier. The C stem and directory name may differ from the case, and one directory may contain multiple programs; each owns only the exact artifacts in its persisted mapping.

A target C may reside under `QCP_examples/<collection>/**`. At init, the controller mirrors its parent under `Rocq/examples/<collection>/**`, then derives exact lib/goal/auto/manual/goal-check candidate paths from `--case`. The nine-field `target_files` persists only this path set, the C path, case, and active theory. Every later snapshot, merge, Coq action, and final check consumes that persisted mapping; no action rederives formal identity from the C stem. For example, `QCP_examples/QCP_demos_LLM/3DGraphField.c --case three_d_graph_field` maps to `Rocq/examples/QCP_demos_LLM/three_d_graph_field_*.v`, never an invalid `3DGraphField_*` module.

Each canonical symexec and clean replay re-parses quoted includes and the annotation-strategy graph from the sealed C path and then determines ordered include/SLP arguments. Those runtime search parameters are not fields of `target_files`. The default profiles are `LLM_bench`/`QCP_demos_LLM → QCP_demos_LLM`, `Applications_human`/`QCP_demos_human → QCP_demos_human`, and `QCP_demos_tutorial → QCP_demos_tutorial`; `Applications_human/convex_hull/**` overrides to LLM, while `Applications_human/fme_ge_gmp/**` overrides to no profile. An unconfigured collection may use only a repository-wide unique match; a bare include with multiple matches fails explicitly. For example, `LLM_bench/Engineering/string/memory.c` recursively reaches `stdlib/string.h` and then a bare `verification_list.h`: human and LLM each supply one, so the target's explicit LLM profile must preserve source identity rather than a global `-I QCP_demos_LLM` or arbitrary basename preference. `LLM_bench/Algorithms/convex_hull_float/**` also adds the fixed `--float-finite-vc`. A global fixed `QCP_demos_LLM` argument must not be restored.

### `before` and generated-refresh transaction

Before delivery of each annotation attempt, the controller seals the current target C and persisted formal/generated roles together into:

```text
verification_runs/<run>/annotation_history/<attempt-id>/before/
```

State stores the aggregate digest, candidate relative path, and present/missing state for each role; only a present file has a digest. `formal_case_lib` and `proof_manual_file` may be missing, and the controller neither seeds a library nor creates a placeholder. `before/` is the pre-attempt state and recovery boundary. It is read-only to the agent and cannot be rebuilt from an edited main root.

Whenever the owner invokes symexec, the controller first stores the generated roles from the persisted mapping in a persistent temporary transaction under the attempt report directory. Its manifest records transaction status, presence, and digests for present files.

The manual may be removed only when:

- absent;
- zero bytes;
- every top-level/split proof is still its generated `Admitted`/`Abort` seed;
- its exact bytes equal the revalidated sealed-before manual for this attempt.

Another `Qed`, `Defined`, custom proof, or unparseable drift returns `protected-proof-manual`.

If main-root symexec fails, the transaction restores every role's prior existence and exact bytes. Success commits and clears it. A prepared transaction left by process interruption is restored before the next call; committed residue is only cleaned.

The owner stage performs no clean replay. Acceptance clean output is stored at:

```text
reports/<run>/annotation-attempts/annotation-attemptN/clean-output-freshness/
```

Final freshness is stored at:

```text
reports/<run>/final-check/symexec-refresh/
```

The latter does not overwrite the proved manual or create another manual role.

## 4. VC-checking debug and reuse paths

This section applies only when a present manual contains at least one VC. When the manual is absent or present with zero VCs, the controller creates no vc-checking round, debug script, reuse hint, or group path; it prepares an empty manifest and continues to mandatory parent goal-check/full Coq and final freshness/full Coq. If goal-check imports a missing manual, the check must fail.

Each vc-checking handoff supplies:

- a current debug script;
- fully qualified Rocq targets for every top-level VC and applicable split goal;
- `controller.py coq-debug --round <current-round>`.

The current script has one canonical path:
`_coq_builds/<current-round>/vc-checking/src/.coq_debug/vc-checking.v`. The handoff renderer, owner
authorization, runtime validation, `coqtop -l`, and acceptance check must all consume the same controller path
helper. No boundary may reconstruct an alternative path that omits the `vc-checking/` component.

Only when the controller binds the immediately preceding sealed proving source does it also supply:

- a reference debug script and command;
- previous group copied-manual, applicable library, and report paths;
- comparable previous targets;
- `reuse_source_raw/`;
- `_coq_builds/<sealed-source-round>/reuse-source/src`.

`reuse_source_raw/` stores the unnormalized raw goal/manual/`formal_case_lib` that are actually present for structural comparison and generated-goal semantic fingerprints. It creates no file for an absent optional role, whose digest is `null`. `reuse-source/src` exists only to show reference goals through `Show.` and is not another formal/library role.

When a source proving round is stale, the manifest parser still uses that round's sealed `reuse_source_raw/` as an explicit seed and revalidates its presence/digests before each consumption. It must not fall back to main-root raw files already updated by an annotation retry.

The debug-build seal mechanically binds:

- local build-tree digest;
- local build file count;
- the accepted selected-dependency artifact digest.

The receipt gains no extra field; `file_count` still counts only local build files. The controller revalidates the local tree and accepted dependency snapshot before and after reference debug. Every imported current module must have a local `.vo` in that build.

The final current script covers only aggressive split goals and `LLM_pre_process` top-level VCs. The reference script covers only previous goals cited by direct or partial decisions. If all decisions are `from scratch`, both reference script and receipt are omitted.

VC-checking may write only the `.coq_debug` paths named by the handoff. It must not modify preserved artifacts or scan another historical round.

## 5. Group paths and overlays

A group handoff may provide:

- `coq-debug`
- `coq-check --target-kind group-development --group <id>`
- `coq-check --target-kind group-check --group <id>`

Before each delivery claim, the controller rerenders these commands from current state, accepted plan, base, and compact manifest.

The controller derives:

- the copied-manual overlay destination and, when `formal_case_lib` is present, the `group_worker_lib` overlay destination;
- exact build `_coq_builds/<round>/<group>/src`;
- a separate incremental development build;
- group-check wrapper;
- assigned witnesses;
- exact debug-script path;
- proof modes and aggressive split assignments;
- optional read-only `proof_reuse.md`;
- exact editable proof spans;
- round-local `public_helper_snapshot.txt` path and digest.

Preparing and runtime use the same canonical debug-script filename function. Before group check/debug, the
controller verifies that the absolute manifest path and runtime target are identical. `coq-debug` passes only the
validated fixed absolute script path inside the build to `coqtop -l`; it never asks the Coq load path to search for a
build-relative name. The same path and digest are checked before and after spawn. Never copy the script, change cwd,
or broaden the load path to make debug succeed.

A group is created only when a present manual has witnesses. Its directory always contains a copied manual, and contains `group_worker_lib` only when `formal_case_lib` is present. With no library, the plan/worker cannot create helpers or modify a shared/differently named library. Reports and builds cannot be written there.

The annotation-gap Markdown has the fixed path `reports/<run>/rounds/<round>/groups/<group>/group_worker_output.md`. Finalize requires it to be a nonempty UTF-8 regular file at that fixed path and includes its digest in the finalized `artifact_sha256`; validation, reuse, feedback/summary, and first or repeated handoff all recheck that path and digest and cannot accept an alias, symlink, or updated bytes.

Before a first group preflight returns `report-repair-required`, the controller freezes the copied manual and optional `group_worker_lib` in `repair_formal_sha256`. That delivery then permits only report/Markdown repair; formal drift becomes `invalid-report`, and only successful finalize clears the temporary repair seal.

Each group may edit only its assigned top-level proof spans and all assigned split-goal proof spans belonging to `aggressive_pre_process` witnesses. Statements, declaration order, unassigned proofs, and `LLM_pre_process` split tokens are protected; comments, whitespace, CRLF/LF, trailing whitespace, and EOF newlines do not grant semantic authorization. An aggressive witness must first complete every split goal, then run `aggressive_pre_process` in the top-level proof and use only `Goal_apply` to apply the corresponding split lemma to each branch. The owner follows this proof principle; the controller still accepts based on proof mode, split completeness, the structural seal, and Rocq results rather than parsing tactic text.

Every new or materially modified helper must use this group's suffix. A helper may retain a historical suffix only when its declaration/proof tokens match the frozen public snapshot or accepted reuse. All groups are independent and cannot read or import sibling output. Accepted-plan order controls fixed numbering and merge; `dispatch_order` only fills concurrency slots and creates no dependency.

For a blocked group with `failure_class: annotation-gap`, finalize seals its copied manual and applicable lib together with the original report. The controller checks structure/ownership/route/helper/import/safety with `require_complete=False` and does not run exact/full group Rocq. Its directory no longer accepts annotation repair. The controller continues dispatching every unclaimed group with the same fixed paths and commands. When the round-wide aggregation is nonempty, it creates neither a mechanical merge result nor a parent overlay, but every group seal remains in `reuse_group_artifacts.groups`; groups passing the structural filter are recorded in `structurally_valid_groups` for the next round's controller-bound reuse source. An accepted-group proof may be direct when the semantic-fingerprint condition holds; a blocked-group proof is at most partial and its helpers are reproved from scratch.

Development, exact, and finalize validation use the same structure checker before creating a build or running Rocq. Group tooling is available only to the currently claimed `running` delivery.

## 6. Unified local-build contract

Annotation, group, parent, final, and debug all use the same controller-owned local-build contract.

### Build-mode selection and configuration source

The sole mode decision lives in the shared
`.agents/scripts/vc-proving/build_mode.py`: when `<main-root>/_build` is a
directory, the controller selects the existing Dune backend; otherwise it
selects the lock-free Makefile backend. Branch names, environment variables,
the presence of `dune-project`/`Makefile`, and command-probing results never
override this decision. Keep `_build` present or absent throughout a run. For
controller wire compatibility, the public action, phase, and state field retain
the names `dune-build` and `dune_preparation`; a Makefile receipt explicitly
contains `build_mode: makefile` and uses its own snapshot filename.

The Dune-mode implementation is unchanged. The controller discovers `coqc`,
`coqtop`, and `dune` from explicit environment settings or PATH, and
dependencies come only from `dune-project`, relevant `dune` files, and Dune
output. Windows setup may explicitly set `COQC_EXE`, `COQTOP_EXE`, `DUNE_EXE`,
and `DUNE_REAL`.

Makefile mode first discovers tools from `COQC_EXE`, `COQTOP_EXE`,
`COQDEP_EXE`, and `MAKE_EXE`. When a Rocq executable is not set explicitly, it
honors `COQBIN`/`SUF`/tool assignments in optional `Rocq/CONFIGURE`, then falls
back to PATH. It seals the presence/bytes of `Rocq/Makefile` and optional
`Rocq/CONFIGURE`, but never invokes a repository aggregate target.
Both modes use the controller-owned canonical flags and load-path mappings.
The controller assumes one sequential run for a main root; neither mode creates
a lock file or PID-owner record or calls a POSIX/Windows locking API.

### Current ownership

Case identity comes only from persisted `target_files`: `--case` supplies the authoritative formal stem and the target directory supplies the active theory. Current ownership includes only:

- this run's exact present generated artifacts;
- the present, explicitly editable `formal_case_lib`.

Neither the C stem, a same-directory `<case>_` prefix, a strategy/helper filename, nor a library import can infer case identity. Other programs in the same directory and shared/differently named libraries are dependencies by default.

### Selected dependency snapshot

Before checking a present `formal_case_lib` during annotation, the selected
backend performs one temporary dependency preparation for the exact library
target. It serves only that local `coqc` and does not enter accepted dependency
state. After annotation acceptance, the main-owned `dune-build` action performs
one formal preparation for the exact goal-check and writes the mode-specific
snapshot directly under the run root. Proof, debug, parent, and final actions
then only revalidate and consume that snapshot; they never resolve dependencies
again.

#### Dune mode

Before each local `coqc` of `formal_case_lib`, both the annotation owner and main acceptance first run the exact library `.vo` Dune target. This result serves only the annotation check and is not written into accepted dependency state.

After annotation acceptance, the main-owned `dune-build` runs only:

```text
dune build --root <main-root> --display=short <persisted-goal-check.vo>
```

Dune discovers dependencies, decides what is missing or stale, and performs the necessary rebuilds. The controller then reads the theory dependency data produced by that build, takes the exact goal-check transitive closure, and atomically writes:

```text
verification_runs/<run>/dune_dependency_snapshot.json
```

The snapshot contains the persisted case identity, current family and current direct edges, dependency source/artifact digests, Dune configuration digests, exact target, and `source_goal_version`. It is a fixed version of Dune's result, not another resolver. When an annotation retry accepts a new version, it overwrites the same path and updates the state receipt; snapshot history is not retained.

Before the formal `dune-build`, the controller removes old ordinary Coq side products under canonical `Rocq/` that would conflict with a Dune rule. A link, directory, or special leaf is not removed and fails explicitly. Dune artifacts are written only under `_build/default`.

`target_files_for_c` maps the case/target from `QCP_examples/<collection>/**/<program>.c` to the mirrored `Rocq/examples/<collection>/**` path, and the exact Dune target directly uses that persisted path. Arbitrary nesting depth, multiple programs in one directory, and non-fixed collection positions must not be replaced by a hard-coded example path; the target directory must remain covered by the repository Dune theory.

#### Makefile mode

The controller runs breadth-batched `coqdep` only at the two preparation
boundaries above. It resolves the exact transitive closure by frontier and
separates the persisted current family from the trusted base. The remainder of
that action does not re-resolve per source, and no `coq-check`, `coq-debug`,
parent, or final action may start `coqdep`. Receipt `dependency_metrics` exposes
batch, process, and node counts.

Formal preparation atomically writes:

```text
verification_runs/<run>/Makefile
verification_runs/<run>/makefile_dependency_snapshot.json
```

The run-local `Makefile` is a controller-generated standalone exact plan. Its
only public goal is `trusted-base`; it carries `.NOTPARALLEL` and admits only
the resolved trusted-base `.vo` set. An argv guard rejects `all`, `core`, every
`examples*` goal, `depend`, or any wider target. The environment drops recursive
Make flags, injected makefiles, and Coq flag/load-path overrides. Temporary
annotation preparation uses identical content in a temporary exact Makefile
and removes it on completion.

Before Make starts, the controller removes ordinary
`.vo/.vos/.vok/.glob/.aux` outputs only for the persisted current family in the
main root; it never deletes incremental trusted-base outputs. A symlink,
reparse point, directory, FIFO, or other special leaf fails explicitly. Make
updates trusted-base `.vo` files only beside canonical `Rocq/` sources and does
not compile the current family. The controller then revalidates unchanged
sources and run Makefile and seals exact/current edges, dependency
source/artifact digests, Makefile/CONFIGURE state, tool paths, case identity,
and `source_goal_version`. An annotation retry overwrites the same paths and
receipt; no snapshot history is retained.

### Load path

The controller reads accepted dependencies through fixed absolute broad
`-R/-Q` mappings. Their physical root is `_build/default` in Dune mode and
main-root `Rocq/` in Makefile mode. Both modes:

1. retain full fixed broad base mappings unchanged, without excluding a current basename or directory;
2. finally add the sole build-local exact current mapping;
3. require, through the snapshot guard, every imported current module to have a local `.vo` in this build rather than satisfying it with an old current side product under a broad Dune mapping.

A different-prefix module in the same directory is readable from the selected base output only when it belongs to the accepted snapshot; source is not copied. Every current dependency must have a build-local `.vo` before its consumer compiles or debugs, preventing fallback to an old artifact.

The build contains zero base `.v` and `.vo` files, creates no run-local base cache, and never compiles base source inside a check.

A present `formal_case_lib` is checked independently with the selected backend's exact target during annotation and may not import this run's generated artifacts. After the formal snapshot is complete, every project import in current source, a group overlay, or a debug script must map to a current/dependency source in the snapshot. Dynamic `Load`, load-path commands, missing source, a project import outside the snapshot, and a changed current edge each fail distinctly.

Group current source cannot dynamically extend the dependency closure. If a proof/helper genuinely needs a new official import, the worker reports it; an annotation retry places that import into accepted source and then performs a new `dune-build` action. The same proving version never starts Dune, Make, or `coqdep` again and writes no group-specific dependency artifact.

The accepted dependency artifact aggregate and local-build digest together bind reuse/debug seals.

### Current compilation cache

Development and mandatory checks share content-addressed current prerequisite `.vo` files under run-local `_coq_builds/current/`. The key contains source, current dependencies, compiler, configuration, flags, the accepted dependency-artifact digest, and normalized version. A mandatory check always executes its final target; development retains its own incremental final-target behavior. A missing, deleted, or corrupt cache entry recompiles only current modules from source.

Every local build stores current-case artifacts only. Preparing, development, exact, validation, parent, and final all read the same snapshot-bound dependency `.vo` files through the selected base load path. They must not copy or separately compile dependency source in their own builds.

No failure may fall back to:

- an aggregate/whole-workspace Dune target or repository Make aggregate target;
- a whole-repository mirror;
- base-source compilation inside a check;
- an old main-root current `.vo`;
- a wider target set.

## 7. Parent and final builds

Parent verify runs only when the round has no annotation gap and every group in a nonempty plan is accepted. It mechanically merges in accepted-plan order, independently of `dispatch_order`. It first revalidates each group seal and structure without repeating a full Rocq run per group, then overlays only the merged manual and/or `proving_merged_lib` that are actually present and runs one full check at:

```text
_coq_builds/<round>/parent/src
```

When both optional roles are absent, the controller creates no fake overlay but still runs parent goal-check/full Coq. Base/merged manifests use a `null` digest for an absent role.

Final-check validates applied main-root files at:

```text
_coq_builds/final-check/src
```

Before it begins, cleanup removes stale `.vo/.vos/.vok/.glob/.aux` by-products for every persisted exact current module identity, including like-named residue for an optional source that is absent, and for the current run outside build areas while preserving the selected trusted-base artifacts (Dune's `_build/default` or Makefile mode's main-root base `.vo` files). A broken symlink, directory, or other non-regular side-product leaf is not “missing” and must produce a cleanup error. The same boundary is scanned again at the end.

Parent and final read only dependency `.vo` files named by the accepted mode-specific snapshot, and each recompiles merged or applied current source in its own local build. Any dependency source/artifact/configuration drift returns a precise blocker; parent/final never invoke Dune, Make, or `coqdep`, widen a target, or compile dependency source internally.

## 8. Long commands and timeouts

Controller-owned external processes have finite wall-clock deadlines:

- one canonical symexec driver and recovery invocation share 600 seconds;
- all child processes in one `dune-build`, `coq-check`, or `coq-debug` share 1800 seconds.

Time spent resolving paths, building the dependency graph, and staging is deducted from the remaining time before another child process starts. No new process starts after the deadline.

The controller places external tools in an independent process group. At timeout it terminates the whole group and forcibly ends it when necessary; output draining remains bounded even if an escaped child retains a pipe. An agent must not restart a raw process or construct an unbounded substitute command.
