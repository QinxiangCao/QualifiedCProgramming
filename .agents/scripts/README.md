# Verification scripts

`verification-orchestrator/controller.py` is the public entry point for one C case:
annotation → native dependencies → VC analysis → proof groups → parent verification
→ publication → final verification. Owner skills supply the mathematical workflow.

```sh
uv run --frozen --python 3.12 python .agents/scripts/verification-orchestrator/controller.py --help
uv run --frozen --python 3.12 python -m pytest .agents/scripts/tests -q
```

The current CLI has 18 commands. `finalize-delivery` records that an owner stopped
writing and directly runs the complete role acceptance. Main follows the returned
`{argv, cwd}` invocations; a shell-only terminal quotes the same arguments for its
actual shell. Script location, target workspace, and caller cwd may differ.

## Data and control flow

State **schema 4** stores fixed run inputs, three `current` task pointers, and one
`attempts` collection. Group owner records live inside their proving attempt.
Tasks are `prepared`, `running`, `returned`, `accepted`, or `blocked`. A same-owner
repair returns that task to `prepared` with feedback and an increased repair index.
An interrupted acceptance resumes from `returned` through `finalize-delivery`.

Actions and waiting owners are derived on demand. They are not persisted alongside
another rounds/session/acceptance state. `pending_retry` records a determined
retry reason and source; group-gap batch routing is derived from current group
facts. Main serializes business-state writes. Pause changes control and its signal
while retaining tasks; resume derives actions again.

Schema 3 and older runs are not migrated. Finish or recover them with their original
code, or initialize a new run from current formal files.

## Code responsibilities

| Modules | Responsibility |
|---|---|
| `controller_state`, `controller_rounds`, `controller_attempts` | Run/task facts, deterministic paths, derived scheduling, ownership and acceptance lifecycle |
| `controller_cli`, `controller_invocations`, `controller_control`, `controller_execution` | Public commands, handoff invocations, pause/cancel and execution diagnostics |
| `controller_tools`, `controller_round_checks`, `controller_dune` | Owner tools, annotation/VC acceptance and dependency-stage transition |
| `proving`, `group_plan_utils`, `proof_manual_utils` | Read current plan/manual/lib, copy group inputs, validate proof boundaries and mechanically merge |
| `controller_proving`, `controller_final` | Parent verification, latest-candidate publication, independent final replay and actual-file checks |
| `annotation_design`, `spec_freeze`, `annotation_refresh`, `symexec_tooling` | Plan/VC comparisons, approved spec boundaries, recoverable publication and one-driver symbolic execution |
| `coq_tooling`, `coq_tooling_common`, native backend modules | One dependency plan, current-source staging/checks/debug/audit, Dune or Make dependency preparation |
| `path_utils`, `file_integrity`, `atomic_file`, `process_adapter` | Confined ordinary files, atomic replacement, bounded processes and cancellation |

Proving writes independent group copies and merged formal candidates. It does not
write base/worker manifests or a duplicate merged-result file. `final_candidate`
records only the proving round; each consumer reads its actual current context.
Owners decide historical proof reuse and helper conflict repair.

## Paths, builds and publication

The mapping remains `QCP_examples/<collection>/.../<input>.c` to
`Rocq/examples/<collection>/.../<case>_*.v`. C and formal stems may differ; logical
path components must be legal Rocq identifiers. Physical roots may contain Unicode
and spaces. Links, reparse points and escapes are rejected before normalization.

An `_build` directory selects Dune; otherwise Make is used. `dependency_plan.json`
contains only `build_mode`, `target`, `case_anchor`, and `dependencies`. Current/base
membership follows from the case family and graph. Both backends share current
compilation, group-wrapper checks, debug and library auditing. Native base builds
are incremental; current sources run coqc on each check. One Coq command shares a
900-second budget across preparation, Dune lock waiting and compilation.

Symbolic execution launches at most one driver per command. Missing/empty required
output fails without an automatic second attempt. Generated files are published
only after validation. Final publication preserves original/candidate bytes and
refuses to overwrite an external edit during recovery.

Timing/log output is diagnostic. `timing_summary.json` includes `run`, `commands`,
`annotation_attempts`, and `rounds`; summed durations are not parallel wall time.

Tests exercise real installed Coq/Dune/Make and controller lifecycles in temporary
workspaces. Native Windows validation remains outstanding; Linux skips or mocked
Windows branches are not a native pass. See the orchestrator's Windows guide and
[refactor review](REFACTOR_REVIEW.md) for the recorded validation scope.
