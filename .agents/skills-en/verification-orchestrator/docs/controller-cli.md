# Controller Public CLI

```text
<python> <scripts>/verification-orchestrator/controller.py --main-root <root> <command> ...
```

Python must be exactly 3.12. For initial commands, use the repository's
`uv run --frozen --python 3.12 python`; structured invocations during a run already contain absolute
interpreter and script paths. `--main-root` defaults to cwd; preserve its supplied value in actions.
All commands except `init-run` and `validate-artifact` require `--run <run-id>`.

## Initialization

```text
init-run --case <formal-stem> --target-c-file <C-path>
```

`--case` is a valid Rocq identifier, independent of the C filename. The C path may be absolute or
main-root-relative and must be inside `QCP_examples/<collection>/...`. Other options:

| Option | Meaning |
|---|---|
| `--formal-case-lib-policy present\|create\|absent` | Use an existing library, create a seed, or keep it absent; defaults according to the current file |
| `--freeze-spec <function>` | Freeze a user-provided specification; repeat or use comma-separated names; omission assigns specification writing to the annotation owner |
| `--max-witnesses-per-group <n>` | Positive integer; default 12 |
| `--max-parallel-group-workers <n>` | Positive integer; default 5 |
| `--symexec-profile standard\|recursive-large` | Select an existing symexec budget; default standard |
| `--problem-statement` / `--problem-statement-file` | Problem text or a UTF-8 file |
| `--target-function` / `--expected-behavior` / `--input-output-contract` | Current problem constraints |
| `--spec-hint` / `--preferred-hidden-property` / `--forbidden-pattern` / `--reference-case-hint` | Repeatable owner hints |
| `--timestamp <YYYYMMDDhhmmss>` | Optional 14-digit run timestamp |

## Current 18 commands

| Command | Arguments besides `--run` | Purpose |
|---|---|---|
| `init-run` | See above | Create a schema 4 run |
| `step` | None | Read current facts and return actions, waiting, and blockers |
| `claim-attempt` | `--next-action --owner` | Claim the current owner action; return its handoff and finalize invocation |
| `finalize-delivery` | `--attempt --owner` | Record that the owner has stopped and directly perform all acceptance checks for its role |
| `retry-round` | `--phase annotation\|vc-checking --reason --previous-attempt` | Execute the retry specified by the current action |
| `unfreeze` | `--round` | Remove the current annotation's specification baseline constraint after user approval |
| `dune-build` | None | Prepare dependencies with the selected native backend, then enter VC checking or empty proving |
| `vc-proving-preparing` | `--round` | Create current group copies and handoffs |
| `vc-proving-verify` | `--round` | Read current groups, mechanically merge, and run the parent check |
| `symexec` | `--round` | Let the annotation owner generate and publish outputs for its current task |
| `coq-check` | `--round --target-kind`; group kinds also require `--group` | Development/exact checks |
| `coq-debug` | `--round`; group owners also require `--group` | Check an authorized debug script/copy |
| `final-apply` | None | Recheck the latest candidate and publish with recovery support |
| `final-check` | None | Check actual files, independent replay, and cleanup; success marks done |
| `pause-run` | `--reason` | Pause the run while retaining task facts |
| `cancel-action` | `--action --reason` | Validate the current/claimed action id and pause the run |
| `resume-run` | None | Recompute actions after explicit resumption |
| `validate-artifact` | `--kind --path`; no `--run` required | Validate the specified file with the runtime validator |

`coq-check --target-kind` supports only `formal-case-lib-design`, `formal-case-lib`,
`group-development`, and `group-check`. `validate-artifact --kind` supports only `agent-report`,
`group-worker-report`, `annotation-plan`, `controller-state`, and `run-log`.

## Usage rules

Execute the controller's returned invocation; do not infer the currently permitted phase from this
table. Claim owner actions first. Main finalizes after the owner stops writing. Repeat finalize for
a `returned` task to continue interrupted acceptance; repairable errors return to a prepared action
for the same owner.

Results vary by command. Tool checks require both successful exit and JSON `passed`; claim returns
`claimed` or `already-claimed`; acceptance returns `accepted`, repair, or a blocker; `step` returns
run status and current actions. Exit code 0, an owner's `completed`, or one `valid` report does not
mean the whole run is complete.

There are no separate annotation/VC acceptance commands. Older-schema runs are not migrated; do not
hand-edit their schema to continue. Recover with their original code or initialize a new run. After
a user pause, `resume-run` requires explicit authorization to resume.
