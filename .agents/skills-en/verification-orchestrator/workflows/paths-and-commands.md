# Paths and Commands

The public entry point is `verification-orchestrator/controller.py` in the running code checkout.
For an initial command:

```sh
uv run --frozen --python 3.12 python .agents/scripts/verification-orchestrator/controller.py --main-root <root> <command> ...
```

Run actions and handoff Commands use `{ "argv": [...], "cwd": "..." }`. Preserve the interpreter,
arguments, and cwd. Pass the array directly when the terminal supports argv; otherwise quote each
argument for the actual shell. Keep tool/session handles until the command actually exits, then
check its exit code and JSON result. Do not add raw Coq/symexec/Dune/Make arguments or invoke internal
modules to bypass the controller.

Script paths come from the running code; `--main-root` selects the workspace. These need not share a
checkout. Interpret relative C paths from main root. `target_files` fixes all canonical files, and
C and formal stems may differ. Collection names and arbitrarily nested subdirectories must still
form valid Rocq logical paths.

## Regular files and publication

Use `/` in repository-relative JSON paths and preserve Coq identity case. Use Path for filesystem
operations. Reject escapes, symlinks, junctions, reparse points, and non-regular inputs; inspect path
components before normalization. C/strategy includes may contain `..` only when direct resolution
remains inside `QCP_examples`. Return ambiguous includes to the owner for repair.

Generated/staged text uses UTF-8/LF; original backups preserve exact bytes. Replace published files
using a temporary file in the destination directory, flushing/fsyncing and closing it before
`os.replace`. Annotation generates in a fresh directory and publishes only after every output is
valid. Failure does not first delete the canonical manual. If the optional manual is truly absent,
do not create a placeholder.

Final publication preserves original/candidate bytes. Recovery checks fixed roles/paths and current
content; never silently overwrite external new content. If a file is in use, preserve originals and
backups and report the actual error.

## Dependency preparation and Rocq

Select Dune when the workspace has an `_build` directory; otherwise select Make. Dune discovers
dependencies through native rules and builds the base. Make uses coqdep and a temporary exact
Makefile. The shared `dependency_plan.json` stores only `build_mode`, `target`, `case_anchor`, and
`dependencies`; compute current/base sources from the current case family and graph.

Both backends share one stage → select dependencies → compile pipeline. Each check reads current
files and prepares native dependencies. Current modules actually run coqc; the base uses native
incremental builds. Staging normalizes generator imports and auto/manual overlaps in memory and
writes only changed content. Final prelude comparisons reuse the same import normalization.

A group wrapper requires only assigned witnesses. Compile an active case library independently even
when goal-check does not import it. VC debug manuals and group copies enter the run build directory
as overlays; the canonical manual stays read-only. Parent checks the complete merged goal-check,
and final apply checks the latest candidate again.

## Tool budgets and output

Dependency preparation, waiting, and compilation for one Coq check/debug share at most 900 seconds.
A Dune workspace lock serializes shared dependency refreshes; group compilation can continue in
parallel after release. Lock waiting consumes the budget and responds to cancellation. Long native
commands report their stage and elapsed time to stderr, leaving stdout for final JSON.

Symexec uses the profile selected at initialization; one command starts at most one driver. Zero-byte
or missing required outputs are failures and do not start a second driver automatically. Progress is
diagnostic and cannot replace a successful exit and complete-output checks.

Zero budget or pending cancellation prevents a new process from starting. Timeout/pause cleans up
the independent process group and descendants, with a bounded output drain. Windows does not
guarantee partial stdout/stderr while a tool runs. Successful cleanup retains final output; if a
detached process still holds a pipe, report `cleanup_incomplete`. Do not continue before the user
explicitly requests resumption.

Final cleanup deletes only permitted generated side products and skips `_coq_builds` before
traversal. Preserve sources, reports, histories, candidates, and base-library artifacts.
