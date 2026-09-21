# Windows Runtime Rules

Follow the repository [Windows setup](../../../../docs/windows-setup.md) for native PowerShell,
uv/Python 3.12, Coq, and the selected build tools. Retain its actual version and executable checks;
Python must be exactly 3.12.

## Commands and paths

Use `uv run --frozen --python 3.12 python` initially. During a run, `{argv, cwd}` already contains
absolute interpreter and script paths. Pass argv directly when supported. For PowerShell text,
use `&` and single-quote each argument, doubling any single quote inside an argument. Do not use
`list2cmdline` as PowerShell quoting or add raw Coq/build arguments.

The script checkout, target workspace, and caller cwd may differ; generated invocations fix the
correct locations. Preserve the distinction between C/formal stems and arbitrarily nested
collection/subdirectory mappings. Physical roots may contain Chinese characters and spaces; Rocq
logical-path components must remain valid. Native tools' own source-filename restrictions still
apply.

Use `/` in relative JSON paths and preserve Coq identity case. Inspect original path components
before normalization; reject symlinks, junctions, reparse points, and escapes. Do not use subst or
links to bypass boundaries. UNC/cloud reparse workspaces are outside the current support scope.

## Files, path length, and recovery

Generated/staged text uses UTF-8/LF; backups preserve original bytes. Group copies are written
independently and do not inherit source read-only attributes. For publication, create temporary
files in the destination directory, flush/fsync and close handles, then use `os.replace`; do not
depend on cross-drive moves.

Annotation generates separately before publishing valid outputs. Final apply saves original and
candidate backups with short role filenames. Recovery inspects current files; external edits or
sharing violations preserve originals and backups and produce a concrete error. Do not retry
indefinitely or recursively relax source-tree permissions.

When system long paths are disabled, init preflights the actual layout, including r10, generated
temporary directories, VC/group/parent builds, final replay/apply, and backups. LongPathsEnabled
does not mean every external tool supports long paths. Prefer a shorter physical checkout and test
Python, symexec, Coq, and the native backend. Do not automatically add a `\\?\` prefix.

## Builds and processes

An `_build` directory selects Dune; otherwise use Make. Both share the four-field dependency plan
and current-source compilation pipeline. Dune uses a workspace lock for shared dependency refreshes.
Make uses a temporary exact Makefile with recipe load paths relative to its fixed cwd, avoiding
repeated long roots. Current modules actually compile on every check.

Native processes and Dune lock waiting for a Coq check/debug share a 900-second budget. Use
`CREATE_NEW_PROCESS_GROUP` and `taskkill /T /F` for descendant cleanup. Zero budget or pending
cancellation prevents process launch. Retrieve final output after successful cleanup; partial
stdout/stderr during execution is not guaranteed on Windows. If detached descendants retain pipes,
report `cleanup_incomplete`; avoid indefinite blocking from synchronously closing streams held by
background reader threads.

Pause changes only control/the signal, retaining tasks and owners. Explicit user resumption derives
actions again. Logs and timing are diagnostic and do not change acceptance results.

## Validation scope

```powershell
uv run --frozen --python 3.12 python -m pytest .agents/scripts/tests -q
```

**Native Windows validation of this refactor is not complete.** Linux tests and mocks do not replace
native results. Sharing-violation and junction fixtures run only on Windows; run real Coq/Dune/Make
smokes when the tools are available.

Native checks should cover roots with Chinese characters, spaces, parentheses, and `&`; a separate
cwd; read-only sources; long r10 paths; optional missing files; cancellation; resuming acceptance of
returned deliveries; and publication recovery. Preserve actual results.
