# Coq Tooling

`controller.py coq-check/coq-debug` is the only external Coq entry point. A group worker executes the two commands from `group_worker_input.md` exactly as rendered and never calls `coq_tooling.py`, raw `coqc` / `coqtop`, Dune, Rocq MCP, or an `_CoqProject`-derived command directly.

## Directory and overlays

- Complete formal dependencies come from the main root.
- A group directory contains only the copied manual and `group_worker_lib`.
- The controller derives the two overlay destinations from current state/manifest.
- The build directory is fixed at the current run's `_coq_builds/<round>/<group>/src`.
- A debug script may be written only to the exact `.coq_debug` path from the handoff.

Failed-proof feedback authorizes edits only to assigned bodies, `group_worker_lib`, or the declared debug script. It does not authorize changes to commands, paths, flags, unassigned witnesses, statements, or `formal_case_lib`.

## Completion

The exact group-check must pass against the current version before writing `group_worker_report.json.status = completed`. The report does not paste Coq argv, cwd, source-digest lists, or complete evidence. Controller review reruns the same fixed group-check and writes a compact status to controller state. Parent verification inspects group contents again and runs the full goal check.

Coq tooling uses the executable configured through `SeparationLogic/CONFIGURE` and the Makefile. Reuse of base `.vo` files is not a private current-run cache; it is the system-wide rule that every run and Coq phase uses the main-root products from a prerequisite full make. Files from every Makefile `-R` / `-Q` load path are staged into the run build as needed. No cache is keyed by base-source digest, Coq version, or flags, and group/parent checks do not rebuild base sources. This trust excludes the current target's lib/goal/auto/manual/check modules: old products are excluded, and the group overlays plus current generated sources are rebuilt. If a required base `.vo` is missing, let the exact check fail and report it; never use raw Coq to compile the base library as a workaround.
