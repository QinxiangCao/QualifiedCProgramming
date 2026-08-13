# Shared agent scripts

This directory contains Python scripts shared by the language-specific agent skills.

Documentation stays under `.agents/skills` and `.agents/skills-en`. Executable scripts live here once and are referenced from both mirrors.

## Rocq build backends

All controller and Rocq executables remain under this shared directory; neither
language mirror owns a script copy.  The public Rocq entry point is
`vc-proving/coq_tooling.py`, which applies one repository-root rule:

- if `<main-root>/_build` is a directory, dispatch to the unchanged Dune
  implementation in `vc-proving/coq_tooling_dune.py`;
- otherwise dispatch to the lock-free Makefile implementation in
  `vc-proving/coq_tooling_makefile.py`.

`vc-proving/build_mode.py` is the sole mode detector. There is no branch-name,
environment-variable, or configuration fallback. Keep `_build` present or
absent for the lifetime of a run so every controller action selects the same
backend.

The Makefile backend resolves the exact dependency graph only at the bounded
annotation/preparation points, uses breadth-batched `coqdep`, and writes one
exact run-local `Makefile` whose only public goal is `trusted-base`. Later
proof, debug, parent, and final actions consume the sealed snapshot and do not
rerun dependency discovery or invoke an aggregate repository Make target.
Explicit `COQC_EXE`/`COQTOP_EXE`/`COQDEP_EXE`/`MAKE_EXE` values take priority;
otherwise Make mode honors executable selection in optional `Rocq/CONFIGURE`
before falling back to `PATH`.

Controller execution assumes one sequential run and creates no lock file or
operating-system lock for either backend.
