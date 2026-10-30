# MiniSat

The solver is built from independent translation units:

| Source | Responsibility |
| --- | --- |
| `solver_qcp_support.c` | Literals, clauses, ordering, activity and database helpers |
| `solver_qcp_analysis.c` | Conflict analysis and learned-clause minimization |
| `solver_qcp_solver_propagate.c` | Watched-literal propagation |
| `solver_qcp_state_search.c` | Solver state, search and public API |
| `vec_qcp.c` | Vector implementation |
| `main_qcp.c` | Native DIMACS command-line frontend |

`solver_qcp.h` contains public declarations and contracts.
`solver_qcp_internal.h` contains the clause layout and contracts for helpers
called across solver files. Helpers used by only one unit remain local to it.
Incremental contract derivations live in `solver_qcp_state_search.c`, so their
obligations are generated once. Shared constants have a single definition in
`solver_qcp_support.c`.

Build and run the native solver from this directory:

```sh
make
.native-build/minisat input.cnf
```

`make BUILD_DIR=/tmp/minisat-build` builds outside the source tree. The build
compiles each source separately, with the trusted native runtime enabled, then
links the objects. C11 mode is required because the legacy API defines `bool`,
`true` and `false` itself.

From the repository root, generate the solver verification conditions with:

```sh
dune build --build-dir=_build1/ \
  @gen-vcs/Applications_human/minisat/solver_qcp_support.c \
  @gen-vcs/Applications_human/minisat/solver_qcp_analysis.c \
  @gen-vcs/Applications_human/minisat/solver_qcp_solver_propagate.c \
  @gen-vcs/Applications_human/minisat/solver_qcp_state_search.c \
  -j24 --diff-command=-
```

The proof module names and function groups are retained. The manifest's
`baseline_source` and `origins` paths describe the historical implementation at
`base_commit`; the monolithic source no longer exists in the current tree.
