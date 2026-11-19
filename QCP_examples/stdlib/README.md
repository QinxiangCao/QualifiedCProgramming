# Verified libc implementation examples

This directory contains the existing QCP standard-library contracts (`string.h`
and `string.strategies`) and implementation case studies under `musl/` and
`glibc/`. The implementation contracts do **not** replace the generic contracts:
the machine models, integer prototypes and memory preconditions differ.

| Case | Implementation / public specification | Formal interface | Scope |
| --- | --- | --- | --- |
| musl strstr | [musl/strstr_RL.c](musl/strstr_RL.c) | `musl/strstr_rel_goal_check.v` | Full adapted dispatcher, short needles and Two-Way; first match or NULL; separated input strings |
| glibc strstr | [glibc/strstr_RL.c](glibc/strstr_RL.c) | `glibc/strstr_goal_check.v` and dynamic search components | Dispatcher, short needles, dynamic Horspool and Two-Way; first match or NULL |
| glibc word strlen | [glibc/strlen_word_spec.h](glibc/strlen_word_spec.h) | `glibc/strlen_word_goal_check.v` | Capacity and exact-size object contracts; actual eight-byte loads |
| glibc byte memmove | [glibc/memmove_spec.h](glibc/memmove_spec.h) | `glibc/memmove_goal_check.v` plus byte/loop interfaces | Separated, left/right overlap, same range and empty copy |

All formal paths in the table are relative to
[`Rocq/examples/stdlib`](../../Rocq/examples/stdlib).
See [verification details](../../docs/stdlib/README.md) for machine models,
source adaptations, proof dependencies and trust boundaries.

## Reproduce

Run from the repository root with the QCP-recommended Coq/Rocq and Dune toolchain
on PATH:

```sh
python3 QCP_examples/stdlib/tools/verify.py
```

The script checks the documented glibc source adaptations, regenerates all 12
translation-unit goals into `.tmp/stdlib-verification`, requires byte-for-byte
equality with the checked-in goals, then builds the complete Rocq interfaces
and assumption audits. It never replaces the formal proof files.

Use `--symexec /path/to/symexec` and `--dune /path/to/dune` for explicit tools.
`--generate-only` and `--build-only` run the two phases separately.
Select the intended opam switch before running the script (or use
`opam exec --switch=<switch> -- python3 QCP_examples/stdlib/tools/verify.py`);
`--dune` alone does not select the Coq/Rocq compiler.
Use `--case glibc/strlen_word` (repeatable) to select individual units. Outputs and
logs stay under `.tmp`; compiled `.vo`/`.glob` files are not contribution sources.

The fixed-length Two-Way/Horspool cases are retained as proof dependencies and
independent regression targets. Historical duplicates, controller attempts,
editor probes and the separate contest problem are not part of this submission.
