# Coq source baseline and synchronization map

This document pins the Coq revisions used by the current Lean migration. It is
the starting point for detecting and synchronizing future Coq updates; it does
not imply that every declaration in each source repository has been migrated.
The exact migrated inventory and all known interface differences remain in
`migration_inconsistencies.md`.

## Current baseline

- Baseline ID: `COQ-BASELINE-2026-07-21`
- Recorded on: `2026-07-21`
- Coq checkout: sibling directory `../annotated_simplec`
- Main repository branch at capture: `master`
- Main repository commit:
  `8e8fc0bd57a71cc92dc7ac93d8e675ab798b4ddb`
- Main repository subject: `update some examples`
- Main repository remote: `git@bitbucket.org:WxWyashen/annotated_simplec.git`
- Lean toolchain: `leanprover/lean4:v4.25.2`

The main commit records the submodule pointers listed below. At capture time the
only dirty source-checkout state was `unifysl/.DS_Store`; no Coq source file
differed from the pinned commits. The baseline therefore describes semantic
source content exactly, despite Git reporting the `unifysl` submodule as dirty.

The `annotated_simplec_lean` directory is the top-level Git repository,
so there is no honest Lean commit hash to pair with the Coq commit. The Lean
side of this row means the current validated workspace snapshot described by
`migration_inconsistencies.md`. If the Lean tree is later placed under version
control, add its commit to the baseline history before advancing the Coq
revision.

## Repository mapping

| Coq repository/path | Pinned commit | Current Lean destination | Migration coverage |
| --- | --- | --- | --- |
| `annotated_simplec` | `8e8fc0bd57a71cc92dc7ac93d8e675ab798b4ddb` | `auxlibs`, `fixedpoints/AUXLib/Relations.lean`, `SeparationLogic`, `examples` | Only the files and generated-witness slices inventoried in `migration_inconsistencies.md`; this is not a repository-wide port. |
| `annotated_simplec/compcert_lib` | `fec8f3f1000158e276e6b70b0a5931a761171e07` | `compcert_lib` | Dependency slices of `Coqlib.v`, `Integers.v`, and `Zbits.v`; not the complete CompCert integer library. |
| `annotated_simplec/fixedpoints` | `b04f77d684cd6337b5eb1889ca7709314f81c193` | `fixedpoints` | The source modules represented under `FP`, including the currently required fixed-point framework closure. |
| `annotated_simplec/listlib` | `78e816b1f679524f8d521e0fbfb2e4cb98a8d2d3` | `auxlibs/AUXLib/ListLib` | Required slices of `Base/Inductive.v`, `Base/Positional.v`, `General/Length.v`, and `General/Forall.v`; full re-export parity remains open. |
| `annotated_simplec/MonadLib` | `71a41c57f060fcd56844d686c8003701843d9dd5` | `MonadLib` | Complete active declarations and tactics from the previously recorded MonadErr core, plus the reached non-error StateRelMonad closure and the `Examples/mergesort.v` and `Examples/kmp.v` dependency slices. The aborted `Hoare_forall` is excluded. Coq root exports for SetMonad, OptionMonad, and ListMonad remain outside this slice (`MIG-MONAD-005`). |
| `annotated_simplec/sets` | `276325c294a9f53d3513c039d6ef9c31b40c9d17` | `sets` | Current SetsClass and relation dependency slices; omitted families remain recorded by `MIG-SETS-001`. |
| `annotated_simplec/unifysl` | `f5160c97eef28c07266bfdee8e1a2fbaa5c20e59` | `unifysl` | The 73-module migration targeting `unifysl-prp-8.20`, including the `demo932` facade; see the dedicated unifysl baseline documents. |

The parent Coq commit also pins the following submodules, but the current Lean
migration does not claim a source slice from them. They are recorded so a
future parent-repository update cannot silently change an untracked dependency.

| Coq submodule | Pinned commit | Current status |
| --- | --- | --- |
| `GraphLib` | `dc30dfc2f7e935cef9e15dfbdd5361c09fc4811b` | No migrated slice. |
| `MaxMinLib` | `ef0acd06e4adb617839b8faee7b37a407b97d38c` | No migrated slice. |
| `sumlib` | `284f49973eb348148b26e8c27c92087460a0975b` | No migrated slice. |

## Update detection

When the Coq checkout advances, do not compare only branch names. Preserve the
old commit above, record the candidate main commit and its submodule pointers,
then inspect both kinds of change:

```bash
git -C ../annotated_simplec diff --name-status \
  8e8fc0bd57a71cc92dc7ac93d8e675ab798b4ddb <new-main-commit> -- \
  auxlibs SeparationLogic examples

git -C ../annotated_simplec diff --submodule=log \
  8e8fc0bd57a71cc92dc7ac93d8e675ab798b4ddb <new-main-commit> -- \
  compcert_lib fixedpoints listlib MonadLib sets unifysl
```

For every changed relevant submodule pointer, compare that repository directly:

```bash
git -C ../annotated_simplec/<submodule> diff --name-status \
  <old-submodule-commit> <new-submodule-commit>
```

Classify each changed migrated source declaration as one of: statement/API,
definition/semantics, typeclass/instance, tactic behavior, notation/parser,
proof-only, import/dependency, or generated-goal change. A proof-only Coq diff
still requires checking `Arguments`, attributes, exported instances, and tactic
side effects before it is declared irrelevant to Lean.

Changes outside the current migrated inventory do not automatically require a
Lean edit. They do require dependency re-scanning when they add an import to a
migrated file, alter a generated witness consumed by the selected examples, or
move a declaration into the active dependency closure.

## Synchronization procedure

1. Add a candidate row to the baseline history without replacing the current
   accepted row.
2. Diff the main repository and all changed relevant submodules from their
   pinned commits.
3. Intersect changed files and declarations with the inventories in
   `migration_inconsistencies.md`; expand the dependency closure before editing
   a downstream Lean module.
4. Synchronize in package order: `unifysl`, `sets`,
   `fixedpoints`, `compcert_lib`, `auxlibs`,
   `SeparationLogic`, `MonadLib`, then `examples`.
5. Preserve source theorem statements and tactic success/failure behavior. Log
   every new unavoidable mismatch or preserved source risk in
   `migration_inconsistencies.md`.
6. Run each affected package's complete `lake build`, API inventory checks,
   source-shaped tactic regressions, forbidden-marker scan, and representative
   `#print axioms` checks.
7. Promote the candidate to the current baseline only after all affected Lean
   packages pass. Record both the new Coq commits and, once available, the Lean
   commit containing the synchronization.

## Baseline history

| Baseline ID | Coq main commit | Lean revision | Result |
| --- | --- | --- | --- |
| `COQ-BASELINE-2026-07-21` | `8e8fc0bd57a71cc92dc7ac93d8e675ab798b4ddb` plus the pinned submodule commits above | Current `annotated_simplec_lean` repository snapshot | Accepted. Exact migrated scope, builds, and residual differences are recorded in `migration_inconsistencies.md`. |
