# Coq source baseline and synchronization map

This document pins the Coq revisions used by the current Lean migration. It is
the starting point for detecting and synchronizing future Coq updates; it does
not imply that every declaration in each source repository has been migrated.
The exact migrated inventory and all known interface differences remain in
`migration_inconsistencies.md`.

## Current baseline

- Baseline ID: `COQ-BASELINE-2026-08-13`
- Recorded on: `2026-08-13`
- Coq checkout: parent directory `..`
- Main repository branch at capture: `master`
- Main repository commit:
  `8f2510abb17ea60651174f1a2138570e176ba4e4`
- Main repository subject: `port to new sac`
- Main repository remote: `git@bitbucket.org:WxWyashen/annotated_simplec.git`
- Lean toolchain: `leanprover/lean4:v4.25.2`

The main commit records the submodule pointers listed below. At capture time the
only dirty source-checkout state was `unifysl/.DS_Store`; no Coq source file
differed from the pinned commits. The baseline therefore describes semantic
source content exactly, despite Git reporting the `unifysl` submodule as dirty.

The Lean migration is tracked in the `annotated_simplec_lean` Git repository at
`git@bitbucket.org:WxWyashen/annotated_simplec_lean.git`. The last workspace
validated wholly against the old baseline is Lean commit
`4e2e067ce12bce65cc71d87de3cca9011f6e2b9a`. Candidate synchronization phase
one is implemented at Lean commit `b895c83`; it updates Mem, IntLib, the parent
repository's central ListLib, and the affected insertion-sort integration.
Independent review correction `adbf47a` restores the exact candidate shape of
`insertion_sort_entail_wit_2` and strengthens its Mem behavior regression.
Phase two is implemented at Lean commit `33ced6e`; it adds the candidate
`CArch`/`CEndian` layer with both pointer architectures and both byte orders.
Phase three is implemented at Lean commit `8209dc1`; it synchronizes candidate
`SeparationLogic/CNotation.v`, including the new scalar constructors,
architecture-indexed size semantics, notation, and CNotation automation.
Independent-review correction `e8b8ced` narrows `const_array_simpl` to the
source alias/arrow pattern and covers the temporary new-type store branches.
Follow-up correction `ac5bab1` expands the type-hash and recursive trust
contract to 131 declarations, including all public notation-dispatch entries,
while retaining the exact 32-assumption source boundary.
Phases 4A and 4B are recorded by Lean commit `3d7ee0f`; they synchronize the
candidate Int128 store slice and executable floating-point dependency closure,
including `FloatLib.v`, floating CommonAssertion/StoreAux declarations, and
both `float_vc` test files. Phase 4C is the independent checkpoint `4e52a0c`
for the parameterized CommonAssertion core. P0-6 is recorded by Lean commit
`e13f7bd`; it parameterizes canonical StoreAux. Follow-up commit `115da51`
fixes every aggregate StoreAux export to the explicit Arch32/BigEndian
compatibility instantiation. P0-7 is recorded by Lean checkpoint `2ec5968`,
with review/test closure `cc69df3`; it propagates the canonical parameters
through arrays, maps, strings, and concurrency modules and adds Array3. P0-8
is recorded by Lean checkpoint `0515ff4`; review closure `e021613` restores
the complete flattened `Include` surface, the source default facade types, and
exhaustive type/axiom contracts for all six top-level aggregate combinations.
P1-2 is recorded by Lean checkpoint `8a8195f`; it synchronizes the candidate
MonadErr and StateRelMonad `Rec` facade, generalized fixed-point interfaces,
Hoare/safeExec rules, isolated program scopes, and shared tactic dispatch.
Follow-up `953a563` closes the complete dual-backend public tactic matrix and
fixes the shared `hoare_rec` parser boundary exposed by that review.
Independent review closure `1e09148` restores the source weak
`StateRelMonad.Hoare_fix_logicv_conj` rule and its non-prime tactic routing,
adds the missing MonadErr `whileretP` family marker, and replaces vacuous
conjunction/API checks with native-fixed-point and concrete safeExec behavior
regressions.
P1-3 is recorded by Lean checkpoint `806fe4b`; it synchronizes the candidate
Sets tactic changes through an extensible simplification set, adds
`Rels.test` normalization, handles `Prop` and recursively lifted function
membership, and locks all six new source test shapes plus no-op and repeated
execution behavior with syntactic normal-form guards.
Independent review closure `c9c22d3` directly tests `unfold_In` and narrows
Prop identity normalization to the `Sets.prop_inj` shape, so unrelated uses of
Lean's `id` remain untouched.
Lean checkpoint `36a6d20` aligns all 487 candidate manual proofs and the nine
changed strategy families (138 correctness theorems), and restores the
source-shaped `sll_shape_lib` file. Checkpoint `b148594` adds the final nine
strategy families, their `avl_shape`/`dll_shape_lib` dependencies, and the
shared tactic coverage needed by their source scripts. The resulting 42
strategy files and 369 correctness theorems have exact Coq/Lean file, theorem,
and target-name agreement. The current dependency migration additionally ports
`MaxMinLib/MaxMin.v` and `MaxMinLib/Interface.v` at submodule commit
`973b797512ef1c16c4ffd6b420e42844a6aaebd7`, and the complete active
seven-file external `listlib` surface at submodule commit
`e942b70071b0bb2429e80a17ad85bd571bcea010`.

## Accepted update history

- Candidate ID: `COQ-CANDIDATE-2026-08-10`
- Candidate main commit:
  `8f2510abb17ea60651174f1a2138570e176ba4e4`
- Candidate subject: `port to new sac`
- Range from the accepted baseline: 25 commits, 146 files,
  71,297 insertions, and 5,433 deletions.
- Status: pulled, audited, synchronized, and **accepted as the Lean migration
  baseline on 2026-08-13**. Phases one through three, phases 4A/4B/4C,
  P0-6, P0-7, P0-8, P1-2, and P1-3 target candidate `8f2510a` for the completed
  Mem/List/CArch/CNotation, Int128, executable FloatLib, parameterized
  CommonAssertion/StoreAux, and parameterized array/map/string/concurrency
  slices, all six aggregate facade combinations, and the migrated
  MonadErr/StateRelMonad slice and the reached Sets tactic behavior. The
  arbitrary-real FloatLib interface is now synchronized using Mathlib `Real`.
  Candidate manual proofs and all strategy files are aligned. The complete
  inventory is 487 manual proofs plus 369 correctness theorems in 42 strategy
  files; the two repository audit scripts report no missing, stale, extra, or
  target-mismatched declaration.
- Detailed impact report and ordered migration plan:
  `coq_update_8f2510a_migration_plan.md`.
- P0-1 至 P0-8 的逐源文件物理归属和兼容层边界：
  `p0_source_mapping.md`。

Accepted submodule pointers are:

| Coq submodule | Accepted commit | Change from previous baseline |
| --- | --- | --- |
| `GraphLib` | `077a6a5f7af1b4a39c8c7c0d277371634e214f17` | Changed. |
| `MaxMinLib` | `973b797512ef1c16c4ffd6b420e42844a6aaebd7` | Changed. |
| `MonadLib` | `98d0996e0c5882ad75d0901646891600b9e847ae` | Changed and relevant to the migrated Monad/example slice. |
| `compcert_lib` | `fec8f3f1000158e276e6b70b0a5931a761171e07` | Unchanged. |
| `fixedpoints` | `b04f77d684cd6337b5eb1889ca7709314f81c193` | Unchanged. |
| `listlib` | `e942b70071b0bb2429e80a17ad85bd571bcea010` | Changed and relevant to the migrated ListLib slice. |
| `sets` | `dd33faa1aaeadf5155faba3896d8dd8cb533d5b5` | Changed and relevant to tactic behavior. |
| `sumlib` | `284f49973eb348148b26e8c27c92087460a0975b` | Unchanged. |
| `unifysl` | `86fce3c365954384ac6877c82f30bc7a24fc4155` | Makefile-only change found in the audited range. |

## Repository mapping

| Coq repository/path | Pinned commit | Current Lean destination | Migration coverage |
| --- | --- | --- | --- |
| `annotated_simplec` | `8f2510abb17ea60651174f1a2138570e176ba4e4` | `auxlibs-lean`, `fixedpoints-lean/AUXLib/Relations.lean`, `separationlogic-lean`, `examples-lean` | The file and generated-witness slices inventoried in `migration_inconsistencies.md`, including all 487 completed source `proof_of_*` witness proofs and all 369 strategy correctness theorems. The nine additional completed helper lemmas in `simple_arith/exgcd_proof_manual.v` are implementation support rather than generated-witness API entries. This is not a repository-wide port. |
| `annotated_simplec/compcert_lib` | `fec8f3f1000158e276e6b70b0a5931a761171e07` | `compcert-lean` | Dependency slices of `Coqlib.v`, `Integers.v`, and `Zbits.v`; not the complete CompCert integer library. |
| `annotated_simplec/flocq` | vendored at main commit `8f2510abb17ea60651174f1a2138570e176ba4e4` (Flocq 4.2.2 source tree) | `flocq-lean` | FloatLib 所需声明切片，不是完整 35 文件库；逐文件与内部适配边界见 [`flocq_source_mapping.md`](flocq_source_mapping.md)。 |
| `annotated_simplec/fixedpoints` | `b04f77d684cd6337b5eb1889ca7709314f81c193` | `fixedpoints-lean` | The source modules represented under `FP`, including the currently required fixed-point framework closure. |
| `annotated_simplec/listlib` | `e942b70071b0bb2429e80a17ad85bd571bcea010` | `listlib-lean`; transparent shared compatibility remains in `auxlibs-lean/AUXLib/ListLib` | Complete active seven-file surface: `Base/Inductive.v`, `Base/Positional.v`, `General/Length.v`, `General/Forall.v`, `General/NoDup.v`, `General/Presuffix.v`, and `General/IndexedElements.v`. Coq-style full re-export through `AUXLib.ListLib` remains open in `MIG-LIST-004` because the Lean package graph would otherwise cycle. |
| `annotated_simplec/MaxMinLib` | `973b797512ef1c16c4ffd6b420e42844a6aaebd7` | `maxminlib-lean` | Complete active semantic declarations from `MaxMin.v` and `Interface.v`, including `TotalOrder`, min/max object and value predicates, congruence instances, Z/Nat/option order instances, and finite-min support. Pattern-notation limitations are recorded by `MIG-MAXMIN-002`. |
| `annotated_simplec/MonadLib` | `98d0996e0c5882ad75d0901646891600b9e847ae` | `monadlib-lean` | Complete active declarations and tactics from the reached MonadErr and non-error StateRelMonad closure, now including the candidate `Rec` facade, generalized mono/continuous APIs, Rec Hoare rules, program scopes, safeExec composition rules, and corresponding RecInterface/Notation tests. The `Examples/mergesort.v` and `Examples/kmp.v` dependency slices remain included. The aborted `Hoare_forall` is excluded. Coq root exports for SetMonad, OptionMonad, and ListMonad remain outside this slice (`MIG-MONAD-005`). Detailed delta audit: `monadlib_p1_2_audit.md`. |
| `annotated_simplec/sets` | `dd33faa1aaeadf5155faba3896d8dd8cb533d5b5` | `sets-lean` | Current SetsClass and relation dependency slices, including synchronized P1-3 tactic behavior; omitted families remain recorded by `MIG-SETS-001`. Detailed tactic audit: `sets_p1_3_audit.md`. |
| `annotated_simplec/unifysl` | `86fce3c365954384ac6877c82f30bc7a24fc4155` | `unifysl-lean` | The 73-module migration targeting `unifysl-prp-8.20`, including the `demo932` facade; the accepted-pointer delta was Makefile-only. See the dedicated unifysl baseline documents. |

The parent Coq commit also pins the following submodules, but the current Lean
migration does not claim a source slice from them. They are recorded so a
future parent-repository update cannot silently change an untracked dependency.

| Coq submodule | Pinned commit | Current status |
| --- | --- | --- |
| `GraphLib` | `077a6a5f7af1b4a39c8c7c0d277371634e214f17` | No migrated slice. |
| `sumlib` | `284f49973eb348148b26e8c27c92087460a0975b` | No migrated slice. |

## Update detection

When the Coq checkout advances, do not compare only branch names. Preserve the
old commit above, record the candidate main commit and its submodule pointers,
then inspect both kinds of change:

```bash
git -C .. diff --name-status \
  8f2510abb17ea60651174f1a2138570e176ba4e4 <new-main-commit> -- \
  auxlibs SeparationLogic examples

git -C .. diff --submodule=log \
  8f2510abb17ea60651174f1a2138570e176ba4e4 <new-main-commit> -- \
  compcert_lib fixedpoints listlib MonadLib sets unifysl
```

For every changed relevant submodule pointer, compare that repository directly:

```bash
git -C ../<submodule> diff --name-status \
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
4. Synchronize in package order: `compcert-lean`, `flocq-lean`,
   `unifysl-lean`, `auxlibs-lean`, `sets-lean`, `maxminlib-lean`,
   `listlib-lean`, `fixedpoints-lean`, `separationlogic-lean`,
   `monadlib-lean`, then `examples-lean`.
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
| `COQ-BASELINE-2026-07-21` | `8e8fc0bd57a71cc92dc7ac93d8e675ab798b4ddb` plus the pinned submodule commits above | `4e2e067ce12bce65cc71d87de3cca9011f6e2b9a` | Accepted workspace. The build passed before starting candidate synchronization. |
| `COQ-BASELINE-2026-08-13` | `8f2510abb17ea60651174f1a2138570e176ba4e4` plus the accepted pointers above | `b895c83`..`c9c22d3` (P0/P1 dependencies), `36a6d20` (manual and changed-strategy examples), `b148594` (complete strategy closure), plus the current MaxMinLib port | Accepted migrated scope. All 487 manual proofs and all 369 strategy correctness theorems are aligned; the current eleven-package build includes the new MaxMinLib dependency package. Modules explicitly outside the migrated inventory remain out of scope rather than being claimed as ported. |
