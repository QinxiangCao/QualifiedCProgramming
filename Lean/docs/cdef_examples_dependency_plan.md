# Cdef and examples dependency plan

## Scope boundary

The Coq Makefile contains two independent build groups:

- `SYMEXEC` contains `Common`, `CoreLang`, `Frontend`, `Asrtdef`, `Cdef`, and
  their support libraries.
- `EXAMPLE` contains SeparationLogic, its proof-side support libraries, and
  the checked-in example goals and proofs.

No active `examples/**/*.v` file imports `SimpleC.CSE`. The checked-in examples
consume already generated goals, SeparationLogic, and proof automation; they do
not depend on the Coq `Cdef` modules at elaboration time. Consequently the Lean
ports should be managed as two tracks. Migrating examples does not have to wait
for Cdef, while regenerating examples from annotated C will eventually require
the Cdef/symbolic-execution track.

The active Makefile scopes are:

- Cdef: 18 files. The eight legacy or experimental files not in `Cdef_FILES`
  are `Assertion_denote.v`, `Ceval_sound.v`, `Cexpr_SymExec.v`,
  `Cexpr_eval.v`, `Cexpr_evalproof.v`, `Cexpr_semantics.v`, `ExprTest.v`, and
  `SymExec_sound.v`.
- examples: 335 unique files listed by `Examples_FILES`,
  `StrategyProof_FILES`, and `Auto_Examples_FILES`. The four checked-in files
  not listed by those variables are `critical_sll_strategy_goal.v`,
  `critical_sll_strategy_goal_check.v`, `critical_sll_strategy_proof.v`, and
  `kmp_lib.v`.

`Frontend` and `CoreLang/CTypesDefDeclSem.v` are members of the broad `SYMEXEC`
build, but none of the 18 active Cdef files imports them. They are not immediate
Cdef prerequisites and should not be pulled into the first Cdef slice.

## Shared prerequisites already available

The following dependencies are already usable from sibling Lean packages:

- `SimpleC.SL` through the completed SeparationLogic aggregate, except for the
  explicitly deferred `pocv02.v`.
- the demo932/unifysl facade and its Proper/setoid bridge;
- the current `SetsClass` dependency slice;
- `AUXLib.Axioms`, `EqDec`, `Feq`, `Idents`, `IntAuto`, `ListLib`, `VMap`,
  Morphisms, and binder rewrite support;
- the current CompCert integer and arithmetic `Coqlib` slices.

The current CompCert `Coqlib` port is not a declaration-complete port. Cdef uses
`Zmod_recombine`, which is present, and later uses `zlt` and `zeq`, which are not
yet exposed. Each Common/ASRT/Cdef phase must therefore audit the exact Coqlib
names it consumes instead of treating the existing file as complete.

## Missing prerequisites for Cdef

### Foundation layer

1. Reuse the completed `AUXLib.Idents`, then add the small standard-`positive`
   compatibility closure needed by ASRT: at least `Pos.eqb` and source-positive
   literals. This is the bounded follow-up recorded by `MIG-IDENTS-001`, not a
   reason to import an entire arithmetic library into the identifier module.
2. Migrate `SimpleC.Common.CTypes`, `COps`, and `Notations` in that order.
3. Migrate `SimpleC.CoreLang.CTypes`. It depends on Common types plus the
   existing `AUXLib.ListLib` and `EqDec`.
4. Migrate the exact `SimpleC.ASRT.DefFiles` closure:
   `DepList`, `PolyExpr_eq_rect`, `ExprDef`, `LocalDef`, `PropDef`, `SepDef`,
   `AsrtDefAux`, `AsrtDef`, and `DefFiles`.

The main technical risk in this layer is `PolyExpr_eq_rect.v`: it is a
2,323-line dependently typed expression implementation using Eqdep-style casts,
dependent lists, type assignments, and typed evaluation. Lean proof
irrelevance helps, but the public dependent indices, substitution operations,
and evaluator types must be preserved rather than replaced by an untyped AST.

### Relation/fixed-point layer

`CStmtSem.v` defines loop semantics with `BW_LFix`; `HoareTriple.v` unfolds
that fixed point in its proofs. Their dependency closure is now available:

- `AUXLib.relations`;
- `FP.LiftConstructors`, `FP.PartialOrder_Setoid`, and `FP.BourbakiWitt`;
- the corresponding `SetsDomain` classes, indexed unions, relation composition,
  orders, omega-lubs, bottoms, and pointwise instances.

The sibling `sets` package now provides the exact general-set and relation
closure, and `fixedpoints` provides all six source FP implementation files,
their aggregate, and the complete declaration surface of `AUXLib.relations`.
The shared `AUXLib.Proper` implementation is used throughout, so this layer does
not introduce a second Morphisms hierarchy. `MIG-SETS-001` still bounds the
unrelated, unported remainder of the standalone SetsClass package.

`AUXLib.Tactics` is only seven source lines and is needed by the final proof
files. Its `prep_from` behavior still requires a direct tactic test rather than
being treated as an import-only shim.

### Arithmetic layer

The active Cdef files contain `lia` calls but no active `nia` call. The first
mapping remains Lean `omega`. The bit, modulo, and power proofs in
`SoundLemma.v` should reuse the migrated CompCert integer lemmas; any concrete
goal not handled by `omega` must be reported before adding a broader arithmetic
dependency. The imported Coq `Psatz` module does not by itself require a
Mathlib dependency because the active sources do not call `nia` or `psatz`.

## Cdef topological migration order

The source Makefile order is not a dependency order. The acyclic import order
for the 18 active files is:

1. `CExprDef.v`
2. `CStmtDef.v`
3. `CStateDef.v`
4. `CExprValHelper.v`
5. `EnvDef.v`
6. `StateDef.v`
7. `AsrtDenote.v`
8. `AsrtEnt.v`
9. `Witness.v`
10. `ExprSymExec.v`
11. `StateMachine.v`
12. `CSemDef.v`
13. `CExprSem.v`
14. `CStmtSem.v`
15. `SoundLemma.v`
16. `HoareTriple.v`
17. `ExprExecSound.v`
18. `SymExecSound.v`

Recommended acceptance stages:

- C1, syntax and state: items 1-6.
- C2, assertion interpretation and symbolic state: items 7-11.
- C3, denotational semantics: items 12-14. Enter this stage only after the
  fixed-point closure is ready.
- C4, soundness: items 15-18. Treat this as a separate proof-completion project.

The first 14 files have no active source `Admitted`. The final four contain 16
admitted declarations: five in `SoundLemma.v`, one in `HoareTriple.v`, one in
`ExprExecSound.v`, and nine in `SymExecSound.v`. A no-`sorry` Lean migration can
port their statements only after choosing one of three explicit policies:

1. prove the missing obligations in Lean;
2. exclude the admitted declarations and every theorem that depends on them;
3. model them as source assumptions and record that trust boundary.

Policy 1 is the only route to a fully proved soundness port. No policy decision
is needed to complete C1-C3.

## Missing prerequisites for examples

The common generated-file header imports SeparationLogic, demo932, Sets,
`AUXLib.int_auto`, `Axioms`, `Feq`, `Idents`, `ListLib`, and `VMap`, plus Coq
list/permutation/morphism/arithmetic libraries. `AUXLib.Idents` and
`AUXLib.VMap` are now complete for this example surface. The remaining common
compatibility work is therefore:

1. source-shaped compatibility for the actually used permutation and standard
   proof tactics, tested on example proof bodies;
2. any additional example tactic behavior not already covered by
   SeparationLogic tests.

The first full generated-strategy automation baseline is complete: all 18
`sll_strategy_proof.v` shapes use the shared Lean normal form and are duplicated
as end-to-end regressions. `MIG-EXAMPLES-002` records the resolved compatibility
layer and the unavoidable tactic-syntax spelling differences.

The imports of `Idents` and `VMap` are often template-generated and unused in a
particular file, but the modules should still be migrated instead of silently
editing hundreds of source-shaped headers.

Additional example clusters should be enabled only when reached:

- the 15 relational/fixed-point files now have their shared `FP`,
  `AUXLib.relations`, closure-induction, and general-set dependencies available;
  their example-local definitions and proofs remain to be migrated;
- 24 concurrent or relational files import `MonadLib`;
- the prime/exgcd group needs `Zquot`/`Znumtheory` compatibility;
- guarded, fine-grained, nested, and triple-critical groups add their local STS
  assembly libraries on top of the already migrated Critical/Nested APIs.

There are source proof gaps in examples as well. Forty-six `_proof_auto.v`
files contain 1,420 `Admitted` placeholders, and
`simple_arith/factorial_proof_manual.v` contains three additional admitted proofs.
These files must not be counted as proved Lean migrations merely because their
statements elaborate. Prefer completed manual proofs and strategy proofs for
the first vertical slices.

## Manual-proof inventory

The active example tree contains 46 files named `_proof_manual.v`. Six are
empty extension shells with imports but no `Lemma` or `Theorem` declaration:
`array_auto`, `dll_auto`, `sll_auto`, `avl_insert`, `simple_arith/add`, and
`simple_arith/max3`. The other 40 files contain 496 declarations. Exactly 45
files have no internal `Admitted`; the exception is `simple_arith/factorial`,
whose three declarations are all admitted. Thus 493 declarations have source
proof scripts, but that number alone does not imply that all transitive source
dependencies are assumption-free.

With the currently migrated shared packages, 24 manual file units need only
their example-local goal/library files before their manual proof can be ported.
Five are the empty shells listed above (excluding blocked `avl_insert`); the 19
nonempty units contain 201 declarations:

- `chars`, `dll_queue`, `eval`, `fieldtest`, `functional_queue`, `global_vars`,
  `poly_sll`, `sll`, `sll_hw`, `sll_insert_sort`, `sll_merge`, `sll_queue`,
  `sum`, and `swap`;
- `simple_arith/Signed_unsigned_test`, `simple_arith/abs`,
  `simple_arith/div_test`, `simple_arith/gcd`, and `simple_arith/mul`;
- empty units `array_auto`, `dll_auto`, `sll_auto`, `simple_arith/add`, and
  `simple_arith/max3`.

The remaining 22 units are not immediate-start units:

- ten MonadLib clients contain 180 manual declarations: `sll_split_while`,
  `int_array_merge_rel`, `sll_merge_rel`, `kmp_rel`, and the six concurrent
  compute/critical variants;
- the BinaryTree/OrdersDecFact group is complete: `avl_insert` is a source-empty
  shell, while all 69 declarations from the six nonempty BST manual files and
  their exact goal/library dependency closure are migrated and tested;
- `simple_arith/Always_pos`, `simple_arith/exgcd`, and
  `simple_arith/test_prime` contain 41 declarations and require the deferred
  nonlinear/number-theory compatibility; `test_prime` also imports an auto
  proof file with 17 source `Admitted` declarations;
- `simple_arith/factorial` has three internal source holes, while
  `simple_arith/delta` has two proved manual declarations but imports an auto
  proof file with two source `Admitted` declarations.

The completed immediate-start and binary-tree groups now comprise 25 nonempty
manual files and 270 migrated proof declarations. The aggregate Lean entry
imports all of them and checks the 69 binary-tree declarations in addition to
the 172 declarations completed before this group.

"Immediate-start" here means that no additional shared package is required;
the paired generated goal and example-local library still have to be migrated
and tested. The `sll` manual unit is now complete: all 29 declarations from
`sll_proof_manual.v` and the exact 29 witness propositions they consume from
`sll_goal.v` are present and tested. The source `sll_goal.v` contains 113
generated definitions in total; the other 84 are outside this manual-proof
slice and are not yet claimed as migrated. `sll_merge_lib` is present for the
next local goal and manual-proof slice.

## Recommended first example slice

The first completed, non-Cdef example slice now has two acceptance layers:

1. `examples/sll_lib.v`;
2. `examples/sll_strategy_goal.v`;
3. `examples/sll_strategy_proof.v`;
4. `examples/sll_strategy_goal_check.v`;
5. the 29-witness dependency slice of `examples/sll_goal.v`;
6. all 29 declarations of `examples/sll_proof_manual.v`.

This slice builds with all three recursive assertions, 12 library lemmas, 18
strategy propositions, 18 correctness proofs, the final correctness assembly,
29 manual witness propositions, and 29 manual proof theorems, without importing
the Cdef pipeline. The 18 strategy proofs and 18 independent strategy
regressions exercise the shared normal form. The 29 manual proofs additionally
exercise source-shaped sequencing of `pre_process`, `Exists`, `Intros`,
`entailer!`, `sep_apply`, relation rewriting, recursive predicate unfolding,
list normalization, arithmetic discharge, and induction. They are acceptance
tests for tactic compatibility: a proof is not accepted merely because the
same theorem can be closed by a direct separation-algebra argument. See
resolved `MIG-EXAMPLES-002` and intentional `MIG-EXAMPLES-003` for the bounded
Lean spellings of those source tactic phases. The source `sll_proof_auto.v` is
an admitted placeholder and is not an acceptance target, and the remaining 84
unreferenced declarations of `sll_goal.v` remain a later generated-goal slice.

## Next example stage

An independent review narrowed the earlier readiness claim. The FP and
`AUXLib.Relations` common layer is available, but the complete set of 15 files
that explicitly imports it is not ready to port as a group: the merge and KMP
families also require the currently unported `MonadLib`. The next work is split
into the following gates.

### E2-0: real closure-induction client (completed)

Migrate `examples/sll_merge_lib.v` before MonadLib. It has eight
definition/inductive declarations and 16 lemmas, does not import MonadLib, and
uses `induction_1n` in `merge_steps_increasing` and `merge_steps_perm` with the
real endpoint-dependent proof context. Both source-shaped proofs are mandatory
end-to-end tests; synthetic closure tests alone are no longer sufficient.
The existing `AUXLib.Permutation` compatibility is exercised by the same file
rather than replaced with a second permutation relation. The Lean module now
contains all eight definition/inductive declarations and 16 lemmas. Its two
closure proofs use `induction_1n` over a shared state invariant/content normal
form, preserving the public six-list theorem interfaces while giving Lean an
explicit endpoint motive.

### E2-1: restore source-shaped rconcat (completed)

Before introducing MonadLib, extend the RelsDomain slice with the source
`lift_PRE_RELS`, `lift_PRE_RELS_ID`, the three `ACCUM_*` property classes, and
the five `ListConn` list instances. Then redefine `FP.rconcat` through
`Rels.concat` exactly as in Coq and close `MIG-FP-001`.

No active MonadLib or example file directly mentions `rconcat`; this was not a
compile blocker. The repair is nevertheless complete: `lift_PRE_RELS`,
`lift_PRE_RELS_ID`, the three accumulation-law classes, all five `ListConn`
instances, the `X • Y` notation, and the generic `Rels.concat` definition shape
are present and regression-tested. `MIG-FP-001` is resolved.

### E2-2: MonadLib aggregate closure

Create sibling package `MonadLib`, requiring `fixedpoints` and the
existing sibling dependencies through local paths. Preserve these source module
paths and migrate them in dependency order:

1. `MonadLib.Monad`, then `OptionMonad.OptionBasic` and `ListMonad.ListBasic`.
2. `SetMonad.SetBasic`, `SetMonad.FixpointLib`, `SetMonad.SetHoare`, and its
   aggregate.
3. `StateRelMonad.StateRelBasic`, `StateRelMonad.FixpointLib`,
   `StateRelMonad.StateRelHoare`, `StateRelMonad.safeexec_lib`, and its aggregate.
4. `MonadErr.MonadErrBasic`, `MonadErr.MonadErrLoop`,
   `MonadErr.MonadErrHoare`, `MonadErr.monadesafe_lib`, and
   `MonadErr.StateRelMonadErr`.
5. `OptionMonad`, `ListMonad`, and the top-level `MonadLib.MonadLib` aggregate.

`MonadErrHoarePartial.v` and `MonadTest.v` are not reachable from the aggregate
used by the target examples and remain outside this dependency slice. Their
omission is a planning boundary, not a claim that the standalone MonadLib
repository is complete.

The monadic notation scope and source call forms must be retained, including
bind, pattern bind, sequencing, `return`, `assume`, `assume!!`, `continue`, and
`break`. Tactics are accepted only after their actual source clients pass. The
minimum behavioral set is `unfold_monad`, `prog_nf`, `unfold_loop`,
`mono_cont_auto`, the `hoare_*` family, `safe_step`, `safe_choice_l/r`, and
`safe_equiv`; isolated one-goal tests do not establish compatibility.

### E2-3: Monad examples and external ListLib slice

Port `MonadLib.Examples.mergesort` first. It is the common semantic dependency
of `sll_merge_rel`, `int_array_merge_rel`, `safeexec_strategy`, and
`sll_split_while`, and directly exercises the fixed-point and Hoare automation.

Before `MonadLib.Examples.kmp`, create the source-shaped `ListLib` compatibility
slice for `ListLib.Base.Positional`, `ListLib.Base.Inductive`, and
`ListLib.General.Length`. These module paths are distinct from
`AUXLib.ListLib`; reuse Lean lists and existing AUXLib lemmas internally without
collapsing the public namespaces. Then port KMP and its MonadErr automation.

### E2-4: vertical example slices

After E2-0 through E2-3, use this order:

1. `sll_merge_rel_lib` plus `safeexec_strategy_goal/proof`.
2. `sll_split_while_goal`, both proof files, and goal check. This is the first
   complete vertical slice because it has the smallest generated proof gap: 28
   goals, 14 source `Admitted` auto obligations, and four manual proofs.
3. `int_array_merge_rel`: 74 goals, 43 source `Admitted` auto obligations, and
   16 manual proofs.
4. `kmp_rel_lib` plus `safeexecE_strategy_goal/proof`, followed by `kmp_rel`:
   76 goals, 44 source `Admitted` auto obligations, and 17 manual proofs.
5. `sll_merge_rel`: 121 goals, 56 source `Admitted` auto obligations, and 29
   manual proofs.

The four `_proof_auto.v` files contain 157 `Admitted` declarations in Coq.
They may be used as obligation inventories, but a Lean goal-check module is
accepted only after every included declaration has a real proof. No source
assumption, `sorry`, weakened theorem, or omitted module member may stand in for
those proofs.

## Acceptance rules

- Preserve source names, binder order, definitions, theorem direction, and
  tactic call forms. Do not replace the typed ASRT/Cdef core with a weaker AST.
- Add per-file API inventories and behavior tests before advancing a stage.
- Reject `sorry`, `admit`, `unsafe`, and source-absent axioms.
- Record only real public-interface or behavior mismatches in
  `migration_inconsistencies.md`; source proof holes and not-yet-migrated
  dependency slices belong in this planning document until a policy is chosen.
- Keep `pocv02.v` deferred. It is not a prerequisite for either the first Cdef
  stages or the first example slice.
