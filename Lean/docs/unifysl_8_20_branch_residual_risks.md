# Unifysl 8.20 Branch Residual Risks

This document is the residual-risk log for retargeting the existing Lean
migration from `unifysl-prp` master to `unifysl-prp-8.20`.

It is intentionally separate from
`docs/unifysl_lean_migration_residual_risks.md`, which records risks from the
original master-based migration.

## Baseline

```text
master source:
  path: unifysl-prp
  branch: master
  commit: b64df6ff7e250f26f6ed1ebb4475accdee99f455

8.20 source:
  path: unifysl-prp_qcp
  branch: unifysl-prp-8.20
  commit: f5160c97eef28c07266bfdee8e1a2fbaa5c20e59
```

## Global Risks

### Branch Retargeting Scope

The current Lean migration was completed against the master branch. The 8.20
branch changes 41 of the 73 already migrated source modules and adds five
`ModelLanguage*` modules. The final `demo932/Interface.v` also expands from
342 lines to 598 lines.

Impact:

- The existing Lean tree is a useful base, but it is not a complete 8.20
  migration.
- Final-interface compatibility cannot be achieved by renaming only the L22
  file.
- Lower-layer API drift must be handled in dependency order.

Mitigation:

- Follow `docs/unifysl_8_20_branch_correction_plan.md`.
- Correct modules layer by layer from L0 to L22.

### Active Versus Commented Source

Some 8.20 files contain large commented legacy blocks. Text search can report
imports and declarations inside comments.

Known files:

```text
SeparationLogic/ShallowEmbedded/Join2Sepcon.v
SeparationLogic/ShallowEmbedded/Model2CoqPropEmp.v
```

Impact:

- A naive dependency scan can overstate the active role of these files.
- The 8.20 final interface uses the new `ModelLanguage*` modules for assembly
  rather than the master-style active content of these legacy files.

Mitigation:

- Strip or manually ignore Coq comments when computing active declarations.
- Keep current Lean master-compatible files unless an explicit cleanup task
  removes them.
- Use `ModelLanguage*` modules for 8.20 final interface assembly.

## Inserted 8.20 Modules

These modules are not yet part of the current Lean migration and must be
introduced during branch correction.

```text
L4  GeneralLogic/ShallowEmbedded/ModelLanguage.v
L7  MinimumLogic/ShallowEmbedded/ModelLanguageMinimumLogic.v
L13 PropositionalLogic/ShallowEmbedded/ModelLanguagePropositionalLogic.v
L14 MetaLogicInj/ShallowEmbedded/ModelLanguageMetaLogic.v
L17 SeparationLogic/ShallowEmbedded/ModelLanguageSeparationLogic.v
```

Risk:

- Their declarations overlap semantically with existing master-era Lean modules
  such as `Join2Sepcon` and `Model2CoqPropEmp`, but the public module
  organization differs.

Mitigation:

- Preserve 8.20 module-qualified names.
- Reuse existing proofs when statements align, but do not hide missing 8.20 API
  behind master names.

## Layer Risk Log

### L0

Status: complete.

Changed 8.20 source files:

```text
lib/Bijection.v
lib/register_typeclass.v
SeparationLogic/Model/SeparationAlgebra.v
```

Known risks:

- `lib/Bijection.v` changed only in the Coq standard-library proof script for
  `nat2_nat_bijection.su_bij`; the public relation, record, and theorem
  statements are unchanged. No Lean API change was needed.
- `lib/register_typeclass.v` changed `RegisterClass` from an explicit Coq
  sort annotation to the default sort form. The Lean implementation already
  exposes `RegisterClass` as a real typeclass and preserves the tactic
  behavior needed downstream. No Lean API change was needed.
- `SeparationLogic/Model/SeparationAlgebra.v` changed `SeparationAlgebra` from
  an explicit Coq sort annotation to the default sort form. Field names and
  semantics are unchanged. No Lean API change was needed.
- Review caveat: Coq 8.20's active `RegisterClass`, `SeparationAlgebra`, and
  `UnitJoinRelation` live in the proposition universe, while current Lean
  encodes these as `Type` classes. This is inherited from the master migration
  and is not a new 8.20 branch delta. It is currently accepted because the
  public fields, instance behavior, and downstream checks align.
- File-level validation passed for `Bijection.lean`, `register_typeclass.lean`,
  and `SeparationAlgebra.lean`.

Blockers:

- No L0 blocker is currently recorded.

### L1

Status: complete.

Changed 8.20 source files:

```text
none detected among the existing 73 migrated modules
```

Known risks:

- No changed files detected among the existing 73 migrated modules.
- File-level validation passed for `GeneralLogic/Base.lean`,
  `Bisimulation.lean`, `Countable.lean`, `Ensembles_ext.lean`, and
  `Equivalence_ext.lean`.

Blockers:

- No L1 blocker is currently recorded.

### L2

Status: complete.

Changed 8.20 source files:

```text
none detected among the existing 73 migrated modules
```

Known risks:

- No changed files detected among the existing 73 migrated modules.
- File-level validation passed for `BasicDeduction.lean`,
  `TheoryOfSequentCalculus.lean`, `PredicateAsLang.lean`,
  `MetaLogicInj/Syntax.lean`, `MinimumLogic/Syntax.lean`,
  `SeparationLogic/Syntax.lean`, `List_Func_ext.lean`, and
  `RelationPairs_ext.lean`.

Blockers:

- No L2 blocker is currently recorded.

### L3

Status: complete.

Changed 8.20 source files:

```text
GeneralLogic/ProofTheory/BasicLogicEquiv.v
```

Known risks:

- 8.20 renames the `EquivDerivable1` projection from
  `logic_equiv_derivable1` to `__logic_equiv_derivable1` and adds
  `Deduction2Equiv_bE` to `GeneralLogic/ProofTheory/BasicLogicEquiv.v`.
- Lean now exposes `__logic_equiv_derivable1` as the `EquivDerivable1` class
  field and public projection theorem. The previous general-logic helper theorem
  `logic_equiv_derivable1` was removed during old-module cleanup.
- Lean now provides `Deduction2Equiv_bE`.
- `LogicGenerator/demo932/Interface.lean` still has a
  `LogicTheoremSig.logic_equiv_derivable1` structure field, matching the
  generated interface surface; this is separate from the general-logic
  `EquivDerivable1` class projection cleanup.
- Review caveat: 8.20 also has a same-basename `Deduction2Equiv_bE` in
  `MinimumLogic/ProofTheory/Minimum.v`; this is an L4 concern if exact
  module-qualified name parity becomes necessary.
- File-level validation passed for all L3 modules after the change.

Blockers:

- No L3 blocker is currently recorded.

### L4

Status: complete.

Changed 8.20 source files:

```text
GeneralLogic/Semantics/Kripke.v
MinimumLogic/ProofTheory/Minimum.v
PropositionalLogic/Semantics/Trivial.v
SeparationLogic/Model/OrderedSA.v
```

New 8.20 module:

```text
GeneralLogic/ShallowEmbedded/ModelLanguage.v
```

Known risks:

- `GeneralLogic/Semantics/Kripke.v`,
  `PropositionalLogic/Semantics/Trivial.v`, and
  `SeparationLogic/Model/OrderedSA.v` only changed Coq sort annotations or
  comments in active declarations. No Lean API change was needed for those
  files.
- `MinimumLogic/ProofTheory/Minimum.v` has a substantial 8.20 API rename. Lean
  now exposes the 8.20 names `DerivableFromProvable`,
  `Derivable1FromProvable`, `ProvableFromDerivable`,
  `ProvableFromDerivable1`, `__derivable_provable`,
  `__derivable1_provable`, `__provable_derivable`,
  `__logic_equiv_provable`, `__provable_derivable1`,
  `provables_modus_ponens`, `provable_axiom1`, `provable_axiom2`,
  `derivables_modus_ponens`, `derivables_impp_intros`,
  `provables_impp_trans`, the `MinimumDeduction` class, its projection-style
  theorem names, `aux_minimun_rule10`, `aux_minimun_rule11`,
  `aux_minimun_rule12`, `Deduction2Axiomatization_minAX'`,
  `Deduction2Axiomatization_GammaD1P'`, `derivables_weaken0`,
  `derivables_impp_elim`, `derivables_impp_theorem`,
  `derivables_multi_impp_theorem`, `derivables_impp_intros_l`,
  `derivables_impp_trans`, `derivables_impp_arg_switch`, and
  `provable_derivable_right`.
- The renamed class names in `Minimum.lean` are Lean `abbrev` aliases over the
  master-compatible classes. This preserves existing migrated code. As with
  the L3 class-field caveat, exact 8.20-style record literals using only the
  new field names would need adapters or a larger class-field refactor.
- 8.20 has a same-basename `Deduction2Equiv_bE` in both
  `GeneralLogic/ProofTheory/BasicLogicEquiv.v` and
  `MinimumLogic/ProofTheory/Minimum.v`. The Lean root namespace contains one
  public `Deduction2Equiv_bE`, added at L3, whose statement matches the common
  theorem shape. No duplicate root constant was introduced.
- `GeneralLogic/ShallowEmbedded/ModelLanguage.lean` was added under namespace
  `Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage`. This avoids root-name
  collisions with the master-era model helpers that were initially migrated
  under `SeparationLogic.ShallowEmbedded.Join2Sepcon` and
  `SeparationLogic.ShallowEmbedded.Model2CoqPropEmp`; those old helper modules
  were later removed during the 8.20 cleanup pass.
- Adding 8.20 public names `derivable1_axiom1` and `derivable1_axiom2` exposed
  an existing downstream private-helper name collision in
  `PropositionalLogic/ProofTheory/Intuitionistic.lean`. The private helpers
  were renamed to narrower private names; no public L8 API changed.
- File-level validation passed for all L4 modules, including the new
  `ModelLanguage.lean`. `lake build Unifysl` also passed after the downstream
  private-helper rename.

Blockers:

- No L4 blocker is currently recorded.

### L5

Status: complete.

Changed 8.20 source files:

```text
MinimumLogic/ProofTheory/RewriteClass.v
MinimumLogic/Semantics/Kripke.v
PropositionalLogic/Sound/Sound_Classical_Trivial.v
```

Known risks:

- `MinimumLogic/Semantics/Kripke.v` only changed the explicit Coq class sort
  annotation of `KripkeMinimumSemantics`; active field statements are
  unchanged. No Lean API change was needed.
- `SeparationLogic/Model/OSAGenerators.v` and
  `SeparationLogic/Semantics/{EmpSemantics,WeakSemantics,StrongSemantics}.v`
  had no 8.20 source delta for this layer.
- `MinimumLogic/ProofTheory/RewriteClass.v` was updated in 8.20 to use the
  L4 renamed minimum-logic helper names and to rename
  `impp_proper_impp` to `provables_impp_proper_impp`. Lean now exposes the
  8.20 instance name directly; the previous master-era instance name was
  removed during cleanup.
- `PropositionalLogic/Sound/Sound_Classical_Trivial.v` renamed several
  soundness lemmas with a `sound_provable_*` prefix. Lean now exposes
  `sound_provable_andp_elim1`, `sound_provable_andp_elim2`,
  `sound_provable_orp_intros1`, `sound_provable_orp_intros2`,
  `sound_provable_orp_elim`, `sound_provable_falsep_elim`, and
  `sound_provable_peirce_law`. The previous master-era short names were
  removed during cleanup.
- File-level validation passed for all L5 modules. `lake build Unifysl`
  passed after the rename cleanup.

Blockers:

- No L5 blocker is currently recorded.

### L6

Status: complete.

Changed 8.20 source files:

```text
MinimumLogic/ProofTheory/TheoryOfJudgement.v
PropositionalLogic/Semantics/Kripke.v
```

Known risks:

- `ProofTheoryPatternsP.v`, `SemanticEquiv.v`, and
  `SeparationLogic/Semantics/FlatSemantics.v` had no 8.20 source delta for
  this layer.
- `PropositionalLogic/Semantics/Kripke.v` only changed explicit Coq class sort
  annotations for the Kripke propositional semantics classes. Active field
  statements are unchanged, so no Lean API change was needed.
- `MinimumLogic/ProofTheory/TheoryOfJudgement.v` changed to use the L4
  renamed `Derivable1FromProvable` / `ProvableFromDerivable1` APIs and added
  `Axiomatization2Deduction_minD`. Lean now exposes
  `Axiomatization2Deduction_GammaPD1` with the 8.20 surface class alias and
  adds a fully proved `Axiomatization2Deduction_minD`.
- File-level validation passed for all L6 modules. `lake build Unifysl`
  passed after the `TheoryOfJudgement.lean` update.

Blockers:

- No L6 blocker is currently recorded.

### L7

Status: complete.

Changed 8.20 source files:

```text
MinimumLogic/ProofTheory/ExtensionTactic.v
SeparationLogic/Sound/Sound_Flat.v
```

New 8.20 module:

```text
MinimumLogic/ShallowEmbedded/ModelLanguageMinimumLogic.v
```

Known risks:

- `MinimumLogic/ProofTheory/ExtensionTactic.v` only changed Coq sort
  annotations for empty registration kinds; Lean tactic and registration
  behavior did not require a semantic change.
- `MinimumLogic/ProofTheory/ProofTheoryPatterns.v` had no 8.20 source delta.
- `MinimumLogic/ShallowEmbedded/ModelLanguageMinimumLogic.v` was added in
  8.20. Lean now provides
  `Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic` with
  `Model2Impp`, `ImppDefinition_Model`, `Model2Impp_Normal`, and `kminSM`,
  built on the L4 model-language base namespace.
- `SeparationLogic/Sound/Sound_Flat.v` renamed several soundness lemmas with
  `sound_provable_*` / `sound_provables_*` names. Lean now exposes
  `sound_provable_sepcon_assoc1`,
  `sound_provables_wand_sepcon_adjoint`,
  `sound_provable_sepcon_mono`,
  `sound_provable_sepcon_elim1`,
  `sound_provable_sepcon_emp_derives`,
  `sound_provable_derives_sepcon_emp`,
  `sound_provable_sepcon_andp_emp_derives`, and
  `sound_provable_emp_dup`. The previous master-era short names were removed
  during cleanup.
- File-level validation passed for all L7 modules, including the new
  `ModelLanguageMinimumLogic.lean`. `lake build Unifysl` passed.

Blockers:

- No L7 blocker is currently recorded.

### L8

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
PropositionalLogic/ProofTheory/Intuitionistic.v
```

Known risks:

- `PropositionalLogic/ProofTheory/Intuitionistic.v` in 8.20 renames many public
  proof rules to `provable_*`, `provables_*`, `derivables_*`, and
  `derivable1s_*` forms. Lean now exposes these 8.20 theorem names directly.
  The previous master-era theorem-name alias block was removed during old-module
  cleanup after the user confirmed there is no external Lean code to preserve.
- The propositional proof-theory class fields in `Intuitionistic.lean` now use
  the 8.20 field/projection names directly, including `provable_*`,
  `derivables_*`, `derivable1s_truep_intros`,
  `derivable1s_impp_andp_adjoint`,
  `derivable1s_contrapositivePP`,
  `derivable1s_contradiction_elim`, and
  `logic_equiv_provable_iffp_intros`.
- The 8.20 theorem name `derivable1_impp_refl` collides at Lean root namespace
  with the L4 minimum-logic theorem already exposed as
  `Unifysl.derivable1_impp_refl`. The L8 theorem is therefore available as the
  module-qualified theorem alias
  `Unifysl.PropositionalLogic.ProofTheory.Intuitionistic.derivable1_impp_refl`,
  while the root name remains owned by the minimum-logic layer.
- `LogicGenerator/demo932/Interface.lean` still contains local helper theorem
  names `derivable1_andp_intros` and `derivable1_impp_andp_adjoint`. The
  corresponding `LogicTheoremSig` fields are already named
  `derivable1s_truep_intros` and `derivable1s_impp_andp_adjoint`; the helper
  theorem names avoid a Lean declaration-name collision with those structure
  fields.
- The 8.20 theorem `provable_andp_impp` is now implemented with its Coq 8.20
  biconditional statement. During cleanup we found that the earlier
  master-migration alias pointed at the different rule now named
  `provable_derives_impp_andp`; that mismatch was fixed and downstream uses were
  updated.
- `TrueAndLogicEquiv` was extended to carry both 8.20 fields
  `logic_equiv_andp_truep` and `logic_equiv_truep_andp`.
- New 8.20 conversion rules `Deduction2LogicEquiv_andpE`,
  `Deduction2LogicEquiv_orpE`, `Deduction2LogicEquiv_truepandpE`, and
  `logic_equiv_andp_swap` are fully proved in Lean from the existing
  `EquivDerivable1`, `AndDeduction`, `OrDeduction`, and `TrueDeduction`
  infrastructure.

Blockers:

- No L8 blocker is currently recorded.

### L9

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
PropositionalLogic/ProofTheory/DeMorgan.v
PropositionalLogic/ProofTheory/RewriteClass.v
```

Known risks:

- `DeMorganAxiomatization` in 8.20 renames the weak excluded middle projection
  to `provable_weak_excluded_middle`. Lean keeps the previous class field for
  source compatibility and adds the 8.20 projection name as a theorem alias.
- `solve_weak_classic` is renamed to `provables_weak_classic` in 8.20. Lean now
  exposes the 8.20 theorem name directly; the previous master-era theorem name
  was removed during old-module cleanup.
- `PropositionalLogic/ProofTheory/RewriteClass.v` renames many `Proper`
  instances to `provables_*`, `derivables_*`, `derivable1s_*`, and
  `logic_equiv_*` names. Lean now exposes the 8.20 instance names directly; the
  previous master-era instance names were removed during old-module cleanup.

Blockers:

- No L9 blocker is currently recorded.

### L10

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
PropositionalLogic/ProofTheory/GodelDummett.v
PropositionalLogic/ProofTheory/ProofTheoryPatterns.v
```

Known risks:

- `GodelDummett.v` changes are proof-script/API-renaming adaptations only; no
  new public Lean name was required.
- `ProofTheoryPatterns.v` renames the root iterated-conjunction lemmas to
  `provable_iter_andp_sepc_right`,
  `provable_iter_andp_unfold_right_assoc`, and
  `provable_iter_andp_unfold_left_assoc`. Lean now exposes the 8.20 theorem
  names directly; the prior root theorem names were removed during old-module
  cleanup.
- The 8.20 name `provable_iter_andp_sepc_right` preserves the source spelling
  `sepc`.

Blockers:

- No L10 blocker is currently recorded.

### L11

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
PropositionalLogic/ProofTheory/TheoryOfClassicalAxioms.v
```

Known risks:

- `TheoryOfClassicalAxioms.v` in 8.20 renames `PeirceLaw.__peirce_law`
  to `__provable_peirce_law` and `ImplyToOr.__impp2orp1` to
  `__provable_derives_negp_orp`. Lean now uses the 8.20 names as the actual
  class fields. The previous master-era namespace aliases were removed during
  old-module cleanup.
- `ImplyToOr2ExcludedMiddle` keeps the 8.20 source context shape, including the
  otherwise unused false-language hypotheses.
- Lean exposes two minimal sequent-calculus helper theorems,
  `Axiomatization2SequentCalculus_orpSC_minimal` and
  `Axiomatization2SequentCalculus_inegpSC_minimal`, as proof infrastructure for
  later files. They are not active Coq declarations, so this is a small extra
  public surface rather than a weakened migration item.

Blockers:

- No L11 blocker is currently recorded.

### L12

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
PropositionalLogic/ProofTheory/Classical.v
```

Known risks:

- `Classical.v` in 8.20 renames many public rules to `provable_*`,
  `provables_*`, `derivables_*`, and `derivable1_*` names. Lean now exposes the
  8.20 theorem names directly; the previous master-era theorem names were
  removed during old-module cleanup.
- `ClassicalAxiomatization`, `ClassicalSequentCalculus`,
-  `ClassicalDeduction`, and `ClassicalPropositionalLogicEquiv` keep their
  previous field names in Lean for constructor compatibility; 8.20 projection
  names such as `provable_peirce_law`, `derivables_by_contradiction`,
  `derivable1_excluded_middle`, `logic_equiv_excluded_middle`, and
  `logic_equiv_DeMorgen` are provided as theorem aliases.
- `deduction_derived_neg` uses the 8.20 field names
  `derivables_negp_andp_fold1`, `derivables_negp_andp_fold2`,
  `derivables_negp_orp_intros`, `derivables_negp_impp`,
  `derivables_negp_impp_fold`, and `derivable_negp_falsep_r`; the previous
  Lean field names are preserved as namespace aliases.
- Register instances keep the Coq numbering for `P2D_reg 10` and `D2P_reg 8`.

Blockers:

- No L12 blocker is currently recorded.

### L13

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
MetaLogicInj/ProofTheory/ProofRules.v
PropositionalLogic/ProofTheory/TheoryOfPropositionalConnectives.v
PropositionalLogic/ShallowEmbedded/PredicatePropositionalLogic.v
```

New 8.20 module:

```text
PropositionalLogic/ShallowEmbedded/ModelLanguagePropositionalLogic.v
```

Known risks:

- `MetaLogicInj/ProofTheory/ProofRules.v` in 8.20 renames Coq-proposition
  proof rules and class fields to `provables_*`, `derivables_*`,
  `derivable1s_*`, and `logic_equiv_*` names. Lean now uses the 8.20 names as
  actual theorem names and class fields where the source changed them. Previous
  master-era theorem names were removed during old-module cleanup.
- The newly active
  `PropositionalLogic/ShallowEmbedded/ModelLanguagePropositionalLogic.v` is
  migrated as
  `Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic`.
  The module keeps Coq declaration names inside this namespace to avoid root
  collisions with other model-language builders.
- `PredicatePropositionalLogic.v` changes are proof-rule rename adaptations.
  `Pred_cpGamma` remains inside a Coq commented block in 8.20 and is therefore
  outside the active API scope.

Blockers:

- No L13 blocker is currently recorded.

### L14

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
SeparationLogic/ProofTheory/SeparationLogic.v
```

New 8.20 module:

```text
MetaLogicInj/ShallowEmbedded/ModelLanguageMetaLogic.v
```

Known risks:

- `SeparationLogic/ProofTheory/SeparationLogic.v` in 8.20 renames many class
  fields and public lemmas to `provable_*`, `provables_*`,
  `derivable1_*`, `derivable1s_*`, and `logic_equiv_*` names. Lean now uses
  the 8.20 field names as the actual class fields and keeps the older field
  names as namespace aliases for existing Lean code.
- Several 8.20 active helper lemmas were added in Lean:
  `derivable1_sepcon_orp_l`, `derivable1_sepcon_orp_r`,
  `logic_equiv_sepcon_orp`, `logic_equiv_orp_sepcon`,
  `logic_equiv_wand`, `derivable1s_emp_l_unfold`, and
  `derivable1s_emp_sepcon_unfold`, plus the renamed provable-level aliases.
- The new metalevel model-language module is migrated as
  `Unifysl.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic`. Its
  declarations are kept in that namespace to avoid collisions with other
  model-language builders.
- Updating the L14 class field names exposed old record labels in the
  initially migrated `Join2Sepcon` helper and in
  `SeparationLogic/ShallowEmbedded/PredicateSeparationLogic.lean`. Those
  labels were mechanically changed to the 8.20 field names; the old helper was
  later removed during cleanup, and predicate proof bodies were unchanged.

Blockers:

- No L14 blocker is currently recorded.

### L15

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
SeparationLogic/ProofTheory/TheoryOfSeparationAxioms.v
```

Known risks:

- `SepconMonoAxiomatization` and `SepconAxiomatization_weak` now use the
  8.20 field names `__provable_sepcon_mono`,
  `__provable_sepcon_comm_impp`, and `__provable_sepcon_assoc1` as actual Lean
  class fields. Older field names are kept as namespace aliases.
- Updating those field names exposed an old record label in
  `SeparationLogic/ShallowEmbedded/PredicateSeparationLogic.lean`; the label
  was mechanically changed to the 8.20 name with no proof-body change.

Blockers:

- No L15 blocker is currently recorded.

### L16

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
SeparationLogic/ProofTheory/Deduction.v
SeparationLogic/ShallowEmbedded/PredicateSeparationLogic.v
```

Known risks:

- `SepconMonoDeduction`, `SepconDeduction_weak`,
  `SepconLogicEquiv_weak_iffp`, and `EmpLogicEquiv_iffp` now use the 8.20
  field names as actual Lean class fields. Older field names remain as
  namespace aliases for compatibility.
- `Deduction2LogicEquiv_sepconE`, `Deduction2LogicEquiv_empE`, and
  `logic_equiv_sepcon_swap` were added to match new active declarations in
  `SeparationLogic/ProofTheory/Deduction.v`.
- `PredicateSeparationLogic.lean` now calls the 8.20 soundness aliases such as
  `sound_provable_sepcon_assoc1`,
  `sound_provables_wand_sepcon_adjoint`,
  `sound_provable_sepcon_elim1`,
  `sound_provable_sepcon_emp_derives`, and
  `sound_provable_derives_sepcon_emp`.

Blockers:

- No L16 blocker is currently recorded.

### L17

Status: corrected and validated against the current Lean build.

Changed 8.20 source files:

```text
SeparationLogic/ProofTheory/RewriteClass.v
SeparationLogic/ShallowEmbedded/Join2Sepcon.v
SeparationLogic/ShallowEmbedded/Model2CoqPropEmp.v
```

New 8.20 module:

```text
SeparationLogic/ShallowEmbedded/ModelLanguageSeparationLogic.v
```

Known risks:

- `SeparationLogic/ProofTheory/RewriteClass.v` renames the eight exported
  `Proper` instances. Lean now exposes the 8.20 names
  `provables_sepcon_proper_impp`, `provables_wand_proper_impp`,
  `provables_sepcon_proper_iffp`, `provables_wand_proper_iffp`,
  `derivable1s_sepcon_proper`, `derivable1s_wand_proper`,
  `logic_equiv_sepcon_proper`, and `logic_equiv_wand_proper` directly. The
  older master-era instance names were removed during old-module cleanup.
- The new 8.20 module
  `SeparationLogic/ShallowEmbedded/ModelLanguageSeparationLogic.v` is migrated
  as
  `Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic` and
  uses the L4/L7 model-language modules as its base.
- `Join2Sepcon.v` and `Model2CoqPropEmp.v` are largely commented in 8.20.
  Existing Lean modules with those names are retained because later Lean files
  and the demo interface still import them. The new 8.20 assembly path should
  prefer `ModelLanguageSeparationLogic`.

Blockers:

- No L17 blocker is currently recorded.

### L18

Status: complete.

Changed 8.20 source files:

```text
SeparationLogic/ProofTheory/Corable.v
SeparationLogic/ProofTheory/DerivedRules.v
SeparationLogic/ProofTheory/TheoryOfCancel.v
```

Known risks:

- `Corable.v` changed proof scripts to use newer theorem names, but active
  declarations and statements are unchanged. No Lean API change was needed.
- `DerivedRules.v` renames several exported lemmas. Lean now exposes the 8.20
  names `provable_andp_sepcon_derives`, `provable_sepcon_andp_derives`,
  `provable_coq_prop_sepcon_andp1`, `provable_coq_prop_sepcon_andp2`, and
  `provable_coq_prop_andp_sepcon2`. Older master-migration helper names were
  made private/internal or removed during old-module cleanup.
- `TheoryOfCancel.v` renames the local associativity helper to
  `provable_sepcon_assoc2`. Lean provides it under
  `Unifysl.SeparationLogic.ProofTheory.TheoryOfCancel.provable_sepcon_assoc2`.
  The previous local name `sepcon_assoc2` was removed during old-module cleanup;
  root `Unifysl.sepcon_assoc2` remains the separation proof-theory theorem.
- File-level validation passed for `Corable.lean`, `DerivedRules.lean`, and
  `TheoryOfCancel.lean`; `lake build Unifysl` passed after the corrections.

Blockers:

- No L18 blocker is currently recorded.

### L19

Status: complete.

Changed 8.20 source files:

```text
SeparationLogic/ProofTheory/IterSepcon.v
```

Known risks:

- `IterSepconAxiomatization_left` and `IterSepconDeduction_left` use the
  8.20 field names `provable_iter_sepcon_derives`,
  `provable_derives_iter_sepcon`, `derivable1_iter_sepcon_l`, and
  `derivable1_iter_sepcon_r`.
- Lean now exposes the 8.20 provable rule names
  `provable_iter_sepcon_spec_left`, `provable_iter_sepcon_spec_right`,
  `provable_sepcon_iter_sepcon`,
  `provable_iter_sepcon_unfold_right_assoc`, and
  `provable_iter_sepcon_unfold_left_assoc` directly. Older root names were
  removed during old-module cleanup.
- The 8.20 theorem
  `IterSepconAxiomatization_left2IterSepconDeduction_left` is implemented using
  the same logical route as Coq: construct the local provable structure from
  `Derivable1`, derive the iterated-separating-conjunction axiomatization from
  the fold-left definition, then translate back through
  `__derivable1_provable`.
- File-level validation passed for `IterSepcon.lean`; `lake build Unifysl`
  passed after the correction.

Blockers:

- No L19 blocker is currently recorded.

### L20

Status: complete.

Changed 8.20 source files:

```text
ShallowQuantifierLogic/ProofTheory.v
```

Known risks:

- `ShallowQuantifierLogic/ProofTheory.v` renames many Coq class projections
  from the master-era names to 8.20 names such as `derivable1s_exp_r`,
  `derivable1s_exp_l`, `derivable1s_allp_r`, `derivable1s_allp_l`,
  `derivable1_exp_andp_l`, `derivable1_exp_sepcon_l`, and
  `derivable1_iter_sepcon_flatten`.
- Lean now exposes these 8.20 names as root theorem projections while
  retaining the master-migration class field names used by existing Lean record
  literals. This keeps current downstream files compiling and gives 8.20-style
  callers the expected names, but exact record-literal field parity would
  require a larger class-field rename pass across downstream interface code.
- Lean now includes the 8.20-added quantifier rules
  `derivable1s_ex_l_unfold`, `derivable1_allp_allp_swap`, and
  `derivable1_exp_allp_swap`.
- Lean now includes the 8.20-added equivalence rules
  `logic_equiv_exp_andp`, `logic_equiv_exp_sepcon`,
  `logic_equiv_sepcon_coq_prop_andp`,
  `logic_equiv_coq_prop_andp_sepcon`, and
  `logic_equiv_coq_prop_andp_sepcon_truep`.
- Lean now exposes the 8.20 names for the separation/coq-prop helper rules and
  iterated-sepcon/coq-prop helper rule while retaining the previous helper
  names for compatibility.
- File-level validation passed for `ShallowQuantifierLogic/ProofTheory.lean`;
  `lake build Unifysl` passed after the correction.

Blockers:

- No L20 blocker is currently recorded.

### L21

Status: complete.

Changed 8.20 source files:

```text
ShallowQuantifierLogic/ModelConstrALL.v
ShallowQuantifierLogic/ModelConstrEX.v
```

Known risks:

- `ModelConstrEX.v` and `ModelConstrALL.v` rename the generated derivable1
  instance from `GammaD1` to `Model2Derivable1`.
- Lean now uses `Model2Derivable1` as the actual instance name in both
  modules. The old `GammaD1` name is retained as a non-instance abbrev so
  existing term-level references remain possible without adding duplicate
  typeclass candidates.
- File-level validation passed for `ModelConstrEX.lean` and
  `ModelConstrALL.lean`; `lake build Unifysl` passed after the correction.

Blockers:

- No L21 blocker is currently recorded.

### L22

Status: complete.

Changed 8.20 source files:

```text
LogicGenerator/demo932/Interface.v
```

Known risks:

- `DerivedNamesSig` now includes the 8.20 derived connectives and judgements
  `iffp` and `provable`, with the same pointwise definitions as Coq.
- Lean now exposes every active 8.20 `LogicTheoremSig` declaration name in
  `Unifysl.LogicGenerator.demo932.LogicTheoremSig`; a name-difference scan
  against `LogicGenerator/demo932/Interface.v` reports no missing declaration
  names.
- The original master-migration structure fields are retained for compatibility
  where downstream Lean code already used them. The 8.20 names are exposed as
  theorem/projection wrappers with the same `self : LogicTheoremSig ...`
  parameter shape as Lean structure projections. Exact record-literal field
  renaming remains a possible cleanup pass after branch correction stabilizes.
- The 8.20 `ModelLanguage*` assembly modules are imported by `Interface.lean`,
  and `LogicTheoremSig'.default` now uses those split model-language helpers
  directly. The older helper modules were removed after confirming that there
  is no external Lean code to preserve and that the root `Unifysl` module no
  longer imports them.
- Coq `LogicTheoremSig'` exports many local instance names from a module body.
  Lean represents the same assembly as `LogicTheoremSig'.default` with local
  `letI` instances; these are usable for constructing the theorem signature
  but are not exposed as independent global instance names.
- File-level validation passed for `Interface.lean`; `lake build Unifysl`
  passed after the correction.

Blockers:

- No L22 blocker is currently recorded.
