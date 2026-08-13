# Unifysl 8.20 Branch Correction Plan

This document records how to correct the existing Lean migration, which was
completed against the `master` branch of `unifysl-prp`, so that it targets
`unifysl-prp-8.20`.

## Baseline

Current source baselines observed locally:

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

The current Lean tree contains 73 migrated `.v` modules under
`unifysl/Unifysl`. Among those 73 source modules, 41 have changed between
`master` and `unifysl-prp-8.20`.

The final target file differs substantially:

```text
master LogicGenerator/demo932/Interface.v: 342 lines
8.20  LogicGenerator/demo932/Interface.v: 598 lines
```

Therefore the correction is not just a final-interface rename pass. It should
be treated as a branch retargeting pass over the dependency layers.

## Global Correction Rules

- Keep using Lean core and Std only.
- Preserve Coq active API names and statement strength for the 8.20 branch.
- Do not patch a lower dependency while correcting a higher layer. If a higher
  layer exposes an insufficient lower interface, record the issue and return to
  the proper lower layer.
- For every corrected layer, run file-level checks, then `lake build Unifysl`,
  then the forbidden-marker scan used by the migration workflow.
- Read Coq comments carefully. Several 8.20 files contain large commented
  legacy blocks whose import lines and declarations must not be counted as
  active dependencies.

## Changed Migrated Files

The following 41 files are part of the existing 73 migrated modules and changed
in the 8.20 branch.

```text
GeneralLogic/ProofTheory/BasicLogicEquiv.v
GeneralLogic/Semantics/Kripke.v
lib/Bijection.v
lib/register_typeclass.v
LogicGenerator/demo932/Interface.v
MetaLogicInj/ProofTheory/ProofRules.v
MinimumLogic/ProofTheory/ExtensionTactic.v
MinimumLogic/ProofTheory/Minimum.v
MinimumLogic/ProofTheory/RewriteClass.v
MinimumLogic/ProofTheory/TheoryOfJudgement.v
MinimumLogic/Semantics/Kripke.v
MinimumLogic/Semantics/Trivial.v
PropositionalLogic/ProofTheory/Classical.v
PropositionalLogic/ProofTheory/DeMorgan.v
PropositionalLogic/ProofTheory/GodelDummett.v
PropositionalLogic/ProofTheory/Intuitionistic.v
PropositionalLogic/ProofTheory/ProofTheoryPatterns.v
PropositionalLogic/ProofTheory/RewriteClass.v
PropositionalLogic/ProofTheory/TheoryOfClassicalAxioms.v
PropositionalLogic/ProofTheory/TheoryOfPropositionalConnectives.v
PropositionalLogic/Semantics/Kripke.v
PropositionalLogic/Semantics/Trivial.v
PropositionalLogic/ShallowEmbedded/PredicatePropositionalLogic.v
PropositionalLogic/Sound/Sound_Classical_Trivial.v
SeparationLogic/Model/OrderedSA.v
SeparationLogic/Model/SeparationAlgebra.v
SeparationLogic/ProofTheory/Corable.v
SeparationLogic/ProofTheory/Deduction.v
SeparationLogic/ProofTheory/DerivedRules.v
SeparationLogic/ProofTheory/IterSepcon.v
SeparationLogic/ProofTheory/RewriteClass.v
SeparationLogic/ProofTheory/SeparationLogic.v
SeparationLogic/ProofTheory/TheoryOfCancel.v
SeparationLogic/ProofTheory/TheoryOfSeparationAxioms.v
SeparationLogic/ShallowEmbedded/Join2Sepcon.v
SeparationLogic/ShallowEmbedded/Model2CoqPropEmp.v
SeparationLogic/ShallowEmbedded/PredicateSeparationLogic.v
SeparationLogic/Sound/Sound_Flat.v
ShallowQuantifierLogic/ModelConstrALL.v
ShallowQuantifierLogic/ModelConstrEX.v
ShallowQuantifierLogic/ProofTheory.v
```

The remaining 32 migrated modules did not change between these two branches,
based on path-level comparison.

## New 8.20 Modules And Layer Placement

The 8.20 branch adds five shallow model-language modules that were not in the
master dependency plan. Their layer placement should be computed from active
imports, not directory names.

| New Coq module | Highest active dependency layer | Correction layer |
| --- | ---: | ---: |
| `GeneralLogic/ShallowEmbedded/ModelLanguage.v` | L3 | L4 |
| `MinimumLogic/ShallowEmbedded/ModelLanguageMinimumLogic.v` | L6 | L7 |
| `PropositionalLogic/ShallowEmbedded/ModelLanguagePropositionalLogic.v` | L12 | L13 |
| `MetaLogicInj/ShallowEmbedded/ModelLanguageMetaLogic.v` | L13 | L14 |
| `SeparationLogic/ShallowEmbedded/ModelLanguageSeparationLogic.v` | L16 | L17 |

These modules replace much of the final-interface assembly role that master
handled through `Join2Sepcon.v` and `Model2CoqPropEmp.v`.

### Active Dependency Notes For New Modules

`GeneralLogic/ShallowEmbedded/ModelLanguage.v`

```text
GeneralLogic/Base.v
GeneralLogic/KripkeModel.v
```

`MinimumLogic/ShallowEmbedded/ModelLanguageMinimumLogic.v`

```text
GeneralLogic/Base.v
GeneralLogic/ProofTheory/BasicDeduction.v
GeneralLogic/ShallowEmbedded/ModelLanguage.v
MinimumLogic/Syntax.v
MinimumLogic/ProofTheory/Minimum.v
MinimumLogic/Semantics/Trivial.v
MinimumLogic/Semantics/Kripke.v
MinimumLogic/Semantics/SemanticEquiv.v
```

`PropositionalLogic/ShallowEmbedded/ModelLanguagePropositionalLogic.v`

```text
GeneralLogic/Base.v
GeneralLogic/ProofTheory/BasicDeduction.v
GeneralLogic/ShallowEmbedded/ModelLanguage.v
MinimumLogic/Syntax.v
MinimumLogic/ProofTheory/Minimum.v
MinimumLogic/Semantics/Trivial.v
MinimumLogic/Semantics/Kripke.v
MinimumLogic/Semantics/SemanticEquiv.v
MinimumLogic/ShallowEmbedded/ModelLanguageMinimumLogic.v
PropositionalLogic/Syntax.v
PropositionalLogic/ProofTheory/Intuitionistic.v
PropositionalLogic/ProofTheory/Classical.v
```

`MetaLogicInj/ShallowEmbedded/ModelLanguageMetaLogic.v`

```text
GeneralLogic/Base.v
GeneralLogic/ShallowEmbedded/PredicateAsLang.v
MetaLogicInj/Syntax.v
MetaLogicInj/ProofTheory/ProofRules.v
GeneralLogic/ShallowEmbedded/ModelLanguage.v
PropositionalLogic/Syntax.v
PropositionalLogic/ShallowEmbedded/ModelLanguagePropositionalLogic.v
```

`SeparationLogic/ShallowEmbedded/ModelLanguageSeparationLogic.v`

```text
GeneralLogic/Base.v
GeneralLogic/ShallowEmbedded/PredicateAsLang.v
GeneralLogic/ProofTheory/BasicDeduction.v
GeneralLogic/ShallowEmbedded/ModelLanguage.v
MinimumLogic/ShallowEmbedded/ModelLanguageMinimumLogic.v
SeparationLogic/Syntax.v
SeparationLogic/Model/SeparationAlgebra.v
SeparationLogic/ShallowEmbedded/PredicateSeparationLogic.v
SeparationLogic/Semantics/WeakSemantics.v
SeparationLogic/ProofTheory/SeparationLogic.v
SeparationLogic/Sound/Sound_Flat.v
SeparationLogic/Semantics/FlatSemantics.v
lib/Ensembles_ext.v
```

## Important Active/Commented Boundary

In the 8.20 branch, these files have changed, but their visible content must be
interpreted carefully:

```text
SeparationLogic/ShallowEmbedded/Join2Sepcon.v
SeparationLogic/ShallowEmbedded/Model2CoqPropEmp.v
```

Large sections of both files are inside Coq comments. A plain text search will
find imports and declarations inside those comments, but those are not active
8.20 declarations. For the 8.20 final interface, the active assembly path goes
through the new `ModelLanguage*` modules instead.

Lean currently contains migrated master-compatible versions of these modules.
Do not delete them during branch correction unless a later explicit cleanup task
asks for that. For 8.20 `demo932.Interface`, prefer the new module-language
assembly path.

## Layered Correction Schedule

The original master migration layers should be reused, with the five inserted
modules above. Only files listed in a layer need correction in that layer unless
an active import difference reveals an additional blocker.

### L0 Correction

Changed files:

```text
lib/Bijection.v
lib/register_typeclass.v
SeparationLogic/Model/SeparationAlgebra.v
```

Focus:

- Compare record fields, class fields, and tactic primitives against 8.20.
- Do not change later registration behavior here unless the 8.20 source changed
  the primitive registration interface itself.

### L1 Correction

No changed file from the existing 73-module migration was detected at this
layer.

Focus:

- Re-run build after L0.
- Do not add compatibility aliases here unless an active 8.20 file in this
  layer requires them.

### L2 Correction

No changed file from the existing 73-module migration was detected at this
layer.

Focus:

- Preserve the existing core syntax and relation infrastructure.

### L3 Correction

Changed files:

```text
GeneralLogic/ProofTheory/BasicLogicEquiv.v
```

Focus:

- Check whether 8.20 changes equivalence/proper instances or field names needed
  by later rewrite modules.

### L4 Correction

Changed files:

```text
GeneralLogic/Semantics/Kripke.v
MinimumLogic/ProofTheory/Minimum.v
PropositionalLogic/Semantics/Trivial.v
SeparationLogic/Model/OrderedSA.v
```

New module:

```text
GeneralLogic/ShallowEmbedded/ModelLanguage.v
```

Focus:

- Add the model-language base module at this layer.
- Check changed minimum proof-theory declarations before later shallow model
  modules use them.

### L5 Correction

Changed files:

```text
MinimumLogic/ProofTheory/RewriteClass.v
MinimumLogic/Semantics/Kripke.v
PropositionalLogic/Sound/Sound_Classical_Trivial.v
```

Focus:

- Re-check rewrite/proper instance names and theorem availability.
- Preserve Lean-safe notation decisions from the master migration.

### L6 Correction

Changed files:

```text
MinimumLogic/ProofTheory/TheoryOfJudgement.v
PropositionalLogic/Semantics/Kripke.v
```

Focus:

- Check judgement conversion theorems because later model-language modules use
  deduction/provable conversion APIs.

### L7 Correction

Changed files:

```text
MinimumLogic/ProofTheory/ExtensionTactic.v
SeparationLogic/Sound/Sound_Flat.v
```

New module:

```text
MinimumLogic/ShallowEmbedded/ModelLanguageMinimumLogic.v
```

Focus:

- Confirm registration and local-instance tactics still match 8.20.
- Add minimum model-language module after semantic equivalence is available.

### L8 Correction

Changed files:

```text
PropositionalLogic/ProofTheory/Intuitionistic.v
```

Focus:

- This layer is large and affects many 8.20 `Interface` names.
- Pay special attention to provable-level and logic-equivalence helper names.

### L9 Correction

Changed files:

```text
PropositionalLogic/ProofTheory/DeMorgan.v
PropositionalLogic/ProofTheory/RewriteClass.v
```

Focus:

- Re-check propositional rewrite instances required by 8.20 interface fields.

### L10 Correction

Changed files:

```text
PropositionalLogic/ProofTheory/GodelDummett.v
PropositionalLogic/ProofTheory/ProofTheoryPatterns.v
```

Focus:

- Re-check module-qualified proof-pattern names.

### L11 Correction

Changed files:

```text
PropositionalLogic/ProofTheory/TheoryOfClassicalAxioms.v
```

Focus:

- Check classical helper names that feed L12 and later theorem assembly.

### L12 Correction

Changed files:

```text
PropositionalLogic/ProofTheory/Classical.v
```

Focus:

- Ensure any public helpers required by 8.20 propositional model-language code
  remain exported.

### L13 Correction

Changed files:

```text
MetaLogicInj/ProofTheory/ProofRules.v
PropositionalLogic/ProofTheory/TheoryOfPropositionalConnectives.v
PropositionalLogic/ShallowEmbedded/PredicatePropositionalLogic.v
```

New module:

```text
PropositionalLogic/ShallowEmbedded/ModelLanguagePropositionalLogic.v
```

Focus:

- Add propositional model-language module after `Classical.v`.
- Re-check Coq-prop proof rules and registration numbers.

### L14 Correction

Changed files:

```text
SeparationLogic/ProofTheory/SeparationLogic.v
```

New module:

```text
MetaLogicInj/ShallowEmbedded/ModelLanguageMetaLogic.v
```

Focus:

- Add metalevel model-language module after `ProofRules.v`.
- Keep separation proof theory aligned with 8.20 before L15/L16 conversions.

### L15 Correction

Changed files:

```text
SeparationLogic/ProofTheory/TheoryOfSeparationAxioms.v
```

Focus:

- Check weak/full separation-proof conversion names and statement strength.

### L16 Correction

Changed files:

```text
SeparationLogic/ProofTheory/Deduction.v
SeparationLogic/ShallowEmbedded/PredicateSeparationLogic.v
```

Focus:

- Re-check separation deduction-to-axiomatization registrations.
- Predicate separation instances may depend on 8.20 propositional predicate
  changes.

### L17 Correction

Changed files:

```text
SeparationLogic/ProofTheory/RewriteClass.v
SeparationLogic/ShallowEmbedded/Join2Sepcon.v
SeparationLogic/ShallowEmbedded/Model2CoqPropEmp.v
```

New module:

```text
SeparationLogic/ShallowEmbedded/ModelLanguageSeparationLogic.v
```

Focus:

- Add separation model-language module.
- Treat `Join2Sepcon.v` and `Model2CoqPropEmp.v` as legacy/master-compatible
  modules unless active 8.20 declarations are found after comment stripping.
- Ensure final interface later uses `ModelLanguageSeparationLogic` where 8.20
  does.

### L18 Correction

Changed files:

```text
SeparationLogic/ProofTheory/Corable.v
SeparationLogic/ProofTheory/DerivedRules.v
SeparationLogic/ProofTheory/TheoryOfCancel.v
```

Focus:

- Re-check derived rules that 8.20 `Interface.v` exposes under generated-style
  names.

### L19 Correction

Changed files:

```text
SeparationLogic/ProofTheory/IterSepcon.v
```

Focus:

- Re-check iterated sepcon fold and registration names.

### L20 Correction

Changed files:

```text
ShallowQuantifierLogic/ProofTheory.v
```

Focus:

- Re-check shallow quantifier distribution and sepcon/andp/coq-prop interaction
  rules, since 8.20 `Interface.v` exposes more generated-style names.

### L21 Correction

Changed files:

```text
ShallowQuantifierLogic/ModelConstrALL.v
ShallowQuantifierLogic/ModelConstrEX.v
```

Focus:

- Re-check model constructor theorem names used by final interface assembly.

### L22 Correction

Changed files:

```text
LogicGenerator/demo932/Interface.v
```

Focus:

- Rebuild `Interface.lean` against the 8.20 active source, not the master
  source.
- Add `iffp` and `provable` to `DerivedNamesSig`.
- Expose the 8.20 `LogicTheoremSig` fields by their 8.20 names.
- Use the new `ModelLanguage*` assembly path.
- Keep Coq module-type assumptions as Lean structure fields, not global
  assumptions.

## 8.20 Interface-Specific API Differences

Compared with the master interface, 8.20 adds many generated-style public names.
The following groups are especially important because current Lean often has
the functionality under master-style names but not the 8.20 exact names.

Old derivation-name surface:

```text
derivable1s_coq_prop_r
derivable1s_coq_prop_l
derivable1_iter_sepcon_l
derivable1_iter_sepcon_r
derivable1s_exp_r
derivable1s_exp_l
derivable1s_allp_r
derivable1s_allp_l
derivable1s_wand_sepcon_adjoint
derivable1_sepcon_emp_l
derivable1_sepcon_emp_r
```

Logic equivalence and rewrite surface:

```text
logic_equiv_andp_comm
logic_equiv_andp_assoc
logic_equiv_andp_swap
logic_equiv_sepcon_comm
logic_equiv_sepcon_assoc
logic_equiv_sepcon_swap
logic_equiv_sepcon_emp
logic_equiv_coq_prop_or
logic_equiv_coq_prop_and
logic_equiv_coq_prop_andp_sepcon
logic_equiv_sepcon_coq_prop_andp
```

Wand and false/coq-prop helper surface:

```text
derivable1_wand_elim1
derivable1_wand_elim2
derivables_false_coq_prop
```

Provable-level surface:

```text
provable_iter_sepcon_derives
provable_derives_iter_sepcon
provable_sepcon_comm_impp
provable_sepcon_assoc1
provable_sepcon_mono
provables_coq_prop_intros
provables_coq_prop_elim
provable_iffp_intros
provable_iffp_elim1
provable_iffp_elim2
provable_orp_intros1
provable_orp_intros2
provable_orp_elim
provable_andp_intros
provable_andp_elim1
provable_andp_elim2
provables_modus_ponens
provable_axiom1
provable_axiom2
provables_impp_trans
provables_andp_proper_impp
provables_orp_proper_impp
provables_sepcon_proper_impp
provables_sepcon_proper_iffp
```

Do not treat these as optional aliases for 8.20. They are active public fields
of `LogicTheoremSig` or active definitions in `LogicTheoremSig'`.

## Recommended Per-Layer Workflow

For each layer:

1. Compare the 8.20 source with the master source for that layer.
2. List active declarations added, removed, renamed, or with changed statement.
3. Update the Lean file only for that layer.
4. Add compatibility names only when they are active 8.20 public API or needed by
   an active 8.20 downstream module.
5. Run file checks and full build.
6. Update `docs/unifysl_8_20_branch_residual_risks.md` with all observed
   issues, including small resolved naming or instance-search differences.

Suggested validation commands:

```bash
cd unifysl
lake build Unifysl
```

Then run the same forbidden-marker scan used by the migration workflow over the
Lean tree, `lakefile.lean`, and `docs/unifysl_8_20_branch_residual_risks.md`.

## Expected End State

The corrected 8.20 migration should have:

- All 8.20 active dependencies represented in Lean.
- The five new `ModelLanguage*` modules inserted at the layers listed above.
- `LogicGenerator/demo932/Interface.lean` aligned with the 8.20 interface,
  including `iffp`, `provable`, and the generated-style theorem field names.
- No reliance on master-only interface field names for the final 8.20 target.
- Clear risk-document entries for any Lean/Coq surface differences that remain.
