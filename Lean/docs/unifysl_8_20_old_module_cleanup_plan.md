# Unifysl 8.20 old module cleanup summary

This document records the final state of the cleanup that followed the demo932
8.20 correction. The detailed per-turn migration and branch-difference notes
remain in:

- `docs/unifysl_8_20_branch_correction_plan.md`
- `docs/unifysl_8_20_branch_residual_risks.md`

## Current Status

- The Lean tree builds with `lake build Unifysl`.
- The project-wide forbidden-marker scan used by the migration workflow has no
  matches.
- The old helper modules
  `Unifysl/SeparationLogic/ShallowEmbedded/Join2Sepcon.lean` and
  `Unifysl/SeparationLogic/ShallowEmbedded/Model2CoqPropEmp.lean` have been
  removed.
- `LogicGenerator/demo932/Interface.lean` now uses the 8.20 split
  model-language namespaces instead of the removed helper modules.
- The large pure alias blocks `Classical820DerivedNames` and the root part of
  `Intuitionistic820DerivedNames` have been removed.

## Cleanup Rules

- Keep `lake build Unifysl` passing after each cleanup batch.
- Preserve the 8.20 public API unless a name is only an internal compatibility
  shim for the earlier master-based Lean migration.
- Do not weaken theorem statements or replace proof content with placeholders.
- Keep generated-interface surface fields when they are part of
  `demo932/Interface.v`, even if similarly named internal helpers were removed.

## Removed Modules

The following master-era helper modules were removed after all in-repository
imports and qualified references were moved to 8.20 split model-language
modules:

```text
Unifysl/SeparationLogic/ShallowEmbedded/Join2Sepcon.lean
Unifysl/SeparationLogic/ShallowEmbedded/Model2CoqPropEmp.lean
```

Replacement namespaces:

```text
Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage
Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic
Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic
Unifysl.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic
Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic
```

## Removed Alias Families

Pure master-era aliases were removed when the corresponding 8.20 name was
available directly. The largest cleaned areas were:

```text
PropositionalLogic/ProofTheory/Intuitionistic.lean
PropositionalLogic/ProofTheory/Classical.lean
PropositionalLogic/ProofTheory/DeMorgan.lean
PropositionalLogic/ProofTheory/RewriteClass.lean
PropositionalLogic/ProofTheory/ProofTheoryPatterns.lean
PropositionalLogic/ProofTheory/TheoryOfClassicalAxioms.lean
MetaLogicInj/ProofTheory/ProofRules.lean
SeparationLogic/ProofTheory/RewriteClass.lean
SeparationLogic/ProofTheory/DerivedRules.lean
SeparationLogic/ProofTheory/IterSepcon.lean
SeparationLogic/ProofTheory/TheoryOfCancel.lean
```

Examples of old names removed in favor of 8.20 names:

```text
solve_weak_classic -> provables_weak_classic
impp_curry_uncurry -> provable_andp_impp
andp_proper_impp -> provables_andp_proper_impp
sepcon_proper_impp -> provables_sepcon_proper_impp
iter_sepcon_spec_left -> provable_iter_sepcon_spec_left
by_contradiction -> provable_by_contradiction
coq_prop_truep -> provables_coq_prop_truep
```

## Field-Level Cleanup

`GeneralLogic/ProofTheory/BasicLogicEquiv.lean` now uses the 8.20
`EquivDerivable1` field directly:

```text
__logic_equiv_derivable1
```

The previous general-logic helper theorem `logic_equiv_derivable1` was removed.
`LogicGenerator/demo932/Interface.lean` still has
`LogicTheoremSig.logic_equiv_derivable1`, because that is a field of the
generated interface structure rather than the general-logic class projection.

`PropositionalLogic/ProofTheory/Intuitionistic.lean` class fields now use 8.20
projection names directly, including:

```text
provable_*
derivables_*
derivable1s_truep_intros
derivable1s_impp_andp_adjoint
derivable1s_contrapositivePP
derivable1s_contradiction_elim
logic_equiv_provable_iffp_intros
```

Root wrapper theorems such as `provable_andp_intros` remain intentionally:
Lean structure projections are class-qualified, while Coq class projections are
global names.

## Retained Exceptions

Two source-level exceptions remain by design.

`PropositionalLogic.ProofTheory.Intuitionistic.derivable1_impp_refl` is kept as
a module-qualified theorem alias because the root name
`Unifysl.derivable1_impp_refl` is already owned by minimum logic.

`LogicGenerator/demo932/Interface.lean` keeps local helper theorem names
`derivable1_andp_intros` and `derivable1_impp_andp_adjoint`. The corresponding
`LogicTheoremSig` fields already use the 8.20 names
`derivable1s_truep_intros` and `derivable1s_impp_andp_adjoint`; the local helper
names avoid a Lean declaration-name collision with those structure fields.

## Validation Commands

Run from `unifysl`:

```bash
lake build Unifysl
```

Then run the shared migration forbidden-marker scan over:

```text
Unifysl
lakefile.lean
../docs/unifysl_8_20_branch_residual_risks.md
../docs/unifysl_8_20_branch_correction_plan.md
../docs/unifysl_8_20_old_module_cleanup_plan.md
```

Optional source-level spot checks:

```bash
rg -n "Classical820DerivedNames|Intuitionistic820DerivedNames|impp_curry_uncurry" Unifysl
rg -n "SeparationLogic\\.ShallowEmbedded\\.Join2Sepcon|SeparationLogic\\.ShallowEmbedded\\.Model2CoqPropEmp" Unifysl
```
