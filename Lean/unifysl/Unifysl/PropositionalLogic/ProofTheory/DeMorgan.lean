import Unifysl.PropositionalLogic.ProofTheory.Intuitionistic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory from `PropositionalLogic/ProofTheory/DeMorgan.v`:
- Class `DeMorganAxiomatization`
- Field `weak_excluded_middle`; 8.20 projection name
  `provable_weak_excluded_middle`
- Theorem `demorgan_negp_andp`
- Theorem `provables_weak_classic`
-/

universe u

namespace Unifysl

open PropositionalLanguageNotation

class DeMorganAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [OrLanguage L] [FalseLanguage L] [NegLanguage L]
    (Gamma : Provable L) : Prop where
  weak_excluded_middle :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((~~ x) || (~~ (~~ x)))

theorem provable_weak_excluded_middle {L : Language.{u}} [MinimumLanguage L]
    [OrLanguage L] [FalseLanguage L] [NegLanguage L]
    [Gamma : Provable L] [DeMorganAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((~~ x) || (~~ (~~ x))) :=
  DeMorganAxiomatization.weak_excluded_middle (Gamma := Gamma)

section DeMorgan

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]
variable [DeMorganAxiomatization L Gamma]

theorem demorgan_negp_andp :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((~~ (x && y)) ⟷ ((~~ x) || (~~ y))) := by
  intro x y
  have hleft :
      @Provable.provable L Gamma ((~~ (x && y)) ⟶ ((~~ x) || (~~ y))) := by
    AddSequentCalculus
    let E : context (L := L) := empty_context (L := L)
    let A : @Language.expr L := ~~ (x && y)
    let Z : @Language.expr L := (~~ x) || (~~ y)
    let Phi : context (L := L) := E ;; A
    have hwem : Phi |--- ((~~ x) || (~~ (~~ x))) :=
      deduction_weaken0 (GammaP := Gamma) Phi _
        (DeMorganAxiomatization.weak_excluded_middle x)
    have hcase_left : Phi |--- ((~~ x) ⟶ Z) := by
      apply (deduction_theorem Phi (~~ x) Z).mp
      exact OrSequentCalculus.derivables_orp_intros1 (Phi ;; (~~ x))
        (~~ x) (~~ y) (derivable_assum1 Phi (~~ x))
    have hcase_right : Phi |--- ((~~ (~~ x)) ⟶ Z) := by
      apply (deduction_theorem Phi (~~ (~~ x)) Z).mp
      let Psi : context (L := L) := Phi ;; (~~ (~~ x))
      have hnoty : Psi |--- (~~ y) := by
        apply derivables_negp_fold Psi y
        let C : context (L := L) := Psi ;; y
        have hA : C |--- A :=
          derivable_assum C A (Or.inl (Or.inl (Or.inr rfl)))
        have hnnx : C |--- (~~ (~~ x)) :=
          derivable_assum C (~~ (~~ x)) (Or.inl (Or.inr rfl))
        have hy : C |--- y :=
          derivable_assum1 Psi y
        have hx_to_false : C |--- (x ⟶ FF) := by
          apply (deduction_theorem C x FF).mp
          let D : context (L := L) := C ;; x
          have hA_D : D |--- A :=
            deduction_weaken1 C x A hA
          have hy_D : D |--- y :=
            deduction_weaken1 C x y hy
          have hx_D : D |--- x :=
            derivable_assum1 C x
          have hxy_D : D |--- (x && y) :=
            AndSequentCalculus.derivables_andp_intros D x y hx_D hy_D
          have hA_unfold_D : D |--- ((x && y) ⟶ FF) :=
            MinimumSequentCalculus.deduction_modus_ponens D A ((x && y) ⟶ FF) hA_D
              (deduction_weaken0 (GammaP := Gamma) D _ (provable_negp_derives (x && y)))
          exact MinimumSequentCalculus.deduction_modus_ponens D (x && y) FF
            hxy_D hA_unfold_D
        have hnx : C |--- (~~ x) := by
          have hfold : C |--- ((x ⟶ FF) ⟶ (~~ x)) :=
            deduction_weaken0 (GammaP := Gamma) C _ (provable_derives_negp x)
          exact MinimumSequentCalculus.deduction_modus_ponens C (x ⟶ FF) (~~ x)
            hx_to_false hfold
        have hnnx_unfold : C |--- ((~~ x) ⟶ FF) :=
          MinimumSequentCalculus.deduction_modus_ponens C (~~ (~~ x)) ((~~ x) ⟶ FF)
            hnnx (deduction_weaken0 (GammaP := Gamma) C _ (provable_negp_derives (~~ x)))
        exact MinimumSequentCalculus.deduction_modus_ponens C (~~ x) FF hnx hnnx_unfold
      exact OrSequentCalculus.derivables_orp_intros2 Psi (~~ x) (~~ y) hnoty
    have hcases : Phi |--- (((~~ x) || (~~ (~~ x))) ⟶ Z) :=
      derivables_orp_elim' Phi (~~ x) (~~ (~~ x)) Z hcase_left hcase_right
    have hZ : Phi |--- Z :=
      MinimumSequentCalculus.deduction_modus_ponens Phi ((~~ x) || (~~ (~~ x))) Z
        hwem hcases
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := Gamma) (GammaD := (inferInstance : Derivable L))
      (A ⟶ Z)).mpr
      ((deduction_theorem E A Z).mp hZ)
  have hright :
      @Provable.provable L Gamma (((~~ x) || (~~ y)) ⟶ (~~ (x && y))) :=
    provable_demorgan_orp_negp x y
  exact provables_iffp_intros _ _ hleft hright

theorem provables_weak_classic :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((~~ x) ⟶ y) ->
        @Provable.provable L Gamma ((~~ (~~ x)) ⟶ y) ->
          @Provable.provable L Gamma y := by
  intro x y hneg hdneg
  have hcases : @Provable.provable L Gamma (((~~ x) || (~~ (~~ x))) ⟶ y) :=
    provables_orp_impp_fold (~~ x) (~~ (~~ x)) y hneg hdneg
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) ((~~ x) || (~~ (~~ x))) y hcases
    (DeMorganAxiomatization.weak_excluded_middle x)

end DeMorgan

end Unifysl
