import Unifysl.PropositionalLogic.ProofTheory.DeMorgan
import Unifysl.PropositionalLogic.ProofTheory.RewriteClass

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory from `PropositionalLogic/ProofTheory/GodelDummett.v`:
- Class `GodelDummettAxiomatization`
- Field `impp_choice`
- Instance/theorem `GodelDummett2DeMorgan`
-/

universe u

namespace Unifysl

open PropositionalLanguageNotation

class GodelDummettAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [OrLanguage L] (Gamma : Provable L) : Prop where
  impp_choice :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) || (y ⟶ x))

section GodelDummett

variable {L : Language.{u}} [MinimumLanguage L]
variable [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [GodelDummettAxiomatization L Gamma]

instance GodelDummett2DeMorgan : DeMorganAxiomatization L Gamma := by
  constructor
  intro x
  let Z : @Language.expr L := (~~ x) || (~~ (~~ x))
  let A : @Language.expr L := x ⟶ (~~ x)
  let B : @Language.expr L := (~~ x) ⟶ x
  have hnotFF : @Provable.provable L Gamma (~~ FF) := by
    let T : @Language.expr L := FF ⟶ FF
    have hT : @Provable.provable L Gamma T :=
      provable_impp_refl FF
    have hdT : @Provable.provable L Gamma (~~ (~~ T)) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) T (~~ (~~ T))
        (IntuitionisticNegAxiomatization.provable_double_negp_intros T) hT
    have hfalseNotT : @Provable.provable L Gamma (FF ⟶ (~~ T)) :=
      FalseAxiomatization.provable_falsep_elim (~~ T)
    have hcontra :
        @Provable.provable L Gamma
          ((FF ⟶ (~~ T)) ⟶ (~~ (~~ T)) ⟶ (~~ FF)) :=
      IntuitionisticNegAxiomatization.provable_contrapositivePP (~~ T) FF
    have hstep : @Provable.provable L Gamma ((~~ (~~ T)) ⟶ (~~ FF)) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) (FF ⟶ (~~ T)) ((~~ (~~ T)) ⟶ (~~ FF))
        hcontra hfalseNotT
    exact MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (~~ (~~ T)) (~~ FF) hstep hdT
  have hnegp_fold :
      forall a : @Language.expr L,
        @Provable.provable L Gamma ((a ⟶ FF) ⟶ (~~ a)) := by
    intro a
    let A0 : @Language.expr L := a ⟶ FF
    have hcontra :
        @Provable.provable L Gamma (A0 ⟶ (~~ FF) ⟶ (~~ a)) :=
      IntuitionisticNegAxiomatization.provable_contrapositivePP FF a
    have hAtoNotFF : @Provable.provable L Gamma (A0 ⟶ (~~ FF)) :=
      aux_minimun_rule00 (~~ FF) A0 hnotFF
    have hmp :
        @Provable.provable L Gamma
          ((A0 ⟶ (~~ FF)) ⟶ (A0 ⟶ (~~ FF) ⟶ (~~ a)) ⟶ A0 ⟶ (~~ a)) :=
      provable_multi_imp_modus_ponens [A0] (~~ FF) (~~ a)
    have hstep :
        @Provable.provable L Gamma ((A0 ⟶ (~~ FF) ⟶ (~~ a)) ⟶ A0 ⟶ (~~ a)) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) (A0 ⟶ (~~ FF))
        ((A0 ⟶ (~~ FF) ⟶ (~~ a)) ⟶ A0 ⟶ (~~ a))
        hmp hAtoNotFF
    exact MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (A0 ⟶ (~~ FF) ⟶ (~~ a)) (A0 ⟶ (~~ a))
      hstep hcontra
  have hAtoNeg : @Provable.provable L Gamma (A ⟶ (~~ x)) := by
    have hnotxToFalse : @Provable.provable L Gamma ((~~ x) ⟶ x ⟶ FF) :=
      IntuitionisticNegAxiomatization.provable_contradiction_elim1 x FF
    have hxNotxToFalse : @Provable.provable L Gamma (x ⟶ (~~ x) ⟶ FF) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) ((~~ x) ⟶ x ⟶ FF) (x ⟶ (~~ x) ⟶ FF)
        (provable_impp_arg_switch (~~ x) x FF)
        hnotxToFalse
    have hmp :
        @Provable.provable L Gamma
          (A ⟶ (x ⟶ (~~ x) ⟶ FF) ⟶ (x ⟶ FF)) :=
      provable_multi_imp_modus_ponens [x] (~~ x) FF
    have hmpSwitched :
        @Provable.provable L Gamma
          ((x ⟶ (~~ x) ⟶ FF) ⟶ A ⟶ (x ⟶ FF)) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) (A ⟶ (x ⟶ (~~ x) ⟶ FF) ⟶ (x ⟶ FF))
        ((x ⟶ (~~ x) ⟶ FF) ⟶ A ⟶ (x ⟶ FF))
        (provable_impp_arg_switch A (x ⟶ (~~ x) ⟶ FF) (x ⟶ FF))
        hmp
    have hAtoFalseImp : @Provable.provable L Gamma (A ⟶ (x ⟶ FF)) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) (x ⟶ (~~ x) ⟶ FF) (A ⟶ (x ⟶ FF))
        hmpSwitched hxNotxToFalse
    exact solve_impp_trans A (x ⟶ FF) (~~ x) hAtoFalseImp (hnegp_fold x)
  have hBtoDNeg : @Provable.provable L Gamma (B ⟶ (~~ (~~ x))) := by
    have hnotxToFalse : @Provable.provable L Gamma ((~~ x) ⟶ x ⟶ FF) :=
      IntuitionisticNegAxiomatization.provable_contradiction_elim1 x FF
    have hmp :
        @Provable.provable L Gamma
          (B ⟶ ((~~ x) ⟶ x ⟶ FF) ⟶ ((~~ x) ⟶ FF)) :=
      provable_multi_imp_modus_ponens [~~ x] x FF
    have hmpSwitched :
        @Provable.provable L Gamma
          (((~~ x) ⟶ x ⟶ FF) ⟶ B ⟶ ((~~ x) ⟶ FF)) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) (B ⟶ ((~~ x) ⟶ x ⟶ FF) ⟶ ((~~ x) ⟶ FF))
        (((~~ x) ⟶ x ⟶ FF) ⟶ B ⟶ ((~~ x) ⟶ FF))
        (provable_impp_arg_switch B ((~~ x) ⟶ x ⟶ FF) ((~~ x) ⟶ FF))
        hmp
    have hBtoFalseImp : @Provable.provable L Gamma (B ⟶ ((~~ x) ⟶ FF)) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) ((~~ x) ⟶ x ⟶ FF) (B ⟶ ((~~ x) ⟶ FF))
        hmpSwitched hnotxToFalse
    exact solve_impp_trans B ((~~ x) ⟶ FF) (~~ (~~ x))
      hBtoFalseImp (hnegp_fold (~~ x))
  have hAZ : @Provable.provable L Gamma (A ⟶ Z) :=
    solve_impp_trans A (~~ x) Z hAtoNeg
      (OrAxiomatization.provable_orp_intros1 (~~ x) (~~ (~~ x)))
  have hBZ : @Provable.provable L Gamma (B ⟶ Z) :=
    solve_impp_trans B (~~ (~~ x)) Z hBtoDNeg
      (OrAxiomatization.provable_orp_intros2 (~~ x) (~~ (~~ x)))
  have hcases : @Provable.provable L Gamma ((A || B) ⟶ Z) := by
    have hstep :
        @Provable.provable L Gamma ((B ⟶ Z) ⟶ (A || B) ⟶ Z) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) (A ⟶ Z) ((B ⟶ Z) ⟶ (A || B) ⟶ Z)
        (OrAxiomatization.provable_orp_elim A B Z) hAZ
    exact MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (B ⟶ Z) ((A || B) ⟶ Z) hstep hBZ
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (A || B) Z hcases
    (GodelDummettAxiomatization.impp_choice x (~~ x))

end GodelDummett

end Unifysl
