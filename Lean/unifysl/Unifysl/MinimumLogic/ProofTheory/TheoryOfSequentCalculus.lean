/- 
Coq inventory from `MinimumLogic/ProofTheory/TheoryOfSequentCalculus.v`:
- Properties: `DeductionMP`, `DeductionImpIntro`, `DeductionImpElim`.
- Lemmas:
  `DeductionMP_DerivableAssu_DeductionWeaken_2_DeductionImpElim`,
  `DeductionImpIntro_DeductionMP_2_DeductionSubst1`,
  `DeductionImpElim_DeductionSubst1_2_DeductionMP`.
- Coq notation `x --> y` is represented in Lean by the safe notation
  `x ⟶ y`, whose underlying operation is `impp`.
-/

import Unifysl.GeneralLogic.ProofTheory.TheoryOfSequentCalculus
import Unifysl.MinimumLogic.Syntax

universe u

namespace Unifysl

section PropertiesOfSequentCalculus

def DeductionMP (L : Language.{u}) (Gamma : Derivable L) [MinimumLanguage L] : Prop :=
  forall (Phi : context (L := L)) (x y : @Language.expr L),
    Gamma.derivable Phi x ->
      Gamma.derivable Phi (x ⟶ y) ->
        Gamma.derivable Phi y

def DeductionImpIntro (L : Language.{u}) (Gamma : Derivable L) [MinimumLanguage L] : Prop :=
  forall (Phi : context (L := L)) (x y : @Language.expr L),
    Gamma.derivable (Union _ Phi (Singleton _ x)) y ->
      Gamma.derivable Phi (x ⟶ y)

def DeductionImpElim (L : Language.{u}) (Gamma : Derivable L) [MinimumLanguage L] : Prop :=
  forall (Phi : context (L := L)) (x y : @Language.expr L),
    Gamma.derivable Phi (x ⟶ y) ->
      Gamma.derivable (Union _ Phi (Singleton _ x)) y

end PropertiesOfSequentCalculus

section TheoryOfSequentCalculus

variable {L : Language.{u}} [Gamma : Derivable L] [MinimumLanguage L]

theorem DeductionMP_DerivableAssu_DeductionWeaken_2_DeductionImpElim :
    DeductionMP L Gamma ->
    DerivableAssu L Gamma ->
    DeductionWeaken L Gamma ->
    DeductionImpElim L Gamma := by
  intro hMP hAssu hWeak Phi x y hImp
  exact hMP (Union _ Phi (Singleton _ x)) x y
    (hAssu (Union _ Phi (Singleton _ x)) x (Or.inr rfl))
    (hWeak Phi (Union _ Phi (Singleton _ x)) (x ⟶ y)
      (by
        intro z hz
        exact Or.inl hz)
      hImp)

theorem DeductionImpIntro_DeductionMP_2_DeductionSubst1 :
    DeductionImpIntro L Gamma ->
    DeductionMP L Gamma ->
    DeductionSubst1 L Gamma := by
  intro hIntro hMP Phi x y hPhiX hPhiXY
  exact hMP Phi x y hPhiX (hIntro Phi x y hPhiXY)

theorem DeductionImpElim_DeductionSubst1_2_DeductionMP :
    DeductionImpElim L Gamma ->
    DeductionSubst1 L Gamma ->
    DeductionMP L Gamma := by
  intro hElim hSubst1 Phi x y hPhiX hPhiImp
  exact hSubst1 Phi x y hPhiX (hElim Phi x y hPhiImp)

end TheoryOfSequentCalculus

end Unifysl
