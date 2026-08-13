/- Coq inventory: unifysl-prp/SeparationLogic/ProofTheory/Corable.v
   - Classes and fields:
     Corable.corable,
     Corable_withAxiomatization.corable_preserved',
     Corable_withAxiomatization.corable_andp_sepcon1,
     MinimumCorable.corable_impp,
     SepconCorable.corable_sepcon,
     CoqPropCorable.corable_coq_prop.
   - Lemmas:
     corable_sepcon_andp2, corable_sepcon_andp1,
     corable_andp_sepcon2, CoqPropCorable2SepconCoqPropAX.
-/

import Unifysl.SeparationLogic.ProofTheory.RewriteClass

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Unifysl

open PropositionalLanguageNotation
open CoqPropInLogicNotation
open SeparationLogicNotation

class Corable (L : Language.{u}) : Type (u + 1) where
  corable : @Language.expr L -> Prop

export Corable (corable)

class Corable_withAxiomatization (L : Language.{u})
    [AndLanguage L] [IffLanguage L] [SepconLanguage L]
    (GammaP : Provable L) (Cor : Corable L) : Prop where
  corable_preserved' :
    forall x y : @Language.expr L,
      @Provable.provable L GammaP (x ⟷ y) ->
        @Corable.corable L Cor x -> @Corable.corable L Cor y
  corable_andp_sepcon1 :
    forall x y z : @Language.expr L,
      @Corable.corable L Cor x ->
        @Provable.provable L GammaP (((x && y) * z) ⟷ (x && (y * z)))

export Corable_withAxiomatization (corable_preserved' corable_andp_sepcon1)

class MinimumCorable (L : Language.{u}) [MinimumLanguage L]
    (Cor : Corable L) : Prop where
  corable_impp :
    forall x y : @Language.expr L,
      @Corable.corable L Cor x ->
        @Corable.corable L Cor y -> @Corable.corable L Cor (x ⟶ y)

export MinimumCorable (corable_impp)

class SepconCorable (L : Language.{u}) [SepconLanguage L]
    (Cor : Corable L) : Prop where
  corable_sepcon :
    forall x y : @Language.expr L,
      @Corable.corable L Cor x ->
        @Corable.corable L Cor y -> @Corable.corable L Cor (x * y)

export SepconCorable (corable_sepcon)

class CoqPropCorable (L : Language.{u}) [CoqPropLanguage L]
    (Cor : Corable L) : Prop where
  corable_coq_prop :
    forall P : Prop, @Corable.corable L Cor (!! P)

export CoqPropCorable (corable_coq_prop)

section CorableRules

variable {L : Language.{u}}
variable [MinimumLanguage L] [AndLanguage L] [IffLanguage L] [SepconLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma] [AndAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [SepconAxiomatization L Gamma]
variable [Cor : Corable L] [CorAX : Corable_withAxiomatization L Gamma Cor]

private theorem iffp_elim1_local :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟷ y) ->
        @Provable.provable L Gamma (x ⟶ y) := by
  intro x y h
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟷ y) (x ⟶ y) (IffAxiomatization.provable_iffp_elim1 x y) h

private theorem iffp_elim2_local :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟷ y) ->
        @Provable.provable L Gamma (y ⟶ x) := by
  intro x y h
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟷ y) (y ⟶ x) (IffAxiomatization.provable_iffp_elim2 x y) h

private theorem corable_iffp_trans :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (x ⟷ y) ->
      @Provable.provable L Gamma (y ⟷ z) ->
      @Provable.provable L Gamma (x ⟷ z) := by
  intro x y z hxy hyz
  exact solve_iffp_intros_minimal x z
    (solve_impp_trans x y z
      (iffp_elim1_local x y hxy)
      (iffp_elim1_local y z hyz))
    (solve_impp_trans z y x
      (iffp_elim2_local y z hyz)
      (iffp_elim2_local x y hxy))

private theorem andp_comm_minimal :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x && y) ⟷ (y && x)) := by
  intro x y
  exact provable_andp_comm x y

private theorem sepcon_comm_minimal :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x * y) ⟷ (y * x)) := by
  intro x y
  exact solve_iffp_intros_minimal (x * y) (y * x)
    (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x y)
    (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) y x)

private theorem andp_right_iffp :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (y ⟷ z) ->
      @Provable.provable L Gamma ((x && y) ⟷ (x && z)) := by
  intro x y z hyz
  letI : ProofTheoryPatternsP.Monotonicity L Gamma andp := andp_Mono
  exact solve_iffp_intros_minimal (x && y) (x && z)
    (ProofTheoryPatternsP.prodp_mono (prodp := andp)
      x y x z (provable_impp_refl x) (iffp_elim1_local y z hyz))
    (ProofTheoryPatternsP.prodp_mono (prodp := andp)
      x z x y (provable_impp_refl x) (iffp_elim2_local y z hyz))

private theorem sepcon_left_iffp :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (x ⟷ y) ->
      @Provable.provable L Gamma ((x * z) ⟷ (y * z)) := by
  intro x y z hxy
  exact solve_iffp_intros_minimal (x * z) (y * z)
    (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      x y z z (iffp_elim1_local x y hxy) (provable_impp_refl z))
    (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      y x z z (iffp_elim2_local x y hxy) (provable_impp_refl z))

theorem corable_sepcon_andp2 :
    forall P Q R : @Language.expr L,
      @Corable.corable L Cor P ->
        @Provable.provable L Gamma ((Q * (R && P)) ⟷ (P && (Q * R))) := by
  intro P Q R hP
  have h1 : @Provable.provable L Gamma
      ((Q * (R && P)) ⟷ ((R && P) * Q)) :=
    sepcon_comm_minimal Q (R && P)
  have h2 : @Provable.provable L Gamma
      (((R && P) * Q) ⟷ ((P && R) * Q)) :=
    sepcon_left_iffp (R && P) (P && R) Q (andp_comm_minimal R P)
  have h3 : @Provable.provable L Gamma
      (((P && R) * Q) ⟷ (P && (R * Q))) :=
    Corable_withAxiomatization.corable_andp_sepcon1
      (GammaP := Gamma) (Cor := Cor) P R Q hP
  have h4 : @Provable.provable L Gamma
      ((P && (R * Q)) ⟷ (P && (Q * R))) :=
    andp_right_iffp P (R * Q) (Q * R) (sepcon_comm_minimal R Q)
  exact corable_iffp_trans (Q * (R && P)) ((R && P) * Q) (P && (Q * R))
    h1
    (corable_iffp_trans ((R && P) * Q) ((P && R) * Q) (P && (Q * R))
      h2
      (corable_iffp_trans ((P && R) * Q) (P && (R * Q)) (P && (Q * R))
        h3 h4))

theorem corable_sepcon_andp1 :
    forall P Q R : @Language.expr L,
      @Corable.corable L Cor P ->
        @Provable.provable L Gamma ((Q * (P && R)) ⟷ (P && (Q * R))) := by
  intro P Q R hP
  have h1 : @Provable.provable L Gamma
      ((Q * (P && R)) ⟷ ((P && R) * Q)) :=
    sepcon_comm_minimal Q (P && R)
  have h2 : @Provable.provable L Gamma
      (((P && R) * Q) ⟷ (P && (R * Q))) :=
    Corable_withAxiomatization.corable_andp_sepcon1
      (GammaP := Gamma) (Cor := Cor) P R Q hP
  have h3 : @Provable.provable L Gamma
      ((P && (R * Q)) ⟷ (P && (Q * R))) :=
    andp_right_iffp P (R * Q) (Q * R) (sepcon_comm_minimal R Q)
  exact corable_iffp_trans (Q * (P && R)) ((P && R) * Q) (P && (Q * R))
    h1 (corable_iffp_trans ((P && R) * Q) (P && (R * Q)) (P && (Q * R)) h2 h3)

theorem corable_andp_sepcon2 :
    forall P Q R : @Language.expr L,
      @Corable.corable L Cor P ->
        @Provable.provable L Gamma (((Q && P) * R) ⟷ (P && (Q * R))) := by
  intro P Q R hP
  have h1 : @Provable.provable L Gamma
      (((Q && P) * R) ⟷ ((P && Q) * R)) :=
    sepcon_left_iffp (Q && P) (P && Q) R (andp_comm_minimal Q P)
  have h2 : @Provable.provable L Gamma
      (((P && Q) * R) ⟷ (P && (Q * R))) :=
    Corable_withAxiomatization.corable_andp_sepcon1
      (GammaP := Gamma) (Cor := Cor) P Q R hP
  exact corable_iffp_trans ((Q && P) * R) ((P && Q) * R) (P && (Q * R)) h1 h2

variable [CoqPropLanguage L] [CoqPropAxiomatization L Gamma]
variable [CoqPropCorable L Cor]

theorem CoqPropCorable2SepconCoqPropAX :
    SepconCoqPropAxiomatization L Gamma := by
  constructor
  intro P Q R
  exact Corable_withAxiomatization.corable_andp_sepcon1
    (GammaP := Gamma) (Cor := Cor) (!! P) Q R
    (CoqPropCorable.corable_coq_prop (L := L) (Cor := Cor) P)

end CorableRules

end Unifysl
