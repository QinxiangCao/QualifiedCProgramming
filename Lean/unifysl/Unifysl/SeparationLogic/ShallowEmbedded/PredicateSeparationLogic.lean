/- Coq inventory: unifysl-prp/SeparationLogic/ShallowEmbedded/PredicateSeparationLogic.v
   - Instance Pred_sepconL
   - Instance Pred_wandL
   - Instance Pred_empL
   - Instance Pred_fsepconSM
   - Instance Pred_fwandSM
   - Instance Pred_empSM
   - Instance Pred_sepconAX_weak
   - Instance Pred_wandAX
   - Instance Pred_sepconAX
   - Instance Pred_gcsGamma
   - Instance Pred_EmpsGamma
-/

import Unifysl.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic
import Unifysl.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms
import Unifysl.SeparationLogic.Sound.Sound_Flat
import Unifysl.SeparationLogic.Model.OSAGenerators
import Unifysl.SeparationLogic.Semantics.FlatSemantics

universe u

namespace Unifysl

open PropositionalLanguageNotation
open SeparationLogicNotation

private abbrev PredSep_MD (A : Type u) : Model.{u} :=
  { model := A }

private abbrev PredSep_eqR (A : Type u) : Relation A :=
  { Krelation := fun m n => m = n }

private abbrev PredSep_SM (A : Type u) : Semantics (Pred_L A) (PredSep_MD A) :=
  Pred_SM A

private instance PredSep_eqPreOrder (A : Type u) :
    @PreOrder A (@Krelation A (PredSep_eqR A)) :=
  eq_preorder A

private def PredSep_eqDownwards (A : Type u) [J : Join A] :
    @DownwardsClosedSeparationAlgebra A (PredSep_eqR A) J := by
  letI : Relation A := PredSep_eqR A
  exact {
  join_Korder_down := by
    intro m1 m2 m n1 n2 hj hn1 hn2
    subst n1
    subst n2
    exact ⟨m, hj, rfl⟩ }

private def PredSep_iffL (A : Type u) : IffLanguage (Pred_L A) := by
  letI : Relation A := PredSep_eqR A
  exact { iffp := fun x y => Semantics.KripkePropositional.iffp x y }

private def PredSep_kiffSM (A : Type u) :
    @KripkeIffSemantics (Pred_L A) (PredSep_iffL A) (PredSep_MD A)
      (unit_kMD (PredSep_MD A))
      (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
      (PredSep_eqR A) (PredSep_SM A) :=
  @KripkeIffSemantics.mk (Pred_L A) (PredSep_iffL A) (PredSep_MD A)
    (unit_kMD (PredSep_MD A))
    (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
    (PredSep_eqR A) (PredSep_SM A)
    (by
      intro x y
      exact Same_set_refl A _)

instance Pred_sepconL (A : Type u) [Join A] : SepconLanguage (Pred_L A) where
  sepcon := WeakSemantics.sepcon

instance Pred_wandL (A : Type u) [Join A] : WandLanguage (Pred_L A) where
  wand := WeakSemantics.wand

instance Pred_empL (A : Type u) [Join A] [Unit A] : EmpLanguage (Pred_L A) where
  emp := EmpSemantics.emp

instance Pred_fsepconSM (A : Type u) [J : Join A] [Unit A] :
    @SepconSemantics (Pred_L A) (Pred_sepconL A) (PredSep_MD A)
      (unit_kMD (PredSep_MD A))
      (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
      (PredSep_eqR A) J (PredSep_SM A) :=
  @SepconSemantics.mk (Pred_L A) (Pred_sepconL A) (PredSep_MD A)
    (unit_kMD (PredSep_MD A))
    (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
    (PredSep_eqR A) J (PredSep_SM A)
    (by
      intro x y
      exact Same_set_refl A _)

instance Pred_fwandSM (A : Type u) [J : Join A] [Unit A] :
    @WandSemantics (Pred_L A) (Pred_wandL A) (PredSep_MD A)
      (unit_kMD (PredSep_MD A))
      (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
      (PredSep_eqR A) J (PredSep_SM A) :=
  @WandSemantics.mk (Pred_L A) (Pred_wandL A) (PredSep_MD A)
    (unit_kMD (PredSep_MD A))
    (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
    (PredSep_eqR A) J (PredSep_SM A)
    (by
      intro x y
      exact Same_set_refl A _)

instance Pred_empSM (A : Type u) [Join A] [U : Unit A] :
    @EmpSemantics (Pred_L A) (Pred_empL A) (PredSep_MD A)
      (unit_kMD (PredSep_MD A))
      (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
      U (PredSep_SM A) :=
  @EmpSemantics.mk (Pred_L A) (Pred_empL A) (PredSep_MD A)
    (unit_kMD (PredSep_MD A))
    (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
    U (PredSep_SM A)
    (by
      exact Same_set_refl A _)

instance Pred_sepconAX_weak (A : Type u) [Join A] [Unit A]
    [SeparationAlgebra A] :
    SepconAxiomatization_weak (Pred_L A) (Pred_Gamma A) where
  __provable_sepcon_comm_impp := by
    intro x y
    letI : Relation A := PredSep_eqR A
    letI : PreOrder (@Krelation A (PredSep_eqR A)) := PredSep_eqPreOrder A
    letI : DownwardsClosedSeparationAlgebra A := PredSep_eqDownwards A
    letI : IffLanguage (Pred_L A) := PredSep_iffL A
    letI : @KripkeIffSemantics (Pred_L A) (PredSep_iffL A) (PredSep_MD A)
        (unit_kMD (PredSep_MD A))
        (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
        (PredSep_eqR A) (PredSep_SM A) := PredSep_kiffSM A
    exact sound_sepcon_comm (L := Pred_L A) (MD := PredSep_MD A)
      (_kMD := unit_kMD (PredSep_MD A))
      (_R := PredSep_eqR A)
      (_J := (inferInstance : Join A))
      (_U := (inferInstance : Unit A))
      (_SA := (inferInstance : SeparationAlgebra A))
      (_dSA := PredSep_eqDownwards A)
      (M := (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)) x y
  __provable_sepcon_assoc1 := by
    intro x y z
    letI : Relation A := PredSep_eqR A
    letI : PreOrder (@Krelation A (PredSep_eqR A)) := PredSep_eqPreOrder A
    letI : DownwardsClosedSeparationAlgebra A := PredSep_eqDownwards A
    letI : IffLanguage (Pred_L A) := PredSep_iffL A
    letI : @KripkeIffSemantics (Pred_L A) (PredSep_iffL A) (PredSep_MD A)
        (unit_kMD (PredSep_MD A))
        (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
        (PredSep_eqR A) (PredSep_SM A) := PredSep_kiffSM A
    exact sound_provable_sepcon_assoc1 (L := Pred_L A) (MD := PredSep_MD A)
      (_kMD := unit_kMD (PredSep_MD A))
      (_R := PredSep_eqR A)
      (_J := (inferInstance : Join A))
      (_U := (inferInstance : Unit A))
      (_SA := (inferInstance : SeparationAlgebra A))
      (_dSA := PredSep_eqDownwards A)
      (M := (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)) x y z

instance Pred_wandAX (A : Type u) [Join A] [Unit A] [SeparationAlgebra A] :
    WandAxiomatization (Pred_L A) (Pred_Gamma A) where
  provables_wand_sepcon_adjoint := by
    intro x y z
    letI : Relation A := PredSep_eqR A
    letI : PreOrder (@Krelation A (PredSep_eqR A)) := PredSep_eqPreOrder A
    letI : DownwardsClosedSeparationAlgebra A := PredSep_eqDownwards A
    letI : IffLanguage (Pred_L A) := PredSep_iffL A
    letI : @KripkeIffSemantics (Pred_L A) (PredSep_iffL A) (PredSep_MD A)
        (unit_kMD (PredSep_MD A))
        (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
        (PredSep_eqR A) (PredSep_SM A) := PredSep_kiffSM A
    exact sound_provables_wand_sepcon_adjoint (L := Pred_L A) (MD := PredSep_MD A)
      (_kMD := unit_kMD (PredSep_MD A))
      (_R := PredSep_eqR A)
      (_J := (inferInstance : Join A))
      (_U := (inferInstance : Unit A))
      (_SA := (inferInstance : SeparationAlgebra A))
      (_dSA := PredSep_eqDownwards A)
      (M := (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)) x y z

instance Pred_sepconAX (A : Type u) [Join A] [Unit A] [SeparationAlgebra A] :
    SepconAxiomatization (Pred_L A) (Pred_Gamma A) := by
  letI : SepconMonoAxiomatization (Pred_L A) (Pred_Gamma A) :=
    Adj2SepconMono
  exact SepconAxiomatizationWeak2SepconAxiomatization

instance Pred_gcsGamma (A : Type u) [Join A] [Unit A] [SeparationAlgebra A]
    [@IncreasingSeparationAlgebra A (PredSep_eqR A) inferInstance] :
    GarbageCollectSeparationLogic (Pred_L A) (Pred_Gamma A) where
  provable_sepcon_elim1 := by
    intro x y
    letI : Relation A := PredSep_eqR A
    letI : PreOrder (@Krelation A (PredSep_eqR A)) := PredSep_eqPreOrder A
    letI : DownwardsClosedSeparationAlgebra A := PredSep_eqDownwards A
    letI : IffLanguage (Pred_L A) := PredSep_iffL A
    letI : @KripkeIffSemantics (Pred_L A) (PredSep_iffL A) (PredSep_MD A)
        (unit_kMD (PredSep_MD A))
        (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
        (PredSep_eqR A) (PredSep_SM A) := PredSep_kiffSM A
    exact sound_provable_sepcon_elim1 (L := Pred_L A) (MD := PredSep_MD A)
      (_kMD := unit_kMD (PredSep_MD A))
      (_R := PredSep_eqR A)
      (_J := (inferInstance : Join A))
      (_U := (inferInstance : Unit A))
      (_SA := (inferInstance : SeparationAlgebra A))
      (_dSA := PredSep_eqDownwards A)
      (_incrSA := (inferInstance :
        @IncreasingSeparationAlgebra A (PredSep_eqR A) (inferInstance : Join A)))
      (M := (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)) x y

instance Pred_EmpsGamma (A : Type u) [Join A] [Unit A] [SeparationAlgebra A]
    [@UnitJoinOrderRelation A inferInstance inferInstance (PredSep_eqR A)] :
    EmpAxiomatization (Pred_L A) (Pred_Gamma A) where
  provable_sepcon_emp_derives := by
    intro x
    letI : Relation A := PredSep_eqR A
    letI : PreOrder (@Krelation A (PredSep_eqR A)) := PredSep_eqPreOrder A
    letI : DownwardsClosedSeparationAlgebra A := PredSep_eqDownwards A
    letI : IffLanguage (Pred_L A) := PredSep_iffL A
    letI : @KripkeIffSemantics (Pred_L A) (PredSep_iffL A) (PredSep_MD A)
        (unit_kMD (PredSep_MD A))
        (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
        (PredSep_eqR A) (PredSep_SM A) := PredSep_kiffSM A
    exact sound_provable_sepcon_emp_derives (L := Pred_L A) (MD := PredSep_MD A)
      (_kMD := unit_kMD (PredSep_MD A))
      (_R := PredSep_eqR A)
      (_J := (inferInstance : Join A))
      (_U := (inferInstance : Unit A))
      (_SA := (inferInstance : SeparationAlgebra A))
      (_dSA := PredSep_eqDownwards A)
      (_UJO_Rel := (inferInstance :
        @UnitJoinOrderRelation A (inferInstance : Unit A)
          (inferInstance : Join A) (PredSep_eqR A)))
      (M := (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)) x
  provable_derives_sepcon_emp := by
    intro x
    letI : Relation A := PredSep_eqR A
    letI : PreOrder (@Krelation A (PredSep_eqR A)) := PredSep_eqPreOrder A
    letI : DownwardsClosedSeparationAlgebra A := PredSep_eqDownwards A
    letI : IffLanguage (Pred_L A) := PredSep_iffL A
    letI : @KripkeIffSemantics (Pred_L A) (PredSep_iffL A) (PredSep_MD A)
        (unit_kMD (PredSep_MD A))
        (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)
        (PredSep_eqR A) (PredSep_SM A) := PredSep_kiffSM A
    exact sound_provable_derives_sepcon_emp (L := Pred_L A) (MD := PredSep_MD A)
      (_kMD := unit_kMD (PredSep_MD A))
      (_R := PredSep_eqR A)
      (_J := (inferInstance : Join A))
      (_U := (inferInstance : Unit A))
      (_SA := (inferInstance : SeparationAlgebra A))
      (_dSA := PredSep_eqDownwards A)
      (_UJO_Rel := (inferInstance :
        @UnitJoinOrderRelation A (inferInstance : Unit A)
          (inferInstance : Join A) (PredSep_eqR A)))
      (M := (Unit.unit : (unit_kMD (PredSep_MD A)).Kmodel)) x

end Unifysl
