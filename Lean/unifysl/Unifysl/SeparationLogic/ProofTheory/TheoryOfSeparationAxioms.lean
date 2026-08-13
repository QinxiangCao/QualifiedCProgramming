/- Coq inventory: unifysl-prp/SeparationLogic/ProofTheory/TheoryOfSeparationAxioms.v
   - Classes:
     SepconMonoAxiomatization, SepconAxiomatization_weak,
     SepconAxiomatization_weak_iffp, EmpAxiomatization_iffp.
   - Conversion lemmas:
     SepconAxiomatizationWeak2SepconAxiomatization,
     SepconAxiomatizationWeakIff2SepconAxiomatizationWeak,
     EmpAxiomatizationIff2EmpAxiomatization.
   - Adjointness-derived lemmas:
     Adj2SepconMono, Adj2SepconOr, Adj2SepconFalse,
     Adj2SepconCoqProp.
-/

import Unifysl.SeparationLogic.ProofTheory.SeparationLogic
import Unifysl.PropositionalLogic.ProofTheory.ProofTheoryPatterns
import Unifysl.MetaLogicInj.ProofTheory.ProofRules

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Unifysl

open PropositionalLanguageNotation
open CoqPropInLogicNotation
open SeparationLogicNotation

class SepconMonoAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [SepconLanguage L] (Gamma : Provable L) : Prop where
  __provable_sepcon_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      (|-- (x1 ⟶ x2)) -> (|-- (y1 ⟶ y2)) ->
        |-- ((x1 * y1) ⟶ (x2 * y2))

namespace SepconMonoAxiomatization

theorem __sepcon_mono {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [Gamma : Provable L]
    [self : SepconMonoAxiomatization L Gamma] :
    forall x1 x2 y1 y2 : @Language.expr L,
      (|-- (x1 ⟶ x2)) -> (|-- (y1 ⟶ y2)) ->
        |-- ((x1 * y1) ⟶ (x2 * y2)) :=
  self.__provable_sepcon_mono

end SepconMonoAxiomatization

class SepconAxiomatization_weak (L : Language.{u}) [MinimumLanguage L]
    [SepconLanguage L] (Gamma : Provable L) : Prop where
  __provable_sepcon_comm_impp :
    forall x y : @Language.expr L, |-- ((x * y) ⟶ (y * x))
  __provable_sepcon_assoc1 :
    forall x y z : @Language.expr L,
      |-- ((x * (y * z)) ⟶ ((x * y) * z))

namespace SepconAxiomatization_weak

theorem __sepcon_comm_impp {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [Gamma : Provable L]
    [self : SepconAxiomatization_weak L Gamma] :
    forall x y : @Language.expr L, |-- ((x * y) ⟶ (y * x)) :=
  self.__provable_sepcon_comm_impp

theorem __sepcon_assoc1 {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [Gamma : Provable L]
    [self : SepconAxiomatization_weak L Gamma] :
    forall x y z : @Language.expr L,
      |-- ((x * (y * z)) ⟶ ((x * y) * z)) :=
  self.__provable_sepcon_assoc1

end SepconAxiomatization_weak

class SepconAxiomatization_weak_iffp (L : Language.{u}) [IffLanguage L]
    [SepconLanguage L] (Gamma : Provable L) : Prop where
  __sepcon_comm :
    forall x y : @Language.expr L, |-- ((x * y) ⟷ (y * x))
  __sepcon_assoc :
    forall x y z : @Language.expr L,
      |-- ((x * (y * z)) ⟷ ((x * y) * z))

class EmpAxiomatization_iffp (L : Language.{u}) [IffLanguage L]
    [SepconLanguage L] [EmpLanguage L] (Gamma : Provable L) : Prop where
  __sepcon_emp :
    forall x : @Language.expr L, |-- ((x * emp) ⟷ x)

theorem SepconAxiomatizationWeak2SepconAxiomatization
    {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [SepconAxiomatization_weak L Gamma]
    [SepconMonoAxiomatization L Gamma] :
    SepconAxiomatization L Gamma := by
  constructor
  · intro x y
    exact SepconAxiomatization_weak.__sepcon_comm_impp (Gamma := Gamma) x y
  · intro x y z
    exact SepconAxiomatization_weak.__sepcon_assoc1 (Gamma := Gamma) x y z
  · intro x1 x2 y1 y2 hx hy
    exact SepconMonoAxiomatization.__sepcon_mono (Gamma := Gamma)
      x1 x2 y1 y2 hx hy

section FromAdjPlusSepconWeakToSepcon

variable {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
variable [WandLanguage L] [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma] [WandAxiomatization L Gamma]
variable [SepconAxiomatization_weak L Gamma]

private theorem sepcon_Comm_from_weak :
    ProofTheoryPatterns.P.Commutativity L Gamma sepcon := by
  constructor
  intro x y
  exact SepconAxiomatization_weak.__sepcon_comm_impp (Gamma := Gamma) x y

theorem Adj2SepconMono : SepconMonoAxiomatization L Gamma := by
  letI : ProofTheoryPatterns.P.Commutativity L Gamma sepcon := sepcon_Comm_from_weak
  letI : ProofTheoryPatterns.P.Adjointness L Gamma sepcon wand := wand_sepcon_Adj
  letI : ProofTheoryPatterns.P.Monotonicity L Gamma sepcon :=
    ProofTheoryPatterns.P.Adjoint2Mono (prodp := sepcon) (funcp := wand)
  constructor
  intro x1 x2 y1 y2 hx hy
  exact ProofTheoryPatterns.P.prodp_mono (prodp := sepcon)
    x1 y1 x2 y2 hx hy

end FromAdjPlusSepconWeakToSepcon

section FromSepconWeakIffToSepconWeak

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L] [SepconLanguage L]
variable [Gamma : Provable L] [MinimumAxiomatization L Gamma]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]
variable [SepconAxiomatization_weak_iffp L Gamma]

theorem SepconAxiomatizationWeakIff2SepconAxiomatizationWeak :
    SepconAxiomatization_weak L Gamma := by
  constructor
  · intro x y
    exact provables_iffp_elim1 (x * y) (y * x)
      (SepconAxiomatization_weak_iffp.__sepcon_comm (Gamma := Gamma) x y)
  · intro x y z
    exact provables_iffp_elim1 (x * (y * z)) ((x * y) * z)
      (SepconAxiomatization_weak_iffp.__sepcon_assoc (Gamma := Gamma) x y z)

end FromSepconWeakIffToSepconWeak

section FromAdjToPropositionalCombination

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L] [CoqPropLanguage L]
variable [SepconLanguage L] [WandLanguage L]
variable [Gamma : Provable L] [MinimumAxiomatization L Gamma]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]
variable [CoqPropAxiomatization L Gamma]
variable [SepconAxiomatization L Gamma] [WandAxiomatization L Gamma]

theorem Adj2SepconOr : SepconOrAxiomatization L Gamma := by
  letI : ProofTheoryPatterns.P.Adjointness L Gamma sepcon wand := wand_sepcon_Adj
  letI : ProofTheoryPatterns.P.RightDistr L Gamma sepcon orp :=
    PropositionalLogic.ProofTheoryPatterns.P.Adjoint2RDistr
      (prodp := sepcon) (funcp := wand)
  constructor
  intro x y z
  exact ProofTheoryPatterns.P.right_distr1 (prodp := sepcon) (sump := orp) z x y

theorem Adj2SepconFalse : SepconFalseAxiomatization L Gamma := by
  letI : ProofTheoryPatterns.P.Adjointness L Gamma sepcon wand := wand_sepcon_Adj
  constructor
  intro x
  exact provables_iffp_elim1 (FF * x) FF
    (PropositionalLogic.ProofTheoryPatterns.P.falsep_prodp
      (prodp := sepcon) (funcp := wand) x)

theorem Adj2SepconCoqProp : SepconCoqPropAxiomatization L Gamma := by
  constructor
  intro P Q R
  apply provables_iffp_intros
  · apply provables_impp_andp_fold
    · exact (WandAxiomatization.wand_sepcon_adjoint
        (Gamma := Gamma) (((!! P) && Q)) R (!! P)).mpr
        (provables_coq_prop_andp_derives P Q (R -* (!! P))
          (fun hP =>
            (WandAxiomatization.wand_sepcon_adjoint
              (Gamma := Gamma) Q R (!! P)).mp
              (aux_minimun_rule00 (!! P) (Q * R)
                (CoqPropAxiomatization.coq_prop_intros
                  (Gamma := Gamma) P hP))))
    · exact SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        (((!! P) && Q)) Q R R
        (AndAxiomatization.provable_andp_elim2 (!! P) Q)
        (provable_impp_refl R)
  · exact provables_coq_prop_andp_derives P (Q * R) (((!! P) && Q) * R)
      (fun hP =>
        SepconAxiomatization.sepcon_mono (Gamma := Gamma)
          Q (((!! P) && Q)) R R
          (provables_iffp_elim2 (((!! P) && Q)) Q
            (provables_coq_prop_andp P Q hP))
          (provable_impp_refl R))

end FromAdjToPropositionalCombination

section FromEmpIffToEmp

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L] [SepconLanguage L] [EmpLanguage L]
variable [Gamma : Provable L] [MinimumAxiomatization L Gamma]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]
variable [SepconAxiomatization L Gamma] [EmpAxiomatization_iffp L Gamma]

theorem EmpAxiomatizationIff2EmpAxiomatization :
    EmpAxiomatization L Gamma := by
  constructor
  · intro x
    exact provables_iffp_elim1 (x * emp) x
      (EmpAxiomatization_iffp.__sepcon_emp (Gamma := Gamma) x)
  · intro x
    exact provables_iffp_elim2 (x * emp) x
      (EmpAxiomatization_iffp.__sepcon_emp (Gamma := Gamma) x)

end FromEmpIffToEmp

end Unifysl
