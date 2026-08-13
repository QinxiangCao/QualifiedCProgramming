/- Coq inventory: unifysl-prp/SeparationLogic/ProofTheory/Deduction.v
   - Conversion lemmas:
     SepconDeduction2SepconAxiomatization_sepconAX,
     Deduction2Axiomatization_sepcon_orp_AX,
     Deduction2Axiomatization_sepcon_falsep_AX,
     Deduction2Axiomatization_esGamma,
     Deduction2Axiomatization_gcsAX,
     Deduction2Axiomatization_empAX,
     Deduction2Axiomatization_desGamma,
     Deduction2Axiomatization_nssGamma,
     WandDeduction2WandAxiomatization_wandAX,
     Axiomatization2Deduction_sepconD.
   - Deduction-level classes:
     SepconMonoDeduction, SepconDeduction_weak,
     SepconLogicEquiv_weak_iffp, EmpLogicEquiv_iffp.
   - Weak/equivalence conversions:
     SepconDeductionWeak2SepconDeduction,
     SepconDeduction_weak2SepconAxiomatization_weak,
     SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp,
     EmpLogicEquiv_iffp2EmpAxiomatization_iffp.
   - Adjointness/equivalence-derived deduction lemmas:
     Adj2SepconMono, SepconLogicEquivWeakIff2SepconDeductionWeak,
     Adj2SepconOrD, Adj2SepconFalse, EmpLogicEquivIff2EmpDeduction.
   - Registration instances:
     reg_Deduction2Axiomatization_sepcon_orpAX,
     reg_Deduction2Axiomatization_sepcon_falsep_AX,
     reg_Deduction2Axiomatization_gcsAX,
     reg_Deduction2Axiomatization_nssGamma,
     reg_Deduction2Axiomatization_empAX,
     reg_WandDeduction1WandAxiomatization,
     reg_SepconDeduction2SepconAxiomatization,
     reg_SepconDeduction_weak2SepconAxiomatization_weak,
     reg_SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp,
     reg_EmpLogicEquiv_iffp2EmpAxiomatization_iffp.
-/

import Unifysl.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms
import Unifysl.MinimumLogic.ProofTheory.ExtensionTactic
import Unifysl.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Unifysl

open PropositionalLanguageNotation
open SeparationLogicNotation
open CoqPropInLogicNotation

private theorem provable_iffp_intros_of {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    (x y : @Language.expr L) :
    (|-- (x ⟶ y)) -> (|-- (y ⟶ x)) -> |-- (x ⟷ y) := by
  intro hxy hyx
  have hstep := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ y) ((y ⟶ x) ⟶ (x ⟷ y))
    (IffAxiomatization.provable_iffp_intros (Gamma := Gamma) x y) hxy
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (y ⟶ x) (x ⟷ y) hstep hyx

section SLFromDeduction2SLFromAxiomatization1

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaD1 : Derivable1 L] [GammaP : Provable L]
variable [SepconLanguage L] [Derivable1Provable L GammaP GammaD1]

theorem SepconDeduction2SepconAxiomatization_sepconAX
    [SepconDeduction L GammaD1] :
    SepconAxiomatization L GammaP := by
  constructor
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * y) (y * x)).mp
        (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x y)
  · intro x y z
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x * (y * z)) ((x * y) * z)).mp
        (SepconDeduction.derivable1_sepcon_assoc1 (GammaD1 := GammaD1) x y z)
  · intro x1 x2 y1 y2 hx hy
    have hxD : x1 |-- x2 :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) x1 x2).mpr hx
    have hyD : y1 |-- y2 :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) y1 y2).mpr hy
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x1 * y1) (x2 * y2)).mp
        (SepconDeduction.derivable1_sepcon_mono
          (GammaD1 := GammaD1) x1 x2 y1 y2 hxD hyD)

variable [OrLanguage L] [AndLanguage L] [TrueLanguage L] [FalseLanguage L]

theorem Deduction2Axiomatization_sepcon_orp_AX
    [SepconOrDeduction L GammaD1] :
    SepconOrAxiomatization L GammaP := by
  constructor
  intro x y z
  exact (Derivable1Provable.derivable1_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD1)
    ((x || y) * z) ((x * z) || (y * z))).mp
      (SepconOrDeduction.orp_sepcon_left (GammaD1 := GammaD1) x y z)

theorem Deduction2Axiomatization_sepcon_falsep_AX
    [SepconFalseDeduction L GammaD1] :
    SepconFalseAxiomatization L GammaP := by
  constructor
  intro x
  exact (Derivable1Provable.derivable1_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD1) (FF * x) FF).mp
      (SepconFalseDeduction.falsep_sepcon_left (GammaD1 := GammaD1) x)

theorem Deduction2Axiomatization_esGamma
    [ExtSeparationLogicDeduction L GammaD1] :
    ExtSeparationLogic L GammaP := by
  constructor
  intro x
  exact (Derivable1Provable.derivable1_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (x * TT)).mp
      (ExtSeparationLogicDeduction.derivable1_sepcon_ext (GammaD1 := GammaD1) x)

theorem Deduction2Axiomatization_gcsAX
    [GarbageCollectSeparationLogicDeduction L GammaD1] :
    GarbageCollectSeparationLogic L GammaP := by
  constructor
  intro x y
  exact (Derivable1Provable.derivable1_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * y) x).mp
      (GarbageCollectSeparationLogicDeduction.derivable1_sepcon_elim1
        (GammaD1 := GammaD1) x y)

end SLFromDeduction2SLFromAxiomatization1

instance reg_Deduction2Axiomatization_sepcon_orpAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `sepcon_orp_AX
        ``Deduction2Axiomatization_sepcon_orp_AX) 10 := {}

instance reg_Deduction2Axiomatization_sepcon_falsep_AX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `sepcon_false_AX
        ``Deduction2Axiomatization_sepcon_falsep_AX) 11 := {}

instance reg_Deduction2Axiomatization_gcsAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `gcsGamma ``Deduction2Axiomatization_gcsAX) 12 := {}

section SLFromDeduction2SLFromAxiomatization2

variable {L : Language.{u}} [MinimumLanguage L]
variable [SepconLanguage L] [EmpLanguage L]
variable [GammaD1 : Derivable1 L] [GammaP : Provable L]
variable [Derivable1Provable L GammaP GammaD1]

theorem Deduction2Axiomatization_empAX
    [EmpDeduction L GammaD1] :
    EmpAxiomatization L GammaP := by
  constructor
  · intro x
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * emp) x).mp
        (EmpDeduction.sepcon_emp_left (GammaD1 := GammaD1) x)
  · intro x
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (x * emp)).mp
        (EmpDeduction.sepcon_emp_right (GammaD1 := GammaD1) x)

section SLFromDeduction2SLFromAxiomatization3

variable [OrLanguage L] [AndLanguage L] [TrueLanguage L] [FalseLanguage L]

theorem Deduction2Axiomatization_desGamma
    [DupEmpSeparationLogicDeduction L GammaD1] :
    DupEmpSeparationLogic L GammaP := by
  constructor
  intro x
  exact (Derivable1Provable.derivable1_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x && emp) (x * x)).mp
      (DupEmpSeparationLogicDeduction.derivable1_emp_dup
        (GammaD1 := GammaD1) x)

theorem Deduction2Axiomatization_nssGamma
    [NonsplitEmpSeparationLogicDeduction L GammaD1] :
    NonsplitEmpSeparationLogic L GammaP := by
  constructor
  intro x
  exact (Derivable1Provable.derivable1_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD1) ((x * TT) && emp) x).mp
      (NonsplitEmpSeparationLogicDeduction.derivable1_emp_sepcon_truep_elim
        (GammaD1 := GammaD1) x)

end SLFromDeduction2SLFromAxiomatization3

end SLFromDeduction2SLFromAxiomatization2

instance reg_Deduction2Axiomatization_nssGamma :
    RegisterClass D12P_reg
      (ProofRegistration.mk `nssGamma ``Deduction2Axiomatization_nssGamma) 13 := {}

instance reg_Deduction2Axiomatization_empAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `empAx ``Deduction2Axiomatization_empAX) 14 := {}

section SLFromDeduction2SLFromAxiomatization4

variable {L : Language.{u}} [MinimumLanguage L]
variable [SepconLanguage L] [WandLanguage L]
variable [GammaD1 : Derivable1 L] [GammaP : Provable L]
variable [Derivable1Provable L GammaP GammaD1]

theorem WandDeduction2WandAxiomatization_wandAX
    [WandDeduction L GammaD1] :
    WandAxiomatization L GammaP := by
  constructor
  intro x y z
  constructor
  · intro h
    have hD : (x * y) |-- z :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * y) z).mpr h
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (y -* z)).mp
        ((WandDeduction.derivable1_wand_sepcon_adjoint
          (GammaD1 := GammaD1) x y z).mp hD)
  · intro h
    have hD : x |-- (y -* z) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (y -* z)).mpr h
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * y) z).mp
        ((WandDeduction.derivable1_wand_sepcon_adjoint
          (GammaD1 := GammaD1) x y z).mpr hD)

end SLFromDeduction2SLFromAxiomatization4

instance reg_WandDeduction1WandAxiomatization :
    RegisterClass D12P_reg
      (ProofRegistration.mk `wandAX
        ``WandDeduction2WandAxiomatization_wandAX) 15 := {}

instance reg_SepconDeduction2SepconAxiomatization :
    RegisterClass D12P_reg
      (ProofRegistration.mk `SAx
        ``SepconDeduction2SepconAxiomatization_sepconAX) 16 := {}

class SepconMonoDeduction (L : Language.{u}) [SepconLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  __provable_sepcon_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      x1 |-- x2 -> y1 |-- y2 -> (x1 * y1) |-- (x2 * y2)

namespace SepconMonoDeduction

theorem __sepcon_mono {L : Language.{u}} [SepconLanguage L]
    [GammaD1 : Derivable1 L] [self : SepconMonoDeduction L GammaD1] :
    forall x1 x2 y1 y2 : @Language.expr L,
      x1 |-- x2 -> y1 |-- y2 -> (x1 * y1) |-- (x2 * y2) :=
  self.__provable_sepcon_mono

end SepconMonoDeduction

class SepconDeduction_weak (L : Language.{u}) [SepconLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  __provable_sepcon_comm_impp :
    forall x y : @Language.expr L, (x * y) |-- (y * x)
  __provable_sepcon_assoc1 :
    forall x y z : @Language.expr L, (x * (y * z)) |-- ((x * y) * z)

namespace SepconDeduction_weak

theorem __sepcon_comm_impp {L : Language.{u}} [SepconLanguage L]
    [GammaD1 : Derivable1 L] [self : SepconDeduction_weak L GammaD1] :
    forall x y : @Language.expr L, (x * y) |-- (y * x) :=
  self.__provable_sepcon_comm_impp

theorem __sepcon_assoc1 {L : Language.{u}} [SepconLanguage L]
    [GammaD1 : Derivable1 L] [self : SepconDeduction_weak L GammaD1] :
    forall x y z : @Language.expr L, (x * (y * z)) |-- ((x * y) * z) :=
  self.__provable_sepcon_assoc1

end SepconDeduction_weak

class SepconLogicEquiv_weak_iffp (L : Language.{u}) [SepconLanguage L]
    (GammaE : LogicEquiv L) : Prop where
  logic_equiv_sepcon_comm :
    forall x y : @Language.expr L, logic_equiv (L := L) (x * y) (y * x)
  logic_equiv_sepcon_assoc :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (x * (y * z)) ((x * y) * z)

namespace SepconLogicEquiv_weak_iffp

theorem __sepcon_comm {L : Language.{u}} [SepconLanguage L]
    [GammaE : LogicEquiv L] [self : SepconLogicEquiv_weak_iffp L GammaE] :
    forall x y : @Language.expr L, logic_equiv (L := L) (x * y) (y * x) :=
  self.logic_equiv_sepcon_comm

theorem __sepcon_assoc {L : Language.{u}} [SepconLanguage L]
    [GammaE : LogicEquiv L] [self : SepconLogicEquiv_weak_iffp L GammaE] :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (x * (y * z)) ((x * y) * z) :=
  self.logic_equiv_sepcon_assoc

end SepconLogicEquiv_weak_iffp

class EmpLogicEquiv_iffp (L : Language.{u}) [SepconLanguage L]
    [EmpLanguage L] (GammaE : LogicEquiv L) : Prop where
  logic_equiv_sepcon_emp :
    forall x : @Language.expr L, logic_equiv (L := L) (x * emp) x

namespace EmpLogicEquiv_iffp

theorem __sepcon_emp {L : Language.{u}} [SepconLanguage L] [EmpLanguage L]
    [GammaE : LogicEquiv L] [self : EmpLogicEquiv_iffp L GammaE] :
    forall x : @Language.expr L, logic_equiv (L := L) (x * emp) x :=
  self.logic_equiv_sepcon_emp

end EmpLogicEquiv_iffp

theorem SepconDeductionWeak2SepconDeduction
    {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
    [GammaD1 : Derivable1 L]
    [SepconDeduction_weak L GammaD1]
    [SepconMonoDeduction L GammaD1] :
    SepconDeduction L GammaD1 := by
  constructor
  · intro x y
    exact SepconDeduction_weak.__sepcon_comm_impp (GammaD1 := GammaD1) x y
  · intro x y z
    exact SepconDeduction_weak.__sepcon_assoc1 (GammaD1 := GammaD1) x y z
  · intro x1 x2 y1 y2 hx hy
    exact SepconMonoDeduction.__sepcon_mono
      (GammaD1 := GammaD1) x1 x2 y1 y2 hx hy

section SepconDeductionWeak2SepconAxiomatizationWeak

variable {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
variable [GammaD1 : Derivable1 L] [GammaP : Provable L]
variable [SepconDeduction_weak L GammaD1]
variable [Derivable1Provable L GammaP GammaD1]

theorem SepconDeduction_weak2SepconAxiomatization_weak :
    SepconAxiomatization_weak L GammaP := by
  constructor
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * y) (y * x)).mp
        (SepconDeduction_weak.__sepcon_comm_impp (GammaD1 := GammaD1) x y)
  · intro x y z
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x * (y * z)) ((x * y) * z)).mp
        (SepconDeduction_weak.__sepcon_assoc1 (GammaD1 := GammaD1) x y z)

end SepconDeductionWeak2SepconAxiomatizationWeak

instance reg_SepconDeduction_weak2SepconAxiomatization_weak :
    RegisterClass D12P_reg
      (ProofRegistration.mk `sepconAX
        ``SepconDeduction_weak2SepconAxiomatization_weak) 17 := {}

section SepconLogicEquivWeakIffpToSepconAxiomatizationWeakIffp

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [IffLanguage L] [SepconLanguage L]
variable [GammaE : LogicEquiv L] [GammaP : Provable L] [GammaD1 : Derivable1 L]
variable [ProvableDerivable1 L GammaP GammaD1]
variable [IffDeduction L GammaD1]
variable [SepconLogicEquiv_weak_iffp L GammaE]
variable [BasicDeduction L GammaD1]
variable [ImpAndAdjointDeduction L GammaD1]
variable [AndDeduction L GammaD1]
variable [Derivable1Provable L GammaP GammaD1]
variable [EquivDerivable1 L GammaD1 GammaE]

theorem SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp :
    SepconAxiomatization_weak_iffp L GammaP := by
  letI : MinimumAxiomatization L GammaP :=
    Deduction2Axiomatization_minAX (L := L) (GammaP := GammaP) (GammaD1 := GammaD1)
  letI : IffAxiomatization L GammaP :=
    Deduction2Axiomatization_iffpAX (L := L) (GammaP := GammaP) (GammaD1 := GammaD1)
  constructor
  · intro x y
    have hD := (__logic_equiv_derivable1 (L := L) (x * y) (y * x)).mp
      (SepconLogicEquiv_weak_iffp.__sepcon_comm (GammaE := GammaE) x y)
    exact provable_iffp_intros_of (x * y) (y * x)
      ((Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * y) (y * x)).mp hD.left)
      ((Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) (y * x) (x * y)).mp hD.right)
  · intro x y z
    have hD := (__logic_equiv_derivable1 (L := L)
      (x * (y * z)) ((x * y) * z)).mp
        (SepconLogicEquiv_weak_iffp.__sepcon_assoc (GammaE := GammaE) x y z)
    exact provable_iffp_intros_of (x * (y * z)) ((x * y) * z)
      ((Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1)
        (x * (y * z)) ((x * y) * z)).mp hD.left)
      ((Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1)
        ((x * y) * z) (x * (y * z))).mp hD.right)

end SepconLogicEquivWeakIffpToSepconAxiomatizationWeakIffp

instance reg_SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp :
    RegisterClass D12P_reg
      (ProofRegistration.mk `sepcon_weak_iffp
        ``SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp) 18 := {}

section EmpLogicEquivIffp2EmpAxiomatizationIffp

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [IffLanguage L] [SepconLanguage L] [EmpLanguage L]
variable [GammaE : LogicEquiv L] [GammaP : Provable L] [GammaD1 : Derivable1 L]
variable [ProvableDerivable1 L GammaP GammaD1]
variable [EmpLogicEquiv_iffp L GammaE]
variable [IffDeduction L GammaD1]
variable [BasicDeduction L GammaD1]
variable [ImpAndAdjointDeduction L GammaD1]
variable [AndDeduction L GammaD1]
variable [Derivable1Provable L GammaP GammaD1]
variable [EquivDerivable1 L GammaD1 GammaE]

theorem EmpLogicEquiv_iffp2EmpAxiomatization_iffp :
    EmpAxiomatization_iffp L GammaP := by
  letI : MinimumAxiomatization L GammaP :=
    Deduction2Axiomatization_minAX (L := L) (GammaP := GammaP) (GammaD1 := GammaD1)
  letI : IffAxiomatization L GammaP :=
    Deduction2Axiomatization_iffpAX (L := L) (GammaP := GammaP) (GammaD1 := GammaD1)
  constructor
  intro x
  have hD := (__logic_equiv_derivable1 (L := L) (x * emp) x).mp
    (EmpLogicEquiv_iffp.__sepcon_emp (GammaE := GammaE) x)
  exact provable_iffp_intros_of (x * emp) x
    ((Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * emp) x).mp hD.left)
    ((Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (x * emp)).mp hD.right)

end EmpLogicEquivIffp2EmpAxiomatizationIffp

instance reg_EmpLogicEquiv_iffp2EmpAxiomatization_iffp :
    RegisterClass D12P_reg
      (ProofRegistration.mk `empAX_iffp
        ``EmpLogicEquiv_iffp2EmpAxiomatization_iffp) 19 := {}

section FromSepconWeakIffToSepconDeductionWeak

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [IffLanguage L] [SepconLanguage L]
variable [GammaE : LogicEquiv L] [GammaD1 : Derivable1 L]
variable [AndDeduction L GammaD1]
variable [ImpAndAdjointDeduction L GammaD1]
variable [IffDeduction L GammaD1]
variable [SepconLogicEquiv_weak_iffp L GammaE]
variable [BasicDeduction L GammaD1]
variable [EquivDerivable1 L GammaD1 GammaE]

theorem SepconLogicEquivWeakIff2SepconDeductionWeak :
    SepconDeduction_weak L GammaD1 := by
  constructor
  · intro x y
    exact ((__logic_equiv_derivable1 (L := L) (x * y) (y * x)).mp
      (SepconLogicEquiv_weak_iffp.__sepcon_comm (GammaE := GammaE) x y)).left
  · intro x y z
    exact ((__logic_equiv_derivable1 (L := L)
      (x * (y * z)) ((x * y) * z)).mp
        (SepconLogicEquiv_weak_iffp.__sepcon_assoc (GammaE := GammaE) x y z)).left

end FromSepconWeakIffToSepconDeductionWeak

section FromAdjToSepconOrDeductionPropositionalCombination

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [IffLanguage L] [SepconLanguage L] [WandLanguage L]
variable [GammaD1 : Derivable1 L]
variable [AndDeduction L GammaD1]
variable [ImpAndAdjointDeduction L GammaD1]
variable [IffDeduction L GammaD1]
variable [SepconDeduction L GammaD1]
variable [WandDeduction L GammaD1]
variable [BasicDeduction L GammaD1]

theorem Adj2SepconOrD [OrLanguage L] [OrDeduction L GammaD1] :
    SepconOrDeduction L GammaD1 := by
  constructor
  intro x y z
  letI : ProofTheoryPatterns.D1.Adjointness L GammaD1 sepcon wand :=
    derivable1_wand_sepcon_Adj (L := L) (GammaD1 := GammaD1)
  letI : ProofTheoryPatterns.D1.RightDistr L GammaD1 sepcon orp :=
    PropositionalLogic.ProofTheoryPatterns.D1.Adjoint2RDistr
      (prodp := sepcon) (funcp := wand)
  exact ProofTheoryPatterns.D1.right_distr1
    (prodp := sepcon) (sump := orp) z x y

end FromAdjToSepconOrDeductionPropositionalCombination

section FromEmpEIffToEmpD

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [IffLanguage L] [SepconLanguage L] [EmpLanguage L]
variable [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
variable [AndDeduction L GammaD1]
variable [ImpAndAdjointDeduction L GammaD1]
variable [IffDeduction L GammaD1]
variable [SepconDeduction L GammaD1]
variable [EmpLogicEquiv_iffp L GammaE]
variable [BasicDeduction L GammaD1]
variable [EquivDerivable1 L GammaD1 GammaE]

theorem EmpLogicEquivIff2EmpDeduction :
    EmpDeduction L GammaD1 := by
  constructor
  · intro x
    exact ((__logic_equiv_derivable1 (L := L) (x * emp) x).mp
      (EmpLogicEquiv_iffp.__sepcon_emp (GammaE := GammaE) x)).left
  · intro x
    exact ((__logic_equiv_derivable1 (L := L) (x * emp) x).mp
      (EmpLogicEquiv_iffp.__sepcon_emp (GammaE := GammaE) x)).right

end FromEmpEIffToEmpD

section Deduction2LogicEquiv

variable {L : Language.{u}}
variable [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
variable [EquivDerivable1 L GammaD1 GammaE]
variable [BasicDeduction L GammaD1]
variable [SepconLanguage L] [EmpLanguage L]
variable [SepconDeduction L GammaD1] [EmpDeduction L GammaD1]

theorem Deduction2LogicEquiv_sepconE :
    SepconLogicEquiv_weak_iffp L GammaE := by
  constructor
  · intro x y
    exact (__logic_equiv_derivable1 (L := L) (x * y) (y * x)).mpr
      ⟨SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x y,
        SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) y x⟩
  · intro x y z
    exact (__logic_equiv_derivable1 (L := L)
      (x * (y * z)) ((x * y) * z)).mpr
        ⟨SepconDeduction.derivable1_sepcon_assoc1
            (GammaD1 := GammaD1) x y z,
          derivable1_sepcon_assoc2 (L := L) x y z⟩

theorem Deduction2LogicEquiv_empE :
    EmpLogicEquiv_iffp L GammaE := by
  constructor
  intro x
  exact (__logic_equiv_derivable1 (L := L) (x * emp) x).mpr
    ⟨EmpDeduction.sepcon_emp_left (GammaD1 := GammaD1) x,
      EmpDeduction.sepcon_emp_right (GammaD1 := GammaD1) x⟩

theorem logic_equiv_sepcon_swap [SepconLogicEquiv_weak_iffp L GammaE] :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (x * (y * z)) (y * (x * z)) := by
  intro x y z
  have hxy_comm : (x * y) |-- (y * x) :=
    SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x y
  have hyx_comm : (y * x) |-- (x * y) :=
    SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) y x
  have hforward : (x * (y * z)) |-- (y * (x * z)) := by
    exact derivable1_trans (x * (y * z)) ((x * y) * z) (y * (x * z))
      (SepconDeduction.derivable1_sepcon_assoc1 (GammaD1 := GammaD1) x y z)
      (derivable1_trans ((x * y) * z) ((y * x) * z) (y * (x * z))
        (SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
          (x * y) (y * x) z z hxy_comm (derivable1_refl z))
        (derivable1_sepcon_assoc2 (L := L) y x z))
  have hback : (y * (x * z)) |-- (x * (y * z)) := by
    exact derivable1_trans (y * (x * z)) ((y * x) * z) (x * (y * z))
      (SepconDeduction.derivable1_sepcon_assoc1 (GammaD1 := GammaD1) y x z)
      (derivable1_trans ((y * x) * z) ((x * y) * z) (x * (y * z))
        (SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
          (y * x) (x * y) z z hyx_comm (derivable1_refl z))
        (derivable1_sepcon_assoc2 (L := L) x y z))
  exact (__logic_equiv_derivable1 (L := L) (x * (y * z)) (y * (x * z))).mpr
    ⟨hforward, hback⟩

end Deduction2LogicEquiv

namespace SeparationLogic
namespace ProofTheory
namespace Deduction

theorem Axiomatization2Deduction_sepconD {L : Language.{u}}
    [MinimumLanguage L] [SepconLanguage L]
    [GammaP : Provable L] [GammaD1 : Derivable1 L]
    [Derivable1Provable L GammaP GammaD1]
    [SepconAxiomatization L GammaP] :
    SepconDeduction L GammaD1 := by
  constructor
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * y) (y * x)).mpr
        (SepconAxiomatization.sepcon_comm_impp (Gamma := GammaP) x y)
  · intro x y z
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x * (y * z)) ((x * y) * z)).mpr
        (SepconAxiomatization.sepcon_assoc1 (Gamma := GammaP) x y z)
  · intro x1 x2 y1 y2 hx hy
    have hxP : |-- (x1 ⟶ x2) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) x1 x2).mp hx
    have hyP : |-- (y1 ⟶ y2) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) y1 y2).mp hy
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x1 * y1) (x2 * y2)).mpr
        (SepconAxiomatization.sepcon_mono (Gamma := GammaP)
          x1 x2 y1 y2 hxP hyP)

theorem Adj2SepconMono {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [SepconLanguage L] [WandLanguage L]
    [GammaD1 : Derivable1 L]
    [AndDeduction L GammaD1]
    [ImpAndAdjointDeduction L GammaD1]
    [WandDeduction L GammaD1]
    [SepconDeduction_weak L GammaD1]
    [BasicDeduction L GammaD1] :
    SepconMonoDeduction L GammaD1 := by
  letI : ProofTheoryPatterns.D1.Commutativity L GammaD1 sepcon := by
    constructor
    intro x y
    exact SepconDeduction_weak.__sepcon_comm_impp (GammaD1 := GammaD1) x y
  letI : ProofTheoryPatterns.D1.Adjointness L GammaD1 sepcon wand :=
    derivable1_wand_sepcon_Adj (L := L) (GammaD1 := GammaD1)
  letI : ProofTheoryPatterns.D1.Monotonicity L GammaD1 sepcon :=
    ProofTheoryPatterns.D1.Adjoint2Mono (prodp := sepcon) (funcp := wand)
  constructor
  intro x1 x2 y1 y2 hx hy
  exact ProofTheoryPatterns.D1.prodp_mono
    (prodp := sepcon) x1 y1 x2 y2 hx hy

theorem Adj2SepconFalse {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] [FalseLanguage L]
    [SepconLanguage L] [WandLanguage L]
    [GammaD1 : Derivable1 L]
    [AndDeduction L GammaD1]
    [ImpAndAdjointDeduction L GammaD1]
    [IffDeduction L GammaD1]
    [SepconDeduction L GammaD1]
    [WandDeduction L GammaD1]
    [FalseDeduction L GammaD1]
    [BasicDeduction L GammaD1] :
    SepconFalseDeduction L GammaD1 := by
  constructor
  intro x
  exact (WandDeduction.derivable1_wand_sepcon_adjoint
    (GammaD1 := GammaD1) FF x FF).mpr
      (FalseDeduction.derivable1_falsep_elim
        (GammaD1 := GammaD1) (x -* FF))

end Deduction
end ProofTheory
end SeparationLogic

end Unifysl
