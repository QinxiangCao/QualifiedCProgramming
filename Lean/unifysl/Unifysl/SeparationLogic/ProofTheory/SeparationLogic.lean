/- Coq inventory: unifysl-prp/SeparationLogic/ProofTheory/SeparationLogic.v
   - Classes:
     SepconAxiomatization, SepconOrAxiomatization,
     SepconCoqPropAxiomatization, SepconFalseAxiomatization,
     EmpAxiomatization, WandAxiomatization, ExtSeparationLogic,
     NonsplitEmpSeparationLogic, DupEmpSeparationLogic,
     MallocFreeSeparationLogic, GarbageCollectSeparationLogic,
     SepconDeduction, SepconOrDeduction, SepconFalseDeduction,
     EmpDeduction, WandDeduction, ExtSeparationLogicDeduction,
     NonsplitEmpSeparationLogicDeduction, DupEmpSeparationLogicDeduction,
     GarbageCollectSeparationLogicDeduction.
   - D1 and provable-level sepcon, emp, wand, distribution, cancel,
     and elimination lemmas.
   - The Coq D1 cancel proof text has no active declarations.
-/

import Unifysl.GeneralLogic.ProofTheory.BasicDeduction
import Unifysl.GeneralLogic.ProofTheory.BasicLogicEquiv
import Unifysl.MinimumLogic.ProofTheory.Minimum
import Unifysl.MinimumLogic.ProofTheory.ProofTheoryPatterns
import Unifysl.PropositionalLogic.ProofTheory.Intuitionistic
import Unifysl.PropositionalLogic.ProofTheory.ProofTheoryPatterns
import Unifysl.PropositionalLogic.ProofTheory.RewriteClass
import Unifysl.MetaLogicInj.ProofTheory.ProofRules
import Unifysl.SeparationLogic.Syntax
import Unifysl.SeparationLogic.Model.SeparationAlgebra

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Unifysl

open PropositionalLanguageNotation
open CoqPropInLogicNotation
open SeparationLogicNotation

class SepconAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [SepconLanguage L] (Gamma : Provable L) : Prop where
  provable_sepcon_comm_impp :
    forall x y : @Language.expr L, |-- ((x * y) ⟶ (y * x))
  provable_sepcon_assoc1 :
    forall x y z : @Language.expr L, |-- ((x * (y * z)) ⟶ ((x * y) * z))
  provable_sepcon_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      (|-- (x1 ⟶ x2)) -> (|-- (y1 ⟶ y2)) ->
        |-- ((x1 * y1) ⟶ (x2 * y2))

namespace SepconAxiomatization

theorem sepcon_comm_impp {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [Gamma : Provable L]
    [self : SepconAxiomatization L Gamma] :
    forall x y : @Language.expr L, |-- ((x * y) ⟶ (y * x)) :=
  self.provable_sepcon_comm_impp

theorem sepcon_assoc1 {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [Gamma : Provable L]
    [self : SepconAxiomatization L Gamma] :
    forall x y z : @Language.expr L, |-- ((x * (y * z)) ⟶ ((x * y) * z)) :=
  self.provable_sepcon_assoc1

theorem sepcon_mono {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [Gamma : Provable L]
    [self : SepconAxiomatization L Gamma] :
    forall x1 x2 y1 y2 : @Language.expr L,
      (|-- (x1 ⟶ x2)) -> (|-- (y1 ⟶ y2)) ->
        |-- ((x1 * y1) ⟶ (x2 * y2)) :=
  self.provable_sepcon_mono

end SepconAxiomatization

class SepconOrAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [OrLanguage L] [SepconLanguage L] (Gamma : Provable L) : Prop where
  provable_orp_sepcon_derives :
    forall x y z : @Language.expr L,
      |-- (((x || y) * z) ⟶ ((x * z) || (y * z)))

namespace SepconOrAxiomatization

theorem orp_sepcon_impp {L : Language.{u}} [MinimumLanguage L]
    [OrLanguage L] [SepconLanguage L] [Gamma : Provable L]
    [self : SepconOrAxiomatization L Gamma] :
    forall x y z : @Language.expr L,
      |-- (((x || y) * z) ⟶ ((x * z) || (y * z))) :=
  self.provable_orp_sepcon_derives

end SepconOrAxiomatization

class SepconCoqPropAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] [CoqPropLanguage L]
    [SepconLanguage L] (Gamma : Provable L) : Prop where
  provable_coq_prop_andp_sepcon1 :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- ((((!! P) && Q) * R) ⟷ ((!! P) && (Q * R)))

namespace SepconCoqPropAxiomatization

theorem prop_andp_sepcon1 {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] [CoqPropLanguage L] [SepconLanguage L]
    [Gamma : Provable L] [self : SepconCoqPropAxiomatization L Gamma] :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- ((((!! P) && Q) * R) ⟷ ((!! P) && (Q * R))) :=
  self.provable_coq_prop_andp_sepcon1

end SepconCoqPropAxiomatization

class SepconFalseAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [FalseLanguage L] [SepconLanguage L] (Gamma : Provable L) : Prop where
  provable_falsep_sepcon_derives :
    forall x : @Language.expr L, |-- ((FF * x) ⟶ FF)

namespace SepconFalseAxiomatization

theorem falsep_sepcon_impp {L : Language.{u}} [MinimumLanguage L]
    [FalseLanguage L] [SepconLanguage L] [Gamma : Provable L]
    [self : SepconFalseAxiomatization L Gamma] :
    forall x : @Language.expr L, |-- ((FF * x) ⟶ FF) :=
  self.provable_falsep_sepcon_derives

end SepconFalseAxiomatization

class EmpAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] (Gamma : Provable L) : Prop where
  provable_sepcon_emp_derives :
    forall x : @Language.expr L, |-- ((x * emp) ⟶ x)
  provable_derives_sepcon_emp :
    forall x : @Language.expr L, |-- (x ⟶ (x * emp))

namespace EmpAxiomatization

theorem sepcon_emp1 {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] [Gamma : Provable L]
    [self : EmpAxiomatization L Gamma] :
    forall x : @Language.expr L, |-- ((x * emp) ⟶ x) :=
  self.provable_sepcon_emp_derives

theorem sepcon_emp2 {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] [Gamma : Provable L]
    [self : EmpAxiomatization L Gamma] :
    forall x : @Language.expr L, |-- (x ⟶ (x * emp)) :=
  self.provable_derives_sepcon_emp

end EmpAxiomatization

class WandAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [SepconLanguage L] [WandLanguage L] (Gamma : Provable L) : Prop where
  provables_wand_sepcon_adjoint :
    forall x y z : @Language.expr L,
      (|-- ((x * y) ⟶ z)) <-> (|-- (x ⟶ (y -* z)))

namespace WandAxiomatization

theorem wand_sepcon_adjoint {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [WandLanguage L] [Gamma : Provable L]
    [self : WandAxiomatization L Gamma] :
    forall x y z : @Language.expr L,
      (|-- ((x * y) ⟶ z)) <-> (|-- (x ⟶ (y -* z))) :=
  self.provables_wand_sepcon_adjoint

end WandAxiomatization

class ExtSeparationLogic (L : Language.{u}) [MinimumLanguage L]
    [TrueLanguage L] [SepconLanguage L] (Gamma : Provable L) : Prop where
  provable_derives_sepcon_truep :
    forall x : @Language.expr L, |-- (x ⟶ (x * TT))

namespace ExtSeparationLogic

theorem sepcon_ext {L : Language.{u}} [MinimumLanguage L]
    [TrueLanguage L] [SepconLanguage L] [Gamma : Provable L]
    [self : ExtSeparationLogic L Gamma] :
    forall x : @Language.expr L, |-- (x ⟶ (x * TT)) :=
  self.provable_derives_sepcon_truep

end ExtSeparationLogic

class NonsplitEmpSeparationLogic (L : Language.{u}) [MinimumLanguage L]
    [AndLanguage L] [TrueLanguage L] [SepconLanguage L] [EmpLanguage L]
    (Gamma : Provable L) : Prop where
  provable_sepcon_truep_andp_emp_derives :
    forall x : @Language.expr L, |-- (((x * TT) && emp) ⟶ x)

namespace NonsplitEmpSeparationLogic

theorem emp_sepcon_truep_elim {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [TrueLanguage L] [SepconLanguage L] [EmpLanguage L]
    [Gamma : Provable L] [self : NonsplitEmpSeparationLogic L Gamma] :
    forall x : @Language.expr L, |-- (((x * TT) && emp) ⟶ x) :=
  self.provable_sepcon_truep_andp_emp_derives

end NonsplitEmpSeparationLogic

class DupEmpSeparationLogic (L : Language.{u}) [MinimumLanguage L]
    [AndLanguage L] [SepconLanguage L] [EmpLanguage L]
    (Gamma : Provable L) : Prop where
  provable_emp_dup :
    forall x : @Language.expr L, |-- ((x && emp) ⟶ (x * x))

namespace DupEmpSeparationLogic

theorem emp_dup {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [SepconLanguage L] [EmpLanguage L] [Gamma : Provable L]
    [self : DupEmpSeparationLogic L Gamma] :
    forall x : @Language.expr L, |-- ((x && emp) ⟶ (x * x)) :=
  self.provable_emp_dup

end DupEmpSeparationLogic

class MallocFreeSeparationLogic (L : Language.{u}) [MinimumLanguage L]
    [AndLanguage L] [TrueLanguage L] [SepconLanguage L] [EmpLanguage L]
    (Gamma : Provable L) : Prop where
  MallocFreeSeparationLogic_NonsplitEmpSeparationLogic :
    NonsplitEmpSeparationLogic L Gamma
  MallocFreeSeparationLogic_DupEmpSeparationLogic :
    DupEmpSeparationLogic L Gamma

instance MallocFreeSeparationLogic_NonsplitEmpSeparationLogic_inst
    {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [TrueLanguage L]
    [SepconLanguage L] [EmpLanguage L] [Gamma : Provable L]
    [mfSL : MallocFreeSeparationLogic L Gamma] :
    NonsplitEmpSeparationLogic L Gamma :=
  mfSL.MallocFreeSeparationLogic_NonsplitEmpSeparationLogic

instance MallocFreeSeparationLogic_DupEmpSeparationLogic_inst
    {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [TrueLanguage L]
    [SepconLanguage L] [EmpLanguage L] [Gamma : Provable L]
    [mfSL : MallocFreeSeparationLogic L Gamma] :
    DupEmpSeparationLogic L Gamma :=
  mfSL.MallocFreeSeparationLogic_DupEmpSeparationLogic

class GarbageCollectSeparationLogic (L : Language.{u}) [MinimumLanguage L]
    [SepconLanguage L] (Gamma : Provable L) : Prop where
  provable_sepcon_elim1 :
    forall x y : @Language.expr L, |-- ((x * y) ⟶ x)

namespace GarbageCollectSeparationLogic

theorem sepcon_elim1 {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [Gamma : Provable L]
    [self : GarbageCollectSeparationLogic L Gamma] :
    forall x y : @Language.expr L, |-- ((x * y) ⟶ x) :=
  self.provable_sepcon_elim1

end GarbageCollectSeparationLogic

class SepconDeduction (L : Language.{u}) [SepconLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1_sepcon_comm :
    forall x y : @Language.expr L, (x * y) |-- (y * x)
  derivable1_sepcon_assoc1 :
    forall x y z : @Language.expr L, (x * (y * z)) |-- ((x * y) * z)
  derivable1_sepcon_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      x1 |-- x2 -> y1 |-- y2 -> (x1 * y1) |-- (x2 * y2)

class SepconOrDeduction (L : Language.{u}) [OrLanguage L] [SepconLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1_orp_sepcon_l :
    forall x y z : @Language.expr L, ((x || y) * z) |-- ((x * z) || (y * z))

namespace SepconOrDeduction

theorem orp_sepcon_left {L : Language.{u}} [OrLanguage L] [SepconLanguage L]
    [GammaD1 : Derivable1 L] [self : SepconOrDeduction L GammaD1] :
    forall x y z : @Language.expr L, ((x || y) * z) |-- ((x * z) || (y * z)) :=
  self.derivable1_orp_sepcon_l

end SepconOrDeduction

class SepconFalseDeduction (L : Language.{u}) [FalseLanguage L] [SepconLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1_falsep_sepcon_l :
    forall x : @Language.expr L, (FF * x) |-- FF

namespace SepconFalseDeduction

theorem falsep_sepcon_left {L : Language.{u}} [FalseLanguage L] [SepconLanguage L]
    [GammaD1 : Derivable1 L] [self : SepconFalseDeduction L GammaD1] :
    forall x : @Language.expr L, (FF * x) |-- FF :=
  self.derivable1_falsep_sepcon_l

end SepconFalseDeduction

class EmpDeduction (L : Language.{u}) [SepconLanguage L] [EmpLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1_sepcon_emp_l :
    forall x : @Language.expr L, (x * emp) |-- x
  derivable1_sepcon_emp_r :
    forall x : @Language.expr L, x |-- (x * emp)

namespace EmpDeduction

theorem sepcon_emp_left {L : Language.{u}} [SepconLanguage L] [EmpLanguage L]
    [GammaD1 : Derivable1 L] [self : EmpDeduction L GammaD1] :
    forall x : @Language.expr L, (x * emp) |-- x :=
  self.derivable1_sepcon_emp_l

theorem sepcon_emp_right {L : Language.{u}} [SepconLanguage L] [EmpLanguage L]
    [GammaD1 : Derivable1 L] [self : EmpDeduction L GammaD1] :
    forall x : @Language.expr L, x |-- (x * emp) :=
  self.derivable1_sepcon_emp_r

end EmpDeduction

class WandDeduction (L : Language.{u}) [SepconLanguage L] [WandLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1s_wand_sepcon_adjoint :
    forall x y z : @Language.expr L,
      (x * y) |-- z <-> x |-- (y -* z)

namespace WandDeduction

theorem derivable1_wand_sepcon_adjoint {L : Language.{u}}
    [SepconLanguage L] [WandLanguage L] [GammaD1 : Derivable1 L]
    [self : WandDeduction L GammaD1] :
    forall x y z : @Language.expr L,
      (x * y) |-- z <-> x |-- (y -* z) :=
  self.derivable1s_wand_sepcon_adjoint

end WandDeduction

class ExtSeparationLogicDeduction (L : Language.{u}) [TrueLanguage L]
    [SepconLanguage L] (GammaD1 : Derivable1 L) : Prop where
  derivable1_sepcon_truep_r :
    forall x : @Language.expr L, x |-- (x * TT)

namespace ExtSeparationLogicDeduction

theorem derivable1_sepcon_ext {L : Language.{u}} [TrueLanguage L]
    [SepconLanguage L] [GammaD1 : Derivable1 L]
    [self : ExtSeparationLogicDeduction L GammaD1] :
    forall x : @Language.expr L, x |-- (x * TT) :=
  self.derivable1_sepcon_truep_r

end ExtSeparationLogicDeduction

class NonsplitEmpSeparationLogicDeduction (L : Language.{u}) [AndLanguage L]
    [TrueLanguage L] [SepconLanguage L] [EmpLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1_sepcon_truep_andp_emp_l :
    forall x : @Language.expr L, ((x * TT) && emp) |-- x

namespace NonsplitEmpSeparationLogicDeduction

theorem derivable1_emp_sepcon_truep_elim {L : Language.{u}}
    [AndLanguage L] [TrueLanguage L] [SepconLanguage L] [EmpLanguage L]
    [GammaD1 : Derivable1 L] [self : NonsplitEmpSeparationLogicDeduction L GammaD1] :
    forall x : @Language.expr L, ((x * TT) && emp) |-- x :=
  self.derivable1_sepcon_truep_andp_emp_l

end NonsplitEmpSeparationLogicDeduction

class DupEmpSeparationLogicDeduction (L : Language.{u}) [AndLanguage L]
    [SepconLanguage L] [EmpLanguage L] (GammaD1 : Derivable1 L) : Prop where
  derivable1_emp_dup :
    forall x : @Language.expr L, (x && emp) |-- (x * x)

class GarbageCollectSeparationLogicDeduction (L : Language.{u}) [SepconLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1_sepcon_elim1 :
    forall x y : @Language.expr L, (x * y) |-- x

section SepconRulesD1

variable {L : Language.{u}} [SepconLanguage L]
variable [GammaD1 : Derivable1 L]
variable [BasicDeduction L GammaD1]
variable [SepconDeduction L GammaD1]

theorem derivable1_sepcon_Comm :
    ProofTheoryPatterns.D1.Commutativity L GammaD1 sepcon := by
  constructor
  intro x y
  exact SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x y

theorem derivable1_sepcon_Mono :
    ProofTheoryPatterns.D1.Monotonicity L GammaD1 sepcon := by
  constructor
  intro x1 y1 x2 y2 hx hy
  exact SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
    x1 x2 y1 y2 hx hy

theorem derivable1_sepcon_Assoc :
    ProofTheoryPatterns.D1.Associativity L GammaD1 sepcon := by
  letI : ProofTheoryPatterns.D1.Commutativity L GammaD1 sepcon := derivable1_sepcon_Comm
  letI : ProofTheoryPatterns.D1.Monotonicity L GammaD1 sepcon := derivable1_sepcon_Mono
  exact ProofTheoryPatterns.D1.Build_Associativity1 (prodp := sepcon)
    (fun x y z =>
      SepconDeduction.derivable1_sepcon_assoc1 (GammaD1 := GammaD1) x y z)

theorem derivable1_sepcon_assoc2 :
    forall x y z : @Language.expr L, ((x * y) * z) |-- (x * (y * z)) := by
  intro x y z
  letI : ProofTheoryPatterns.D1.Associativity L GammaD1 sepcon := derivable1_sepcon_Assoc
  exact ProofTheoryPatterns.D1.prodp_assoc2 (prodp := sepcon) x y z

theorem orp_sepcon_right [OrLanguage L] [OrDeduction L GammaD1] :
    forall x y z : @Language.expr L, ((x * z) || (y * z)) |-- ((x || y) * z) := by
  intro x y z
  apply OrDeduction.derivable1_orp_elim
  · exact SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
      x (x || y) z z
      (OrDeduction.derivable1_orp_intros1 (GammaD1 := GammaD1) x y)
      (derivable1_refl z)
  · exact SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
      y (x || y) z z
      (OrDeduction.derivable1_orp_intros2 (GammaD1 := GammaD1) x y)
      (derivable1_refl z)

theorem derivable1_orp_sepcon_r [OrLanguage L] [OrDeduction L GammaD1] :
    forall x y z : @Language.expr L, ((x * z) || (y * z)) |-- ((x || y) * z) :=
  orp_sepcon_right

theorem falsep_sepcon_right [FalseLanguage L] [FalseDeduction L GammaD1] :
    forall x : @Language.expr L, FF |-- (FF * x) := by
  intro x
  exact FalseDeduction.derivable1_falsep_elim (GammaD1 := GammaD1) (FF * x)

theorem derivable1_falsep_sepcon_r [FalseLanguage L] [FalseDeduction L GammaD1] :
    forall x : @Language.expr L, FF |-- (FF * x) :=
  falsep_sepcon_right

section Emp

variable [EmpLanguage L]
variable [EmpDeduction L GammaD1]

theorem derivable1_sepcon_LU :
    ProofTheoryPatterns.D1.LeftUnit L GammaD1 emp sepcon := by
  constructor
  · intro x
    exact derivable1_trans (emp * x) (x * emp) x
      (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) emp x)
      (EmpDeduction.sepcon_emp_left (GammaD1 := GammaD1) x)
  · intro x
    exact derivable1_trans x (x * emp) (emp * x)
      (EmpDeduction.sepcon_emp_right (GammaD1 := GammaD1) x)
      (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x emp)

theorem derivable1_sepcon_RU :
    ProofTheoryPatterns.D1.RightUnit L GammaD1 emp sepcon := by
  constructor
  · intro x
    exact EmpDeduction.sepcon_emp_left (GammaD1 := GammaD1) x
  · intro x
    exact EmpDeduction.sepcon_emp_right (GammaD1 := GammaD1) x

end Emp

variable [GammaE : LogicEquiv L]
variable [EquivDerivable1 L GammaD1 GammaE]
variable [BasicLogicEquiv L GammaE]

theorem sepcon_comm_logic_equiv :
    forall x y : @Language.expr L, logic_equiv (L := L) (x * y) (y * x) := by
  intro x y
  letI : ProofTheoryPatterns.D1.Commutativity L GammaD1 sepcon := derivable1_sepcon_Comm
  exact PropositionalLogic.ProofTheoryPatterns.D1.prodp_comm (prodp := sepcon) x y

theorem __logic_equiv_sepcon_comm :
    forall x y : @Language.expr L, logic_equiv (L := L) (x * y) (y * x) :=
  sepcon_comm_logic_equiv

theorem sepcon_assoc_logic_equiv :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (x * (y * z)) ((x * y) * z) := by
  intro x y z
  letI : ProofTheoryPatterns.D1.Associativity L GammaD1 sepcon := derivable1_sepcon_Assoc
  exact PropositionalLogic.ProofTheoryPatterns.D1.prodp_assoc (prodp := sepcon) x y z

theorem __logic_equiv_sepcon_assoc :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (x * (y * z)) ((x * y) * z) :=
  sepcon_assoc_logic_equiv

section EmpEquiv

variable [EmpLanguage L]
variable [EmpDeduction L GammaD1]

theorem sepcon_emp_logic_equiv :
    forall x : @Language.expr L, logic_equiv (L := L) (x * emp) x := by
  intro x
  letI : ProofTheoryPatterns.D1.RightUnit L GammaD1 emp sepcon := derivable1_sepcon_RU
  exact PropositionalLogic.ProofTheoryPatterns.D1.right_unit (prodp := sepcon) (e := emp) x

theorem provable_sepcon_emp_logic_equiv :
    forall x : @Language.expr L, logic_equiv (L := L) (x * emp) x :=
  sepcon_emp_logic_equiv

theorem emp_sepcon_logic_equiv :
    forall x : @Language.expr L, logic_equiv (L := L) (emp * x) x := by
  intro x
  letI : ProofTheoryPatterns.D1.LeftUnit L GammaD1 emp sepcon := derivable1_sepcon_LU
  exact PropositionalLogic.ProofTheoryPatterns.D1.left_unit (prodp := sepcon) (e := emp) x

end EmpEquiv

variable [OrLanguage L] [FalseLanguage L]
variable [OrDeduction L GammaD1] [FalseDeduction L GammaD1]
variable [SepconOrDeduction L GammaD1]
variable [SepconFalseDeduction L GammaD1]

theorem derivable1_sepcon_orp_l :
    forall x y z : @Language.expr L, (z * (x || y)) |-- ((z * x) || (z * y)) := by
  intro x y z
  have hcomm1 : (z * (x || y)) |-- ((x || y) * z) :=
    SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) z (x || y)
  have hdist : ((x || y) * z) |-- ((x * z) || (y * z)) :=
    SepconOrDeduction.derivable1_orp_sepcon_l (GammaD1 := GammaD1) x y z
  have hcomm2 : ((x * z) || (y * z)) |-- ((z * x) || (z * y)) :=
    derivable1_orp_mono (x * z) (z * x) (y * z) (z * y)
      (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x z)
      (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) y z)
  exact derivable1_trans (z * (x || y)) ((x || y) * z) ((z * x) || (z * y))
    hcomm1
    (derivable1_trans ((x || y) * z) ((x * z) || (y * z))
      ((z * x) || (z * y)) hdist hcomm2)

theorem derivable1_sepcon_orp_r :
    forall x y z : @Language.expr L, ((z * x) || (z * y)) |-- (z * (x || y)) := by
  intro x y z
  apply OrDeduction.derivable1_orp_elim
  · exact SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
      z z x (x || y) (derivable1_refl z)
      (OrDeduction.derivable1_orp_intros1 (GammaD1 := GammaD1) x y)
  · exact SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
      z z y (x || y) (derivable1_refl z)
      (OrDeduction.derivable1_orp_intros2 (GammaD1 := GammaD1) x y)

theorem logic_equiv_sepcon_orp :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (z * (x || y)) ((z * x) || (z * y)) := by
  intro x y z
  exact (__logic_equiv_derivable1 (L := L)
    (z * (x || y)) ((z * x) || (z * y))).mpr
      ⟨derivable1_sepcon_orp_l x y z, derivable1_sepcon_orp_r x y z⟩

theorem logic_equiv_orp_sepcon :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) ((x || y) * z) ((x * z) || (y * z)) := by
  intro x y z
  exact (__logic_equiv_derivable1 (L := L)
    ((x || y) * z) ((x * z) || (y * z))).mpr
      ⟨SepconOrDeduction.derivable1_orp_sepcon_l (GammaD1 := GammaD1) x y z,
        derivable1_orp_sepcon_r x y z⟩

theorem derivable1_sepcon_orp_RDistr :
    ProofTheoryPatterns.D1.RightDistr L GammaD1 sepcon orp := by
  constructor
  · intro x y z
    exact SepconOrDeduction.orp_sepcon_left (GammaD1 := GammaD1) y z x
  · intro x y z
    exact orp_sepcon_right y z x

theorem derivable1_sepcon_orp_LDistr :
    ProofTheoryPatterns.D1.LeftDistr L GammaD1 sepcon orp := by
  letI : ProofTheoryPatterns.D1.Commutativity L GammaD1 sepcon := derivable1_sepcon_Comm
  letI : ProofTheoryPatterns.D1.Monotonicity L GammaD1 orp := derivable1_orp_Mono
  letI : ProofTheoryPatterns.D1.RightDistr L GammaD1 sepcon orp := derivable1_sepcon_orp_RDistr
  exact ProofTheoryPatterns.D1.RightDistr2LeftDistr (prodp := sepcon) (sump := orp)

theorem sepcon_orp_distr_r :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) ((x || y) * z) ((x * z) || (y * z)) := by
  intro x y z
  letI : ProofTheoryPatterns.D1.RightDistr L GammaD1 sepcon orp := derivable1_sepcon_orp_RDistr
  exact PropositionalLogic.ProofTheoryPatterns.D1.prodp_sump_distr_r (prodp := sepcon) (sump := orp) z x y

theorem logic_equiv_orp_sepcon_distr :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) ((x || y) * z) ((x * z) || (y * z)) :=
  sepcon_orp_distr_r

theorem sepcon_orp_distr_l :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (x * (y || z)) ((x * y) || (x * z)) := by
  intro x y z
  letI : ProofTheoryPatterns.D1.LeftDistr L GammaD1 sepcon orp := derivable1_sepcon_orp_LDistr
  exact PropositionalLogic.ProofTheoryPatterns.D1.prodp_sump_distr_l (prodp := sepcon) (sump := orp) x y z

theorem logic_equiv_sepcon_orp_distr :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (x * (y || z)) ((x * y) || (x * z)) :=
  sepcon_orp_distr_l

theorem falsep_sepcon_logic_equiv :
    forall x : @Language.expr L, logic_equiv (L := L) (FF * x) FF := by
  intro x
  exact (__logic_equiv_derivable1 (FF * x) FF).mpr
    ⟨SepconFalseDeduction.falsep_sepcon_left (GammaD1 := GammaD1) x,
      falsep_sepcon_right x⟩

theorem logic_equiv_falsep_sepcon :
    forall x : @Language.expr L, logic_equiv (L := L) (FF * x) FF :=
  falsep_sepcon_logic_equiv

theorem sepcon_falsep_logic_equiv :
    forall x : @Language.expr L, logic_equiv (L := L) (x * FF) FF := by
  intro x
  exact (__logic_equiv_derivable1 (x * FF) FF).mpr
    ⟨derivable1_trans (x * FF) (FF * x) FF
        (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x FF)
        (SepconFalseDeduction.falsep_sepcon_left (GammaD1 := GammaD1) x),
      FalseDeduction.derivable1_falsep_elim (GammaD1 := GammaD1) (x * FF)⟩

theorem logic_equiv_sepcon_falsep :
    forall x : @Language.expr L, logic_equiv (L := L) (x * FF) FF :=
  sepcon_falsep_logic_equiv

end SepconRulesD1

section WandRulesD1

variable {L : Language.{u}} [SepconLanguage L] [WandLanguage L]
variable [GammaD1 : Derivable1 L]
variable [BasicDeduction L GammaD1]
variable [WandDeduction L GammaD1]

theorem derivable1_wand_sepcon_Adj :
    ProofTheoryPatterns.D1.Adjointness L GammaD1 sepcon wand := by
  constructor
  intro x y z
  exact WandDeduction.derivable1_wand_sepcon_adjoint (GammaD1 := GammaD1) x y z

theorem derivable1_wand_sepcon_modus_ponens1 :
    forall x y : @Language.expr L, ((x -* y) * x) |-- y := by
  intro x y
  letI : ProofTheoryPatterns.D1.Adjointness L GammaD1 sepcon wand := derivable1_wand_sepcon_Adj
  exact ProofTheoryPatterns.D1.adjoint_modus_ponens (prodp := sepcon) (funcp := wand) x y

theorem derivable1_wand_elim1 :
    forall x y : @Language.expr L, ((x -* y) * x) |-- y :=
  derivable1_wand_sepcon_modus_ponens1

variable [SepconDeduction L GammaD1]

theorem derivable1_wand_sepcon_modus_ponens2 :
    forall x y : @Language.expr L, (x * (x -* y)) |-- y := by
  intro x y
  exact derivable1_trans (x * (x -* y)) ((x -* y) * x) y
    (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x (x -* y))
    (derivable1_wand_sepcon_modus_ponens1 x y)

theorem derivable1_wand_elim2 :
    forall x y : @Language.expr L, (x * (x -* y)) |-- y :=
  derivable1_wand_sepcon_modus_ponens2

theorem derivable1_wand_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      x2 |-- x1 -> y1 |-- y2 -> (x1 -* y1) |-- (x2 -* y2) := by
  intro x1 x2 y1 y2 hx hy
  letI : ProofTheoryPatterns.D1.Adjointness L GammaD1 sepcon wand := derivable1_wand_sepcon_Adj
  letI : ProofTheoryPatterns.D1.Monotonicity L GammaD1 sepcon := derivable1_sepcon_Mono
  exact ProofTheoryPatterns.D1.funcp_mono (prodp := sepcon) (funcp := wand)
    x1 y1 x2 y2 hx hy

variable [AndLanguage L] [OrLanguage L]
variable [GammaE : LogicEquiv L]
variable [EquivDerivable1 L GammaD1 GammaE]
variable [BasicLogicEquiv L GammaE]
variable [AndDeduction L GammaD1] [OrDeduction L GammaD1]
variable [SepconOrDeduction L GammaD1]

theorem logic_equiv_wand :
    forall x y x' y' : @Language.expr L,
      logic_equiv (L := L) x x' ->
      logic_equiv (L := L) y y' ->
      logic_equiv (L := L) (x -* y) (x' -* y') := by
  intro x y x' y' hx hy
  have hxD := (__logic_equiv_derivable1 (L := L) x x').mp hx
  have hyD := (__logic_equiv_derivable1 (L := L) y y').mp hy
  exact (__logic_equiv_derivable1 (L := L) (x -* y) (x' -* y')).mpr
    ⟨derivable1_wand_mono x x' y y' hxD.right hyD.left,
      derivable1_wand_mono x' x y' y hxD.left hyD.right⟩

theorem wand_andp_logic_equiv :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (x -* (y && z)) ((x -* y) && (x -* z)) := by
  intro x y z
  letI : ProofTheoryPatterns.D1.Adjointness L GammaD1 sepcon wand := derivable1_wand_sepcon_Adj
  exact PropositionalLogic.ProofTheoryPatterns.D1.funcp_andp_distr_r (prodp := sepcon) (funcp := wand) x y z

theorem logic_equiv_provable_wand_andp :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (x -* (y && z)) ((x -* y) && (x -* z)) :=
  wand_andp_logic_equiv

theorem orp_wand_logic_equiv :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) ((x || y) -* z) ((x -* z) && (y -* z)) := by
  intro x y z
  letI : ProofTheoryPatterns.D1.Adjointness L GammaD1 sepcon wand := derivable1_wand_sepcon_Adj
  letI : ProofTheoryPatterns.D1.Commutativity L GammaD1 sepcon := derivable1_sepcon_Comm
  exact PropositionalLogic.ProofTheoryPatterns.D1.orp_funcp (prodp := sepcon) (funcp := wand) x y z

theorem logic_equiv_provable_wand_orp :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) ((x || y) -* z) ((x -* z) && (y -* z)) :=
  orp_wand_logic_equiv

theorem derivable1_sepcon_elim2
    [GarbageCollectSeparationLogicDeduction L GammaD1] :
    forall x y : @Language.expr L, (x * y) |-- y := by
  intro x y
  exact derivable1_trans (x * y) (y * x) y
    (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x y)
    (GarbageCollectSeparationLogicDeduction.derivable1_sepcon_elim1
      (GammaD1 := GammaD1) y x)

theorem derivable1_emp_sepcon_elim1 [TrueLanguage L] [EmpLanguage L]
    [TrueDeduction L GammaD1] [EmpDeduction L GammaD1]
    [NonsplitEmpSeparationLogicDeduction L GammaD1] :
    forall x y : @Language.expr L, (((x * y) && emp) |-- x) := by
  intro x y
  let s : @Language.expr L := (x * y) && emp
  have hsep : s |-- (x * TT) := by
    exact derivable1_trans s (x * y) (x * TT)
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) (x * y) emp)
      (SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
        x x y TT (derivable1_refl x)
        (TrueDeduction.derivable1_truep_intros (GammaD1 := GammaD1) y))
  have hemp : s |-- emp :=
    AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (x * y) emp
  have hpack : s |-- ((x * TT) && emp) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
      s (x * TT) emp hsep hemp
  exact derivable1_trans s ((x * TT) && emp) x hpack
    (NonsplitEmpSeparationLogicDeduction.derivable1_emp_sepcon_truep_elim
      (GammaD1 := GammaD1) x)

theorem derivable1_provable_sepcon_andp_emp_derives [TrueLanguage L] [EmpLanguage L]
    [TrueDeduction L GammaD1] [EmpDeduction L GammaD1]
    [NonsplitEmpSeparationLogicDeduction L GammaD1] :
    forall x y : @Language.expr L, (((x * y) && emp) |-- x) :=
  derivable1_emp_sepcon_elim1

theorem derivable1_emp_sepcon_elim2 [TrueLanguage L] [EmpLanguage L]
    [TrueDeduction L GammaD1] [EmpDeduction L GammaD1]
    [NonsplitEmpSeparationLogicDeduction L GammaD1] :
    forall x y : @Language.expr L, (((x * y) && emp) |-- y) := by
  intro x y
  let s : @Language.expr L := (x * y) && emp
  have hsep : s |-- (y * TT) := by
    exact derivable1_trans s (x * y) (y * TT)
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) (x * y) emp)
      (derivable1_trans (x * y) (y * x) (y * TT)
        (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x y)
        (SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
          y y x TT (derivable1_refl y)
          (TrueDeduction.derivable1_truep_intros (GammaD1 := GammaD1) x)))
  have hemp : s |-- emp :=
    AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (x * y) emp
  have hpack : s |-- ((y * TT) && emp) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
      s (y * TT) emp hsep hemp
  exact derivable1_trans s ((y * TT) && emp) y hpack
    (NonsplitEmpSeparationLogicDeduction.derivable1_emp_sepcon_truep_elim
      (GammaD1 := GammaD1) y)

theorem derivable1_provable_emp_sepcon_elim2 [TrueLanguage L] [EmpLanguage L]
    [TrueDeduction L GammaD1] [EmpDeduction L GammaD1]
    [NonsplitEmpSeparationLogicDeduction L GammaD1] :
    forall x y : @Language.expr L, (((x * y) && emp) |-- y) :=
  derivable1_emp_sepcon_elim2

theorem derivable1s_emp_l_unfold [EmpLanguage L] [EmpDeduction L GammaD1] :
    forall x y : @Language.expr L, emp |-- y -> x |-- (x * y) := by
  intro x y hy
  have hleft := (__logic_equiv_derivable1 (L := L) (emp * x) x).mp
    (emp_sepcon_logic_equiv x)
  have hmono : (emp * x) |-- (y * x) :=
    SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
      emp y x x hy (derivable1_refl x)
  exact derivable1_trans x (emp * x) (x * y) hleft.right
    (derivable1_trans (emp * x) (y * x) (x * y) hmono
      (SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) y x))

theorem derivable1s_emp_sepcon_unfold [EmpLanguage L] [EmpDeduction L GammaD1] :
    forall x y z : @Language.expr L, x |-- z -> emp |-- y -> x |-- (z * y) := by
  intro x y z hxz hy
  exact derivable1_trans x z (z * y) hxz (derivable1s_emp_l_unfold z y hy)

end WandRulesD1

section Axiomatization2Deduction

variable {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
variable [GammaP : Provable L] [GammaD1 : Derivable1 L]
variable [Derivable1Provable L GammaP GammaD1]
variable [MinimumAxiomatization L GammaP]
variable [SepconAxiomatization L GammaP]

theorem Axiomatization2Deduction_sepconD :
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

theorem Axiomatization2Deduction_wandD [WandLanguage L]
    [WandAxiomatization L GammaP] :
    WandDeduction L GammaD1 := by
  constructor
  intro x y z
  constructor
  · intro h
    have hP : |-- ((x * y) ⟶ z) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * y) z).mp h
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (y -* z)).mpr
        ((WandAxiomatization.wand_sepcon_adjoint (Gamma := GammaP) x y z).mp hP)
  · intro h
    have hP : |-- (x ⟶ (y -* z)) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (y -* z)).mp h
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * y) z).mpr
        ((WandAxiomatization.wand_sepcon_adjoint (Gamma := GammaP) x y z).mpr hP)

theorem Axiomatization2Deduction_empD [EmpLanguage L]
    [EmpAxiomatization L GammaP] :
    EmpDeduction L GammaD1 := by
  constructor
  · intro x
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x * emp) x).mpr
        (EmpAxiomatization.sepcon_emp1 (Gamma := GammaP) x)
  · intro x
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (x * emp)).mpr
        (EmpAxiomatization.sepcon_emp2 (Gamma := GammaP) x)

end Axiomatization2Deduction

section SepconRulesP

variable {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [SepconAxiomatization L Gamma]

theorem sepcon_Comm :
    ProofTheoryPatterns.P.Commutativity L Gamma sepcon := by
  constructor
  intro x y
  exact SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x y

theorem sepcon_Mono :
    ProofTheoryPatterns.P.Monotonicity L Gamma sepcon := by
  constructor
  intro x1 y1 x2 y2 hx hy
  exact SepconAxiomatization.sepcon_mono (Gamma := Gamma)
    x1 x2 y1 y2 hx hy

theorem sepcon_Assoc :
    ProofTheoryPatterns.P.Associativity L Gamma sepcon := by
  letI : ProofTheoryPatterns.P.Commutativity L Gamma sepcon := sepcon_Comm
  letI : ProofTheoryPatterns.P.Monotonicity L Gamma sepcon := sepcon_Mono
  exact ProofTheoryPatterns.P.Build_Associativity1 (prodp := sepcon)
    (fun x y z => SepconAxiomatization.sepcon_assoc1 (Gamma := Gamma) x y z)

theorem sepcon_assoc2 :
    forall x y z : @Language.expr L, |-- (((x * y) * z) ⟶ (x * (y * z))) := by
  intro x y z
  letI : ProofTheoryPatterns.P.Associativity L Gamma sepcon := sepcon_Assoc
  exact ProofTheoryPatterns.P.prodp_assoc2 (prodp := sepcon) x y z

theorem provable_sepcon_assoc2 :
    forall x y z : @Language.expr L, |-- (((x * y) * z) ⟶ (x * (y * z))) :=
  sepcon_assoc2

variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]

theorem sepcon_comm :
    forall x y : @Language.expr L, |-- ((x * y) ⟷ (y * x)) := by
  intro x y
  letI : ProofTheoryPatterns.P.Commutativity L Gamma sepcon := sepcon_Comm
  exact PropositionalLogic.ProofTheoryPatterns.P.prodp_comm (prodp := sepcon) x y

theorem provable_sepcon_impp_comm :
    forall x y : @Language.expr L, |-- ((x * y) ⟷ (y * x)) :=
  sepcon_comm

theorem sepcon_assoc :
    forall x y z : @Language.expr L, |-- ((x * (y * z)) ⟷ ((x * y) * z)) := by
  intro x y z
  letI : ProofTheoryPatterns.P.Associativity L Gamma sepcon := sepcon_Assoc
  exact PropositionalLogic.ProofTheoryPatterns.P.prodp_assoc (prodp := sepcon) x y z

theorem provable_sepcon_assoc :
    forall x y z : @Language.expr L, |-- ((x * (y * z)) ⟷ ((x * y) * z)) :=
  sepcon_assoc

theorem impp_orp_sepcon :
    forall x y z : @Language.expr L,
      |-- (((x * z) || (y * z)) ⟶ ((x || y) * z)) := by
  intro x y z
  exact provables_orp_impp_fold (x * z) (y * z) ((x || y) * z)
    (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      x (x || y) z z (OrAxiomatization.provable_orp_intros1 x y)
      (provable_impp_refl z))
    (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      y (x || y) z z (OrAxiomatization.provable_orp_intros2 x y)
      (provable_impp_refl z))

theorem provable_derives_orp_sepcon :
    forall x y z : @Language.expr L,
      |-- (((x * z) || (y * z)) ⟶ ((x || y) * z)) :=
  impp_orp_sepcon

theorem impp_falsep_sepcon :
    forall x : @Language.expr L, |-- (FF ⟶ (FF * x)) := by
  intro x
  exact FalseAxiomatization.provable_falsep_elim (Gamma := Gamma) (FF * x)

theorem provable_derives_falsep_sepcon :
    forall x : @Language.expr L, |-- (FF ⟶ (FF * x)) :=
  impp_falsep_sepcon

variable [SepconOrAxiomatization L Gamma]
variable [SepconFalseAxiomatization L Gamma]

theorem sepcon_orp_RDistr :
    ProofTheoryPatterns.P.RightDistr L Gamma sepcon orp := by
  constructor
  · intro x y z
    exact SepconOrAxiomatization.orp_sepcon_impp (Gamma := Gamma) y z x
  · intro x y z
    exact impp_orp_sepcon y z x

theorem sepcon_orp_LDistr :
    ProofTheoryPatterns.P.LeftDistr L Gamma sepcon orp := by
  letI : ProofTheoryPatterns.P.Commutativity L Gamma sepcon := sepcon_Comm
  letI : ProofTheoryPatterns.P.Monotonicity L Gamma orp := orp_Mono
  letI : ProofTheoryPatterns.P.RightDistr L Gamma sepcon orp := sepcon_orp_RDistr
  exact ProofTheoryPatterns.P.RightDistr2LeftDistr (prodp := sepcon) (sump := orp)

theorem sepcon_orp_distr_r_iffp :
    forall x y z : @Language.expr L,
      |-- (((x || y) * z) ⟷ ((x * z) || (y * z))) := by
  intro x y z
  letI : ProofTheoryPatterns.P.RightDistr L Gamma sepcon orp := sepcon_orp_RDistr
  exact PropositionalLogic.ProofTheoryPatterns.P.prodp_sump_distr_r (prodp := sepcon) (sump := orp) z x y

theorem provable_orp_sepcon :
    forall x y z : @Language.expr L,
      |-- (((x || y) * z) ⟷ ((x * z) || (y * z))) :=
  sepcon_orp_distr_r_iffp

theorem sepcon_orp_distr_l_iffp :
    forall x y z : @Language.expr L,
      |-- ((x * (y || z)) ⟷ ((x * y) || (x * z))) := by
  intro x y z
  letI : ProofTheoryPatterns.P.LeftDistr L Gamma sepcon orp := sepcon_orp_LDistr
  exact PropositionalLogic.ProofTheoryPatterns.P.prodp_sump_distr_l (prodp := sepcon) (sump := orp) x y z

theorem provable_sepcon_orp :
    forall x y z : @Language.expr L,
      |-- ((x * (y || z)) ⟷ ((x * y) || (x * z))) :=
  sepcon_orp_distr_l_iffp

theorem falsep_sepcon :
    forall x : @Language.expr L, |-- ((FF * x) ⟷ FF) := by
  intro x
  exact provables_iffp_intros (FF * x) FF
    (SepconFalseAxiomatization.falsep_sepcon_impp (Gamma := Gamma) x)
    (impp_falsep_sepcon x)

theorem provable_falsep_sepcon :
    forall x : @Language.expr L, |-- ((FF * x) ⟷ FF) :=
  falsep_sepcon

theorem sepcon_falsep :
    forall x : @Language.expr L, |-- ((x * FF) ⟷ FF) := by
  intro x
  exact provables_iffp_intros (x * FF) FF
    (solve_impp_trans (x * FF) (FF * x) FF
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x FF)
      (SepconFalseAxiomatization.falsep_sepcon_impp (Gamma := Gamma) x))
    (FalseAxiomatization.provable_falsep_elim (Gamma := Gamma) (x * FF))

theorem provable_sepcon_falsep :
    forall x : @Language.expr L, |-- ((x * FF) ⟷ FF) :=
  sepcon_falsep

variable [EmpLanguage L]
variable [EmpAxiomatization L Gamma]

theorem sepcon_emp :
    forall x : @Language.expr L, |-- ((x * emp) ⟷ x) := by
  intro x
  exact provables_iffp_intros (x * emp) x
    (EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) x)
    (EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) x)

theorem provable_sepcon_emp :
    forall x : @Language.expr L, |-- ((x * emp) ⟷ x) :=
  sepcon_emp

theorem sepcon_LU :
    ProofTheoryPatterns.P.LeftUnit L Gamma emp sepcon := by
  constructor
  · intro x
    exact solve_impp_trans (emp * x) (x * emp) x
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) emp x)
      (EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) x)
  · intro x
    exact solve_impp_trans x (x * emp) (emp * x)
      (EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) x)
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x emp)

theorem sepcon_RU :
    ProofTheoryPatterns.P.RightUnit L Gamma emp sepcon := by
  constructor
  · intro x
    exact EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) x
  · intro x
    exact EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) x

theorem cancel_ready :
    forall x y : @Language.expr L, (|-- ((x * emp) ⟶ y)) -> |-- (x ⟶ y) := by
  intro x y h
  exact solve_impp_trans x (x * emp) y
    (EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) x) h

theorem provables_emp_sepcon_unfold :
    forall x y : @Language.expr L, (|-- ((x * emp) ⟶ y)) -> |-- (x ⟶ y) :=
  cancel_ready

theorem cancel_one_succeed :
    forall u x y z : @Language.expr L,
      (|-- ((x * y) ⟶ z)) -> |-- ((((u * x) * y) ⟶ (u * z))) := by
  intro u x y z h
  exact solve_impp_trans ((u * x) * y) (u * (x * y)) (u * z)
    (sepcon_assoc2 u x y)
    (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      u u (x * y) z (provable_impp_refl u) h)

theorem provables_sepcon_impp_unfold :
    forall u x y z : @Language.expr L,
      (|-- ((x * y) ⟶ z)) -> |-- ((((u * x) * y) ⟶ (u * z))) :=
  cancel_one_succeed

theorem cancel_one_giveup :
    forall x y z w v : @Language.expr L,
      (|-- ((x * (y * z)) ⟶ (w * v))) ->
        |-- ((((y * x) * z) ⟶ (w * v))) := by
  intro x y z w v h
  have hmono : |-- (((y * x) * z) ⟶ ((x * y) * z)) :=
    SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      (y * x) (x * y) z z
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) y x)
      (provable_impp_refl z)
  exact solve_impp_trans ((y * x) * z) ((x * y) * z) (w * v) hmono
    (solve_impp_trans ((x * y) * z) (x * (y * z)) (w * v)
      (sepcon_assoc2 x y z) h)

theorem provables_sepcon_sepcon_unfold :
    forall x y z w v : @Language.expr L,
      (|-- ((x * (y * z)) ⟶ (w * v))) ->
        |-- ((((y * x) * z) ⟶ (w * v))) :=
  cancel_one_giveup

theorem cancel_rev :
    forall x y z w : @Language.expr L,
      (|-- (((y * x) * z) ⟶ w)) -> |-- ((x * (y * z)) ⟶ w) := by
  intro x y z w h
  have hmono : |-- (((x * y) * z) ⟶ ((y * x) * z)) :=
    SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      (x * y) (y * x) z z
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x y)
      (provable_impp_refl z)
  exact solve_impp_trans (x * (y * z)) ((x * y) * z) w
    (SepconAxiomatization.sepcon_assoc1 (Gamma := Gamma) x y z)
    (solve_impp_trans ((x * y) * z) ((y * x) * z) w hmono h)

theorem provables_sepcon_assoc :
    forall x y z w : @Language.expr L,
      (|-- (((y * x) * z) ⟶ w)) -> |-- ((x * (y * z)) ⟶ w) :=
  cancel_rev

theorem cancel_finish :
    forall x : @Language.expr L, |-- ((x * emp) ⟶ x) := by
  intro x
  exact EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) x

end SepconRulesP

section WandRulesP

variable {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L] [WandLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [WandAxiomatization L Gamma]

theorem wand_sepcon_Adj :
    ProofTheoryPatterns.P.Adjointness L Gamma sepcon wand := by
  constructor
  intro x y z
  exact WandAxiomatization.wand_sepcon_adjoint (Gamma := Gamma) x y z

theorem provable_wand_sepcon_modus_ponens1 :
    forall x y : @Language.expr L, |-- (((x -* y) * x) ⟶ y) := by
  intro x y
  letI : ProofTheoryPatterns.P.Adjointness L Gamma sepcon wand := wand_sepcon_Adj
  exact ProofTheoryPatterns.P.adjoint_modus_ponens (prodp := sepcon) (funcp := wand) x y

theorem provable_wand_elim1 :
    forall x y : @Language.expr L, |-- (((x -* y) * x) ⟶ y) :=
  provable_wand_sepcon_modus_ponens1

variable [SepconAxiomatization L Gamma]

theorem provable_wand_sepcon_modus_ponens2 :
    forall x y : @Language.expr L, |-- ((x * (x -* y)) ⟶ y) := by
  intro x y
  exact solve_impp_trans (x * (x -* y)) ((x -* y) * x) y
    (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x (x -* y))
    (provable_wand_sepcon_modus_ponens1 x y)

theorem provable_wand_elim2 :
    forall x y : @Language.expr L, |-- ((x * (x -* y)) ⟶ y) :=
  provable_wand_sepcon_modus_ponens2

theorem wand_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      (|-- (x2 ⟶ x1)) -> (|-- (y1 ⟶ y2)) ->
        |-- ((x1 -* y1) ⟶ (x2 -* y2)) := by
  intro x1 x2 y1 y2 hx hy
  letI : ProofTheoryPatterns.P.Adjointness L Gamma sepcon wand := wand_sepcon_Adj
  letI : ProofTheoryPatterns.P.Monotonicity L Gamma sepcon := sepcon_Mono
  exact ProofTheoryPatterns.P.funcp_mono (prodp := sepcon) (funcp := wand)
    x1 y1 x2 y2 hx hy

theorem provables_wand_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      (|-- (x2 ⟶ x1)) -> (|-- (y1 ⟶ y2)) ->
        |-- ((x1 -* y1) ⟶ (x2 -* y2)) :=
  wand_mono

variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]
variable [SepconOrAxiomatization L Gamma]
variable [SepconFalseAxiomatization L Gamma]

theorem wand_andp :
    forall x y z : @Language.expr L,
      |-- ((x -* (y && z)) ⟷ ((x -* y) && (x -* z))) := by
  intro x y z
  letI : ProofTheoryPatterns.P.Adjointness L Gamma sepcon wand := wand_sepcon_Adj
  exact PropositionalLogic.ProofTheoryPatterns.P.funcp_andp_distr_r (prodp := sepcon) (funcp := wand) x y z

theorem provable_wand_andp :
    forall x y z : @Language.expr L,
      |-- ((x -* (y && z)) ⟷ ((x -* y) && (x -* z))) :=
  wand_andp

theorem orp_wand :
    forall x y z : @Language.expr L,
      |-- (((x || y) -* z) ⟷ ((x -* z) && (y -* z))) := by
  intro x y z
  letI : ProofTheoryPatterns.P.Adjointness L Gamma sepcon wand := wand_sepcon_Adj
  letI : ProofTheoryPatterns.P.Commutativity L Gamma sepcon := sepcon_Comm
  exact PropositionalLogic.ProofTheoryPatterns.P.orp_funcp (prodp := sepcon) (funcp := wand) x y z

theorem provable_wand_orp :
    forall x y z : @Language.expr L,
      |-- (((x || y) -* z) ⟷ ((x -* z) && (y -* z))) :=
  orp_wand

theorem sepcon_elim2 [GarbageCollectSeparationLogic L Gamma] :
    forall x y : @Language.expr L, |-- ((x * y) ⟶ y) := by
  intro x y
  exact solve_impp_trans (x * y) (y * x) y
    (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x y)
    (GarbageCollectSeparationLogic.sepcon_elim1 (Gamma := Gamma) y x)

theorem provable_sepcon_elim2 [GarbageCollectSeparationLogic L Gamma] :
    forall x y : @Language.expr L, |-- ((x * y) ⟶ y) :=
  sepcon_elim2

theorem emp_sepcon_elim1 [EmpLanguage L] [EmpAxiomatization L Gamma]
    [NonsplitEmpSeparationLogic L Gamma] :
    forall x y : @Language.expr L, |-- ((((x * y) && emp) ⟶ x)) := by
  intro x y
  let s : @Language.expr L := (x * y) && emp
  have htoTT : |-- (y ⟶ TT) :=
    provables_impp_elim y TT provable_truep
  have hsep : |-- (s ⟶ (x * TT)) := by
    exact solve_impp_trans s (x * y) (x * TT)
      (AndAxiomatization.provable_andp_elim1 (x * y) emp)
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        x x y TT (provable_impp_refl x) htoTT)
  have hemp : |-- (s ⟶ emp) :=
    AndAxiomatization.provable_andp_elim2 (x * y) emp
  have hpack : |-- (s ⟶ ((x * TT) && emp)) :=
    provables_impp_andp_fold s (x * TT) emp hsep hemp
  exact solve_impp_trans s ((x * TT) && emp) x hpack
    (NonsplitEmpSeparationLogic.emp_sepcon_truep_elim (Gamma := Gamma) x)

theorem provable_sepcon_andp_emp_derives [EmpLanguage L] [EmpAxiomatization L Gamma]
    [NonsplitEmpSeparationLogic L Gamma] :
    forall x y : @Language.expr L, |-- ((((x * y) && emp) ⟶ x)) :=
  emp_sepcon_elim1

theorem emp_sepcon_elim2 [EmpLanguage L] [EmpAxiomatization L Gamma]
    [NonsplitEmpSeparationLogic L Gamma] :
    forall x y : @Language.expr L, |-- ((((x * y) && emp) ⟶ y)) := by
  intro x y
  let s : @Language.expr L := (x * y) && emp
  have htoTT : |-- (x ⟶ TT) :=
    provables_impp_elim x TT provable_truep
  have hsep : |-- (s ⟶ (y * TT)) := by
    exact solve_impp_trans s (x * y) (y * TT)
      (AndAxiomatization.provable_andp_elim1 (x * y) emp)
      (solve_impp_trans (x * y) (y * x) (y * TT)
        (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x y)
        (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
          y y x TT (provable_impp_refl y) htoTT))
  have hemp : |-- (s ⟶ emp) :=
    AndAxiomatization.provable_andp_elim2 (x * y) emp
  have hpack : |-- (s ⟶ ((y * TT) && emp)) :=
    provables_impp_andp_fold s (y * TT) emp hsep hemp
  exact solve_impp_trans s ((y * TT) && emp) y hpack
    (NonsplitEmpSeparationLogic.emp_sepcon_truep_elim (Gamma := Gamma) y)

theorem provable_emp_sepcon_elim2 [EmpLanguage L] [EmpAxiomatization L Gamma]
    [NonsplitEmpSeparationLogic L Gamma] :
    forall x y : @Language.expr L, |-- ((((x * y) && emp) ⟶ y)) :=
  emp_sepcon_elim2

end WandRulesP

end Unifysl
