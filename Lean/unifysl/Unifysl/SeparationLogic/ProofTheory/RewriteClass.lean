import Unifysl.SeparationLogic.ProofTheory.Deduction

/-!
Coq inventory from `SeparationLogic/ProofTheory/RewriteClass.v`:
- Active exported instances:
  `provables_sepcon_proper_impp`, `provables_wand_proper_impp`,
  `provables_sepcon_proper_iffp`, `provables_wand_proper_iffp`,
  `derivable1s_sepcon_proper`, `derivable1s_wand_proper`,
  `logic_equiv_sepcon_proper`, `logic_equiv_wand_proper`.
- Final `Existing Instances` command re-exports the same eight instances.

Lean note: the Coq relations `fun x y => |-- impp x y` and
`fun x y => |-- iffp x y` are represented here by private relation
aliases with the same semantics.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Unifysl

open Relation_ext
open PropositionalLanguageNotation
open SeparationLogicNotation

section RewriteClass1

variable {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L] [WandLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [SepconAxiomatization L Gamma]
variable [WandAxiomatization L Gamma]

private def provableImppRel : @Language.expr L -> @Language.expr L -> Prop :=
  fun x y => @Provable.provable L Gamma (x ⟶ y)

instance provables_sepcon_proper_impp :
    Proper
      (provableImppRel (L := L) (Gamma := Gamma) ==>
        provableImppRel (L := L) (Gamma := Gamma) ==>
        provableImppRel (L := L) (Gamma := Gamma))
      (fun x y : @Language.expr L => x * y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact SepconAxiomatization.sepcon_mono (Gamma := Gamma) x1 x2 y1 y2 hx hy

instance provables_wand_proper_impp :
    Proper
      (flipRel (provableImppRel (L := L) (Gamma := Gamma)) ==>
        provableImppRel (L := L) (Gamma := Gamma) ==>
        provableImppRel (L := L) (Gamma := Gamma))
      (fun x y : @Language.expr L => x -* y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact wand_mono (Gamma := Gamma) x1 x2 y1 y2 hx hy

variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L]
variable [AndAxiomatization L Gamma]
variable [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma]
variable [TrueAxiomatization L Gamma]

private def provableIffpRel : @Language.expr L -> @Language.expr L -> Prop :=
  fun x y => @Provable.provable L Gamma (x ⟷ y)

instance provables_sepcon_proper_iffp :
    Proper
      (provableIffpRel (L := L) (Gamma := Gamma) ==>
        provableIffpRel (L := L) (Gamma := Gamma) ==>
        provableIffpRel (L := L) (Gamma := Gamma))
      (fun x y : @Language.expr L => x * y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact provables_iffp_intros (x1 * y1) (x2 * y2)
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        x1 x2 y1 y2
        (provables_iffp_elim1 x1 x2 hx)
        (provables_iffp_elim1 y1 y2 hy))
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        x2 x1 y2 y1
        (provables_iffp_elim2 x1 x2 hx)
        (provables_iffp_elim2 y1 y2 hy))

instance provables_wand_proper_iffp :
    Proper
      (provableIffpRel (L := L) (Gamma := Gamma) ==>
        provableIffpRel (L := L) (Gamma := Gamma) ==>
        provableIffpRel (L := L) (Gamma := Gamma))
      (fun x y : @Language.expr L => x -* y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact provables_iffp_intros (x1 -* y1) (x2 -* y2)
      (wand_mono (Gamma := Gamma)
        x1 x2 y1 y2
        (provables_iffp_elim2 x1 x2 hx)
        (provables_iffp_elim1 y1 y2 hy))
      (wand_mono (Gamma := Gamma)
        x2 x1 y2 y1
        (provables_iffp_elim1 x1 x2 hx)
        (provables_iffp_elim2 y1 y2 hy))

end RewriteClass1

section RewriteClass2

variable {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
variable [GammaD : Derivable1 L]
variable [SepconDeduction L GammaD]

instance derivable1s_sepcon_proper :
    Proper (derivable1 (L := L) ==> derivable1 (L := L) ==> derivable1 (L := L))
      (fun x y : @Language.expr L => x * y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD)
      x1 x2 y1 y2 hx hy

variable [WandLanguage L]
variable [WandDeduction L GammaD]
variable [BasicDeduction L GammaD]

instance derivable1s_wand_proper :
    Proper
      (flipRel (derivable1 (L := L)) ==> derivable1 (L := L) ==> derivable1 (L := L))
      (fun x y : @Language.expr L => x -* y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact derivable1_wand_mono (L := L) (GammaD1 := GammaD) x1 x2 y1 y2 hx hy

end RewriteClass2

section RewriteClass3

variable {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
variable [GammaD1 : Derivable1 L]
variable [GammaE : LogicEquiv L]
variable [EquivDerivable1 L GammaD1 GammaE]
variable [SepconDeduction L GammaD1]

instance logic_equiv_sepcon_proper :
    Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
      (fun x y : @Language.expr L => x * y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    have hxD := (__logic_equiv_derivable1 (L := L) x1 x2).mp hx
    have hyD := (__logic_equiv_derivable1 (L := L) y1 y2).mp hy
    exact (__logic_equiv_derivable1 (L := L) (x1 * y1) (x2 * y2)).mpr
      ⟨SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
          x1 x2 y1 y2 hxD.left hyD.left,
        SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
          x2 x1 y2 y1 hxD.right hyD.right⟩

variable [WandLanguage L]
variable [WandDeduction L GammaD1]
variable [BasicDeduction L GammaD1]

instance logic_equiv_wand_proper :
    Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
      (fun x y : @Language.expr L => x -* y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    have hxD := (__logic_equiv_derivable1 (L := L) x1 x2).mp hx
    have hyD := (__logic_equiv_derivable1 (L := L) y1 y2).mp hy
    exact (__logic_equiv_derivable1 (L := L) (x1 -* y1) (x2 -* y2)).mpr
      ⟨derivable1_wand_mono (L := L) (GammaD1 := GammaD1)
          x1 x2 y1 y2 hxD.right hyD.left,
        derivable1_wand_mono (L := L) (GammaD1 := GammaD1)
          x2 x1 y2 y1 hxD.left hyD.right⟩

end RewriteClass3

end Unifysl
