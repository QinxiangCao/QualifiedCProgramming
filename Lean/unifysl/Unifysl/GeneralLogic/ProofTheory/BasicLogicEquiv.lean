import Unifysl.GeneralLogic.ProofTheory.BasicDeduction

/-!
Coq inventory from `GeneralLogic/ProofTheory/BasicLogicEquiv.v`:
- Class `BasicLogicEquiv` with fields `logic_equiv_refl`,
  `logic_equiv_symm`, `logic_equiv_trans`.
- Class `EquivDerivable1` with field `__logic_equiv_derivable1`
  in the 8.20 branch.
- Lemma `Deduction2Equiv_bE`.
- Rewrite/proper support: `logic_equiv_impp_rewrite`,
  `logic_equiv_refl_instance`, `logic_equiv_symm_instance`,
  `logic_equiv_trans_instance`, `logic_equiv_trans_equiv`,
  `logic_equiv_proper_logic_equiv`, `logic_equiv_proper_derivable1`.
-/

universe u

namespace Unifysl

open Relation_ext

class BasicLogicEquiv (L : Language.{u}) (Gamma : LogicEquiv L) : Prop where
  logic_equiv_refl : forall x : @Language.expr L, Gamma.logic_equiv x x
  logic_equiv_symm :
    forall x y : @Language.expr L,
      Gamma.logic_equiv x y -> Gamma.logic_equiv y x
  logic_equiv_trans :
    forall x y z : @Language.expr L,
      Gamma.logic_equiv x y -> Gamma.logic_equiv y z -> Gamma.logic_equiv x z

class EquivDerivable1 (L : Language.{u}) (GammaD : Derivable1 L)
    (GammaE : LogicEquiv L) : Prop where
  __logic_equiv_derivable1 :
    forall x y : @Language.expr L,
      GammaE.logic_equiv x y <-> GammaD.derivable1 x y /\ GammaD.derivable1 y x

theorem logic_equiv_refl {L : Language.{u}} [Gamma : LogicEquiv L]
    [bE : BasicLogicEquiv L Gamma] (x : @Language.expr L) :
    logic_equiv (L := L) x x :=
  bE.logic_equiv_refl x

theorem logic_equiv_symm {L : Language.{u}} [Gamma : LogicEquiv L]
    [bE : BasicLogicEquiv L Gamma] (x y : @Language.expr L) :
    logic_equiv (L := L) x y -> logic_equiv (L := L) y x :=
  bE.logic_equiv_symm x y

theorem logic_equiv_trans {L : Language.{u}} [Gamma : LogicEquiv L]
    [bE : BasicLogicEquiv L Gamma] (x y z : @Language.expr L) :
    logic_equiv (L := L) x y -> logic_equiv (L := L) y z ->
      logic_equiv (L := L) x z :=
  bE.logic_equiv_trans x y z

theorem __logic_equiv_derivable1 {L : Language.{u}} [GammaD : Derivable1 L]
    [GammaE : LogicEquiv L] [GammaED1 : EquivDerivable1 L GammaD GammaE]
    (x y : @Language.expr L) :
    logic_equiv (L := L) x y <->
      derivable1 (L := L) x y /\ derivable1 (L := L) y x :=
  GammaED1.__logic_equiv_derivable1 x y

theorem Deduction2Equiv_bE {L : Language.{u}} [GammaD : Derivable1 L]
    [GammaE : LogicEquiv L] [GammaED1 : EquivDerivable1 L GammaD GammaE]
    [bD : BasicDeduction L GammaD] : BasicLogicEquiv L GammaE where
  logic_equiv_refl := by
    intro x
    exact (__logic_equiv_derivable1 x x).mpr
      ⟨derivable1_refl x, derivable1_refl x⟩
  logic_equiv_symm := by
    intro x y hxy
    exact (__logic_equiv_derivable1 y x).mpr
      ⟨((__logic_equiv_derivable1 x y).mp hxy).right,
        ((__logic_equiv_derivable1 x y).mp hxy).left⟩
  logic_equiv_trans := by
    intro x y z hxy hyz
    have hxyD := (__logic_equiv_derivable1 x y).mp hxy
    have hyzD := (__logic_equiv_derivable1 y z).mp hyz
    exact (__logic_equiv_derivable1 x z).mpr
      ⟨derivable1_trans x y z hxyD.left hyzD.left,
        derivable1_trans z y x hyzD.right hxyD.right⟩

section RewriteClass

variable {L : Language.{u}} [GammaE : LogicEquiv L] [bE : BasicLogicEquiv L GammaE]

instance logic_equiv_impp_rewrite : RewriteRelation (logic_equiv (L := L)) where

instance logic_equiv_refl_instance : Reflexive (logic_equiv (L := L)) := by
  intro x
  exact logic_equiv_refl x

instance logic_equiv_symm_instance : Symmetric (logic_equiv (L := L)) := by
  intro x y hxy
  exact logic_equiv_symm x y hxy

instance logic_equiv_trans_instance : Transitive (logic_equiv (L := L)) := by
  intro x y z hxy hyz
  exact logic_equiv_trans x y z hxy hyz

instance logic_equiv_trans_equiv : Equivalence (logic_equiv (L := L)) where
  refl := logic_equiv_refl_instance
  symm := by
    intro x y hxy
    exact logic_equiv_symm x y hxy
  trans := by
    intro x y z hxy hyz
    exact logic_equiv_trans x y z hxy hyz

instance logic_equiv_proper_logic_equiv :
    Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> implRel)
      (logic_equiv (L := L)) where
  proper := by
    intro x1 x2 hx y1 y2 hy hxy
    exact logic_equiv_trans x2 y1 y2
      (logic_equiv_trans x2 x1 y1 (logic_equiv_symm x1 x2 hx) hxy) hy

instance logic_equiv_proper_derivable1
    [GammaD1 : Derivable1 L] [GammaED1 : EquivDerivable1 L GammaD1 GammaE]
    [bD : BasicDeduction L GammaD1] :
    Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> implRel)
      (derivable1 (L := L)) where
  proper := by
    intro x1 x2 hx y1 y2 hy hxy
    have hxDer := (__logic_equiv_derivable1 x1 x2).mp hx
    have hyDer := (__logic_equiv_derivable1 y1 y2).mp hy
    exact derivable1_trans x2 y1 y2
      (derivable1_trans x2 x1 y1 hxDer.right hxy) hyDer.left

end RewriteClass

end Unifysl
