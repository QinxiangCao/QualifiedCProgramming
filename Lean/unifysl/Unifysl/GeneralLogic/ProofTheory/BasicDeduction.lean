import Unifysl.GeneralLogic.Base

/-!
Coq inventory from `GeneralLogic/ProofTheory/BasicDeduction.v`:
- Class `BasicDeduction` with fields `derivable1_refl`, `derivable1_trans`.
- Rewrite/proper support: `Derivable_impp_rewrite`,
  `derivable1_refl_instance`, `derivable1_trans_instance`,
  `derivable1_proper_derivable1`.
- Coq rewrite smoke test is represented by `TestRewriteClass.test_rewrite_class`.
-/

universe u

namespace Unifysl

open Relation_ext

class BasicDeduction (L : Language.{u}) (Gamma : Derivable1 L) : Prop where
  derivable1_refl : forall x : @Language.expr L, Gamma.derivable1 x x
  derivable1_trans :
    forall x y z : @Language.expr L,
      Gamma.derivable1 x y -> Gamma.derivable1 y z -> Gamma.derivable1 x z

theorem derivable1_refl {L : Language.{u}} [Gamma : Derivable1 L]
    [BD : BasicDeduction L Gamma] (x : @Language.expr L) : x |-- x :=
  BD.derivable1_refl x

theorem derivable1_trans {L : Language.{u}} [Gamma : Derivable1 L]
    [BD : BasicDeduction L Gamma] (x y z : @Language.expr L) :
    x |-- y -> y |-- z -> x |-- z :=
  BD.derivable1_trans x y z

class RewriteRelation {A : Sort u} (R : A -> A -> Prop) : Prop where

def flipRel {A : Sort u} (R : A -> A -> Prop) : A -> A -> Prop :=
  fun x y => R y x

def implRel (P Q : Prop) : Prop :=
  P -> Q

section BDRewriteClass

variable {L : Language.{u}} [Gamma : Derivable1 L] [BD : BasicDeduction L Gamma]

instance Derivable_impp_rewrite : RewriteRelation (derivable1 (L := L)) where

instance derivable1_refl_instance : Reflexive (derivable1 (L := L)) := by
  intro x
  exact derivable1_refl x

instance derivable1_trans_instance :
    Transitive (derivable1 (L := L)) := by
  intro x y z hxy hyz
  exact derivable1_trans x y z hxy hyz

instance derivable1_trans_lean_instance :
    Trans (derivable1 (L := L)) (derivable1 (L := L)) (derivable1 (L := L)) where
  trans := by
    intro x y z hxy hyz
    exact derivable1_trans x y z hxy hyz

instance derivable1_proper_derivable1 :
    Proper (flipRel (derivable1 (L := L)) ==> derivable1 (L := L) ==> implRel)
      (derivable1 (L := L)) where
  proper := by
    intro x1 x2 hx y1 y2 hy hxy
    exact derivable1_trans x2 y1 y2 (derivable1_trans x2 x1 y1 hx hxy) hy

end BDRewriteClass

namespace TestRewriteClass

theorem test_rewrite_class {L : Language.{u}} [Gamma : Derivable1 L]
    [BD : BasicDeduction L Gamma] (x1 x2 y1 y2 : @Language.expr L) :
    x1 |-- x2 -> y1 |-- y2 -> x2 |-- y1 -> x1 |-- y2 := by
  intro hx hy hmid
  exact derivable1_trans x1 y1 y2 (derivable1_trans x1 x2 y1 hx hmid) hy

end TestRewriteClass

end Unifysl
