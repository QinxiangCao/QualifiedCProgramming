import Unifysl.Lib.Coqlib
import Unifysl.Lib.Relation_ext

namespace Unifysl

open Relation_ext

instance list_Reflexive {A : Type u} {R : relation A} {EqA : Equivalence R} :
    Reflexive (List.Forall₂ R) := by
  intro x
  induction x with
  | nil =>
      exact List.Forall₂.nil
  | cons a xs ih =>
      exact List.Forall₂.cons (EqA.refl a) ih

instance list_Symmetric {A : Type u} {R : relation A} {EqA : Equivalence R} :
    Symmetric (List.Forall₂ R) := by
  intro x y h
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | cons hxy _ ih =>
      exact List.Forall₂.cons (EqA.symm hxy) ih

instance list_Transitive {A : Type u} {R : relation A} {EqA : Equivalence R} :
    Transitive (List.Forall₂ R) := by
  intro x y z hxy hyz
  induction hxy generalizing z with
  | nil =>
      cases hyz
      exact List.Forall₂.nil
  | cons hxy hxs ih =>
      cases hyz with
      | cons hyz hys =>
          exact List.Forall₂.cons (EqA.trans hxy hyz) (ih _ hys)

instance list_Equivalence {A : Type u} {R : relation A} {EqA : Equivalence R} :
    Equivalence (List.Forall₂ R) where
  refl := @list_Reflexive A R EqA
  symm := by
    intro x y h
    exact @list_Symmetric A R EqA x y h
  trans := by
    intro x y z hxy hyz
    exact @list_Transitive A R EqA x y z hxy hyz

theorem resp_Reflexive {A : Type u} {B : Type v} (f : A -> B) (R : relation B)
    {RR : Reflexive R} :
    Reflexive (respectful_relation f R) := by
  intro x
  exact RR (f x)

theorem resp_Symmetric {A : Type u} {B : Type v} (f : A -> B) (R : relation B)
    {SR : Symmetric R} :
    Symmetric (respectful_relation f R) := by
  intro x y h
  exact SR (f x) (f y) h

theorem resp_Transitive {A : Type u} {B : Type v} (f : A -> B) (R : relation B)
    {TR : Transitive R} :
    Transitive (respectful_relation f R) := by
  intro x y z hxy hyz
  exact TR (f x) (f y) (f z) hxy hyz

theorem resp_Equivalence {A : Type u} {B : Type v} (f : A -> B) (R : relation B)
    {ER : Equivalence R} :
    Equivalence (respectful_relation f R) := by
  constructor
  · intro x
    exact ER.refl (f x)
  · intro x y h
    exact ER.symm h
  · intro x y z hxy hyz
    exact ER.trans hxy hyz

end Unifysl
