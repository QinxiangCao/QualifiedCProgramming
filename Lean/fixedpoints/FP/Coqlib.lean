import Std

universe u v w x

namespace FP

theorem fold_right_map {A1 : Type u} {B1 : Type v}
    {A2 : Type w} {B2 : Type x}
    (f1 : A1 -> B1 -> B1) (f2 : A2 -> B2 -> B2)
    (gA : A1 -> A2) (gB : B1 -> B2)
    (h : forall a b, gB (f1 a b) = f2 (gA a) (gB b)) :
    forall (l : List A1) (b : B1),
      gB (l.foldr f1 b) = (l.map gA).foldr f2 (gB b) := by
  intro l
  induction l with
  | nil => intro b; rfl
  | cons a l ih =>
      intro b
      simp only [List.foldr, List.map]
      rw [h, ih]

theorem fold_left_map {A1 : Type u} {B1 : Type v}
    {A2 : Type w} {B2 : Type x}
    (f1 : A1 -> B1 -> A1) (f2 : A2 -> B2 -> A2)
    (gA : A1 -> A2) (gB : B1 -> B2)
    (h : forall a b, gA (f1 a b) = f2 (gA a) (gB b)) :
    forall (l : List B1) (a : A1),
      gA (l.foldl f1 a) = (l.map gB).foldl f2 (gA a) := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons b l ih =>
      intro a
      simp only [List.foldl, List.map]
      rw [ih, h]

theorem NoDup_app_iff {A : Type u} (l1 l2 : List A) :
    (l1 ++ l2).Nodup <->
      l1.Nodup /\ l2.Nodup /\ forall x, x ∈ l1 -> x ∈ l2 -> False := by
  rw [List.nodup_append]
  constructor
  · rintro ⟨h1, h2, hdisjoint⟩
    exact ⟨h1, h2, fun x hx1 hx2 => hdisjoint x hx1 x hx2 rfl⟩
  · rintro ⟨h1, h2, hdisjoint⟩
    exact ⟨h1, h2, fun a ha b hb hab => by
      subst b
      exact hdisjoint a ha hb⟩

end FP
