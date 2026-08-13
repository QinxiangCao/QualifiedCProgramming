namespace List

abbrev get? (xs : List α) (i : Nat) : Option α :=
  xs[i]?

inductive Forall (P : α -> Prop) : List α -> Prop where
| nil : Forall P []
| cons {x : α} {xs : List α} : P x -> Forall P xs -> Forall P (x :: xs)

inductive Forall₂ (P : α -> β -> Prop) : List α -> List β -> Prop where
| nil : Forall₂ P [] []
| cons {x : α} {y : β} {xs : List α} {ys : List β} :
    P x y -> Forall₂ P xs ys -> Forall₂ P (x :: xs) (y :: ys)

end List

namespace Unifysl

theorem prop_ext : forall A B : Prop, (A <-> B) -> A = B := by
  intro A B h
  exact propext h

private theorem Forall_impl {A : Type u} {P Q : A -> Prop}
    (h : forall x, P x -> Q x) :
    forall {xs : List A}, List.Forall P xs -> List.Forall Q xs
  | [], List.Forall.nil => List.Forall.nil
  | x :: _, List.Forall.cons hx hxs => List.Forall.cons (h x hx) (Forall_impl h hxs)

private theorem Forall_mem {A : Type u} {P : A -> Prop} {xs : List A}
    (h : List.Forall P xs) : forall x, x ∈ xs -> P x := by
  induction h with
  | nil =>
      intro x hx
      cases hx
  | cons hx hxs ih =>
      intro y hy
      cases hy with
      | head =>
          exact hx
      | tail _ hy =>
          exact ih y hy

private theorem Forall_of_forall_mem {A : Type u} {P : A -> Prop} :
    forall {xs : List A}, (forall x, x ∈ xs -> P x) -> List.Forall P xs
  | [], _ => List.Forall.nil
  | x :: xs, h =>
      List.Forall.cons (h x (List.Mem.head xs))
        (Forall_of_forall_mem (fun y hy => h y (List.Mem.tail x hy)))

theorem fin_subset_match {A : Type u} {B : Type v} {P : A -> B -> Prop} :
    forall (X : A -> Prop) (Y : B -> Prop),
      (forall x, X x -> exists y, P x y /\ Y y) ->
      forall xs, List.Forall (fun x => X x) xs ->
        exists ys, List.Forall₂ P xs ys /\ List.Forall (fun y => Y y) ys := by
  intro X Y h xs hxs
  induction hxs with
  | nil =>
      exact ⟨[], List.Forall₂.nil, List.Forall.nil⟩
  | cons hx hxs ih =>
      rcases ih with ⟨ys, hrel, hall⟩
      rcases h _ hx with ⟨y, hpy, hy⟩
      exact ⟨y :: ys, List.Forall₂.cons hpy hrel, List.Forall.cons hy hall⟩

theorem Forall2_lr_rev {A : Type u} {B : Type v} {P : A -> B -> Prop} :
    forall xs ys,
      List.Forall₂ (fun y x => P x y) ys xs ->
      List.Forall₂ P xs ys := by
  intro xs ys h
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | cons hxy hrest ih =>
      exact List.Forall₂.cons hxy ih

theorem Forall_app_iff :
    forall {A : Type u} (P : A -> Prop) (l1 l2 : List A),
      List.Forall P (l1 ++ l2) <-> List.Forall P l1 /\ List.Forall P l2 := by
  intro A P l1
  induction l1 with
  | nil =>
      intro l2
      constructor
      · intro h
        exact ⟨List.Forall.nil, h⟩
      · intro h
        exact h.2
  | cons x xs ih =>
      intro l2
      constructor
      · intro h
        cases h with
        | cons hx htail =>
            have hboth := (ih l2).mp htail
            exact ⟨List.Forall.cons hx hboth.1, hboth.2⟩
      · intro h
        cases h.1 with
        | cons hx hxs =>
            exact List.Forall.cons hx ((ih l2).mpr ⟨hxs, h.2⟩)

inductive remove_rel {A : Type u} : A -> List A -> List A -> Prop where
| remove_rel_nil : forall a, remove_rel a [] []
| remove_rel_cons_eq : forall a xs ys, remove_rel a xs ys -> remove_rel a (a :: xs) ys
| remove_rel_cons_neq :
    forall a b xs ys, a ≠ b -> remove_rel a xs ys -> remove_rel a (b :: xs) (b :: ys)

export remove_rel (remove_rel_nil remove_rel_cons_eq remove_rel_cons_neq)

theorem remove_rel_In :
    forall (A : Type u) (l1 l2 : List A) (x : A), remove_rel x l1 l2 -> ¬ x ∈ l2 := by
  intro A l1 l2 x h
  induction h with
  | remove_rel_nil =>
      intro hx
      cases hx
  | remove_rel_cons_eq xs ys h ih =>
      exact ih
  | remove_rel_cons_neq b xs ys hneq hrel ih =>
      intro hx
      cases hx with
      | head =>
          exact hneq rfl
      | tail _ hx =>
          exact ih hx

theorem remove_rel_exist :
    forall (A : Type u) (l1 : List A) (x : A)
      (_DEC : forall y, x = y \/ x ≠ y), exists l2, remove_rel x l1 l2 := by
  intro A l1 x DEC
  induction l1 with
  | nil =>
      exact ⟨[], remove_rel_nil x⟩
  | cons a xs ih =>
      rcases ih with ⟨l2, hrel⟩
      cases DEC a with
      | inl heq =>
          subst heq
          exact ⟨l2, remove_rel_cons_eq x xs l2 hrel⟩
      | inr hneq =>
          exact ⟨a :: l2, remove_rel_cons_neq x a xs l2 hneq hrel⟩

theorem remove_rel_result_belong :
    forall (A : Type u) (l1 l2 : List A) (x : A),
      remove_rel x l1 l2 -> List.Forall (fun y => y ∈ l1) l2 := by
  intro A l1 l2 x h
  induction h with
  | remove_rel_nil =>
      exact List.Forall.nil
  | remove_rel_cons_eq xs ys h ih =>
      exact Forall_impl (fun y hy => List.Mem.tail x hy) ih
  | remove_rel_cons_neq b xs ys hneq hrel ih =>
      exact List.Forall.cons (List.Mem.head xs)
        (Forall_impl (fun y hy => List.Mem.tail b hy) ih)

def isSome {A : Type u} (o : Option A) : Prop :=
  match o with
  | some _ => True
  | none => False

theorem nth_error_in_bounds :
    forall {A : Type u} (l : List A) i, (0 <= i /\ i < l.length) ->
      exists x, List.get? l i = some x := by
  intro A l i h
  cases hget : List.get? l i with
  | none =>
      have hle : l.length <= i := (List.getElem?_eq_none_iff).mp hget
      exact False.elim ((Nat.not_le_of_gt h.2) hle)
  | some x =>
      exact ⟨x, rfl⟩

theorem nth_error_app :
    forall {T : Type u} (al bl : List T) (j : Nat),
      List.get? (al ++ bl) (al.length + j) = List.get? bl j := by
  intro T al bl j
  simpa [List.get?, Nat.add_sub_cancel_left] using
    (List.getElem?_append_right (l₁ := al) (l₂ := bl)
      (i := al.length + j) (Nat.le_add_right al.length j))

theorem nth_error_app1 :
    forall {T : Type u} (al bl : List T) (j : Nat),
      j < al.length -> List.get? (al ++ bl) j = List.get? al j := by
  intro T al bl j h
  simpa [List.get?] using
    (List.getElem?_append_left (l₁ := al) (l₂ := bl) (i := j) h)

theorem nth_error_None_iff :
    forall {A : Type u} (l : List A) n, List.get? l n = none <-> n >= l.length := by
  intro A l n
  simp [List.get?]

theorem Forall_rev :
    forall {A : Type u} (P : A -> Prop) (l : List A),
      List.Forall P l.reverse <-> List.Forall P l := by
  intro A P l
  constructor
  · intro h
    exact Forall_of_forall_mem (fun x hx => Forall_mem h x ((List.mem_reverse).mpr hx))
  · intro h
    exact Forall_of_forall_mem (fun x hx => Forall_mem h x ((List.mem_reverse).mp hx))

end Unifysl
