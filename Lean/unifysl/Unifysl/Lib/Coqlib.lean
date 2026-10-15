import Mathlib.Data.List.Defs

namespace List

abbrev get? (xs : List α) (i : Nat) : Option α :=
  xs[i]?

namespace Forall

theorem nil {P : α -> Prop} : List.Forall P [] := by
  simp [List.Forall]

theorem cons {P : α -> Prop} {x : α} {xs : List α}
    (hx : P x) (hxs : List.Forall P xs) : List.Forall P (x :: xs) := by
  cases xs with
  | nil => simpa [List.Forall] using hx
  | cons y ys => simpa [List.Forall] using And.intro hx hxs

@[elab_as_elim, induction_eliminator]
protected noncomputable def rec {P : α -> Prop}
    {motive : (xs : List α) -> List.Forall P xs -> Sort v}
    (nil : motive [] List.Forall.nil)
    (cons : forall {x xs} (hx : P x) (hxs : List.Forall P xs),
      motive xs hxs -> motive (x :: xs) (List.Forall.cons hx hxs)) :
    forall {xs} (hxs : List.Forall P xs), motive xs hxs := by
  intro xs
  induction xs with
  | nil =>
      intro hxs
      simpa only [Subsingleton.elim hxs List.Forall.nil] using nil
  | cons x xs ih =>
      intro hxs
      have parts : P x /\ List.Forall P xs := by
        cases xs with
        | nil => simpa [List.Forall] using hxs
        | cons y ys => simpa [List.Forall] using hxs
      have step := cons parts.1 parts.2 (ih parts.2)
      simpa only [Subsingleton.elim hxs (List.Forall.cons parts.1 parts.2)] using step

@[elab_as_elim, cases_eliminator]
protected noncomputable def casesOn {P : α -> Prop}
    {motive : (xs : List α) -> List.Forall P xs -> Sort v}
    (hxs : List.Forall P xs)
    (nil : motive [] List.Forall.nil)
    (cons : forall {x xs} (hx : P x) (hxs : List.Forall P xs),
      motive (x :: xs) (List.Forall.cons hx hxs)) : motive xs hxs := by
  cases xs with
  | nil =>
      simpa only [Subsingleton.elim hxs List.Forall.nil] using nil
  | cons x xs =>
      have parts : P x /\ List.Forall P xs := by
        cases xs with
        | nil => simpa [List.Forall] using hxs
        | cons y ys => simpa [List.Forall] using hxs
      have step := cons parts.1 parts.2
      simpa only [Subsingleton.elim hxs (List.Forall.cons parts.1 parts.2)] using step

end Forall

end List

namespace Unifysl

theorem coq_list_forall_cons_iff {A : Type u} {P : A -> Prop}
    {x : A} {xs : List A} :
    List.Forall P (x :: xs) <-> P x /\ List.Forall P xs := by
  cases xs <;> simp [List.Forall]

theorem coq_list_forall_iff_forall_mem {A : Type u} {P : A -> Prop}
    {xs : List A} :
    List.Forall P xs <-> forall x, x ∈ xs -> P x := by
  induction xs with
  | nil => simp [List.Forall]
  | cons x xs ih =>
      rw [coq_list_forall_cons_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨hx, hxs⟩ y (rfl | hy)
        · exact hx
        · exact ih.mp hxs y hy
      · intro h
        exact ⟨h x (Or.inl rfl), ih.mpr (fun y hy => h y (Or.inr hy))⟩

theorem coq_list_forall_impl {A : Type u} {P Q : A -> Prop}
    (h : forall x, P x -> Q x) {xs : List A}
    (hxs : List.Forall P xs) : List.Forall Q xs :=
  coq_list_forall_iff_forall_mem.mpr fun x hx =>
    h x (coq_list_forall_iff_forall_mem.mp hxs x hx)

theorem prop_ext : forall A B : Prop, (A <-> B) -> A = B := by
  intro A B h
  exact propext h

private theorem Forall_impl {A : Type u} {P Q : A -> Prop}
    (h : forall x, P x -> Q x) :
    forall {xs : List A}, List.Forall P xs -> List.Forall Q xs :=
  fun {_} hxs => coq_list_forall_impl h hxs

private theorem Forall_mem {A : Type u} {P : A -> Prop} {xs : List A}
    (h : List.Forall P xs) : forall x, x ∈ xs -> P x :=
  coq_list_forall_iff_forall_mem.mp h

private theorem Forall_of_forall_mem {A : Type u} {P : A -> Prop} :
    forall {xs : List A}, (forall x, x ∈ xs -> P x) -> List.Forall P xs :=
  fun {_} h => coq_list_forall_iff_forall_mem.mpr h

theorem fin_subset_match {A : Type u} {B : Type v} {P : A -> B -> Prop} :
    forall (X : A -> Prop) (Y : B -> Prop),
      (forall x, X x -> exists y, P x y /\ Y y) ->
      forall xs, List.Forall (fun x => X x) xs ->
        exists ys, List.Forall₂ P xs ys /\ List.Forall (fun y => Y y) ys := by
  intro X Y h xs hxs
  induction xs with
  | nil =>
      exact ⟨[], List.Forall₂.nil, List.Forall.nil⟩
  | cons x xs ih =>
      rcases coq_list_forall_cons_iff.mp hxs with ⟨hx, htail⟩
      rcases ih htail with ⟨ys, hrel, hall⟩
      rcases h x hx with ⟨y, hpy, hy⟩
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
        rcases coq_list_forall_cons_iff.mp h with ⟨hx, htail⟩
        have hboth := (ih l2).mp htail
        exact ⟨List.Forall.cons hx hboth.1, hboth.2⟩
      · intro h
        rcases coq_list_forall_cons_iff.mp h.1 with ⟨hx, hxs⟩
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
