import ListLib.Base.Positional
import AUXLib.ListLib.NPerm

namespace ListLib

universe u v w

theorem Forall2_split {A : Type u} {B : Type v}
    (P : A -> B -> Prop) (n : Nat) (xs : List A) (ys : List B) :
    Forall2 P xs ys ->
      Forall2 P (firstn n xs) (firstn n ys) /\
      Forall2 P (skipn n xs) (skipn n ys) := by
  induction n generalizing xs ys with
  | zero =>
      intro h
      exact ⟨AUXLib.Forall2.nil, h⟩
  | succ n ih =>
      intro h
      cases xs with
      | nil =>
          cases ys with
          | nil => exact ⟨AUXLib.Forall2.nil, AUXLib.Forall2.nil⟩
          | cons y ys => cases h
      | cons x xs =>
          cases ys with
          | nil => cases h
          | cons y ys =>
              cases h with
              | cons hxy hrest =>
                  rcases ih xs ys hrest with ⟨hfirst, hskip⟩
                  exact ⟨AUXLib.Forall2.cons hxy hfirst, hskip⟩

theorem Forall2_congr (A : Type u) (B : Type v)
    (p p' : A -> B -> Prop) (xs : List A) (ys : List B) :
    (forall x y, In x xs -> In y ys -> p x y -> p' x y) ->
    Forall2 p xs ys ->
    Forall2 p' xs ys := by
  intro himpl h
  induction h with
  | nil => exact AUXLib.Forall2.nil
  | cons hxy hrest ih =>
      apply AUXLib.Forall2.cons
      · apply himpl
        · simp [In, AUXLib.In]
        · simp [In, AUXLib.In]
        · exact hxy
      · apply ih
        intro x y hx hy hxy'
        exact himpl x y (by simp [In, AUXLib.In, hx])
          (by simp [In, AUXLib.In, hy]) hxy'

theorem Forall2_cons_nil_l {A : Type u} {B : Type v}
    {R : A -> B -> Prop} (xs : List B) :
    Forall2 R ([] : List A) xs -> xs = [] := by
  intro h
  cases h
  rfl

theorem Forall2_cons_nil_inv_l {A : Type u} {B : Type v}
    {R : A -> B -> Prop} (x : A) (ys : List B) :
    Forall2 R [x] ys -> exists y, ys = [y] /\ R x y := by
  intro h
  cases ys with
  | nil => cases h
  | cons y ys' =>
      cases h with
      | cons hxy htail =>
          have hy : ys' = [] := Forall2_cons_nil_l ys' htail
          subst ys'
          exact ⟨y, rfl, hxy⟩

theorem Forall2_cons_inv_l {A : Type u} {B : Type v}
    {R : A -> B -> Prop} (x : A) (xs : List A) (ys : List B) :
    Forall2 R (x :: xs) ys ->
      exists y ys', ys = y :: ys' /\ R x y /\ Forall2 R xs ys' := by
  intro h
  cases h with
  | cons hxy htail =>
      exact ⟨_, _, rfl, hxy, htail⟩

theorem Forall2_cons_nil_r {A : Type u} {B : Type v}
    {R : A -> B -> Prop} (xs : List A) :
    Forall2 R xs ([] : List B) -> xs = [] := by
  intro h
  cases h
  rfl

theorem Forall2_cons_nil_inv_r {A : Type u} {B : Type v}
    {R : A -> B -> Prop} (xs : List A) (y : B) :
    Forall2 R xs [y] -> exists x, xs = [x] /\ R x y := by
  intro h
  cases xs with
  | nil => cases h
  | cons x xs' =>
      cases h with
      | cons hxy htail =>
          have hx : xs' = [] := Forall2_cons_nil_r xs' htail
          subst xs'
          exact ⟨x, rfl, hxy⟩

theorem Forall2_cons_inv_r {A : Type u} {B : Type v}
    {R : A -> B -> Prop} (xs : List A) (y : B) (ys : List B) :
    Forall2 R xs (y :: ys) ->
      exists x xs', xs = x :: xs' /\ R x y /\ Forall2 R xs' ys := by
  intro h
  cases h with
  | cons hxy htail =>
      exact ⟨_, _, rfl, hxy, htail⟩

theorem Forall2_nth_iff (A : Type u) (B : Type v)
    (P : A -> B -> Prop) (xs : List A) (ys : List B)
    (dx : A) (dy : B) :
    Forall2 P xs ys <->
      (xs.length = ys.length /\
        forall n, n < xs.length -> P (nth n xs dx) (nth n ys dy)) :=
  AUXLib.Forall2_nth_iff A B P xs ys dx dy

theorem Forall2_map1 {A : Type u} {B : Type v} {C : Type w} :
    forall (P : C -> B -> Prop) (xs : List A) (ys : List B)
      (f : A -> C),
      Forall2 (fun x y => P (f x) y) xs ys <->
        Forall2 P (xs.map f) ys := by
  intro P xs
  induction xs with
  | nil =>
      intro ys f
      cases ys <;> constructor <;> intro h <;> cases h <;>
        exact AUXLib.Forall2.nil
  | cons x xs ih =>
      intro ys f
      cases ys with
      | nil =>
          constructor <;> intro h <;> cases h
      | cons y ys =>
          constructor
          · intro h
            cases h with
            | cons hxy hrest =>
                exact AUXLib.Forall2.cons hxy ((ih ys f).mp hrest)
          · intro h
            cases h with
            | cons hxy hrest =>
                exact AUXLib.Forall2.cons hxy ((ih ys f).mpr hrest)

theorem Forall2_map2 {A : Type u} {B : Type v} {C : Type w} :
    forall (P : A -> C -> Prop) (xs : List A) (ys : List B)
      (f : B -> C),
      Forall2 (fun x y => P x (f y)) xs ys <->
        Forall2 P xs (ys.map f) := by
  intro P xs
  induction xs with
  | nil =>
      intro ys f
      cases ys <;> constructor <;> intro h <;> cases h <;>
        exact AUXLib.Forall2.nil
  | cons x xs ih =>
      intro ys f
      cases ys with
      | nil =>
          constructor <;> intro h <;> cases h
      | cons y ys =>
          constructor
          · intro h
            cases h with
            | cons hxy hrest =>
                exact AUXLib.Forall2.cons hxy ((ih ys f).mp hrest)
          · intro h
            cases h with
            | cons hxy hrest =>
                exact AUXLib.Forall2.cons hxy ((ih ys f).mpr hrest)

theorem Forall2_and {A : Type u} {B : Type v}
    (R1 R2 : A -> B -> Prop) (l : List A) (l' : List B) :
    Forall2 R1 l l' ->
    Forall2 R2 l l' ->
    Forall2 (fun a b => R1 a b /\ R2 a b) l l' := by
  intro h1 h2
  induction h1 with
  | nil => exact AUXLib.Forall2.nil
  | cons hxy hrest ih =>
      cases h2 with
      | cons hxy2 hrest2 =>
          exact AUXLib.Forall2.cons ⟨hxy, hxy2⟩ (ih hrest2)

theorem Forall2_and_inv {A : Type u} {B : Type v}
    (R1 R2 : A -> B -> Prop) (l : List A) (l' : List B) :
    Forall2 (fun a b => R1 a b /\ R2 a b) l l' ->
    Forall2 R1 l l' /\ Forall2 R2 l l' := by
  intro h
  induction h with
  | nil => exact ⟨AUXLib.Forall2.nil, AUXLib.Forall2.nil⟩
  | cons hxy _ ih =>
      exact ⟨AUXLib.Forall2.cons hxy.1 ih.1,
        AUXLib.Forall2.cons hxy.2 ih.2⟩

theorem Forall2_and_Forall_l {A : Type u} {B : Type v}
    (P : A -> Prop) (R : A -> B -> Prop) (l : List A) (l' : List B) :
    Forall P l ->
    Forall2 R l l' ->
    Forall2 (fun a b => P a /\ R a b) l l' := by
  intro hp hr
  induction hr with
  | nil => exact AUXLib.Forall2.nil
  | cons hxy hrest ih =>
      cases hp with
      | cons hpx hptail =>
          exact AUXLib.Forall2.cons ⟨hpx, hxy⟩ (ih hptail)

theorem Forall2_and_Forall_r {A : Type u} {B : Type v}
    (P : A -> Prop) (R : A -> B -> Prop) (l : List A) (l' : List B) :
    Forall2 R l l' ->
    Forall P l ->
    Forall2 (fun a b => R a b /\ P a) l l' := by
  intro hr hp
  induction hr with
  | nil => exact AUXLib.Forall2.nil
  | cons hxy hrest ih =>
      cases hp with
      | cons hpx hptail =>
          exact AUXLib.Forall2.cons ⟨hxy, hpx⟩ (ih hptail)

theorem Forall_in_cons {A : Type u} (l : List A) (e : A) (p : List A) :
    Forall (fun x => In x (e :: l)) p ->
    Not (In e p) ->
    Forall (fun x => In x l) p := by
  intro hp hnot
  induction hp with
  | nil => exact AUXLib.Forall.nil
  | cons hx hrest ih =>
      rename_i x xs
      apply AUXLib.Forall.cons
      · have hx' : x = e \/ In x l := by
          simpa [In, AUXLib.In] using hx
        rcases hx' with hxe | hxl
        · exact False.elim (hnot (by cases hxe; simp [In, AUXLib.In]))
        · exact hxl
      · apply ih
        intro he
        exact hnot (by simp [In, AUXLib.In, he])

end ListLib
