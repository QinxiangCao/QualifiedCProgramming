import AUXLib.Axioms
import AUXLib.EqDec
import Std.Tactic
import Lean.Elab.Tactic.Omega

namespace AUXLib

universe u v

abbrev In {A : Type u} (x : A) (l : List A) : Prop := x ∈ l
abbrev incl {A : Type u} (l1 l2 : List A) : Prop :=
  forall x, In x l1 -> In x l2
abbrev NoDup {A : Type u} (l : List A) : Prop := l.Nodup
abbrev Permutation {A : Type u} (l1 l2 : List A) : Prop := l1.Perm l2

inductive Forall {A : Type u} (P : A -> Prop) : List A -> Prop where
  | nil : Forall P []
  | cons {x xs} : P x -> Forall P xs -> Forall P (x :: xs)

namespace Forall

theorem mem {A : Type u} {P : A -> Prop} {x : A} {xs : List A}
    (h : Forall P xs) (hx : x ∈ xs) : P x := by
  induction h with
  | nil => simp at hx
  | cons hp _ ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hp
      · exact ih hx

theorem iff_forall_mem {A : Type u} {P : A -> Prop} {xs : List A} :
    Forall P xs <-> forall x, x ∈ xs -> P x := by
  constructor
  · intro h x hx
    exact h.mem hx
  · intro h
    induction xs with
    | nil => exact .nil
    | cons x xs ih =>
        exact .cons (h x (by simp)) (ih (by
          intro y hy
          exact h y (by simp [hy])))

theorem perm {A : Type u} {P : A -> Prop} {xs ys : List A}
    (h : Forall P xs) (hp : Permutation xs ys) : Forall P ys := by
  rw [iff_forall_mem] at h ⊢
  intro x hx
  exact h x (hp.mem_iff.mpr hx)

end Forall

inductive Forall2 {A : Type u} {B : Type v} (P : A -> B -> Prop) :
    List A -> List B -> Prop where
  | nil : Forall2 P [] []
  | cons {x y xs ys} : P x y -> Forall2 P xs ys -> Forall2 P (x :: xs) (y :: ys)

namespace Forall2

theorem length_eq {A : Type u} {B : Type v} {P : A -> B -> Prop}
    {xs : List A} {ys : List B} (h : Forall2 P xs ys) : xs.length = ys.length := by
  induction h <;> simp_all

theorem append {A : Type u} {B : Type v} {P : A -> B -> Prop}
    {xs1 xs2 : List A} {ys1 ys2 : List B}
    (h1 : Forall2 P xs1 ys1) (h2 : Forall2 P xs2 ys2) :
    Forall2 P (xs1 ++ xs2) (ys1 ++ ys2) := by
  induction h1 with
  | nil => exact h2
  | cons hp _ ih => exact .cons hp ih

end Forall2

abbrev seq (start len : Nat) : List Nat := List.range' start len
abbrev nth {A : Type u} (n : Nat) (l : List A) (d : A) : A := l.getD n d
abbrev firstn {A : Type u} (n : Nat) (l : List A) : List A := l.take n
abbrev skipn {A : Type u} (n : Nat) (l : List A) : List A := l.drop n
abbrev «repeat» {A : Type u} (a : A) (n : Nat) : List A := List.replicate n a
abbrev combine {A : Type u} {B : Type v} (l1 : List A) (l2 : List B) : List (A × B) :=
  List.zip l1 l2

def Zlength {A : Type u} (l : List A) : Int := Int.ofNat l.length

@[simp] theorem Zlength_correct {A : Type u} (l : List A) :
    Zlength l = Int.ofNat l.length := rfl

@[simp] theorem Zlength_nil {A : Type u} : Zlength ([] : List A) = 0 := rfl

@[simp] theorem Zlength_cons {A : Type u} (x : A) (xs : List A) :
    Zlength (x :: xs) = Zlength xs + 1 := by
  simp [Zlength]

theorem Zlength_nonneg {A : Type u} (l : List A) :
    0 <= Zlength l := by
  simp [Zlength]

theorem Zlength_app {A : Type u} (l1 l2 : List A) :
    Zlength (l1 ++ l2) = Zlength l1 + Zlength l2 := by
  simp [Zlength]

def Znth {A : Type u} (n : Int) (l : List A) (d : A) : A :=
  l.getD n.toNat d

def Znth_error {A : Type u} (l : List A) (n : Int) : Option A :=
  if 0 <= n then l[n.toNat]? else none

def tl_error {A : Type u} (l : List A) : Option A :=
  l[l.length - 1]?

def replace_nth {A : Type u} : Nat -> List A -> A -> List A
  | _, [], _ => []
  | 0, _ :: xs, a => a :: xs
  | n + 1, x :: xs, a => x :: replace_nth n xs a

def replace_Znth {A : Type u} (n : Int) (a : A) (l : List A) : List A :=
  replace_nth n.toNat l a

def Nsublist {A : Type u} (lo hi : Nat) (l : List A) : List A :=
  (l.take hi).drop lo

def sublist {A : Type u} (lo hi : Int) (l : List A) : List A :=
  (l.take hi.toNat).drop lo.toNat

theorem Zsublist_nil {A : Type u} (l : List A) (a b : Int)
    (h : b <= a) : sublist a b l = [] := by
  unfold sublist
  apply List.drop_eq_nil_of_le
  have htake := List.length_take_le b.toNat l
  have hnat : b.toNat <= a.toNat := by omega
  omega

theorem Zsublist_of_nil {A : Type u} (i j : Int) :
    sublist i j ([] : List A) = [] := by
  simp [sublist]

theorem sublist_self {A : Type u} (l : List A) (x : Int)
    (h : x = Zlength l) : sublist 0 x l = l := by
  subst x
  simp [sublist, Zlength]

theorem sublist_cons1 {A : Type u} (n : Int) (a : A) (l : List A)
    (h : 1 <= n) : sublist 0 n (a :: l) = a :: sublist 0 (n - 1) l := by
  have hn : n.toNat = (n - 1).toNat + 1 := by omega
  unfold sublist
  simp only [Int.toNat_zero, List.drop_zero]
  rw [hn]
  rfl

theorem sublist_cons2 {A : Type u} (m n : Int) (a : A) (l : List A)
    (hmn : 1 <= m ∧ m <= n) (_hn : n <= Zlength (a :: l)) :
    sublist m n (a :: l) = sublist (m - 1) (n - 1) l := by
  have hm : m.toNat = (m - 1).toNat + 1 := by omega
  have hn : n.toNat = (n - 1).toNat + 1 := by omega
  unfold sublist
  rw [hm, hn]
  rfl

@[simp] theorem Znth0_cons {A : Type u} (d a : A) (l : List A) :
    Znth 0 (a :: l) d = a := rfl

theorem Znth_cons {A : Type u} (d : A) (n : Int) (a : A) (l : List A)
    (hn : n > 0) : Znth n (a :: l) d = Znth (n - 1) l d := by
  unfold Znth
  have hnat : n.toNat = (n - 1).toNat + 1 := by omega
  rw [hnat]
  simp

@[simp] theorem Znth_error_cons_0 {A : Type u} (x : A) (l : List A) :
    Znth_error (x :: l) 0 = some x := by
  simp [Znth_error]

theorem Znth_error_cons {A : Type u} (m n : Int) (x : A) (l : List A)
    (hn0 : n ≠ 0) (hn : n = m + 1) :
    Znth_error (x :: l) n = Znth_error l m := by
  subst n
  by_cases hm : 0 <= m
  · have hs : (m + 1).toNat = m.toNat + 1 := by omega
    have hm1 : 0 <= m + 1 := by omega
    simp [Znth_error, hm, hm1, hs]
  · have hm1 : Not (0 <= m + 1) := by omega
    simp [Znth_error, hm, hm1]

theorem Znth_repeat {A : Type u} (d : A) (n : Nat) (i : Int) :
    Znth i («repeat» d n) d = d := by
  unfold Znth
  generalize i.toNat = k
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      cases k with
      | zero => rfl
      | succ k =>
          simp only [«repeat», List.replicate_succ, List.getD_cons_succ]
          exact ih k

theorem Znth_repeat_lt {A : Type u} (a : A) (n : Nat) (i : Int) (d : A)
    (h : 0 <= i ∧ i < Int.ofNat n) : Znth i («repeat» d n) a = d := by
  cases i with
  | negSucc i => omega
  | ofNat i =>
      have hi : i < n := Int.ofNat_lt.mp h.2
      have hi' : (Int.ofNat i).toNat < («repeat» d n).length := by
        simpa [«repeat»] using hi
      unfold Znth
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      simp

theorem replace_Znth_cons {A : Type u} (n : Int) (a b : A) (l : List A)
    (hn : n > 0) :
    replace_Znth n a (b :: l) = b :: replace_Znth (n - 1) a l := by
  unfold replace_Znth
  have hs : n.toNat = (n - 1).toNat + 1 := by omega
  rw [hs]
  rfl

theorem replace_Znth_Znth {A : Type u} (n : Int) (l : List A) (a0 : A) :
    replace_Znth n (Znth n l a0) l = l := by
  unfold replace_Znth Znth
  generalize n.toNat = m
  induction l generalizing m with
  | nil => simp [replace_nth]
  | cons x xs ih =>
      cases m with
      | zero => rfl
      | succ m =>
          simp only [List.getD_cons_succ, replace_nth]
          rw [ih]

private theorem getD_replace_nth_same {A : Type u} (d : A) (l : List A)
    (n : Nat) (v : A) (h : n < l.length) :
    (replace_nth n l v).getD n d = v := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [replace_nth, List.getD_cons_succ]
          apply ih
          simpa using h

private theorem getD_replace_nth_diff {A : Type u} (d : A) (l : List A)
    (i j : Nat) (v : A) (hi : i < l.length) (hj : j < l.length)
    (hne : i ≠ j) :
    (replace_nth i l v).getD j d = l.getD j d := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact False.elim (hne rfl)
          | succ j => rfl
      | succ i =>
          cases j with
          | zero => rfl
          | succ j =>
              simp only [replace_nth, List.getD_cons_succ]
              apply ih
              · simpa using hi
              · simpa using hj
              · intro hij
                apply hne
                simp [hij]

theorem Znth_replace_Znth_Same {A : Type u} (d : A) (l : List A)
    (i : Int) (v : A) (h : 0 <= i ∧ i < Zlength l) :
    Znth i (replace_Znth i v l) d = v := by
  cases i with
  | negSucc i =>
      simp at h
  | ofNat i =>
      have hi : i < l.length := by
        exact Int.ofNat_lt.mp h.2
      exact getD_replace_nth_same d l i v hi

theorem Znth_replace_Znth_Diff {A : Type u} (d : A) (l : List A)
    (i j : Int) (v : A)
    (hi : 0 <= i ∧ i < Zlength l) (hj : 0 <= j ∧ j < Zlength l)
    (hne : i ≠ j) :
    Znth j (replace_Znth i v l) d = Znth j l d := by
  cases i with
  | negSucc i => simp at hi
  | ofNat i =>
      cases j with
      | negSucc j => simp at hj
      | ofNat j =>
          have hin : i < l.length := Int.ofNat_lt.mp hi.2
          have hjn : j < l.length := Int.ofNat_lt.mp hj.2
          have hnat : i ≠ j := by
            intro h
            apply hne
            simp [h]
          exact getD_replace_nth_diff d l i j v hin hjn hnat
