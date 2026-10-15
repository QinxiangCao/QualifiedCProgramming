import AUXLib.ListLib.LengthCompat
import Std.Tactic

namespace ListLib

universe u v

abbrev Znth {A : Type u} := @AUXLib.Znth A
abbrev Znth_error {A : Type u} := @AUXLib.Znth_error A
abbrev tl_error {A : Type u} := @AUXLib.tl_error A
abbrev nth {A : Type u} := @AUXLib.nth A
abbrev firstn {A : Type u} := @AUXLib.firstn A
abbrev skipn {A : Type u} := @AUXLib.skipn A
abbrev In {A : Type u} := @AUXLib.In A
abbrev incl {A : Type u} := @AUXLib.incl A
abbrev NoDup {A : Type u} := @AUXLib.NoDup A
abbrev Permutation {A : Type u} := @AUXLib.Permutation A
abbrev Forall {A : Type u} := @AUXLib.Forall A
abbrev Forall2 {A : Type u} {B : Type v} := @AUXLib.Forall2 A B
abbrev replace_nth {A : Type u} := @AUXLib.replace_nth A
abbrev replace_Znth {A : Type u} := @AUXLib.replace_Znth A
abbrev Nsublist {A : Type u} := @AUXLib.Nsublist A
abbrev sublist {A : Type u} := @AUXLib.sublist A
abbrev Zlength {A : Type u} := @AUXLib.Zlength A

abbrev Znth_cons {A : Type u} := @AUXLib.Znth_cons A
abbrev Znth_error_cons_0 {A : Type u} := @AUXLib.Znth_error_cons_0 A
abbrev Znth_error_cons {A : Type u} := @AUXLib.Znth_error_cons A
abbrev Znth_repeat {A : Type u} := @AUXLib.Znth_repeat A
abbrev Znth_repeat_lt {A : Type u} := @AUXLib.Znth_repeat_lt A
abbrev replace_Znth_cons {A : Type u} := @AUXLib.replace_Znth_cons A
abbrev replace_Znth_Znth {A : Type u} := @AUXLib.replace_Znth_Znth A
abbrev Znth_replace_Znth_Same {A : Type u} := @AUXLib.Znth_replace_Znth_Same A
abbrev Znth_replace_Znth_Diff {A : Type u} := @AUXLib.Znth_replace_Znth_Diff A
abbrev Zsublist_nil {A : Type u} := @AUXLib.Zsublist_nil A
abbrev Zsublist_of_nil {A : Type u} := @AUXLib.Zsublist_of_nil A

theorem Znth0_cons {A : Type u} (d a : A) (l : List A) :
    Znth 0 (a :: l) d = a := rfl

private theorem Nsublist_Nsublist {A : Type u} (i j k m : Nat) (l : List A)
    (hki : k <= i) (hij : i + m <= j) :
    ((((l.take j).drop m).take i).drop k) =
      (l.take (i + m)).drop (k + m) := by
  rw [List.drop_take, List.drop_drop, List.drop_take]
  rw [List.take_take, List.drop_take]
  have hmin : i - k <= j - (m + k) := by omega
  have hsub : i + m - (k + m) = i - k := by omega
  rw [Nat.min_eq_left hmin, hsub, Nat.add_comm k m]

theorem Zsublist_Zsublist {A : Type u} (i j k m : Int) (l : List A)
    (hm : 0 <= m) (hki : 0 <= k /\ k <= i) (hij : i <= j - m) :
    sublist k i (sublist m j l) = sublist (k + m) (i + m) l := by
  have hi : 0 <= i := by omega
  have hj : 0 <= j := by omega
  have hkiNat : k.toNat <= i.toNat := by omega
  have hijNat : i.toNat + m.toNat <= j.toNat := by omega
  have hkm : (k + m).toNat = k.toNat + m.toNat := by omega
  have him : (i + m).toNat = i.toNat + m.toNat := by omega
  unfold sublist AUXLib.sublist
  rw [hkm, him]
  exact Nsublist_Nsublist i.toNat j.toNat k.toNat m.toNat l hkiNat hijNat

theorem Zsublist_Zsublist0 {A : Type u} (i j k : Int) (l : List A)
    (hk : 0 <= k) (hki : k <= i /\ i <= j) :
    sublist k i (sublist 0 j l) = sublist k i l := by
  simpa using Zsublist_Zsublist i j k 0 l (by omega) ⟨hk, hki.1⟩ (by omega)

theorem Zsublist_Zsublist00 {A : Type u} (i j : Int) (l : List A)
    (h : 0 <= i /\ i <= j) :
    sublist 0 i (sublist 0 j l) = sublist 0 i l := by
  exact Zsublist_Zsublist0 i j 0 l (by omega) ⟨by omega, h.2⟩

private theorem getD_take_of_lt {A : Type u} (d : A) (l : List A)
    (bound index : Nat) (h : index < bound) :
    (firstn bound l).getD index d = l.getD index d := by
  induction l generalizing bound index with
  | nil => simp [firstn]
  | cons x xs ih =>
      cases bound with
      | zero => omega
      | succ bound =>
          cases index with
          | zero => rfl
          | succ index =>
              simp only [firstn, List.take_succ_cons, List.getD_cons_succ]
              exact ih bound index (by omega)

private theorem getD_drop {A : Type u} (d : A) (l : List A)
    (start index : Nat) :
    (l.drop start).getD index d = l.getD (index + start) d := by
  induction start generalizing l with
  | zero => simp
  | succ start ih =>
      cases l with
      | nil => simp
      | cons x xs =>
          simpa only [skipn, List.drop_succ_cons, List.getD_cons_succ,
            Nat.add_succ] using ih xs

theorem nth_firstn {A : Type u} (l : List A) (n m : Nat) (d : A)
    (h : n < m) :
    nth n (firstn m l) d = nth n l d := by
  exact getD_take_of_lt d l m n h

theorem firstn_skipSn {A : Type u} (d : A) (n : Nat) (l : List A)
    (h : n < l.length) :
    l = firstn n l ++ nth n l d :: skipn (Nat.succ n) l := by
  induction n generalizing l with
  | zero =>
      cases l with
      | nil => simp at h
      | cons x xs => rfl
  | succ n ih =>
      cases l with
      | nil => simp at h
      | cons x xs =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
          simpa [firstn, skipn, nth] using congrArg (List.cons x) (ih xs h)

theorem length_sublist {A : Type u} (lo hi : Nat) (l : List A)
    (h : lo <= hi /\ hi <= l.length) :
    (Nsublist lo hi l).length = hi - lo := by
  unfold Nsublist AUXLib.Nsublist
  simp [Nat.min_eq_left h.2]

theorem length_sublist' {A : Type u} (i j : Nat) (l : List A) :
    (Nsublist i j l).length = min j l.length - i := by
  simp [Nsublist, AUXLib.Nsublist]

theorem nth_sublist {A : Type u} (d : A) (lo i hi : Nat) (l : List A)
    (h : i < hi - lo) :
    nth i (Nsublist lo hi l) d = nth (i + lo) l d := by
  unfold Nsublist AUXLib.Nsublist
  unfold nth AUXLib.nth
  rw [getD_drop]
  rw [getD_take_of_lt]
  omega

private theorem tl_error_eq_getLast? {A : Type u} (l : List A) :
    tl_error l = l.getLast? := by
  unfold tl_error AUXLib.tl_error
  exact List.getLast?_eq_getElem?.symm

theorem tl_error_last {A : Type u} (a : A) (l : List A) :
    tl_error (l ++ [a]) = some a := by
  rw [tl_error_eq_getLast?]
  simp

theorem tl_error_app_skipn_connected {A : Type u} (l1 l2 : List A)
    (_hl1 : l1 ≠ []) (hl2 : l2 ≠ [])
    (hhead : tl_error l1 = l2.head?) :
    tl_error (l1 ++ skipn 1 l2) = tl_error l2 := by
  rw [tl_error_eq_getLast?] at hhead
  rw [tl_error_eq_getLast? (l1 ++ skipn 1 l2), tl_error_eq_getLast? l2]
  cases l2 with
  | nil => contradiction
  | cons b t =>
      cases t with
      | nil =>
          simp only [skipn, List.drop_succ_cons, List.drop_nil, List.append_nil,
            List.head?_cons] at hhead ⊢
          exact hhead
      | cons c cs =>
          simp only [skipn, List.drop_succ_cons, List.drop_zero,
            List.getLast?_append]
          cases hlast : (c :: cs).getLast? with
          | none =>
              have hnil : (c :: cs : List A) = [] :=
                List.getLast?_eq_none_iff.mp hlast
              contradiction
          | some z =>
              simp [hlast]

end ListLib
