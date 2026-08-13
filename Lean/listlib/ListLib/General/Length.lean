import ListLib.Base.Inductive
import Std.Tactic

namespace ListLib

open AUXLib

universe u

abbrev Zlength_nonneg {A : Type u} := @AUXLib.Zlength_nonneg A
abbrev Zlength_correct {A : Type u} := @AUXLib.Zlength_correct A
abbrev Zlength_nil {A : Type u} := @AUXLib.Zlength_nil A
abbrev Zlength_cons {A : Type u} := @AUXLib.Zlength_cons A
abbrev Zlength_app {A : Type u} := @AUXLib.Zlength_app A
abbrev app_Znth2 {A : Type u} := @AUXLib.app_Znth2 A
abbrev Znth_indep {A : Type u} := @AUXLib.Znth_indep A
abbrev replace_Znth_app_r {A : Type u} := @AUXLib.replace_Znth_app_r A
abbrev replace_Znth_nothing {A : Type u} := @AUXLib.replace_Znth_nothing A
abbrev sublist_length {A : Type u} := @AUXLib.sublist_length A
abbrev sublist_app_exact1 {A : Type u} := @AUXLib.sublist_app_exact1 A
abbrev sublist_single {A : Type u} := @AUXLib.sublist_single A
abbrev sublist_split {A : Type u} := @AUXLib.sublist_split A
abbrev sublist_split_app_r {A : Type u} := @AUXLib.sublist_split_app_r A
abbrev Znth_sublist {A : Type u} := @AUXLib.Znth_sublist A
abbrev Znth_sublist_lt {A : Type u} := @AUXLib.Znth_sublist_lt A
abbrev sublist_self {A : Type u} := @AUXLib.sublist_self A

theorem Zlength_app_cons {A : Type} (l : List A) (a : A) :
    Zlength (l ++ [a]) = Zlength l + 1 := by
  simpa using AUXLib.Zlength_app l [a]

private theorem getD_append_left {A : Type} (d : A) (l l' : List A)
    (n : Nat) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  induction l generalizing n with
  | nil => simp at h
  | cons a l ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
          simpa only [List.cons_append, List.getD_cons_succ] using ih n h

theorem app_Znth1 {A : Type} (d : A) (l l' : List A) (i : Int)
    (h : 0 <= i /\ i < Zlength l) :
    Znth i (l ++ l') d = Znth i l d := by
  unfold Znth AUXLib.Znth
  simp only [Zlength, AUXLib.Zlength] at h
  cases i with
  | negSucc n => omega
  | ofNat n =>
      exact getD_append_left d l l' n (Int.ofNat_lt.mp h.2)

theorem sublist_split_app_l {A : Type} (lo hi : Int) (l1 l2 : List A)
    (hlohi : 0 <= lo /\ lo <= hi) (hhi : hi <= Zlength l1) :
    sublist lo hi (l1 ++ l2) = sublist lo hi l1 := by
  unfold sublist AUXLib.sublist
  simp only [List.take_append]
  have hh : hi.toNat <= l1.length := by
    unfold Zlength at hhi
    cases hi with
    | negSucc n => omega
    | ofNat n => exact Int.ofNat_le.mp hhi
  have hzero : hi.toNat - l1.length = 0 := Nat.sub_eq_zero_of_le hh
  rw [hzero]
  simp

theorem Zlength_sublist {A : Type} (lo hi : Int) (l : List A)
    (hlohi : 0 <= lo /\ lo <= hi) (hhi : hi <= Zlength l) :
    Zlength (sublist lo hi l) = hi - lo := by
  unfold Zlength AUXLib.Zlength
  rw [AUXLib.sublist_length lo hi l hlohi hhi]
  exact Int.toNat_sub_of_le hlohi.2

theorem Zlength_sublist' {A : Type} (l : List A) (i j : Int) :
    Zlength (sublist i j l) =
      Int.ofNat (min j.toNat l.length - i.toNat) := by
  simp [Zlength, sublist, AUXLib.Zlength, AUXLib.sublist]

theorem list_eq_ext {A : Type} (l1 l2 : List A) (d : A) :
    (Zlength l1 = Zlength l2 /\
      forall i, 0 <= i /\ i < Zlength l1 -> Znth i l1 d = Znth i l2 d) ->
    l1 = l2 := by
  rintro ⟨hlen, hnth⟩
  have hlenNat : l1.length = l2.length := by
    unfold Zlength at hlen
    exact Int.ofNat_inj.mp hlen
  apply List.ext_get hlenNat
  · intro n h1 h2
    have hi : (0 : Int) <= Int.ofNat n /\ Int.ofNat n < Zlength l1 :=
      ⟨Int.ofNat_zero_le n, Int.ofNat_lt.mpr h1⟩
    have h := hnth (Int.ofNat n) hi
    unfold Znth AUXLib.Znth at h
    have hd1 : l1.getD n d = l1.get ⟨n, h1⟩ := by
      simp [List.getD_eq_getElem?_getD, h1]
    have hd2 : l2.getD n d = l2.get ⟨n, h2⟩ := by
      simp [List.getD_eq_getElem?_getD, h2]
    exact hd1.symm.trans (h.trans hd2)

theorem sublist_one_ele {A : Type} (d : A) (l : List A) (n : Int)
    (hn : 0 <= n /\ n < Zlength l) :
    sublist n (n + 1) l = [Znth n l d] :=
  sublist_single d n l hn

end ListLib
