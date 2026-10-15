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
abbrev sublist_cons1 {A : Type u} := @AUXLib.sublist_cons1 A
abbrev sublist_cons2 {A : Type u} := @AUXLib.sublist_cons2 A
abbrev Znth_sublist {A : Type u} := @AUXLib.Znth_sublist A
abbrev Znth_sublist_lt {A : Type u} := @AUXLib.Znth_sublist_lt A
abbrev sublist_self {A : Type u} := @AUXLib.sublist_self A

theorem Zlength_app_cons {A : Type u} (l : List A) (a : A) :
    Zlength (l ++ [a]) = Zlength l + 1 := by
  simp [Zlength, AUXLib.Zlength]

private theorem getD_append_left {A : Type u} (d : A) (l l' : List A)
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

theorem app_Znth1 {A : Type u} (d : A) (l l' : List A) (i : Int)
    (h : 0 <= i /\ i < Zlength l) :
    Znth i (l ++ l') d = Znth i l d := by
  unfold Znth AUXLib.Znth
  simp only [Zlength, AUXLib.Zlength] at h
  cases i with
  | negSucc n => omega
  | ofNat n =>
      exact getD_append_left d l l' n (Int.ofNat_lt.mp h.2)

theorem replace_nth_app_l {A : Type u} (n : Nat) (a : A)
    (l1 l2 : List A) (h : n < l1.length) :
    replace_nth n (l1 ++ l2) a = replace_nth n l1 a ++ l2 := by
  induction n generalizing l1 with
  | zero =>
      cases l1 with
      | nil => simp at h
      | cons x xs => rfl
  | succ n ih =>
      cases l1 with
      | nil => simp at h
      | cons x xs =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
          simp only [List.cons_append, replace_nth, AUXLib.replace_nth,
            List.cons.injEq, true_and]
          exact ih xs h

theorem replace_nth_app_r {A : Type u} (n : Nat) (a : A)
    (l1 l2 : List A) (h : l1.length <= n) :
    replace_nth n (l1 ++ l2) a =
      replace_nth n l1 a ++ replace_nth (n - l1.length) l2 a := by
  induction l1 generalizing n with
  | nil => simp [replace_nth, AUXLib.replace_nth]
  | cons x xs ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at h
          simp only [List.cons_append, replace_nth, AUXLib.replace_nth,
            List.length_cons, Nat.succ_sub_succ_eq_sub,
            List.cons.injEq, true_and]
          exact ih n h

theorem replace_Znth_app_l {A : Type u} (n : Int) (a : A)
    (l1 l2 : List A) (hn : 0 <= n) (hlen : n < Zlength l1) :
    replace_Znth n a (l1 ++ l2) = replace_Znth n a l1 ++ l2 := by
  cases n with
  | negSucc n => omega
  | ofNat n =>
      unfold replace_Znth AUXLib.replace_Znth
      exact replace_nth_app_l n a l1 l2 (Int.ofNat_lt.mp hlen)

theorem Znth_error_range {A : Type u} (l : List A) (n : Int) (a : A)
    (h : Znth_error l n = some a) :
    0 <= n /\ n < Zlength l := by
  unfold Znth_error AUXLib.Znth_error at h
  by_cases hn : 0 <= n
  · simp [hn] at h
    have hlt : n.toNat < l.length := (List.getElem?_eq_some_iff.mp h).1
    constructor
    · exact hn
    · simp [Zlength]
      omega
  · simp [hn] at h

theorem Znth_error_Some_cons {A : Type u} (m n : Int) (x : A)
    (l : List A) (a : A) (hn : n = m + 1)
    (h : Znth_error l m = some a) :
    Znth_error (x :: l) n = some a := by
  have hrange := Znth_error_range l m a h
  have hn0 : n ≠ 0 := by omega
  change AUXLib.Znth_error (x :: l) n = some a
  rw [AUXLib.Znth_error_cons m n x l hn0 hn]
  simpa using h

theorem sublist_split_app_l {A : Type u} (lo hi : Int) (l1 l2 : List A)
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

theorem Zlength_sublist {A : Type u} (lo hi : Int) (l : List A)
    (hlohi : 0 <= lo /\ lo <= hi) (hhi : hi <= Zlength l) :
    Zlength (sublist lo hi l) = hi - lo := by
  unfold Zlength AUXLib.Zlength
  rw [AUXLib.sublist_length lo hi l hlohi hhi]
  exact Int.toNat_sub_of_le hlohi.2

theorem Zlength_sublist' {A : Type u} (l : List A) (i j : Int) :
    Zlength (sublist i j l) =
      Int.ofNat (min j.toNat l.length - i.toNat) := by
  simp [Zlength, sublist, AUXLib.Zlength, AUXLib.sublist]

theorem Zlength_sublist0 {A : Type u} (hi : Int) (l : List A)
    (h : 0 <= hi /\ hi <= Zlength l) :
    Zlength (sublist 0 hi l) = hi := by
  have hlen := Zlength_sublist (0 : Int) hi l ⟨by omega, h.1⟩ h.2
  omega

theorem list_eq_ext {A : Type u} (l1 l2 : List A) (d : A) :
    l1 = l2 <->
      (Zlength l1 = Zlength l2 /\
        forall i, 0 <= i /\ i < Zlength l1 -> Znth i l1 d = Znth i l2 d) := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, by intro i _; rfl⟩
  · rintro ⟨hlen, hnth⟩
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

theorem Znth_sublist0 {A : Type u} (d : A) (i hi : Int) (l : List A)
    (h : 0 <= i /\ i < hi) :
    Znth i (sublist 0 hi l) d = Znth i l d := by
  have h' : 0 <= i /\ i < hi - 0 := by omega
  simpa using Znth_sublist d 0 i hi l (by omega) h'

theorem Znth_sublist_ge {A : Type u} (d : A) (lo hi : Int)
    (l : List A) (i : Int) (hlohi : 0 <= lo /\ lo <= hi)
    (hhi : hi <= Zlength l) (hiRange : hi - lo <= i) :
    Znth i (sublist lo hi l) d = d := by
  unfold Znth AUXLib.Znth
  have hlen := sublist_length lo hi l hlohi hhi
  have hbound : (sublist lo hi l).length <= i.toNat := by
    rw [hlen]
    omega
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_eq_none hbound]

theorem length_nonnil {A : Type u} (l : List A) (h : l ≠ []) :
    l.length > 0 := by
  cases l with
  | nil => contradiction
  | cons x xs => simp

theorem sublist_nil {A : Type u} (l : List A) (a b : Nat)
    (h : b <= a) : Nsublist a b l = [] := by
  unfold Nsublist AUXLib.Nsublist
  apply List.drop_eq_nil_of_le
  have htake := List.length_take_le b l
  omega

theorem Nsublist_single {A : Type u} (d : A) (n : Nat) (l : List A)
    (h : n < l.length) :
    Nsublist n (n + 1) l = [nth n l d] := by
  unfold Nsublist AUXLib.Nsublist nth AUXLib.nth
  rw [List.drop_take]
  have hsub : n + 1 - n = 1 := by omega
  rw [hsub]
  have hdrop : l.drop n = l[n] :: l.drop (n + 1) :=
    List.drop_eq_getElem_cons h
  have hget : l.getD n d = l[n] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  calc
    List.take 1 (l.drop n) = [l[n]] := by
      rw [hdrop]
      rfl
    _ = [l.getD n d] := congrArg (fun x => [x]) hget.symm

theorem sublist_one_ele {A : Type u} (d : A) (i : Nat)
    (text : List A) (ch : A)
    (h : 0 <= i /\ i < text.length) (hch : ch = nth i text d) :
    Nsublist 0 i text ++ [ch] = Nsublist 0 (i + 1) text := by
  subst ch
  unfold Nsublist AUXLib.Nsublist nth AUXLib.nth
  rw [List.drop_zero, List.drop_zero]
  have hget : text.getD i d = text[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h.2]
  rw [hget]
  exact (List.take_succ_eq_append_getElem h.2).symm

theorem sublist_one_ele' {A : Type u} (d : A) (i : Nat) (text : List A)
    (h : 0 <= i /\ i < text.length) :
    Nsublist 0 (i + 1) text = Nsublist 0 i text ++ [nth i text d] := by
  exact (sublist_one_ele d i text (nth i text d) h rfl).symm

theorem sublist_single' {A : Type u} (d : A) (n : Nat) (l : List A)
    (h : 0 < n /\ n <= l.length) :
    Nsublist (n - 1) n l = [nth (n - 1) l d] := by
  have hn : n = (n - 1) + 1 := by omega
  rw [hn]
  apply Nsublist_single
  omega

theorem Nsublist_self {A : Type u} (l : List A) (x : Nat)
    (h : x = l.length) :
    Nsublist 0 x l = l := by
  subst x
  simp [Nsublist, AUXLib.Nsublist]

theorem Nsublist_split_app_l {A : Type u} (lo hi : Nat)
    (l1 l2 : List A) (_hlohi : lo <= hi) (hhi : hi <= l1.length) :
    Nsublist lo hi (l1 ++ l2) = Nsublist lo hi l1 := by
  unfold Nsublist AUXLib.Nsublist
  rw [List.take_append]
  have hzero : hi - l1.length = 0 := Nat.sub_eq_zero_of_le hhi
  rw [hzero]
  simp

theorem Nsublist_split_app_r {A : Type u} (lo hi len : Nat)
    (l1 l2 : List A) (hlen : l1.length = len)
    (h : len <= lo /\ lo <= hi) :
    Nsublist lo hi (l1 ++ l2) = Nsublist (lo - len) (hi - len) l2 := by
  subst len
  unfold Nsublist AUXLib.Nsublist
  rw [List.take_append, List.take_of_length_le (Nat.le_trans h.1 h.2)]
  rw [List.drop_append]
  simp [List.drop_eq_nil_of_le h.1]

theorem Nsublist_split {A : Type u} (lo hi mid : Nat) (l : List A)
    (_hlomid : 0 <= lo /\ lo <= mid)
    (hmidhi : mid <= hi /\ hi <= l.length) :
    Nsublist lo hi l = Nsublist lo mid l ++ Nsublist mid hi l := by
  unfold Nsublist AUXLib.Nsublist
  simp only [List.drop_take]
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega]
  rw [List.take_add]
  congr 1
  rw [List.drop_drop]
  congr 2 <;> omega

theorem Zsublist_one_ele {A : Type u} (d : A) (l : List A) (n : Int)
    (hn : 0 <= n /\ n < Zlength l) :
    sublist n (n + 1) l = [Znth n l d] :=
  sublist_single d n l hn

end ListLib
