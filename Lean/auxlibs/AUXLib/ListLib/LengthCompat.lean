import AUXLib.ListLib.Base

namespace AUXLib

universe u

theorem firstn_all2 {A : Type u} (n : Nat) (l : List A)
    (h : l.length <= n) : firstn n l = l := by
  exact List.take_of_length_le h

theorem repeat_length {A : Type u} (x : A) (n : Nat) :
    («repeat» x n).length = n := by
  exact List.length_replicate

theorem repeat_app {A : Type u} (x : A) (n m : Nat) :
    «repeat» x (n + m) = «repeat» x n ++ «repeat» x m := by
  exact List.replicate_append_replicate.symm

private theorem getD_append_right {A : Type u} (d : A) (l1 l2 : List A)
    (n : Nat) (h : l1.length <= n) :
    (l1 ++ l2).getD n d = l2.getD (n - l1.length) d := by
  induction l1 generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at h
          simpa only [List.cons_append, List.getD_cons_succ, List.length_cons,
            Nat.succ_sub_succ_eq_sub] using ih n h

theorem app_Znth2 {A : Type u} (d : A) (l l' : List A) (i : Int)
    (h : i >= Zlength l) :
    Znth i (l ++ l') d = Znth (i - Zlength l) l' d := by
  cases i with
  | negSucc i =>
      exfalso
      exact (Int.negSucc_not_nonneg i).mp
        (Int.le_trans (Int.ofNat_zero_le l.length) h)
  | ofNat i =>
      unfold Znth
      simpa [Zlength] using
        getD_append_right d l l' i (Int.ofNat_le.mp h)

theorem Znth_indep {A : Type u} (l : List A) (n : Int) (d d' : A)
    (h : 0 <= n /\ n < Zlength l) : Znth n l d = Znth n l d' := by
  cases n with
  | negSucc n => omega
  | ofNat n =>
      have hn : n < l.length := by
        simp only [Zlength] at h
        exact Int.ofNat_lt.mp h.2
      unfold Znth
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

private theorem replace_nth_app_right {A : Type u} (n : Nat) (a : A)
    (l1 l2 : List A) (h : l1.length <= n) :
    replace_nth n (l1 ++ l2) a =
      replace_nth n l1 a ++ replace_nth (n - l1.length) l2 a := by
  induction l1 generalizing n with
  | nil => simp [replace_nth]
  | cons x xs ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at h
          simpa only [List.cons_append, replace_nth, List.length_cons,
            Nat.succ_sub_succ_eq_sub, List.cons.injEq, true_and] using ih n h

private theorem replace_nth_nothing {A : Type u} (n : Nat) (l : List A)
    (a : A) (h : l.length <= n) : replace_nth n l a = l := by
  induction l generalizing n with
  | nil => simp [replace_nth]
  | cons x xs ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [replace_nth, List.cons.injEq, true_and]
          exact ih n (by simpa using h)

theorem replace_Znth_app_r {A : Type u} (n : Int) (a : A)
    (l1 l2 : List A) (h : n >= Zlength l1) :
    replace_Znth n a (l1 ++ l2) =
      replace_Znth n a l1 ++ replace_Znth (n - Zlength l1) a l2 := by
  cases n with
  | negSucc n =>
      exfalso
      exact (Int.negSucc_not_nonneg n).mp
        (Int.le_trans (Int.ofNat_zero_le l1.length) h)
  | ofNat n =>
      unfold replace_Znth
      simpa [Zlength] using
        replace_nth_app_right n a l1 l2 (Int.ofNat_le.mp h)

theorem replace_Znth_nothing {A : Type u} (n : Int) (l : List A) (a : A)
    (h : n >= Zlength l) : replace_Znth n a l = l := by
  cases n with
  | negSucc n =>
      exfalso
      exact (Int.negSucc_not_nonneg n).mp
        (Int.le_trans (Int.ofNat_zero_le l.length) h)
  | ofNat n =>
      unfold replace_Znth
      exact replace_nth_nothing n l a (Int.ofNat_le.mp h)

theorem sublist_length {A : Type u} (lo hi : Int) (l : List A)
    (hlohi : 0 <= lo /\ lo <= hi) (hhi : hi <= Zlength l) :
    (sublist lo hi l).length = (hi - lo).toNat := by
  cases lo with
  | negSucc lo => omega
  | ofNat lo =>
      cases hi with
      | negSucc hi => omega
      | ofNat hi =>
          have hhiNat : hi <= l.length := by
            simp only [Zlength] at hhi
            exact Int.ofNat_le.mp hhi
          simp [sublist, Nat.min_eq_left hhiNat]

theorem sublist_app_exact1 {A : Type u} (l1 l2 : List A) :
    sublist 0 (Zlength l1) (l1 ++ l2) = l1 := by
  simp [sublist, Zlength]

theorem sublist_single {A : Type u} (d : A) (n : Int) (l : List A)
    (h : 0 <= n /\ n < Zlength l) :
    sublist n (n + 1) l = [Znth n l d] := by
  cases n with
  | negSucc n => omega
  | ofNat n =>
      have hn : n < l.length := by
        simp only [Zlength] at h
        exact Int.ofNat_lt.mp h.2
      unfold sublist Znth
      change (l.take (n + 1)).drop n = [l.getD n d]
      rw [List.drop_take]
      have hsub : n + 1 - n = 1 := by omega
      rw [hsub]
      have hd : l.drop n = l[n] :: l.drop (n + 1) :=
        List.drop_eq_getElem_cons hn
      have hget : l.getD n d = l[n] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
      calc
        List.take 1 (List.drop n l) = [l[n]] := by
          rw [hd]
          rfl
        _ = [l.getD n d] := congrArg (fun x => [x]) hget.symm

theorem sublist_split {A : Type u} (lo hi mid : Int) (l : List A)
    (hlomid : 0 <= lo /\ lo <= mid)
    (hmidhi : mid <= hi /\ hi <= Zlength l) :
    sublist lo hi l = sublist lo mid l ++ sublist mid hi l := by
  have hlo : 0 <= lo := hlomid.1
  have hmid : 0 <= mid := by omega
  have hhi : 0 <= hi := by omega
  unfold sublist
  simp only [List.drop_take]
  rw [show hi.toNat - lo.toNat =
      (mid.toNat - lo.toNat) + (hi.toNat - mid.toNat) by omega]
  rw [List.take_add]
  congr 1
  rw [List.drop_drop]
  congr 2 <;> omega

theorem sublist_split_app_r {A : Type u} (lo hi len : Int)
    (l1 l2 : List A) (hlen : Zlength l1 = len)
    (h : len <= lo /\ lo <= hi) :
    sublist lo hi (l1 ++ l2) = sublist (lo - len) (hi - len) l2 := by
  simp only [Zlength] at hlen
  subst len
  cases lo with
  | negSucc lo =>
      exfalso
      exact (Int.negSucc_not_nonneg lo).mp
        (Int.le_trans (Int.ofNat_zero_le l1.length) h.1)
  | ofNat lo =>
      cases hi with
      | negSucc hi =>
          exfalso
          exact (Int.negSucc_not_nonneg hi).mp
            (Int.le_trans (Int.ofNat_zero_le lo) h.2)
      | ofNat hi =>
          have hlo : l1.length <= lo := Int.ofNat_le.mp h.1
          have hhi : l1.length <= hi :=
            Nat.le_trans hlo (Int.ofNat_le.mp h.2)
          have hNat : (List.take hi (l1 ++ l2)).drop lo =
              (List.take (hi - l1.length) l2).drop (lo - l1.length) := by
            rw [List.take_append, List.take_of_length_le hhi, List.drop_append]
            simp [List.drop_eq_nil_of_le hlo]
          simpa [sublist] using hNat

private theorem getD_take_of_lt {A : Type u} (d : A) (l : List A)
    (bound index : Nat) (h : index < bound) :
    (l.take bound).getD index d = l.getD index d := by
  induction l generalizing bound index with
  | nil => simp
  | cons x xs ih =>
      cases bound with
      | zero => omega
      | succ bound =>
          cases index with
          | zero => rfl
          | succ index =>
              simp only [List.take_succ_cons, List.getD_cons_succ]
              exact ih bound index (by omega)

private theorem getD_drop {A : Type u} (d : A) (l : List A)
    (start index : Nat) :
    (l.drop start).getD index d = l.getD (start + index) d := by
  induction start generalizing l with
  | zero => simp
  | succ start ih =>
      cases l with
      | nil => simp
      | cons x xs =>
          simpa only [List.drop_succ_cons, Nat.succ_add,
            List.getD_cons_succ] using ih xs

theorem Znth_sublist {A : Type u} (d : A) (lo i hi : Int) (l : List A)
    (hlo : 0 <= lo) (hiRange : 0 <= i /\ i < hi - lo) :
    Znth i (sublist lo hi l) d = Znth (i + lo) l d := by
  unfold Znth sublist
  rw [List.drop_take]
  have hiNat : i.toNat < hi.toNat - lo.toNat := by omega
  rw [getD_take_of_lt d (l.drop lo.toNat) (hi.toNat - lo.toNat) i.toNat hiNat]
  rw [getD_drop]
  have hindex : (i + lo).toNat = lo.toNat + i.toNat := by omega
  rw [hindex]

theorem Znth_sublist_lt {A : Type u} (d : A) (lo hi : Int)
    (l : List A) (i : Int) (hlohi : 0 <= lo /\ lo <= hi)
    (hhi : hi <= Zlength l) (hiRange : 0 <= i /\ i < hi - lo) :
    Znth i (sublist lo hi l) d = Znth (lo + i) l d := by
  have hindex : 0 <= i + lo /\ i + lo < Zlength l := by omega
  calc
    Znth i (sublist lo hi l) d = Znth (i + lo) l d :=
      Znth_sublist d lo i hi l hlohi.1 hiRange
    _ = Znth (i + lo) l d := Znth_indep l (i + lo) d d hindex
    _ = Znth (lo + i) l d := by rw [Int.add_comm]

end AUXLib
