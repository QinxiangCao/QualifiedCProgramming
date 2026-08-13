import AUXLib.ListLib.LengthCompat

namespace ListLib

universe u

abbrev Znth {A : Type u} := @AUXLib.Znth A
abbrev Znth_error {A : Type u} := @AUXLib.Znth_error A
abbrev tl_error {A : Type u} := @AUXLib.tl_error A
abbrev replace_nth {A : Type u} := @AUXLib.replace_nth A
abbrev replace_Znth {A : Type u} := @AUXLib.replace_Znth A
abbrev Nsublist {A : Type u} := @AUXLib.Nsublist A
abbrev sublist {A : Type u} := @AUXLib.sublist A
abbrev Zlength {A : Type u} := @AUXLib.Zlength A

abbrev Znth_cons {A : Type u} := @AUXLib.Znth_cons A
abbrev Znth_error_cons {A : Type u} := @AUXLib.Znth_error_cons A
abbrev Znth_repeat {A : Type u} := @AUXLib.Znth_repeat A
abbrev Znth_repeat_lt {A : Type u} := @AUXLib.Znth_repeat_lt A
abbrev replace_Znth_cons {A : Type u} := @AUXLib.replace_Znth_cons A
abbrev replace_Znth_Znth {A : Type u} := @AUXLib.replace_Znth_Znth A
abbrev Znth_replace_Znth_Same {A : Type u} := @AUXLib.Znth_replace_Znth_Same A
abbrev Znth_replace_Znth_Diff {A : Type u} := @AUXLib.Znth_replace_Znth_Diff A
abbrev Zsublist_nil {A : Type u} := @AUXLib.Zsublist_nil A
abbrev Zsublist_of_nil {A : Type u} := @AUXLib.Zsublist_of_nil A

theorem Znth0_cons {A : Type} (d a : A) (l : List A) :
    Znth 0 (a :: l) d = a := rfl

private theorem Nsublist_Nsublist {A : Type} (i j k m : Nat) (l : List A)
    (hki : k <= i) (hij : i + m <= j) :
    ((((l.take j).drop m).take i).drop k) =
      (l.take (i + m)).drop (k + m) := by
  rw [List.drop_take, List.drop_drop, List.drop_take]
  rw [List.take_take, List.drop_take]
  have hmin : i - k <= j - (m + k) := by omega
  have hsub : i + m - (k + m) = i - k := by omega
  rw [Nat.min_eq_left hmin, hsub, Nat.add_comm k m]

theorem Zsublist_Zsublist {A : Type} (i j k m : Int) (l : List A)
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

theorem Zsublist_Zsublist0 {A : Type} (i j k : Int) (l : List A)
    (hk : 0 <= k) (hki : k <= i /\ i <= j) :
    sublist k i (sublist 0 j l) = sublist k i l := by
  simpa using Zsublist_Zsublist i j k 0 l (by omega) ⟨hk, hki.1⟩ (by omega)

theorem Zsublist_Zsublist00 {A : Type} (i j : Int) (l : List A)
    (h : 0 <= i /\ i <= j) :
    sublist 0 i (sublist 0 j l) = sublist 0 i l := by
  exact Zsublist_Zsublist0 i j 0 l (by omega) ⟨by omega, h.2⟩

end ListLib
