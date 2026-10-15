import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib
open AUXLib

def DeletePair (a b : List Int) : Prop :=
  ∃ i : Int, (0 ≤ i ∧ i < Zlength a - 1) ∧ Znth i a 0 = Znth (i + 1) a 0 ∧
    b = sublist 0 i a ++ sublist (i + 2) (Zlength a) a

def ReducedFrom (a b : List Int) : Prop :=
  ∃ st : List (List Int), st ≠ [] ∧ Znth 0 st [] = a ∧ Znth (Zlength st - 1) st [] = b ∧
    (∀ i : Int, (0 ≤ i ∧ i < Zlength st - 1) → DeletePair (Znth i st []) (Znth (i + 1) st [])) ∧
    ¬ ∃ q, DeletePair b q

def Pre (s : List Int) : Prop := True

def Spec (s out : List Int) : Prop := ReducedFrom s out


private theorem len_pos {A : Type u} (l : List A) (h : l ≠ []) : 0 < Zlength l := by
  cases l with
  | nil => contradiction
  | cons x xs => have := Zlength_nonneg xs; rw [Zlength_cons]; omega

private theorem nth_append {A : Type u} (d : A) (l l' : List A) (i : Int)
    (h : 0 ≤ i ∧ i < Zlength l) : Znth i (l ++ l') d = Znth i l d :=
  ListLib.app_Znth1 d l l' i h

private theorem sub_append {A : Type u} (lo hi : Int) (l l' : List A)
    (h : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l) :
    sublist lo hi (l ++ l') = sublist lo hi l :=
  ListLib.sublist_split_app_l lo hi l l' h hh

private theorem nth_prefix {A : Type u} (d : A) (i hi : Int) (l : List A)
    (h : 0 ≤ i ∧ i < hi) : Znth i (sublist 0 hi l) d = Znth i l d :=
  ListLib.Znth_sublist0 d i hi l h

private theorem len_prefix {A : Type u} (hi : Int) (l : List A)
    (h : 0 ≤ hi ∧ hi ≤ Zlength l) : Zlength (sublist 0 hi l) = hi :=
  ListLib.Zlength_sublist0 hi l h

private theorem len_snoc {A : Type u} (l : List A) (a : A) : Zlength (l ++ [a]) = Zlength l + 1 := by
  simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.zero_add]

theorem DeletePair_snoc__stack_transitions (a b : List Int) (c : Int)
    (h : DeletePair a b) : DeletePair (a ++ [c]) (b ++ [c]) := by
  rcases h with ⟨k, hk, he, rfl⟩
  refine ⟨k, by rw [len_snoc]; omega, ?_, ?_⟩
  · rw [nth_append 0 a [c] k (by omega), nth_append 0 a [c] (k + 1) (by omega)]
    exact he
  · rw [sublist_split (k + 2) (Zlength (a ++ [c])) (Zlength a) (a ++ [c])
      (by omega) (by rw [len_snoc]; omega)]
    rw [sub_append 0 k a [c] (by omega) (by omega),
      sub_append (k + 2) (Zlength a) a [c] (by omega) (by omega)]
    rw [sublist_split_app_r (Zlength a) (Zlength (a ++ [c])) (Zlength a) a [c] rfl
      (by rw [len_snoc]; omega), len_snoc]
    simp only [Int.sub_self, add_sub_cancel_left]
    change (sublist 0 k a ++ sublist (k + 2) (Zlength a) a) ++ [c] =
      sublist 0 k a ++ (sublist (k + 2) (Zlength a) a ++ [c])
    exact List.append_assoc _ _ _

theorem no_DeletePair_snoc__stack_transitions (st : List Int) (c : Int)
    (hn : ¬ ∃ q, DeletePair st q)
    (hb : st = [] ∨ Znth (Zlength st - 1) st 0 ≠ c) :
    ¬ ∃ q, DeletePair (st ++ [c]) q := by
  rintro ⟨q, k, hk, he, hq⟩
  rw [len_snoc] at hk
  by_cases hi : k < Zlength st - 1
  · apply hn
    refine ⟨_, k, ⟨hk.1, hi⟩, ?_, rfl⟩
    rw [nth_append 0 st [c] k (by omega), nth_append 0 st [c] (k + 1) (by omega)] at he
    exact he
  · have hk' : k = Zlength st - 1 := by omega
    rcases hb with rfl | hb
    · simp only [Zlength_nil] at hk; omega
    · subst k
      rw [nth_append 0 st [c] (Zlength st - 1) (by omega),
        app_Znth2 0 st [c] (Zlength st - 1 + 1) (by omega)] at he
      have heq : Zlength st - 1 + 1 - Zlength st = 0 := by omega
      rw [heq] at he
      exact hb he

theorem no_DeletePair_prefix__stack_transitions (st : List Int)
    (hn : ¬ ∃ q, DeletePair st q) :
    ¬ ∃ q, DeletePair (sublist 0 (Zlength st - 1) st) q := by
  rintro ⟨q, k, hk, he, hq⟩
  by_cases hs : st = []
  · subst st
    change 0 ≤ k ∧ k < -1 at hk
    omega
  · have hl := len_pos st hs
    rw [len_prefix _ st (by omega)] at hk
    apply hn
    refine ⟨_, k, by omega, ?_, rfl⟩
    rw [nth_prefix 0 k (Zlength st - 1) st (by omega),
      nth_prefix 0 (k + 1) (Zlength st - 1) st (by omega)] at he
    exact he

theorem DeletePair_last_equal__stack_transitions (st : List Int) (c : Int)
    (hs : st ≠ []) (hl : Znth (Zlength st - 1) st 0 = c) :
    DeletePair (st ++ [c]) (sublist 0 (Zlength st - 1) st) := by
  have hp := len_pos st hs
  refine ⟨Zlength st - 1, by rw [len_snoc]; omega, ?_, ?_⟩
  · rw [nth_append 0 st [c] _ (by omega), app_Znth2 0 st [c] _ (by omega)]
    have he : Zlength st - 1 + 1 - Zlength st = 0 := by omega
    rw [he]
    exact hl
  · rw [sub_append 0 (Zlength st - 1) st [c] (by omega) (by omega),
      Zsublist_nil (st ++ [c]) _ _ (by rw [len_snoc]; omega), List.append_nil]

theorem Zlength_map__stack_transitions {A : Type u} {B : Type v} (f : A → B) (l : List A) :
    Zlength (l.map f) = Zlength l := by simp only [Zlength, List.length_map]

theorem Znth_map__stack_transitions {A : Type u} {B : Type v} (f : A → B)
    (l : List A) (d : A) (db : B) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    Znth i (l.map f) db = f (Znth i l d) := by
  cases i with
  | negSucc n => omega
  | ofNat n =>
    have hn : n < l.length := Int.ofNat_lt.mp hi.2
    change (l.map f).getD n db = f (l.getD n d)
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem hn, Option.map_some, Option.getD_some]


theorem Spec_extend_keep_distinct__stack_transitions (xs st : List Int) (c : Int)
    (hs : Spec xs st) (hb : st = [] ∨ Znth (Zlength st - 1) st 0 ≠ c) :
    Spec (xs ++ [c]) (st ++ [c]) := by
  rcases hs with ⟨states, hne, hf, hl, ht, hn⟩
  have hlen := len_pos states hne
  refine ⟨states.map (fun l => l ++ [c]), ?_, ?_, ?_, ?_,
    no_DeletePair_snoc__stack_transitions st c hn hb⟩
  · intro he
    have hh := congrArg Zlength he
    rw [Zlength_map__stack_transitions, Zlength_nil] at hh
    omega
  · rw [Znth_map__stack_transitions _ states [] [] 0 (by omega), hf]
  · rw [Zlength_map__stack_transitions,
      Znth_map__stack_transitions _ states [] [] (Zlength states - 1) (by omega), hl]
  · intro k hk
    rw [Zlength_map__stack_transitions] at hk
    rw [Znth_map__stack_transitions _ states [] [] k (by omega),
      Znth_map__stack_transitions _ states [] [] (k + 1) (by omega)]
    exact DeletePair_snoc__stack_transitions _ _ c (ht k hk)

theorem Spec_extend_drop_equal__stack_transitions (xs st : List Int) (c : Int)
    (hs : Spec xs st) (hst : st ≠ []) (hb : Znth (Zlength st - 1) st 0 = c) :
    Spec (xs ++ [c]) (sublist 0 (Zlength st - 1) st) := by
  rcases hs with ⟨states, hne, hf, hl, ht, hn⟩
  let lifted := states.map (fun l => l ++ [c])
  let out := sublist 0 (Zlength st - 1) st
  have hlen := len_pos states hne
  have hllen : Zlength lifted = Zlength states := Zlength_map__stack_transitions _ states
  have hlift (i : Int) (hi : 0 ≤ i ∧ i < Zlength states) :
      Znth i lifted [] = Znth i states [] ++ [c] :=
    Znth_map__stack_transitions _ states [] [] i hi
  refine ⟨lifted ++ [out], ?_, ?_, ?_, ?_, no_DeletePair_prefix__stack_transitions st hn⟩
  · exact List.append_ne_nil_of_right_ne_nil _ (by intro h; cases h)
  · rw [nth_append [] lifted [out] 0 (by omega), hlift 0 (by omega), hf]
  · rw [len_snoc, app_Znth2 [] lifted [out] _ (by omega)]
    have he : Zlength lifted + 1 - 1 - Zlength lifted = 0 := by omega
    rw [he]
    rfl
  · intro k hk
    rw [len_snoc] at hk
    by_cases hi : k < Zlength lifted - 1
    · rw [nth_append [] lifted [out] k (by omega),
        nth_append [] lifted [out] (k + 1) (by omega),
        hlift k (by omega), hlift (k + 1) (by omega)]
      exact DeletePair_snoc__stack_transitions _ _ c (ht k (by omega))
    · have he : k = Zlength lifted - 1 := by omega
      subst k
      rw [nth_append [] lifted [out] _ (by omega),
        app_Znth2 [] lifted [out] _ (by omega)]
      have he : Zlength lifted - 1 + 1 - Zlength lifted = 0 := by omega
      rw [he, hlift _ (by omega), hllen, hl]
      exact DeletePair_last_equal__stack_transitions st c hst hb

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib
