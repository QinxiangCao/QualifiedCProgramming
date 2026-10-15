import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array

private theorem shape_rec (storeA : Int → Int → Int → SacContext.rules.expr)
    (k : Nat) (x lo hi : Int) :
    store_undef_array_rec SacContext.rules (fun x lo => EX a : Int, storeA x lo a) x lo hi k |--
      EX l : List Int, store_array_rec SacContext.rules storeA x lo hi l := by
  induction k generalizing lo with
  | zero =>
    simp only [store_undef_array_rec]
    Intros_p he
    Exists ([] : List Int)
    simp only [store_array_rec]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals solve | assumption | rfl | trivial
  | succ k ih =>
    simp only [store_undef_array_rec]
    Intros a
    sep_apply (ih (lo+1))
    Intros l
    Exists (a::l)
    simp only [store_array_rec]
    cancel

private theorem shape_full (x n : Int) :
    int64Array.full_shape x n |-- EX l : List Int, int64Array.full x n l := by
  apply shape_rec

private theorem prefix_length (l : List Int) (n : Int) (hn : 0 ≤ n ∧ n ≤ Zlength l) :
    Zlength (sublist 0 n l) = n := by
  have h : Zlength (sublist 0 n l)=n-0 := ListLib.Zlength_sublist 0 n l (by omega) hn.2
  omega

private theorem prefix_nth (l : List Int) (n q : Int) (hq : 0 ≤ q ∧ q < n) :
    Znth q (sublist 0 n l) 0 = Znth q l 0 := by
  simpa only [Int.add_zero] using Znth_sublist 0 0 q n l (by omega) (by omega)

private theorem prefix_succ (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    sublist 0 (i+1) l = sublist 0 i l ++ [Znth i l 0] := by
  rw [sublist_split 0 (i+1) i l (by omega) (by omega),sublist_single 0 i l hi]

theorem proof_of_hpush_entail_wit_1_split_goal_1 : hpush_entail_wit_1_split_goal_1 := by
  intro v_pre sm hs l cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact push_sift_state_init__hpush_sift_up l hs v_pre PreH1 (by omega) PreH5

theorem proof_of_hpush_entail_wit_1_split_goal_2 : hpush_entail_wit_1_split_goal_2 := by
  intro v_pre sm hs l cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  intro q hq
  by_cases he : q = hs
  · subst q
    rw [Znth_replace_Znth_Same 0 l hs v_pre (by omega)]
    omega
  · rw [Znth_replace_Znth_Diff 0 l hs q v_pre (by omega) (by omega) (Ne.symm he)]
    exact PreH7 q (by omega)

theorem proof_of_hpush_entail_wit_1_split_goal_3 : hpush_entail_wit_1_split_goal_3 := by
  intro v_pre sm hs l cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simpa only [Zlength_replace_Znth] using PreH4

theorem proof_of_hpush_entail_wit_1 : hpush_entail_wit_1 := by
  unfold hpush_entail_wit_1
  right
  intro v_pre sm hs l cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpush_entail_wit_1_split_goal_1 v_pre sm hs l cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_hpush_entail_wit_1_split_goal_2 v_pre sm hs l cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_hpush_entail_wit_1_split_goal_3 v_pre sm hs l cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_hpush_entail_wit_2_split_goal_1 : hpush_entail_wit_2_split_goal_1 := by
  intro v_pre sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH13

theorem proof_of_hpush_entail_wit_2_split_goal_2 : hpush_entail_wit_2_split_goal_2 := by
  intro v_pre sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  rfl

theorem proof_of_hpush_entail_wit_2_split_goal_3 : hpush_entail_wit_2_split_goal_3 := by
  intro v_pre sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have h := heap_parent_range__hpush_sift_up i PreH1
  change 0 ≤ Z.quot (i-1) 2 ∧ Z.quot (i-1) 2 < i at h
  omega

theorem proof_of_hpush_entail_wit_2_split_goal_4 : hpush_entail_wit_2_split_goal_4 := by
  intro v_pre sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have h := heap_parent_range__hpush_sift_up i PreH1
  change 0 ≤ Z.quot (i-1) 2 ∧ Z.quot (i-1) 2 < i at h
  omega

theorem proof_of_hpush_entail_wit_2 : hpush_entail_wit_2 := by
  unfold hpush_entail_wit_2
  right
  intro v_pre sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpush_entail_wit_2_split_goal_1 v_pre sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_hpush_entail_wit_2_split_goal_2 v_pre sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_hpush_entail_wit_2_split_goal_3 v_pre sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_hpush_entail_wit_2_split_goal_4 v_pre sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_hpush_entail_wit_3_split_goal_1 : hpush_entail_wit_3_split_goal_1 := by
  intro v_pre sm hs l cap cur_2 i p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact push_sift_state_swap__hpush_sift_up l cur_2 hs i p v_pre PreH2 (by omega) PreH7 PreH8 PreH11 PreH1 PreH17

theorem proof_of_hpush_entail_wit_3_split_goal_2 : hpush_entail_wit_3_split_goal_2 := by
  intro v_pre sm hs l cap cur_2 i p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro q hq
  have hz := Zlength_replace_Znth cur_2 p (Znth i cur_2 0)
  by_cases he : q = i
  · subst q
    rw [Znth_replace_Znth_Same 0 _ i _ (by omega)]
    exact PreH16 p (by omega)
  · rw [Znth_replace_Znth_Diff 0 _ i q _ (by omega) (by omega) (Ne.symm he)]
    by_cases hp : q = p
    · subst q
      rw [Znth_replace_Znth_Same 0 cur_2 p _ (by omega)]
      exact PreH16 i (by omega)
    · rw [Znth_replace_Znth_Diff 0 cur_2 p q _ (by omega) (by omega) (Ne.symm hp)]
      exact PreH16 q hq

theorem proof_of_hpush_entail_wit_3_split_goal_3 : hpush_entail_wit_3_split_goal_3 := by
  intro v_pre sm hs l cap cur_2 i p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simpa only [Zlength_replace_Znth] using PreH6

theorem proof_of_hpush_entail_wit_3 : hpush_entail_wit_3 := by
  unfold hpush_entail_wit_3
  right
  intro v_pre sm hs l cap cur_2 i p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpush_entail_wit_3_split_goal_1 v_pre sm hs l cap cur_2 i p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpush_entail_wit_3_split_goal_2 v_pre sm hs l cap cur_2 i p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpush_entail_wit_3_split_goal_3 v_pre sm hs l cap cur_2 i p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_hpush_return_wit_1_split_goal_1 : hpush_return_wit_1_split_goal_1 := by
  intro v_pre sm hs l cap i_2 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH13

theorem proof_of_hpush_return_wit_1_split_goal_2 : hpush_return_wit_1_split_goal_2 := by
  intro v_pre sm hs l cap i_2 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH14.2.2.1

theorem proof_of_hpush_return_wit_1_split_goal_3 : hpush_return_wit_1_split_goal_3 := by
  intro v_pre sm hs l cap i_2 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  apply push_sift_state_to_heap_ordered__hpush_sift_up l cur hs i_2 v_pre PreH14
  exact Or.inl (by omega)

theorem proof_of_hpush_return_wit_1 : hpush_return_wit_1 := by
  unfold hpush_return_wit_1
  right
  intro v_pre sm hs l cap i_2 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpush_return_wit_1_split_goal_1 v_pre sm hs l cap i_2 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_hpush_return_wit_1_split_goal_2 v_pre sm hs l cap i_2 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_hpush_return_wit_1_split_goal_3 v_pre sm hs l cap i_2 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_hpush_return_wit_2_split_goal_1 : hpush_return_wit_2_split_goal_1 := by
  intro v_pre sm hs l cap cur i_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH16

theorem proof_of_hpush_return_wit_2_split_goal_2 : hpush_return_wit_2_split_goal_2 := by
  intro v_pre sm hs l cap cur i_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH17.2.2.1

theorem proof_of_hpush_return_wit_2_split_goal_3 : hpush_return_wit_2_split_goal_3 := by
  intro v_pre sm hs l cap cur i_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply push_sift_state_to_heap_ordered__hpush_sift_up l cur hs i_2 v_pre PreH17
  right
  simpa only [← PreH11] using PreH1

theorem proof_of_hpush_return_wit_2 : hpush_return_wit_2 := by
  unfold hpush_return_wit_2
  right
  intro v_pre sm hs l cap cur i_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpush_return_wit_2_split_goal_1 v_pre sm hs l cap cur i_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpush_return_wit_2_split_goal_2 v_pre sm hs l cap cur i_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpush_return_wit_2_split_goal_3 v_pre sm hs l cap cur i_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_hpop_entail_wit_1 : hpop_entail_wit_1 := by
  intro hsum_pre hsize_pre heap_pre sm hs l cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  Left
  Exists (replace_Znth 0 (Znth (hs-1) l 0) l)
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve
      | assumption
      | (repeat constructor <;> assumption)
      | omega
      | simpa only [Zlength_replace_Znth] using PreH4
      | exact fun q hq => heap_root_is_max__hpop_sift_left_child l hs q PreH5 hq
      | exact fun q hq => pop_init_bounds__hpop_sift_left_child l hs cap q PreH1 PreH2 PreH4 PreH7 hq
      | exact pop_sift_state_init__hpop_sift_left_child l hs cap PreH1 PreH2 PreH4 PreH5

theorem proof_of_hpop_entail_wit_2_1_split_goal_1 : hpop_entail_wit_2_1_split_goal_1 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  subst i
  apply pop_sift_state_swap_right__hpop_sift_right_child l cur_2 hs 0
  all_goals first | assumption | omega

theorem proof_of_hpop_entail_wit_2_1_split_goal_2 : hpop_entail_wit_2_1_split_goal_2 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simpa only [Zlength_replace_Znth] using PreH10

theorem proof_of_hpop_entail_wit_2_1 : hpop_entail_wit_2_1 := by
  unfold hpop_entail_wit_2_1
  right
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_entail_wit_2_1_split_goal_1 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_hpop_entail_wit_2_1_split_goal_2 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_hpop_entail_wit_2_2_split_goal_1 : hpop_entail_wit_2_2_split_goal_1 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  apply pop_sift_state_swap_right__hpop_sift_right_child l cur_2 hs i
  all_goals first | assumption | omega

theorem proof_of_hpop_entail_wit_2_2_split_goal_2 : hpop_entail_wit_2_2_split_goal_2 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simpa only [Zlength_replace_Znth] using PreH10

theorem proof_of_hpop_entail_wit_2_2 : hpop_entail_wit_2_2 := by
  unfold hpop_entail_wit_2_2
  right
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_entail_wit_2_2_split_goal_1 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_hpop_entail_wit_2_2_split_goal_2 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_hpop_entail_wit_2_3_split_goal_1 : hpop_entail_wit_2_3_split_goal_1 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  subst i
  apply pop_sift_state_swap_right__hpop_sift_right_child l cur_2 hs 0
  all_goals first | assumption | omega

theorem proof_of_hpop_entail_wit_2_3_split_goal_2 : hpop_entail_wit_2_3_split_goal_2 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simpa only [Zlength_replace_Znth] using PreH10

theorem proof_of_hpop_entail_wit_2_3 : hpop_entail_wit_2_3 := by
  unfold hpop_entail_wit_2_3
  right
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_entail_wit_2_3_split_goal_1 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_hpop_entail_wit_2_3_split_goal_2 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_hpop_entail_wit_2_4_split_goal_1 : hpop_entail_wit_2_4_split_goal_1 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  apply pop_sift_state_swap_right__hpop_sift_right_child l cur_2 hs i
  all_goals first | assumption | omega

theorem proof_of_hpop_entail_wit_2_4_split_goal_2 : hpop_entail_wit_2_4_split_goal_2 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simpa only [Zlength_replace_Znth] using PreH10

theorem proof_of_hpop_entail_wit_2_4 : hpop_entail_wit_2_4 := by
  unfold hpop_entail_wit_2_4
  right
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_entail_wit_2_4_split_goal_1 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_hpop_entail_wit_2_4_split_goal_2 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_hpop_entail_wit_2_5_split_goal_1 : hpop_entail_wit_2_5_split_goal_1 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply pop_sift_state_swap_left__hpop_sift_left_child l cur_2 hs cap i
  all_goals first | assumption | omega | (intro h; simp only [show 2*i+2 = 2*i+1+1 by omega]; omega)

theorem proof_of_hpop_entail_wit_2_5_split_goal_2 : hpop_entail_wit_2_5_split_goal_2 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simpa only [Zlength_replace_Znth] using PreH9

theorem proof_of_hpop_entail_wit_2_5 : hpop_entail_wit_2_5 := by
  unfold hpop_entail_wit_2_5
  right
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_entail_wit_2_5_split_goal_1 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpop_entail_wit_2_5_split_goal_2 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_hpop_entail_wit_2_6_split_goal_1 : hpop_entail_wit_2_6_split_goal_1 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  subst i
  apply pop_sift_state_swap_left__hpop_sift_left_child l cur_2 hs cap 0
  all_goals first | assumption | omega | (intro h; simp only [show 2*0+2 = 2*0+1+1 by omega]; omega)

theorem proof_of_hpop_entail_wit_2_6_split_goal_2 : hpop_entail_wit_2_6_split_goal_2 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simpa only [Zlength_replace_Znth] using PreH9

theorem proof_of_hpop_entail_wit_2_6 : hpop_entail_wit_2_6 := by
  unfold hpop_entail_wit_2_6
  right
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_entail_wit_2_6_split_goal_1 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpop_entail_wit_2_6_split_goal_2 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_hpop_entail_wit_2_7_split_goal_1 : hpop_entail_wit_2_7_split_goal_1 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  subst i
  apply pop_sift_state_swap_left__hpop_sift_left_child l cur_2 hs cap 0
  all_goals first | assumption | omega | (intro h; exact PreH2)

theorem proof_of_hpop_entail_wit_2_7_split_goal_2 : hpop_entail_wit_2_7_split_goal_2 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simpa only [Zlength_replace_Znth] using PreH10

theorem proof_of_hpop_entail_wit_2_7 : hpop_entail_wit_2_7 := by
  unfold hpop_entail_wit_2_7
  right
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_entail_wit_2_7_split_goal_1 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_hpop_entail_wit_2_7_split_goal_2 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_hpop_entail_wit_2_8_split_goal_1 : hpop_entail_wit_2_8_split_goal_1 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  apply pop_sift_state_swap_left__hpop_sift_left_child l cur_2 hs cap i
  all_goals first | assumption | omega | (intro h; simp only [show 2*i+2 = 2*i+1+1 by omega]; omega)

theorem proof_of_hpop_entail_wit_2_8_split_goal_2 : hpop_entail_wit_2_8_split_goal_2 := by
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simpa only [Zlength_replace_Znth] using PreH10

theorem proof_of_hpop_entail_wit_2_8 : hpop_entail_wit_2_8 := by
  unfold hpop_entail_wit_2_8
  right
  intro sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_entail_wit_2_8_split_goal_1 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_hpop_entail_wit_2_8_split_goal_2 sm hs l cap i cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_hpop_return_wit_1_split_goal_1 : hpop_return_wit_1_split_goal_1 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH14

theorem proof_of_hpop_return_wit_1_split_goal_2 : hpop_return_wit_1_split_goal_2 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  omega

theorem proof_of_hpop_return_wit_1_split_goal_3 : hpop_return_wit_1_split_goal_3 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact pop_perm_extract_root__hpop_return l cur hs i_3 PreH15 (by omega) (by omega)

theorem proof_of_hpop_return_wit_1_split_goal_4 : hpop_return_wit_1_split_goal_4 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  apply pop_sift_state_exit__hpop_return l cur hs i_3 PreH15 (by omega)
  all_goals intro h; omega

theorem proof_of_hpop_return_wit_1 : hpop_return_wit_1 := by
  unfold hpop_return_wit_1
  right
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_return_wit_1_split_goal_1 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_hpop_return_wit_1_split_goal_2 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_hpop_return_wit_1_split_goal_3 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_hpop_return_wit_1_split_goal_4 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_hpop_return_wit_2_split_goal_1 : hpop_return_wit_2_split_goal_1 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH14

theorem proof_of_hpop_return_wit_2_split_goal_2 : hpop_return_wit_2_split_goal_2 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  omega

theorem proof_of_hpop_return_wit_2_split_goal_3 : hpop_return_wit_2_split_goal_3 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact pop_perm_extract_root__hpop_return l cur hs i_3 PreH15 (by omega) (by omega)

theorem proof_of_hpop_return_wit_2_split_goal_4 : hpop_return_wit_2_split_goal_4 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  apply pop_sift_state_exit__hpop_return l cur hs i_3 PreH15 (by omega)
  all_goals intro h; omega

theorem proof_of_hpop_return_wit_2 : hpop_return_wit_2 := by
  unfold hpop_return_wit_2
  right
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_return_wit_2_split_goal_1 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_hpop_return_wit_2_split_goal_2 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_hpop_return_wit_2_split_goal_3 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_hpop_return_wit_2_split_goal_4 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_hpop_return_wit_3_split_goal_1 : hpop_return_wit_3_split_goal_1 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH15

theorem proof_of_hpop_return_wit_3_split_goal_2 : hpop_return_wit_3_split_goal_2 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  omega

theorem proof_of_hpop_return_wit_3_split_goal_3 : hpop_return_wit_3_split_goal_3 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact pop_perm_extract_root__hpop_return l cur hs i_3 PreH16 (by omega) (by omega)

theorem proof_of_hpop_return_wit_3_split_goal_4 : hpop_return_wit_3_split_goal_4 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  apply pop_sift_state_exit__hpop_return l cur hs i_3 PreH16 (by omega)
  all_goals intro h; omega

theorem proof_of_hpop_return_wit_3 : hpop_return_wit_3 := by
  unfold hpop_return_wit_3
  right
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_return_wit_3_split_goal_1 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_hpop_return_wit_3_split_goal_2 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_hpop_return_wit_3_split_goal_3 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_hpop_return_wit_3_split_goal_4 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_hpop_return_wit_4_split_goal_1 : hpop_return_wit_4_split_goal_1 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH15

theorem proof_of_hpop_return_wit_4_split_goal_2 : hpop_return_wit_4_split_goal_2 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  omega

theorem proof_of_hpop_return_wit_4_split_goal_3 : hpop_return_wit_4_split_goal_3 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact pop_perm_extract_root__hpop_return l cur hs i_3 PreH16 (by omega) (by omega)

theorem proof_of_hpop_return_wit_4_split_goal_4 : hpop_return_wit_4_split_goal_4 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  apply pop_sift_state_exit__hpop_return l cur hs i_3 PreH16 (by omega)
  all_goals intro h; omega

theorem proof_of_hpop_return_wit_4 : hpop_return_wit_4 := by
  unfold hpop_return_wit_4
  right
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_return_wit_4_split_goal_1 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_hpop_return_wit_4_split_goal_2 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_hpop_return_wit_4_split_goal_3 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_hpop_return_wit_4_split_goal_4 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_hpop_return_wit_5_split_goal_1 : hpop_return_wit_5_split_goal_1 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH16

theorem proof_of_hpop_return_wit_5_split_goal_2 : hpop_return_wit_5_split_goal_2 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  omega

theorem proof_of_hpop_return_wit_5_split_goal_3 : hpop_return_wit_5_split_goal_3 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact pop_perm_extract_root__hpop_return l cur hs i_3 PreH17 (by omega) (by omega)

theorem proof_of_hpop_return_wit_5_split_goal_4 : hpop_return_wit_5_split_goal_4 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply pop_sift_state_exit__hpop_return l cur hs i_3 PreH17 (by omega)
  all_goals intro h; omega

theorem proof_of_hpop_return_wit_5 : hpop_return_wit_5 := by
  unfold hpop_return_wit_5
  right
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_return_wit_5_split_goal_1 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpop_return_wit_5_split_goal_2 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpop_return_wit_5_split_goal_3 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpop_return_wit_5_split_goal_4 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_hpop_return_wit_6_split_goal_1 : hpop_return_wit_6_split_goal_1 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH16

theorem proof_of_hpop_return_wit_6_split_goal_2 : hpop_return_wit_6_split_goal_2 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  omega

theorem proof_of_hpop_return_wit_6_split_goal_3 : hpop_return_wit_6_split_goal_3 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact pop_perm_extract_root__hpop_return l cur hs i_3 PreH17 (by omega) (by omega)

theorem proof_of_hpop_return_wit_6_split_goal_4 : hpop_return_wit_6_split_goal_4 := by
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply pop_sift_state_exit__hpop_return l cur hs i_3 PreH17 (by omega)
  all_goals intro h; omega

theorem proof_of_hpop_return_wit_6 : hpop_return_wit_6 := by
  unfold hpop_return_wit_6
  right
  intro sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_hpop_return_wit_6_split_goal_1 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpop_return_wit_6_split_goal_2 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpop_return_wit_6_split_goal_3 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_hpop_return_wit_6_split_goal_4 sm hs l cap i_3 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_sift_candidates_entail_wit_1_split_goal_1 : sift_candidates_entail_wit_1_split_goal_1 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  exact sift_state_init__sift_cand_step t0 b0 (hi_pre+1) root_pre (by omega) PreH7

theorem proof_of_sift_candidates_entail_wit_1_split_goal_2 : sift_candidates_entail_wit_1_split_goal_2 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  exact PreH8

theorem proof_of_sift_candidates_entail_wit_1 : sift_candidates_entail_wit_1 := by
  unfold sift_candidates_entail_wit_1
  right
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sift_candidates_entail_wit_1_split_goal_1 hi_pre root_pre bhi blo thi tlo b0 t0 cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_sift_candidates_entail_wit_1_split_goal_2 hi_pre root_pre bhi blo thi tlo b0 t0 cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8

theorem proof_of_sift_candidates_entail_wit_2_1_split_goal_1 : sift_candidates_entail_wit_2_1_split_goal_1 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hz := PreH13.1.2.1
  apply sift_state_swap__sift_cand_step t0 b0 t_2 b_2 (hi_pre+1) root_pre root (2*root+1+1)
  all_goals first
    | assumption
    | omega
    | exact heap_parent_child__sift_cand_step _ root (by omega) (by omega)
    | (intro s hs0 hsz hp
       rcases heap_parent_inv__sift_cand_step s root hs0 hp with he | he
       · subst s; omega
       · subst s
         have hcanon : 2*root+2 = 2*root+1+1 := by omega
         rw [hcanon] <;> omega)

theorem proof_of_sift_candidates_entail_wit_2_1_split_goal_2 : sift_candidates_entail_wit_2_1_split_goal_2 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [Zlength_replace_Znth]
  omega

theorem proof_of_sift_candidates_entail_wit_2_1_split_goal_3 : sift_candidates_entail_wit_2_1_split_goal_3 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [Zlength_replace_Znth]
  omega

theorem proof_of_sift_candidates_entail_wit_2_1 : sift_candidates_entail_wit_2_1 := by
  unfold sift_candidates_entail_wit_2_1
  right
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sift_candidates_entail_wit_2_1_split_goal_1 hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_entail_wit_2_1_split_goal_2 hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_entail_wit_2_1_split_goal_3 hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_sift_candidates_entail_wit_2_2_split_goal_1 : sift_candidates_entail_wit_2_2_split_goal_1 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hz := PreH12.1.2.1
  apply sift_state_swap__sift_cand_step t0 b0 t_2 b_2 (hi_pre+1) root_pre root (2*root+1)
  all_goals first
    | assumption
    | omega
    | exact heap_parent_child__sift_cand_step _ root (by omega) (by omega)
    | (intro s hs0 hsz hp
       rcases heap_parent_inv__sift_cand_step s root hs0 hp with he | he
       · subst s; omega
       · subst s
         have hcanon : 2*root+2 = 2*root+1+1 := by omega
         rw [hcanon]
         omega)

theorem proof_of_sift_candidates_entail_wit_2_2_split_goal_2 : sift_candidates_entail_wit_2_2_split_goal_2 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simp only [Zlength_replace_Znth]
  omega

theorem proof_of_sift_candidates_entail_wit_2_2_split_goal_3 : sift_candidates_entail_wit_2_2_split_goal_3 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simp only [Zlength_replace_Znth]
  omega

theorem proof_of_sift_candidates_entail_wit_2_2 : sift_candidates_entail_wit_2_2 := by
  unfold sift_candidates_entail_wit_2_2
  right
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sift_candidates_entail_wit_2_2_split_goal_1 hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sift_candidates_entail_wit_2_2_split_goal_2 hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sift_candidates_entail_wit_2_2_split_goal_3 hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_sift_candidates_entail_wit_2_3_split_goal_1 : sift_candidates_entail_wit_2_3_split_goal_1 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hz := PreH13.1.2.1
  apply sift_state_swap__sift_cand_step t0 b0 t_2 b_2 (hi_pre+1) root_pre root (2*root+1)
  all_goals first
    | assumption
    | omega
    | exact heap_parent_child__sift_cand_step _ root (by omega) (by omega)
    | (intro s hs0 hsz hp
       rcases heap_parent_inv__sift_cand_step s root hs0 hp with he | he
       · subst s; omega
       · subst s
         have hcanon : 2*root+2 = 2*root+1+1 := by omega
         rw [hcanon]
         omega)

theorem proof_of_sift_candidates_entail_wit_2_3_split_goal_2 : sift_candidates_entail_wit_2_3_split_goal_2 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [Zlength_replace_Znth]
  omega

theorem proof_of_sift_candidates_entail_wit_2_3_split_goal_3 : sift_candidates_entail_wit_2_3_split_goal_3 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [Zlength_replace_Znth]
  omega

theorem proof_of_sift_candidates_entail_wit_2_3 : sift_candidates_entail_wit_2_3 := by
  unfold sift_candidates_entail_wit_2_3
  right
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sift_candidates_entail_wit_2_3_split_goal_1 hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_entail_wit_2_3_split_goal_2 hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_entail_wit_2_3_split_goal_3 hi_pre root_pre bhi blo thi tlo b0 t0 cap b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_sift_candidates_return_wit_1_split_goal_1 : sift_candidates_return_wit_1_split_goal_1 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH12

theorem proof_of_sift_candidates_return_wit_1_split_goal_2 : sift_candidates_return_wit_1_split_goal_2 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have h1 := PreH13.1.1
  have h2 := PreH13.1.2.1
  have hz : cap = Zlength b0 := by omega
  simpa only [hz] using PreH13.2.2.1

theorem proof_of_sift_candidates_return_wit_1_split_goal_3 : sift_candidates_return_wit_1_split_goal_3 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have h2 := PreH13.1.2.1
  have hz : cap = Zlength t0 := by omega
  simpa only [hz] using PreH13.2.1

theorem proof_of_sift_candidates_return_wit_1_split_goal_4 : sift_candidates_return_wit_1_split_goal_4 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH13.1

theorem proof_of_sift_candidates_return_wit_1_split_goal_5 : sift_candidates_return_wit_1_split_goal_5 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  apply sift_state_exit__sift_cand_exit t0 b0 t b (hi_pre+1) root_pre root PreH13
  intro child hc0 hcs hp
  rcases heap_parent_children__sift_cand_exit child root hc0 hp with he | he
  · subst child; omega
  · subst child; omega

theorem proof_of_sift_candidates_return_wit_1 : sift_candidates_return_wit_1 := by
  unfold sift_candidates_return_wit_1
  right
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sift_candidates_return_wit_1_split_goal_1 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_return_wit_1_split_goal_2 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_return_wit_1_split_goal_3 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_return_wit_1_split_goal_4 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_return_wit_1_split_goal_5 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_sift_candidates_return_wit_2_split_goal_1 : sift_candidates_return_wit_2_split_goal_1 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH11

theorem proof_of_sift_candidates_return_wit_2_split_goal_2 : sift_candidates_return_wit_2_split_goal_2 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have h1 := PreH12.1.1
  have h2 := PreH12.1.2.1
  have hz : cap = Zlength b0 := by omega
  simpa only [hz] using PreH12.2.2.1

theorem proof_of_sift_candidates_return_wit_2_split_goal_3 : sift_candidates_return_wit_2_split_goal_3 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have h2 := PreH12.1.2.1
  have hz : cap = Zlength t0 := by omega
  simpa only [hz] using PreH12.2.1

theorem proof_of_sift_candidates_return_wit_2_split_goal_4 : sift_candidates_return_wit_2_split_goal_4 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH12.1

theorem proof_of_sift_candidates_return_wit_2_split_goal_5 : sift_candidates_return_wit_2_split_goal_5 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  apply sift_state_exit__sift_cand_exit t0 b0 t b (hi_pre+1) root_pre root PreH12
  intro child hc0 hcs hp
  rcases heap_parent_children__sift_cand_exit child root hc0 hp with he | he
  · subst child; omega
  · subst child; omega

theorem proof_of_sift_candidates_return_wit_2 : sift_candidates_return_wit_2 := by
  unfold sift_candidates_return_wit_2
  right
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sift_candidates_return_wit_2_split_goal_1 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sift_candidates_return_wit_2_split_goal_2 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sift_candidates_return_wit_2_split_goal_3 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sift_candidates_return_wit_2_split_goal_4 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sift_candidates_return_wit_2_split_goal_5 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_sift_candidates_return_wit_3_split_goal_1 : sift_candidates_return_wit_3_split_goal_1 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH12

theorem proof_of_sift_candidates_return_wit_3_split_goal_2 : sift_candidates_return_wit_3_split_goal_2 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have h1 := PreH13.1.1
  have h2 := PreH13.1.2.1
  have hz : cap = Zlength b0 := by omega
  simpa only [hz] using PreH13.2.2.1

theorem proof_of_sift_candidates_return_wit_3_split_goal_3 : sift_candidates_return_wit_3_split_goal_3 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have h2 := PreH13.1.2.1
  have hz : cap = Zlength t0 := by omega
  simpa only [hz] using PreH13.2.1

theorem proof_of_sift_candidates_return_wit_3_split_goal_4 : sift_candidates_return_wit_3_split_goal_4 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH13.1

theorem proof_of_sift_candidates_return_wit_3_split_goal_5 : sift_candidates_return_wit_3_split_goal_5 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  apply sift_state_exit__sift_cand_exit t0 b0 t b (hi_pre+1) root_pre root PreH13
  intro child hc0 hcs hp
  rcases heap_parent_children__sift_cand_exit child root hc0 hp with he | he
  · subst child; omega
  · subst child; omega

theorem proof_of_sift_candidates_return_wit_3 : sift_candidates_return_wit_3 := by
  unfold sift_candidates_return_wit_3
  right
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sift_candidates_return_wit_3_split_goal_1 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_return_wit_3_split_goal_2 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_return_wit_3_split_goal_3 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_return_wit_3_split_goal_4 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sift_candidates_return_wit_3_split_goal_5 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_sift_candidates_return_wit_4_split_goal_1 : sift_candidates_return_wit_4_split_goal_1 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact PreH9

theorem proof_of_sift_candidates_return_wit_4_split_goal_2 : sift_candidates_return_wit_4_split_goal_2 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have h1 := PreH10.1.1
  have h2 := PreH10.1.2.1
  have hz : cap = Zlength b0 := by omega
  simpa only [hz] using PreH10.2.2.1

theorem proof_of_sift_candidates_return_wit_4_split_goal_3 : sift_candidates_return_wit_4_split_goal_3 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have h2 := PreH10.1.2.1
  have hz : cap = Zlength t0 := by omega
  simpa only [hz] using PreH10.2.1

theorem proof_of_sift_candidates_return_wit_4_split_goal_4 : sift_candidates_return_wit_4_split_goal_4 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact PreH10.1

theorem proof_of_sift_candidates_return_wit_4_split_goal_5 : sift_candidates_return_wit_4_split_goal_5 := by
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  apply sift_state_exit__sift_cand_exit t0 b0 t b (hi_pre+1) root_pre root PreH10
  intro child hc0 hcs hp
  rcases heap_parent_children__sift_cand_exit child root hc0 hp with he | he
  · subst child; omega
  · subst child; omega

theorem proof_of_sift_candidates_return_wit_4 : sift_candidates_return_wit_4 := by
  unfold sift_candidates_return_wit_4
  right
  intro hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sift_candidates_return_wit_4_split_goal_1 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sift_candidates_return_wit_4_split_goal_2 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sift_candidates_return_wit_4_split_goal_3 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sift_candidates_return_wit_4_split_goal_4 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sift_candidates_return_wit_4_split_goal_5 hi_pre root_pre bhi blo thi tlo b0 t0 cap b t root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_sort_candidates_safety_wit_1_split_goal_1 : sort_candidates_safety_wit_1_split_goal_1 := by
  intro n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
  dump_pre_spatial
  have h := quot2_bounds__sort_build_phase n_pre PreH1
  change Z.quot n_pre 2 - 1 ≤ 2147483647
  omega

theorem proof_of_sort_candidates_safety_wit_1_split_goal_2 : sort_candidates_safety_wit_1_split_goal_2 := by
  intro n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
  dump_pre_spatial
  have h := quot2_bounds__sort_build_phase n_pre PreH1
  change -2147483648 ≤ Z.quot n_pre 2 - 1
  omega

theorem proof_of_sort_candidates_safety_wit_1 : sort_candidates_safety_wit_1 := by
  unfold sort_candidates_safety_wit_1
  right
  intro n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
  split_pures
  all_goals first
    | exact proof_of_sort_candidates_safety_wit_1_split_goal_1 n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
    | exact proof_of_sort_candidates_safety_wit_1_split_goal_2 n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5

theorem proof_of_sort_candidates_entail_wit_1_split_goal_1 : sort_candidates_entail_wit_1_split_goal_1 := by
  intro n_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
  apply heap_ordered_from_half__sort_build_phase t0 n_pre _ PreH1
  omega

theorem proof_of_sort_candidates_entail_wit_1_split_goal_2 : sort_candidates_entail_wit_1_split_goal_2 := by
  intro n_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
  exact zip_perm_refl__sort_build_phase t0 b0 (by omega)

theorem proof_of_sort_candidates_entail_wit_1_split_goal_3 : sort_candidates_entail_wit_1_split_goal_3 := by
  intro n_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
  exact PreH5

theorem proof_of_sort_candidates_entail_wit_1_split_goal_4 : sort_candidates_entail_wit_1_split_goal_4 := by
  intro n_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
  have h := quot2_bounds__sort_build_phase n_pre PreH1
  omega

theorem proof_of_sort_candidates_entail_wit_1 : sort_candidates_entail_wit_1 := by
  unfold sort_candidates_entail_wit_1
  right
  intro n_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_candidates_entail_wit_1_split_goal_1 n_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
      | exact proof_of_sort_candidates_entail_wit_1_split_goal_2 n_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
      | exact proof_of_sort_candidates_entail_wit_1_split_goal_3 n_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5
      | exact proof_of_sort_candidates_entail_wit_1_split_goal_4 n_pre bhi blo thi tlo b0 t0 PreH1 PreH2 PreH3 PreH4 PreH5

theorem proof_of_sort_candidates_entail_wit_2_split_goal_1 : sort_candidates_entail_wit_2_split_goal_1 := by
  intro n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  simpa only [Int.sub_add_cancel] using PreH10

theorem proof_of_sort_candidates_entail_wit_2_split_goal_2 : sort_candidates_entail_wit_2_split_goal_2 := by
  intro n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact PreH8

theorem proof_of_sort_candidates_entail_wit_2_split_goal_3 : sort_candidates_entail_wit_2_split_goal_3 := by
  intro n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have h := quot2_bounds__sort_build_phase n_pre (by omega)
  omega

theorem proof_of_sort_candidates_entail_wit_2 : sort_candidates_entail_wit_2 := by
  unfold sort_candidates_entail_wit_2
  right
  intro n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_candidates_entail_wit_2_split_goal_1 n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sort_candidates_entail_wit_2_split_goal_2 n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sort_candidates_entail_wit_2_split_goal_3 n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_sort_candidates_entail_wit_3_split_goal_1 : sort_candidates_entail_wit_3_split_goal_1 := by
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 root b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simpa only [Int.sub_add_cancel] using PreH3

theorem proof_of_sort_candidates_entail_wit_3_split_goal_2 : sort_candidates_entail_wit_3_split_goal_2 := by
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 root b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact zip_perm_trans__sort_build_phase t0 b0 t_2 b_2 t1 b1 PreH16 PreH4

theorem proof_of_sort_candidates_entail_wit_3_split_goal_3 : sort_candidates_entail_wit_3_split_goal_3 := by
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 root b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH7

theorem proof_of_sort_candidates_entail_wit_3 : sort_candidates_entail_wit_3 := by
  unfold sort_candidates_entail_wit_3
  right
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 root b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_candidates_entail_wit_3_split_goal_1 n_pre bhi blo thi tlo b0 t0 t_2 b_2 root b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_sort_candidates_entail_wit_3_split_goal_2 n_pre bhi blo thi tlo b0 t0 t_2 b_2 root b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_sort_candidates_entail_wit_3_split_goal_3 n_pre bhi blo thi tlo b0 t0 t_2 b_2 root b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_sort_candidates_entail_wit_4_split_goal_1 : sort_candidates_entail_wit_4_split_goal_1 := by
  intro n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact heap_sort_state_full__sort_build_phase t_2 n_pre (by omega)

theorem proof_of_sort_candidates_entail_wit_4_split_goal_2 : sort_candidates_entail_wit_4_split_goal_2 := by
  intro n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  unfold HeapOrdered
  have he : root+1=0 := by omega
  simpa only [he] using PreH10

theorem proof_of_sort_candidates_entail_wit_4_split_goal_3 : sort_candidates_entail_wit_4_split_goal_3 := by
  intro n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact PreH8

theorem proof_of_sort_candidates_entail_wit_4 : sort_candidates_entail_wit_4 := by
  unfold sort_candidates_entail_wit_4
  right
  intro n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_candidates_entail_wit_4_split_goal_1 n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sort_candidates_entail_wit_4_split_goal_2 n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sort_candidates_entail_wit_4_split_goal_3 n_pre bhi blo thi tlo b0 t0 b_2 t_2 root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_sort_candidates_entail_wit_5_split_goal_1 : sort_candidates_entail_wit_5_split_goal_1 := by
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  simpa only [Int.sub_add_cancel] using PreH7

theorem proof_of_sort_candidates_entail_wit_5_split_goal_2 : sort_candidates_entail_wit_5_split_goal_2 := by
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  exact PreH5

theorem proof_of_sort_candidates_entail_wit_5 : sort_candidates_entail_wit_5 := by
  unfold sort_candidates_entail_wit_5
  right
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_candidates_entail_wit_5_split_goal_1 n_pre bhi blo thi tlo b0 t0 t_2 b_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_sort_candidates_entail_wit_5_split_goal_2 n_pre bhi blo thi tlo b0 t0 t_2 b_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8

theorem proof_of_sort_candidates_entail_wit_6_split_goal_1 : sort_candidates_entail_wit_6_split_goal_1 := by
  intro n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact heap_sort_state_swap__sort_extract_phase t_2 n_pre hi PreH6 (by omega) PreH5 PreH10 PreH11

theorem proof_of_sort_candidates_entail_wit_6_split_goal_2 : sort_candidates_entail_wit_6_split_goal_2 := by
  intro n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simpa only [Int.sub_add_cancel,Int.zero_add] using heap_ordered_from_swap__sort_extract_phase t_2 n_pre hi PreH6 (by omega) PreH5 PreH10

theorem proof_of_sort_candidates_entail_wit_6_split_goal_3 : sort_candidates_entail_wit_6_split_goal_3 := by
  intro n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact zip_perm_swap0__sort_extract_phase t0 b0 t_2 b hi PreH9 (by omega)

theorem proof_of_sort_candidates_entail_wit_6_split_goal_4 : sort_candidates_entail_wit_6_split_goal_4 := by
  intro n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  intro q hq
  have ht := Zlength_replace_Znth t_2 0 (Znth hi t_2 0)
  have hb := Zlength_replace_Znth b 0 (Znth hi b 0)
  by_cases he : q = hi
  · subst q
    rw [Znth_replace_Znth_Same 0 _ hi _ (by omega),Znth_replace_Znth_Same 0 _ hi _ (by omega)]
    exact PreH8 0 (by omega)
  · rw [Znth_replace_Znth_Diff 0 _ hi q _ (by omega) (by omega) (Ne.symm he),
        Znth_replace_Znth_Diff 0 _ hi q _ (by omega) (by omega) (Ne.symm he)]
    by_cases h0 : q = 0
    · subst q
      rw [Znth_replace_Znth_Same 0 t_2 0 _ (by omega),Znth_replace_Znth_Same 0 b 0 _ (by omega)]
      exact PreH8 hi (by omega)
    · rw [Znth_replace_Znth_Diff 0 t_2 0 q _ (by omega) (by omega) (Ne.symm h0),
          Znth_replace_Znth_Diff 0 b 0 q _ (by omega) (by omega) (Ne.symm h0)]
      exact PreH8 q hq

theorem proof_of_sort_candidates_entail_wit_6_split_goal_5 : sort_candidates_entail_wit_6_split_goal_5 := by
  intro n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simpa only [Zlength_replace_Znth] using PreH7

theorem proof_of_sort_candidates_entail_wit_6_split_goal_6 : sort_candidates_entail_wit_6_split_goal_6 := by
  intro n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simpa only [Zlength_replace_Znth] using PreH6

theorem proof_of_sort_candidates_entail_wit_6_split_goal_7 : sort_candidates_entail_wit_6_split_goal_7 := by
  intro n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  symm
  apply Znth_replace_Znth_Same
  simp only [Zlength_replace_Znth]
  omega

theorem proof_of_sort_candidates_entail_wit_6 : sort_candidates_entail_wit_6 := by
  unfold sort_candidates_entail_wit_6
  right
  intro n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_candidates_entail_wit_6_split_goal_1 n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_sort_candidates_entail_wit_6_split_goal_2 n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_sort_candidates_entail_wit_6_split_goal_3 n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_sort_candidates_entail_wit_6_split_goal_4 n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_sort_candidates_entail_wit_6_split_goal_5 n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_sort_candidates_entail_wit_6_split_goal_6 n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_sort_candidates_entail_wit_6_split_goal_7 n_pre bhi blo thi tlo b0 t0 b t_2 hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_sort_candidates_entail_wit_7_split_goal_1 : sort_candidates_entail_wit_7_split_goal_1 := by
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 hi v b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [Int.sub_add_cancel] at PreH5 PreH6
  exact heap_sort_state_after_sift__sort_extract_phase t_2 b_2 t1 b1 n_pre hi PreH13 PreH14 PreH1 PreH2 (by omega) PreH4.2.2.2 PreH5 PreH6 PreH18

theorem proof_of_sort_candidates_entail_wit_7_split_goal_2 : sort_candidates_entail_wit_7_split_goal_2 := by
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 hi v b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact PreH3

theorem proof_of_sort_candidates_entail_wit_7_split_goal_3 : sort_candidates_entail_wit_7_split_goal_3 := by
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 hi v b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact zip_perm_trans__sort_extract_phase t0 b0 t_2 b_2 t1 b1 PreH16 PreH4

theorem proof_of_sort_candidates_entail_wit_7_split_goal_4 : sort_candidates_entail_wit_7_split_goal_4 := by
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 hi v b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact PreH7

theorem proof_of_sort_candidates_entail_wit_7 : sort_candidates_entail_wit_7 := by
  unfold sort_candidates_entail_wit_7
  right
  intro n_pre bhi blo thi tlo b0 t0 t_2 b_2 hi v b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_candidates_entail_wit_7_split_goal_1 n_pre bhi blo thi tlo b0 t0 t_2 b_2 hi v b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_sort_candidates_entail_wit_7_split_goal_2 n_pre bhi blo thi tlo b0 t0 t_2 b_2 hi v b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_sort_candidates_entail_wit_7_split_goal_3 n_pre bhi blo thi tlo b0 t0 t_2 b_2 hi v b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_sort_candidates_entail_wit_7_split_goal_4 n_pre bhi blo thi tlo b0 t0 t_2 b_2 hi v b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_sort_candidates_return_wit_1_split_goal_1 : sort_candidates_return_wit_1_split_goal_1 := by
  intro n_pre bhi blo thi tlo b0 t0 b t hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH8

theorem proof_of_sort_candidates_return_wit_1_split_goal_2 : sort_candidates_return_wit_1_split_goal_2 := by
  intro n_pre bhi blo thi tlo b0 t0 b t hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact heap_sort_done_nondecreasing__sort_extract_phase t n_pre hi PreH6 PreH4 PreH1 PreH11

theorem proof_of_sort_candidates_return_wit_1 : sort_candidates_return_wit_1 := by
  unfold sort_candidates_return_wit_1
  right
  intro n_pre bhi blo thi tlo b0 t0 b t hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_candidates_return_wit_1_split_goal_1 n_pre bhi blo thi tlo b0 t0 b t hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_sort_candidates_return_wit_1_split_goal_2 n_pre bhi blo thi tlo b0 t0 b t hi PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_sort_candidates_partial_solve_wit_1_pure_split_goal_1 : sort_candidates_partial_solve_wit_1_pure_split_goal_1 := by
  intro n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 t b root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  dump_pre_spatial
  exact PreH12

theorem proof_of_sort_candidates_partial_solve_wit_1_pure : sort_candidates_partial_solve_wit_1_pure := by
  unfold sort_candidates_partial_solve_wit_1_pure
  right
  intro n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 t b root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  all_goals first
    | exact proof_of_sort_candidates_partial_solve_wit_1_pure_split_goal_1 n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 t b root PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_sort_candidates_partial_solve_wit_10_pure_split_goal_1 : sort_candidates_partial_solve_wit_10_pure_split_goal_1 := by
  intro n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 t b hi v PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dump_pre_spatial
  exact PreH14

theorem proof_of_sort_candidates_partial_solve_wit_10_pure : sort_candidates_partial_solve_wit_10_pure := by
  unfold sort_candidates_partial_solve_wit_10_pure
  right
  intro n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 t b hi v PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  all_goals first
    | exact proof_of_sort_candidates_partial_solve_wit_10_pure_split_goal_1 n_pre cand_base_pre cand_t_pre bhi blo thi tlo b0 t0 t b hi v PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change (((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) <= 9223372036854775807)
  have hsh := PreH25 i (by omega)
  have hr := (rem5_quot5_spec__solver_safety_cand_a (j-Znth i sh 0)).2
  omega

theorem proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change ((-9223372036854775808) <= ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5))
  have hsh := PreH25 i (by omega)
  have hr := (rem5_quot5_spec__solver_safety_cand_a (j-Znth i sh 0)).2
  omega

theorem proof_of_solver_safety_wit_20 : solver_safety_wit_20 := by
  unfold solver_safety_wit_20
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_20_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_solver_safety_wit_20_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_safety_wit_27_split_goal_1 : solver_safety_wit_27_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change (((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) <= 9223372036854775807)
  have hsh := PreH24 i (by omega)
  have hr := (rem5_quot5_spec__solver_safety_cand_a (j-Znth i sh 0)).2
  omega

theorem proof_of_solver_safety_wit_27_split_goal_2 : solver_safety_wit_27_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change ((-9223372036854775808) <= ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5))
  have hsh := PreH24 i (by omega)
  have hr := (rem5_quot5_spec__solver_safety_cand_a (j-Znth i sh 0)).2
  omega

theorem proof_of_solver_safety_wit_27 : solver_safety_wit_27 := by
  unfold solver_safety_wit_27
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_27_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    | exact proof_of_solver_safety_wit_27_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_safety_wit_33_split_goal_1 : solver_safety_wit_33_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) <= 9223372036854775807)
  have hsh := PreH25 i (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  omega

theorem proof_of_solver_safety_wit_33_split_goal_2 : solver_safety_wit_33_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change ((-9223372036854775808) <= ((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)))
  have hsh := PreH25 i (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  omega

theorem proof_of_solver_safety_wit_33 : solver_safety_wit_33 := by
  unfold solver_safety_wit_33
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_33_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_solver_safety_wit_33_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_safety_wit_34_split_goal_1 : solver_safety_wit_34_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) <= 9223372036854775807)
  have hsh := PreH24 i (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  omega

theorem proof_of_solver_safety_wit_34_split_goal_2 : solver_safety_wit_34_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change ((-9223372036854775808) <= ((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)))
  have hsh := PreH24 i (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  omega

theorem proof_of_solver_safety_wit_34 : solver_safety_wit_34 := by
  unfold solver_safety_wit_34
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_34_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    | exact proof_of_solver_safety_wit_34_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_safety_wit_35_split_goal_1 : solver_safety_wit_35_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change ((((Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5) * c_pre) - ((Z.quot (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) - j) 5) * W)) <= 9223372036854775807)
  have hsh := PreH25 i (by omega)
  have hq := target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j hsh (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_35_split_goal_2 : solver_safety_wit_35_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change ((-9223372036854775808) <= (((Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5) * c_pre) - ((Z.quot (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) - j) 5) * W)))
  have hsh := PreH25 i (by omega)
  have hq := target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j hsh (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_35 : solver_safety_wit_35 := by
  unfold solver_safety_wit_35
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_35_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_solver_safety_wit_35_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_safety_wit_36_split_goal_1 : solver_safety_wit_36_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change (((Z.quot (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) - j) 5) * W) <= 9223372036854775807)
  have hsh := PreH25 i (by omega)
  have hq := target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j hsh (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_36_split_goal_2 : solver_safety_wit_36_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change ((-9223372036854775808) <= ((Z.quot (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) - j) 5) * W))
  have hsh := PreH25 i (by omega)
  have hq := target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j hsh (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_36 : solver_safety_wit_36 := by
  unfold solver_safety_wit_36
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_36_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_solver_safety_wit_36_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_safety_wit_39_split_goal_1 : solver_safety_wit_39_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change (((Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5) * c_pre) <= 9223372036854775807)
  have hr := rem5_shift_bounds__solver_safety_cand_b (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_39_split_goal_2 : solver_safety_wit_39_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  change ((-9223372036854775808) <= ((Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5) * c_pre))
  have hr := rem5_shift_bounds__solver_safety_cand_b (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_39 : solver_safety_wit_39 := by
  unfold solver_safety_wit_39
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_39_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_solver_safety_wit_39_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_safety_wit_41_split_goal_1 : solver_safety_wit_41_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change ((((Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5) * c_pre) - ((Z.quot (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) - j) 5) * W)) <= 9223372036854775807)
  have hsh := PreH24 i (by omega)
  have hq := target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j hsh (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_41_split_goal_2 : solver_safety_wit_41_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change ((-9223372036854775808) <= (((Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5) * c_pre) - ((Z.quot (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) - j) 5) * W)))
  have hsh := PreH24 i (by omega)
  have hq := target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j hsh (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_41 : solver_safety_wit_41 := by
  unfold solver_safety_wit_41
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_41_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    | exact proof_of_solver_safety_wit_41_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_safety_wit_42_split_goal_1 : solver_safety_wit_42_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change (((Z.quot (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) - j) 5) * W) <= 9223372036854775807)
  have hsh := PreH24 i (by omega)
  have hq := target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j hsh (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_42_split_goal_2 : solver_safety_wit_42_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change ((-9223372036854775808) <= ((Z.quot (((Znth i sh (0 : Int)) + (Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5)) - j) 5) * W))
  have hsh := PreH24 i (by omega)
  have hq := target_quot_bounds__solver_safety_cand_b (Znth i sh 0) j hsh (by omega)
  have hr := rem5_shift_bound__solver_safety_cand_a (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_42 : solver_safety_wit_42 := by
  unfold solver_safety_wit_42
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_42_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    | exact proof_of_solver_safety_wit_42_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_safety_wit_45_split_goal_1 : solver_safety_wit_45_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change (((Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5) * c_pre) <= 9223372036854775807)
  have hr := rem5_shift_bounds__solver_safety_cand_b (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_45_split_goal_2 : solver_safety_wit_45_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  change ((-9223372036854775808) <= ((Z.rem ((Z.rem (j - (Znth i sh (0 : Int))) 5) + 5) 5) * c_pre))
  have hr := rem5_shift_bounds__solver_safety_cand_b (j-Znth i sh 0)
  nlinarith

theorem proof_of_solver_safety_wit_45 : solver_safety_wit_45 := by
  unfold solver_safety_wit_45
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_45_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    | exact proof_of_solver_safety_wit_45_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_safety_wit_57_split_goal_1 : solver_safety_wit_57_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  dump_pre_spatial
  change ((hsum + ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W)) <= 9223372036854775807)
  have hst := PreH34 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_57_split_goal_2 : solver_safety_wit_57_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  dump_pre_spatial
  change ((-9223372036854775808) <= (hsum + ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W)))
  have hst := PreH34 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_57 : solver_safety_wit_57 := by
  unfold solver_safety_wit_57
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_57_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
    | exact proof_of_solver_safety_wit_57_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39

theorem proof_of_solver_safety_wit_58_split_goal_1 : solver_safety_wit_58_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  dump_pre_spatial
  change (((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W) <= 9223372036854775807)
  have hst := PreH34 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_58_split_goal_2 : solver_safety_wit_58_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  dump_pre_spatial
  change ((-9223372036854775808) <= ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W))
  have hst := PreH34 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_58 : solver_safety_wit_58 := by
  unfold solver_safety_wit_58
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_58_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
    | exact proof_of_solver_safety_wit_58_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39

theorem proof_of_solver_safety_wit_59_split_goal_1 : solver_safety_wit_59_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  dump_pre_spatial
  change ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) <= 9223372036854775807)
  have hst := PreH34 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_59_split_goal_2 : solver_safety_wit_59_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  dump_pre_spatial
  change ((-9223372036854775808) <= (k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)))
  have hst := PreH34 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_59 : solver_safety_wit_59 := by
  unfold solver_safety_wit_59
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_59_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
    | exact proof_of_solver_safety_wit_59_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39

theorem proof_of_solver_safety_wit_63_split_goal_1 : solver_safety_wit_63_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  dump_pre_spatial
  change ((hsum + ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W)) <= 9223372036854775807)
  have hst := PreH36 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_63_split_goal_2 : solver_safety_wit_63_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  dump_pre_spatial
  change ((-9223372036854775808) <= (hsum + ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W)))
  have hst := PreH36 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_63 : solver_safety_wit_63 := by
  unfold solver_safety_wit_63
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_63_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
    | exact proof_of_solver_safety_wit_63_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41

theorem proof_of_solver_safety_wit_64_split_goal_1 : solver_safety_wit_64_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  dump_pre_spatial
  change (((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W) <= 9223372036854775807)
  have hst := PreH36 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_64_split_goal_2 : solver_safety_wit_64_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  dump_pre_spatial
  change ((-9223372036854775808) <= ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W))
  have hst := PreH36 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_64 : solver_safety_wit_64 := by
  unfold solver_safety_wit_64
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_64_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
    | exact proof_of_solver_safety_wit_64_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41

theorem proof_of_solver_safety_wit_65_split_goal_1 : solver_safety_wit_65_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  dump_pre_spatial
  change ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) <= 9223372036854775807)
  have hst := PreH36 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_65_split_goal_2 : solver_safety_wit_65_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  dump_pre_spatial
  change ((-9223372036854775808) <= (k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)))
  have hst := PreH36 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_a k_pre W j (Znth i st 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_65 : solver_safety_wit_65 := by
  unfold solver_safety_wit_65
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_65_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
    | exact proof_of_solver_safety_wit_65_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41

theorem proof_of_solver_safety_wit_69_split_goal_1 : solver_safety_wit_69_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  dump_pre_spatial
  change ((hsum + ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W)) <= 9223372036854775807)
  have hst := PreH33 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_69_split_goal_2 : solver_safety_wit_69_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  dump_pre_spatial
  change ((-9223372036854775808) <= (hsum + ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W)))
  have hst := PreH33 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_69 : solver_safety_wit_69 := by
  unfold solver_safety_wit_69
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_69_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
    | exact proof_of_solver_safety_wit_69_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38

theorem proof_of_solver_safety_wit_70_split_goal_1 : solver_safety_wit_70_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  dump_pre_spatial
  change (((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W) <= 9223372036854775807)
  have hst := PreH33 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_70_split_goal_2 : solver_safety_wit_70_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  dump_pre_spatial
  change ((-9223372036854775808) <= ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W))
  have hst := PreH33 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_70 : solver_safety_wit_70 := by
  unfold solver_safety_wit_70
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_70_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
    | exact proof_of_solver_safety_wit_70_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38

theorem proof_of_solver_safety_wit_71_split_goal_1 : solver_safety_wit_71_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  dump_pre_spatial
  change ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) <= 9223372036854775807)
  have hst := PreH33 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_71_split_goal_2 : solver_safety_wit_71_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  dump_pre_spatial
  change ((-9223372036854775808) <= (k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)))
  have hst := PreH33 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_71 : solver_safety_wit_71 := by
  unfold solver_safety_wit_71
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_71_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
    | exact proof_of_solver_safety_wit_71_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38

theorem proof_of_solver_safety_wit_75_split_goal_1 : solver_safety_wit_75_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  dump_pre_spatial
  change ((hsum + ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W)) <= 9223372036854775807)
  have hst := PreH35 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_75_split_goal_2 : solver_safety_wit_75_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  dump_pre_spatial
  change ((-9223372036854775808) <= (hsum + ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W)))
  have hst := PreH35 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_75 : solver_safety_wit_75 := by
  unfold solver_safety_wit_75
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_75_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    | exact proof_of_solver_safety_wit_75_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_solver_safety_wit_76_split_goal_1 : solver_safety_wit_76_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  dump_pre_spatial
  change (((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W) <= 9223372036854775807)
  have hst := PreH35 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_76_split_goal_2 : solver_safety_wit_76_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  dump_pre_spatial
  change ((-9223372036854775808) <= ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) * W))
  have hst := PreH35 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_76 : solver_safety_wit_76 := by
  unfold solver_safety_wit_76
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_76_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    | exact proof_of_solver_safety_wit_76_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_solver_safety_wit_77_split_goal_1 : solver_safety_wit_77_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  dump_pre_spatial
  change ((k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)) <= 9223372036854775807)
  have hst := PreH35 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_77_split_goal_2 : solver_safety_wit_77_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  dump_pre_spatial
  change ((-9223372036854775808) <= (k_pre * (Z.quot ((Znth i st (0 : Int)) - j) 5)))
  have hst := PreH35 i (by omega)
  have hb := sweep_total_int64_bounds__solver_safety_sweep_b k_pre W j (Znth i st 0) hsum (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem proof_of_solver_safety_wit_77 : solver_safety_wit_77 := by
  unfold solver_safety_wit_77
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_77_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
    | exact proof_of_solver_safety_wit_77_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh ct cb st sb hl W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  sep_apply (shape_full shifted_pre n_pre)
  Intros sh
  sep_apply (shape_full cand_t_pre n_pre)
  Intros ct
  sep_apply (shape_full cand_base_pre n_pre)
  Intros cb
  sep_apply (shape_full heap_pre n_pre)
  Intros hl
  prop_apply (int64Array.full_Zlength shifted_pre n_pre sh)
  Intros_p hsh
  prop_apply (int64Array.full_Zlength cand_t_pre n_pre ct)
  Intros_p hct
  prop_apply (int64Array.full_Zlength cand_base_pre n_pre cb)
  Intros_p hcb
  prop_apply (int64Array.full_Zlength heap_pre n_pre hl)
  Intros_p hhl
  Exists hl cb ct sh
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve
      | trivial
      | assumption
      | omega
      | (unfold WCost; omega)
      | (intro q hq; omega)

theorem proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  sep_apply (shape_full shifted_pre n_pre)
  Intros sh
  sep_apply (shape_full cand_t_pre n_pre)
  Intros ct
  sep_apply (shape_full cand_base_pre n_pre)
  Intros cb
  sep_apply (shape_full heap_pre n_pre)
  Intros hl
  prop_apply (int64Array.full_Zlength shifted_pre n_pre sh)
  Intros_p hsh
  prop_apply (int64Array.full_Zlength cand_t_pre n_pre ct)
  Intros_p hct
  prop_apply (int64Array.full_Zlength cand_base_pre n_pre cb)
  Intros_p hcb
  prop_apply (int64Array.full_Zlength heap_pre n_pre hl)
  Intros_p hhl
  Exists hl cb ct sh
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve
      | trivial
      | assumption
      | omega
      | (unfold WCost; omega)
      | (intro q hq; omega)

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply shifted_prefix_step__solver_shift_loop
  · omega
  · exact PreH21

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  simpa only [Zlength_replace_Znth] using PreH17

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_solver_entail_wit_2_split_goal_2 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply residue_best_zero__solver_shift_loop

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  intro q hq
  rw [PreH21 q (by omega)]
  have hb := PreH10 q (by omega)
  omega

theorem proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have he : n_pre = i := by omega
  simpa only [he] using PreH21

theorem proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH10

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_3_split_goal_1 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_solver_entail_wit_3_split_goal_2 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_solver_entail_wit_3_split_goal_3 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_solver_entail_wit_3_split_goal_4 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  intro q hq
  omega

theorem proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  intro q hq
  omega

theorem proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact PreH23

theorem proof_of_solver_entail_wit_4_1_split_goal_4 : solver_entail_wit_4_1_split_goal_4 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact PreH10

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  unfold solver_entail_wit_4_1
  right
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_1_split_goal_1 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
      | exact proof_of_solver_entail_wit_4_1_split_goal_2 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
      | exact proof_of_solver_entail_wit_4_1_split_goal_3 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
      | exact proof_of_solver_entail_wit_4_1_split_goal_4 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  intro q hq
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  intro q hq
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_3 : solver_entail_wit_4_2_split_goal_3 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact PreH22

theorem proof_of_solver_entail_wit_4_2_split_goal_4 : solver_entail_wit_4_2_split_goal_4 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact PreH10

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  unfold solver_entail_wit_4_2
  right
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_2_split_goal_1 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_4_2_split_goal_2 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_4_2_split_goal_3 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_4_2_split_goal_4 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := PreH25 i (by omega)
  apply cand_prefix_step__solver_cand_fill
  all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  simp only [Zlength_replace_Znth]
  assumption

theorem proof_of_solver_entail_wit_5_1_split_goal_3 : solver_entail_wit_5_1_split_goal_3 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  simp only [Zlength_replace_Znth]
  assumption

theorem proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1 := by
  unfold solver_entail_wit_5_1
  right
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_1_split_goal_1 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | exact proof_of_solver_entail_wit_5_1_split_goal_2 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | exact proof_of_solver_entail_wit_5_1_split_goal_3 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hb := PreH24 i (by omega)
  apply cand_prefix_step__solver_cand_fill
  all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_5_2_split_goal_2 : solver_entail_wit_5_2_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  simp only [Zlength_replace_Znth]
  assumption

theorem proof_of_solver_entail_wit_5_2_split_goal_3 : solver_entail_wit_5_2_split_goal_3 := by
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  simp only [Zlength_replace_Znth]
  assumption

theorem proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2 := by
  unfold solver_entail_wit_5_2
  right
  intro c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_2_split_goal_1 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
      | exact proof_of_solver_entail_wit_5_2_split_goal_2 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
      | exact proof_of_solver_entail_wit_5_2_split_goal_3 c_pre b_pre k_pre n_pre contributions hl_2 cb_2 ct_2 sh_2 i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl_2 cb_2 ct_2 sh_2 i_2 best j W b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have he : i_2=n_pre := by omega
  subst i_2
  Exists b1 t1 hl_2 cb_2 ct_2 sh_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl_2 cb_2 ct_2 sh_2 i_2 best j W b1 t1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have he : i_2=n_pre := by omega
  subst i_2
  Exists b1 t1 hl_2 cb_2 ct_2 sh_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st_2 sb_2 hl_2 W j best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2 0
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve
      | trivial
      | assumption
      | omega
      | apply heap_ordered_zero__solver_postsort_sweep_init
      | (symm; apply zsum_sublist_0_0__solver_postsort_sweep_init)
      | apply heap_content_empty__solver_postsort_sweep_init
      | (apply sweep_best_at_zero__solver_postsort_sweep_init; omega; assumption)
      | (intro q hq; omega)

theorem proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st_2 sb_2 hl_2 W j best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2 0
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve
      | trivial
      | assumption
      | omega
      | apply heap_ordered_zero__solver_postsort_sweep_init
      | (symm; apply zsum_sublist_0_0__solver_postsort_sweep_init)
      | apply heap_content_empty__solver_postsort_sweep_init
      | (apply sweep_best_at_zero__solver_postsort_sweep_init; omega; assumption)
      | (intro q hq; omega)

theorem proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb_2 st_2 hl_2 cb_2 ct_2 sh_2 hsum i best j W l1 l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  simp only [Int.add_sub_cancel] at *
  rcases PreH49 with ⟨hmin,hsum⟩
  have hlen := prefix_length l1 (k_pre+1) (by omega)
  have hub : ∀ y, y ∈ Znth i sb_2 0 :: sublist 0 k_pre hl_2 → y ≤ Znth 0 l1 0 := by
    intro y hy
    have hy' := PreH9.mem_iff.mpr hy
    obtain ⟨q,hq,he⟩ := In_Znth__solver_heap_maintain _ y hy'
    rw [hlen] at hq
    rw [prefix_nth l1 (k_pre+1) q hq] at he
    rw [← he]
    exact PreH4 q (by omega)
  have hpp := PreH9.symm.trans PreH3
  have hzp : ZSum (sublist 0 (k_pre+1) l1)-Znth 0 l1 0 = ZSum (sublist 0 k_pre l1_2) := by
    rw [zsum_permutation__solver_heap_maintain _ _ PreH3,zsum_cons__solver_heap_maintain]
    omega
  have hbold : ∀ y, y ∈ Znth i sb_2 0 :: sublist 0 k_pre hl_2 → -600000000000 ≤ y ∧ y ≤ 4000 := by
    intro y hy
    rcases List.mem_cons.mp hy with he | hy
    · subst y
      have h := PreH45 i (by omega)
      omega
    · exact sublist_In_bounds__solver_heap_maintain hl_2 k_pre (-600000000000) 4000 (by omega) (fun q hq => PreH46 q (by omega)) y hy
  have hbnew : ∀ y, y ∈ sublist 0 k_pre l1_2 → -600000000000 ≤ y ∧ y ≤ 4000 := by
    intro y hy
    exact hbold y (hpp.mem_iff.mpr (List.mem_cons_of_mem _ hy))
  have hlnew := prefix_length l1_2 k_pre (by omega)
  have hz := zsum_bounds__solver_heap_maintain _ _ _ hbnew
  rw [hlnew] at hz
  have hmsm : MinSubMultiset (sublist 0 (i+1) sb_2) (sublist 0 k_pre l1_2) := by
    rw [prefix_succ sb_2 i (by omega)]
    exact min_sub_multiset_push_pop__solver_heap_maintain _ _ _ _ _ hmin hpp hub
  have hbn : ∀ q, (0 ≤ q ∧ q < k_pre) → -600000000000 ≤ Znth q l1_2 0 ∧ Znth q l1_2 0 ≤ 4000 := by
    intro q hq
    rw [← prefix_nth l1_2 k_pre q hq]
    exact hbnew _ (Znth_In__solver_heap_maintain _ q (by omega))
  have hhc : HeapContent sb_2 (i+1) (sublist 0 k_pre l1_2) (ZSum (sublist 0 (k_pre+1) l1)-Znth 0 l1 0) := ⟨hmsm,hzp⟩
  Exists sb_2 st_2 l1_2 cb_2 ct_2 sh_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb_2 st_2 hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W l1 l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hk : hsize=k_pre := by omega
  simp only [hk] at *
  simp only [Int.add_sub_cancel] at *
  rcases PreH50 with ⟨hmin,hsum⟩
  have hlen := prefix_length l1 (k_pre+1) (by omega)
  have hub : ∀ y, y ∈ Znth i sb_2 0 :: sublist 0 k_pre hl_2 → y ≤ Znth 0 l1 0 := by
    intro y hy
    have hy' := PreH9.mem_iff.mpr hy
    obtain ⟨q,hq,he⟩ := In_Znth__solver_heap_maintain _ y hy'
    rw [hlen] at hq
    rw [prefix_nth l1 (k_pre+1) q hq] at he
    rw [← he]
    exact PreH4 q (by omega)
  have hpp := PreH9.symm.trans PreH3
  have hzp : ZSum (sublist 0 (k_pre+1) l1)-Znth 0 l1 0 = ZSum (sublist 0 k_pre l1_2) := by
    rw [zsum_permutation__solver_heap_maintain _ _ PreH3,zsum_cons__solver_heap_maintain]
    omega
  have hbold : ∀ y, y ∈ Znth i sb_2 0 :: sublist 0 k_pre hl_2 → -600000000000 ≤ y ∧ y ≤ 4000 := by
    intro y hy
    rcases List.mem_cons.mp hy with he | hy
    · subst y
      have h := PreH46 i (by omega)
      omega
    · exact sublist_In_bounds__solver_heap_maintain hl_2 k_pre (-600000000000) 4000 (by omega) (fun q hq => PreH47 q (by omega)) y hy
  have hbnew : ∀ y, y ∈ sublist 0 k_pre l1_2 → -600000000000 ≤ y ∧ y ≤ 4000 := by
    intro y hy
    exact hbold y (hpp.mem_iff.mpr (List.mem_cons_of_mem _ hy))
  have hlnew := prefix_length l1_2 k_pre (by omega)
  have hz := zsum_bounds__solver_heap_maintain _ _ _ hbnew
  rw [hlnew] at hz
  have hmsm : MinSubMultiset (sublist 0 (i+1) sb_2) (sublist 0 k_pre l1_2) := by
    rw [prefix_succ sb_2 i (by omega)]
    exact min_sub_multiset_push_pop__solver_heap_maintain _ _ _ _ _ hmin hpp hub
  have hbn : ∀ q, (0 ≤ q ∧ q < k_pre) → -600000000000 ≤ Znth q l1_2 0 ∧ Znth q l1_2 0 ≤ 4000 := by
    intro q hq
    rw [← prefix_nth l1_2 k_pre q hq]
    exact hbnew _ (Znth_In__solver_heap_maintain _ q (by omega))
  have hhc : HeapContent sb_2 (i+1) (sublist 0 k_pre l1_2) (ZSum (sublist 0 (k_pre+1) l1)-Znth 0 l1 0) := ⟨hmsm,hzp⟩
  Exists sb_2 st_2 l1_2 cb_2 ct_2 sh_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb_2 st_2 hl_2 cb_2 ct_2 sh_2 hsum i best j W l1 l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  simp only [Int.add_sub_cancel] at *
  rcases PreH48 with ⟨hmin,hsum⟩
  have hlen := prefix_length l1 (k_pre+1) (by omega)
  have hub : ∀ y, y ∈ Znth i sb_2 0 :: sublist 0 k_pre hl_2 → y ≤ Znth 0 l1 0 := by
    intro y hy
    have hy' := PreH9.mem_iff.mpr hy
    obtain ⟨q,hq,he⟩ := In_Znth__solver_heap_maintain _ y hy'
    rw [hlen] at hq
    rw [prefix_nth l1 (k_pre+1) q hq] at he
    rw [← he]
    exact PreH4 q (by omega)
  have hpp := PreH9.symm.trans PreH3
  have hzp : ZSum (sublist 0 (k_pre+1) l1)-Znth 0 l1 0 = ZSum (sublist 0 k_pre l1_2) := by
    rw [zsum_permutation__solver_heap_maintain _ _ PreH3,zsum_cons__solver_heap_maintain]
    omega
  have hbold : ∀ y, y ∈ Znth i sb_2 0 :: sublist 0 k_pre hl_2 → -600000000000 ≤ y ∧ y ≤ 4000 := by
    intro y hy
    rcases List.mem_cons.mp hy with he | hy
    · subst y
      have h := PreH44 i (by omega)
      omega
    · exact sublist_In_bounds__solver_heap_maintain hl_2 k_pre (-600000000000) 4000 (by omega) (fun q hq => PreH45 q (by omega)) y hy
  have hbnew : ∀ y, y ∈ sublist 0 k_pre l1_2 → -600000000000 ≤ y ∧ y ≤ 4000 := by
    intro y hy
    exact hbold y (hpp.mem_iff.mpr (List.mem_cons_of_mem _ hy))
  have hlnew := prefix_length l1_2 k_pre (by omega)
  have hz := zsum_bounds__solver_heap_maintain _ _ _ hbnew
  rw [hlnew] at hz
  have hmsm : MinSubMultiset (sublist 0 (i+1) sb_2) (sublist 0 k_pre l1_2) := by
    rw [prefix_succ sb_2 i (by omega)]
    exact min_sub_multiset_push_pop__solver_heap_maintain _ _ _ _ _ hmin hpp hub
  have hbn : ∀ q, (0 ≤ q ∧ q < k_pre) → -600000000000 ≤ Znth q l1_2 0 ∧ Znth q l1_2 0 ≤ 4000 := by
    intro q hq
    rw [← prefix_nth l1_2 k_pre q hq]
    exact hbnew _ (Znth_In__solver_heap_maintain _ q (by omega))
  have hhc : HeapContent sb_2 (i+1) (sublist 0 k_pre l1_2) (ZSum (sublist 0 (k_pre+1) l1)-Znth 0 l1 0) := ⟨hmsm,hzp⟩
  Exists sb_2 st_2 l1_2 cb_2 ct_2 sh_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb_2 st_2 hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W l1 l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have hk : hsize=k_pre := by omega
  simp only [hk] at *
  simp only [Int.add_sub_cancel] at *
  rcases PreH49 with ⟨hmin,hsum⟩
  have hlen := prefix_length l1 (k_pre+1) (by omega)
  have hub : ∀ y, y ∈ Znth i sb_2 0 :: sublist 0 k_pre hl_2 → y ≤ Znth 0 l1 0 := by
    intro y hy
    have hy' := PreH9.mem_iff.mpr hy
    obtain ⟨q,hq,he⟩ := In_Znth__solver_heap_maintain _ y hy'
    rw [hlen] at hq
    rw [prefix_nth l1 (k_pre+1) q hq] at he
    rw [← he]
    exact PreH4 q (by omega)
  have hpp := PreH9.symm.trans PreH3
  have hzp : ZSum (sublist 0 (k_pre+1) l1)-Znth 0 l1 0 = ZSum (sublist 0 k_pre l1_2) := by
    rw [zsum_permutation__solver_heap_maintain _ _ PreH3,zsum_cons__solver_heap_maintain]
    omega
  have hbold : ∀ y, y ∈ Znth i sb_2 0 :: sublist 0 k_pre hl_2 → -600000000000 ≤ y ∧ y ≤ 4000 := by
    intro y hy
    rcases List.mem_cons.mp hy with he | hy
    · subst y
      have h := PreH45 i (by omega)
      omega
    · exact sublist_In_bounds__solver_heap_maintain hl_2 k_pre (-600000000000) 4000 (by omega) (fun q hq => PreH46 q (by omega)) y hy
  have hbnew : ∀ y, y ∈ sublist 0 k_pre l1_2 → -600000000000 ≤ y ∧ y ≤ 4000 := by
    intro y hy
    exact hbold y (hpp.mem_iff.mpr (List.mem_cons_of_mem _ hy))
  have hlnew := prefix_length l1_2 k_pre (by omega)
  have hz := zsum_bounds__solver_heap_maintain _ _ _ hbnew
  rw [hlnew] at hz
  have hmsm : MinSubMultiset (sublist 0 (i+1) sb_2) (sublist 0 k_pre l1_2) := by
    rw [prefix_succ sb_2 i (by omega)]
    exact min_sub_multiset_push_pop__solver_heap_maintain _ _ _ _ _ hmin hpp hub
  have hbn : ∀ q, (0 ≤ q ∧ q < k_pre) → -600000000000 ≤ Znth q l1_2 0 ∧ Znth q l1_2 0 ≤ 4000 := by
    intro q hq
    rw [← prefix_nth l1_2 k_pre q hq]
    exact hbnew _ (Znth_In__solver_heap_maintain _ q (by omega))
  have hhc : HeapContent sb_2 (i+1) (sublist 0 k_pre l1_2) (ZSum (sublist 0 (k_pre+1) l1)-Znth 0 l1 0) := ⟨hmsm,hzp⟩
  Exists sb_2 st_2 l1_2 cb_2 ct_2 sh_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_8_5 : solver_entail_wit_8_5 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st_2 hl cb_2 ct_2 sh_2 hsum hsize i best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  subst hsize
  rcases PreH45 with ⟨hmin,hsum⟩
  have hlhl := prefix_length hl i (by omega)
  have hlsb := prefix_length sb i (by omega)
  have hp0 : List.Perm (sublist 0 i sb) (sublist 0 i hl) := submultiset_full_perm__solver_heap_maintain _ _ hmin.1 (by omega)
  have hp1 : List.Perm (sublist 0 (i+1) sb) (sublist 0 (i+1) l1) := by
    rw [prefix_succ sb i (by omega)]
    exact (List.perm_append_singleton _ _).trans ((hp0.cons _).trans PreH4.symm)
  have hzs : ZSum (sublist 0 i hl)+Znth i sb 0 = ZSum (sublist 0 (i+1) l1) := by
    rw [zsum_permutation__solver_heap_maintain _ _ PreH4,zsum_cons__solver_heap_maintain]
    omega
  have hbsb : ∀ y, y ∈ sublist 0 (i+1) sb → -600000000000 ≤ y ∧ y ≤ 4000 := by
    apply sublist_In_bounds__solver_heap_maintain sb (i+1) (-600000000000) 4000 (by omega)
    intro q hq
    have h := PreH41 q (by omega)
    omega
  have hbl1 : ∀ y, y ∈ sublist 0 (i+1) l1 → -600000000000 ≤ y ∧ y ≤ 4000 := fun y hy => hbsb y (hp1.mem_iff.mpr hy)
  have hll1 := prefix_length l1 (i+1) (by omega)
  have hz := zsum_bounds__solver_heap_maintain _ _ _ hbl1
  rw [hll1] at hz
  have hbn : ∀ q, (0 ≤ q ∧ q < i+1) → -600000000000 ≤ Znth q l1 0 ∧ Znth q l1 0 ≤ 4000 := by
    intro q hq
    rw [← prefix_nth l1 (i+1) q hq]
    exact hbl1 _ (Znth_In__solver_heap_maintain _ q (by omega))
  have hhc : HeapContent sb (i+1) (sublist 0 (i+1) l1) (ZSum (sublist 0 i hl)+Znth i sb 0) := ⟨min_sub_multiset_whole__solver_heap_maintain _ _ hp1,hzs⟩
  have hmax : Int.max_signed = (2147483647:Int) := rfl
  have hminI : Int.min_signed = (-2147483648:Int) := rfl
  Exists sb st_2 l1 cb_2 ct_2 sh_2 (i+1)
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_8_6 : solver_entail_wit_8_6 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st_2 hl cb_2 ct_2 sh_2 hsum hsize i best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  subst hsize
  rcases PreH44 with ⟨hmin,hsum⟩
  have hlhl := prefix_length hl i (by omega)
  have hlsb := prefix_length sb i (by omega)
  have hp0 : List.Perm (sublist 0 i sb) (sublist 0 i hl) := submultiset_full_perm__solver_heap_maintain _ _ hmin.1 (by omega)
  have hp1 : List.Perm (sublist 0 (i+1) sb) (sublist 0 (i+1) l1) := by
    rw [prefix_succ sb i (by omega)]
    exact (List.perm_append_singleton _ _).trans ((hp0.cons _).trans PreH4.symm)
  have hzs : ZSum (sublist 0 i hl)+Znth i sb 0 = ZSum (sublist 0 (i+1) l1) := by
    rw [zsum_permutation__solver_heap_maintain _ _ PreH4,zsum_cons__solver_heap_maintain]
    omega
  have hbsb : ∀ y, y ∈ sublist 0 (i+1) sb → -600000000000 ≤ y ∧ y ≤ 4000 := by
    apply sublist_In_bounds__solver_heap_maintain sb (i+1) (-600000000000) 4000 (by omega)
    intro q hq
    have h := PreH40 q (by omega)
    omega
  have hbl1 : ∀ y, y ∈ sublist 0 (i+1) l1 → -600000000000 ≤ y ∧ y ≤ 4000 := fun y hy => hbsb y (hp1.mem_iff.mpr hy)
  have hll1 := prefix_length l1 (i+1) (by omega)
  have hz := zsum_bounds__solver_heap_maintain _ _ _ hbl1
  rw [hll1] at hz
  have hbn : ∀ q, (0 ≤ q ∧ q < i+1) → -600000000000 ≤ Znth q l1 0 ∧ Znth q l1 0 ≤ 4000 := by
    intro q hq
    rw [← prefix_nth l1 (i+1) q hq]
    exact hbl1 _ (Znth_In__solver_heap_maintain _ q (by omega))
  have hhc : HeapContent sb (i+1) (sublist 0 (i+1) l1) (ZSum (sublist 0 i hl)+Znth i sb 0) := ⟨min_sub_multiset_whole__solver_heap_maintain _ _ hp1,hzs⟩
  have hmax : Int.max_signed = (2147483647:Int) := rfl
  have hminI : Int.min_signed = (-2147483648:Int) := rfl
  Exists sb st_2 l1 cb_2 ct_2 sh_2 (i+1)
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st sb_2 hl_2 W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hall := tie_cost_from_sweep__solver_sweep_value contributions sh_2 ct_2 cb_2 st sb_2 hl_2 n_pre k_pre b_pre c_pre W j i hsum
  have hv := hall (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega)
  rcases hv with ⟨hks,hsv,htc,hlo,hhi⟩
  Exists sb_2 hl_2 cb_2 ct_2 sh_2 st
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega | rfl

theorem proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st sb_2 hl_2 W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  subst hsize
  have hall := tie_cost_from_sweep__solver_sweep_value contributions sh_2 ct_2 cb_2 st sb_2 hl_2 n_pre k_pre b_pre c_pre W j i hsum
  have hv := hall (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega)
  rcases hv with ⟨hks,hsv,htc,hlo,hhi⟩
  Exists sb_2 hl_2 cb_2 ct_2 sh_2 st
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega | rfl

theorem proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st sb_2 hl_2 W j best i hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hall := tie_cost_from_sweep__solver_sweep_value contributions sh_2 ct_2 cb_2 st sb_2 hl_2 n_pre k_pre b_pre c_pre W j i hsum
  have hv := hall (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega)
  rcases hv with ⟨hks,hsv,htc,hlo,hhi⟩
  Exists sb_2 hl_2 cb_2 ct_2 sh_2 st
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega | rfl

theorem proof_of_solver_entail_wit_9_4 : solver_entail_wit_9_4 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st sb_2 hl_2 W j best i hsize hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  subst hsize
  have hall := tie_cost_from_sweep__solver_sweep_value contributions sh_2 ct_2 cb_2 st sb_2 hl_2 n_pre k_pre b_pre c_pre W j i hsum
  have hv := hall (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega) (by first | assumption | omega)
  rcases hv with ⟨hks,hsv,htc,hlo,hhi⟩
  Exists sb_2 hl_2 cb_2 ct_2 sh_2 st
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega | rfl

theorem proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st_2 sb_2 hl_2 W j best i hsum total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hn : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1) total := by
    apply best_state_step__solver_best_update (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i) (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1)) best total
    · exact PreH44
    · exact sweep_set_step__solver_best_update contributions k_pre b_pre c_pre j st_2 sb_2 W i total (by omega) PreH42
    · omega
    · exact Or.inl (by omega)
  by_cases hcase : k_pre < i+1
  · Left
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2
    split_pure_spatial
    · Intros; cancel
    · Intros
      split_pures <;> dump_pre_spatial
      all_goals solve | trivial | assumption | omega | tauto
  · Right
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2
    split_pure_spatial
    · Intros; cancel
    · Intros
      split_pures <;> dump_pre_spatial
      all_goals solve | trivial | assumption | omega | tauto

theorem proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st_2 sb_2 hl_2 W j best i hsum total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  have hn : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1) total := by
    apply best_state_step__solver_best_update (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i) (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1)) best total
    · exact PreH46
    · exact sweep_set_step__solver_best_update contributions k_pre b_pre c_pre j st_2 sb_2 W i total (by omega) PreH44
    · omega
    · exact Or.inr (by omega)
  by_cases hcase : k_pre < i+1
  · Left
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2
    split_pure_spatial
    · Intros; cancel
    · Intros
      split_pures <;> dump_pre_spatial
      all_goals solve | trivial | assumption | omega | tauto
  · Right
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2
    split_pure_spatial
    · Intros; cancel
    · Intros
      split_pures <;> dump_pre_spatial
      all_goals solve | trivial | assumption | omega | tauto

theorem proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st_2 sb_2 hl_2 W j best i hsum total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  have hn : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1) best := by
    apply best_state_keep__solver_best_update (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i) (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1)) best total
    · exact PreH46
    · exact sweep_set_step__solver_best_update contributions k_pre b_pre c_pre j st_2 sb_2 W i total (by omega) PreH44
    · omega
    · omega
  by_cases hcase : k_pre < i+1
  · Left
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2
    split_pure_spatial
    · Intros; cancel
    · Intros
      split_pures <;> dump_pre_spatial
      all_goals solve | trivial | assumption | omega | tauto
  · Right
    Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2
    split_pure_spatial
    · Intros; cancel
    · Intros
      split_pures <;> dump_pre_spatial
      all_goals solve | trivial | assumption | omega | tauto

theorem proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st_2 sb_2 hl_2 W j best i hsize_3 hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hn : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1) best := by
    apply best_state_same__solver_best_update (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i) (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1)) best
    · exact sweep_set_stall__solver_best_update contributions k_pre b_pre c_pre j st_2 sb_2 W i (by omega)
    · exact PreH41
  Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2 hsize_3
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega | tauto

theorem proof_of_solver_entail_wit_10_5 : solver_entail_wit_10_5 := by
  left
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sh_2 ct_2 cb_2 st_2 sb_2 hl_2 W j best i hsize_3 hsum PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hn : SweepBest contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1) best := by
    apply best_state_same__solver_best_update (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W i) (SweepSet contributions k_pre b_pre c_pre j st_2 sb_2 W (i+1)) best
    · exact sweep_set_stall__solver_best_update contributions k_pre b_pre c_pre j st_2 sb_2 W i (by omega)
    · exact PreH40
  Exists sb_2 st_2 hl_2 cb_2 ct_2 sh_2 hsize_3
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | omega | tauto

theorem proof_of_solver_entail_wit_11_1_split_goal_1 : solver_entail_wit_11_1_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have he : i=n_pre := by omega
  rw [he] at PreH40
  apply residue_best_of_sweep_best__solver_residue_rollup contributions sh_2 ct_2 cb_2 st sb n_pre k_pre b_pre c_pre j W best
  all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_11_1_split_goal_2 : solver_entail_wit_11_1_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  assumption

theorem proof_of_solver_entail_wit_11_1_split_goal_3 : solver_entail_wit_11_1_split_goal_3 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  assumption

theorem proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1 := by
  unfold solver_entail_wit_11_1
  right
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_11_1_split_goal_1 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
      | exact proof_of_solver_entail_wit_11_1_split_goal_2 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
      | exact proof_of_solver_entail_wit_11_1_split_goal_3 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_solver_entail_wit_11_2_split_goal_1 : solver_entail_wit_11_2_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have he : i=n_pre := by omega
  rw [he] at PreH41
  apply residue_best_of_sweep_best__solver_residue_rollup contributions sh_2 ct_2 cb_2 st sb n_pre k_pre b_pre c_pre j W best
  all_goals solve | trivial | assumption | omega

theorem proof_of_solver_entail_wit_11_2_split_goal_2 : solver_entail_wit_11_2_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  assumption

theorem proof_of_solver_entail_wit_11_2_split_goal_3 : solver_entail_wit_11_2_split_goal_3 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  assumption

theorem proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2 := by
  unfold solver_entail_wit_11_2
  right
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_11_2_split_goal_1 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
      | exact proof_of_solver_entail_wit_11_2_split_goal_2 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
      | exact proof_of_solver_entail_wit_11_2_split_goal_3 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41

theorem proof_of_solver_entail_wit_11_3_split_goal_1 : solver_entail_wit_11_3_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have he : i=n_pre := by omega
  rw [he] at PreH39
  rcases PreH39 with ⟨heq,hnone⟩ | ⟨hge,hm⟩
  · obtain ⟨v,hv⟩ := sweep_set_inhabited__solver_residue_rollup contributions st sb k_pre b_pre c_pre j W n_pre (by omega) (by omega) (by omega)
    exact False.elim (hnone v hv)
  · omega

theorem proof_of_solver_entail_wit_11_3_split_goal_2 : solver_entail_wit_11_3_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  assumption

theorem proof_of_solver_entail_wit_11_3_split_goal_3 : solver_entail_wit_11_3_split_goal_3 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  assumption

theorem proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3 := by
  unfold solver_entail_wit_11_3
  right
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_11_3_split_goal_1 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
      | exact proof_of_solver_entail_wit_11_3_split_goal_2 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
      | exact proof_of_solver_entail_wit_11_3_split_goal_3 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39

theorem proof_of_solver_entail_wit_11_4_split_goal_1 : solver_entail_wit_11_4_split_goal_1 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have he : i=n_pre := by omega
  rw [he] at PreH40
  rcases PreH40 with ⟨heq,hnone⟩ | ⟨hge,hm⟩
  · obtain ⟨v,hv⟩ := sweep_set_inhabited__solver_residue_rollup contributions st sb k_pre b_pre c_pre j W n_pre (by omega) (by omega) (by omega)
    exact False.elim (hnone v hv)
  · omega

theorem proof_of_solver_entail_wit_11_4_split_goal_2 : solver_entail_wit_11_4_split_goal_2 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  assumption

theorem proof_of_solver_entail_wit_11_4_split_goal_3 : solver_entail_wit_11_4_split_goal_3 := by
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  assumption

theorem proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4 := by
  unfold solver_entail_wit_11_4
  right
  intro c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_11_4_split_goal_1 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
      | exact proof_of_solver_entail_wit_11_4_split_goal_2 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
      | exact proof_of_solver_entail_wit_11_4_split_goal_3 c_pre b_pre k_pre n_pre contributions sb st hl_2 cb_2 ct_2 sh_2 hsum hsize i best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_solver_entail_wit_12_1_split_goal_1 : solver_entail_wit_12_1_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dump_pre_spatial
  have hj : j=5 := by omega
  subst j
  rcases PreH24 with ⟨heq,hnone⟩ | ⟨hge,hm⟩
  · omega
  · apply min_value_of_subset_ext__solver_final_spec _ _ _ _ hm
    exact tie_cost_residue_cover__solver_final_spec contributions k_pre b_pre c_pre

theorem proof_of_solver_entail_wit_12_1_split_goal_spatial : solver_entail_wit_12_1_split_goal_spatial := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  sep_apply (int64Array.full_to_full_shape shifted_pre n_pre sh)
  sep_apply (int64Array.full_to_full_shape cand_t_pre n_pre ct)
  sep_apply (int64Array.full_to_full_shape cand_base_pre n_pre cb)
  sep_apply (int64Array.full_to_full_shape heap_pre n_pre hl)
  cancel

theorem proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1 := by
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · exact proof_of_solver_entail_wit_12_1_split_goal_spatial heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  · exact proof_of_solver_entail_wit_12_1_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_12_2_split_goal_1 : solver_entail_wit_12_2_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  have hj : j=5 := by omega
  subst j
  rcases PreH23 with ⟨heq,hnone⟩ | ⟨hge,hm⟩
  · obtain ⟨v,hv⟩ := tie_cost_inhabited__solver_final_spec contributions k_pre b_pre c_pre (by omega) (by omega) (by omega) (by omega)
    exact False.elim (hnone v ((tie_cost_residue_cover__solver_final_spec contributions k_pre b_pre c_pre v).mpr hv))
  · omega

theorem proof_of_solver_entail_wit_12_2_split_goal_spatial : solver_entail_wit_12_2_split_goal_spatial := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  sep_apply (int64Array.full_to_full_shape shifted_pre n_pre sh)
  sep_apply (int64Array.full_to_full_shape cand_t_pre n_pre ct)
  sep_apply (int64Array.full_to_full_shape cand_base_pre n_pre cb)
  sep_apply (int64Array.full_to_full_shape heap_pre n_pre hl)
  cancel

theorem proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2 := by
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · exact proof_of_solver_entail_wit_12_2_split_goal_spatial heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  · exact proof_of_solver_entail_wit_12_2_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre contributions hl cb ct sh best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_partial_solve_wit_11_pure_split_goal_1 : solver_partial_solve_wit_11_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  dump_pre_spatial
  intro i hi
  have hb := PreH41 i (by omega)
  exact hb

theorem proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure := by
  unfold solver_partial_solve_wit_11_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  all_goals first
    | exact proof_of_solver_partial_solve_wit_11_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42

theorem proof_of_solver_partial_solve_wit_12_pure_split_goal_1 : solver_partial_solve_wit_12_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  dump_pre_spatial
  intro i hi
  have hb := PreH40 i (by omega)
  exact hb

theorem proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure := by
  unfold solver_partial_solve_wit_12_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  all_goals first
    | exact proof_of_solver_partial_solve_wit_12_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions hl cb ct sh i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41

theorem proof_of_solver_partial_solve_wit_17_pure_split_goal_1 : solver_partial_solve_wit_17_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  dump_pre_spatial
  intro i hi
  have hb := PreH54 i (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_17_pure : solver_partial_solve_wit_17_pure := by
  unfold solver_partial_solve_wit_17_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  all_goals first
    | exact proof_of_solver_partial_solve_wit_17_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58

theorem proof_of_solver_partial_solve_wit_18_pure_split_goal_1 : solver_partial_solve_wit_18_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61
  dump_pre_spatial
  intro i hi
  have hb := PreH57 i (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_18_pure : solver_partial_solve_wit_18_pure := by
  unfold solver_partial_solve_wit_18_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61
  all_goals first
    | exact proof_of_solver_partial_solve_wit_18_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61

theorem proof_of_solver_partial_solve_wit_19_pure_split_goal_1 : solver_partial_solve_wit_19_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  dump_pre_spatial
  intro i hi
  have hb := PreH53 i (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_19_pure : solver_partial_solve_wit_19_pure := by
  unfold solver_partial_solve_wit_19_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  all_goals first
    | exact proof_of_solver_partial_solve_wit_19_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57

theorem proof_of_solver_partial_solve_wit_20_pure_split_goal_1 : solver_partial_solve_wit_20_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60
  dump_pre_spatial
  intro i hi
  have hb := PreH56 i (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_20_pure : solver_partial_solve_wit_20_pure := by
  unfold solver_partial_solve_wit_20_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60
  all_goals first
    | exact proof_of_solver_partial_solve_wit_20_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_2 best j W PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60

theorem proof_of_solver_partial_solve_wit_21_pure_split_goal_1 : solver_partial_solve_wit_21_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_21_pure_split_goal_2 : solver_partial_solve_wit_21_pure_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_21_pure_split_goal_3 : solver_partial_solve_wit_21_pure_split_goal_3 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_21_pure_split_goal_4 : solver_partial_solve_wit_21_pure_split_goal_4 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_21_pure_split_goal_5 : solver_partial_solve_wit_21_pure_split_goal_5 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  assumption

theorem proof_of_solver_partial_solve_wit_21_pure_split_goal_6 : solver_partial_solve_wit_21_pure_split_goal_6 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  have hz := zsum_range_from_znth__solver_hpop_call_pre hl k_pre (-600000000000) 4000 (by omega) (fun q hq => PreH61 q (by omega))
  have hb := PreH60 i_2 (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_21_pure_split_goal_7 : solver_partial_solve_wit_21_pure_split_goal_7 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  have hz := zsum_range_from_znth__solver_hpop_call_pre hl k_pre (-600000000000) 4000 (by omega) (fun q hq => PreH61 q (by omega))
  have hb := PreH60 i_2 (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_21_pure : solver_partial_solve_wit_21_pure := by
  unfold solver_partial_solve_wit_21_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  split_pures
  all_goals first
    | exact proof_of_solver_partial_solve_wit_21_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_21_pure_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_21_pure_split_goal_3 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_21_pure_split_goal_4 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_21_pure_split_goal_5 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_21_pure_split_goal_6 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_21_pure_split_goal_7 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65

theorem proof_of_solver_partial_solve_wit_22_pure_split_goal_1 : solver_partial_solve_wit_22_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
  dump_pre_spatial
  subst hsize
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_22_pure_split_goal_2 : solver_partial_solve_wit_22_pure_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
  dump_pre_spatial
  subst hsize
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_22_pure_split_goal_3 : solver_partial_solve_wit_22_pure_split_goal_3 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
  dump_pre_spatial
  subst hsize
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_22_pure_split_goal_4 : solver_partial_solve_wit_22_pure_split_goal_4 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
  dump_pre_spatial
  subst hsize
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_22_pure_split_goal_5 : solver_partial_solve_wit_22_pure_split_goal_5 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
  dump_pre_spatial
  assumption

theorem proof_of_solver_partial_solve_wit_22_pure_split_goal_6 : solver_partial_solve_wit_22_pure_split_goal_6 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  have hz := zsum_range_from_znth__solver_hpop_call_pre hl hsize (-600000000000) 4000 (by omega) (fun q hq => PreH62 q (by omega))
  have hb := PreH61 i_3 (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_22_pure_split_goal_7 : solver_partial_solve_wit_22_pure_split_goal_7 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  have hz := zsum_range_from_znth__solver_hpop_call_pre hl hsize (-600000000000) 4000 (by omega) (fun q hq => PreH62 q (by omega))
  have hb := PreH61 i_3 (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_22_pure : solver_partial_solve_wit_22_pure := by
  unfold solver_partial_solve_wit_22_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
  split_pures
  all_goals first
    | exact proof_of_solver_partial_solve_wit_22_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
    | exact proof_of_solver_partial_solve_wit_22_pure_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
    | exact proof_of_solver_partial_solve_wit_22_pure_split_goal_3 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
    | exact proof_of_solver_partial_solve_wit_22_pure_split_goal_4 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
    | exact proof_of_solver_partial_solve_wit_22_pure_split_goal_5 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
    | exact proof_of_solver_partial_solve_wit_22_pure_split_goal_6 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66
    | exact proof_of_solver_partial_solve_wit_22_pure_split_goal_7 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66

theorem proof_of_solver_partial_solve_wit_23_pure_split_goal_1 : solver_partial_solve_wit_23_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_23_pure_split_goal_2 : solver_partial_solve_wit_23_pure_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_23_pure_split_goal_3 : solver_partial_solve_wit_23_pure_split_goal_3 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_23_pure_split_goal_4 : solver_partial_solve_wit_23_pure_split_goal_4 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_23_pure_split_goal_5 : solver_partial_solve_wit_23_pure_split_goal_5 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
  dump_pre_spatial
  assumption

theorem proof_of_solver_partial_solve_wit_23_pure_split_goal_6 : solver_partial_solve_wit_23_pure_split_goal_6 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  have hz := zsum_range_from_znth__solver_hpop_call_pre hl k_pre (-600000000000) 4000 (by omega) (fun q hq => PreH60 q (by omega))
  have hb := PreH59 i_2 (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_23_pure_split_goal_7 : solver_partial_solve_wit_23_pure_split_goal_7 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  have hz := zsum_range_from_znth__solver_hpop_call_pre hl k_pre (-600000000000) 4000 (by omega) (fun q hq => PreH60 q (by omega))
  have hb := PreH59 i_2 (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_23_pure : solver_partial_solve_wit_23_pure := by
  unfold solver_partial_solve_wit_23_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
  split_pures
  all_goals first
    | exact proof_of_solver_partial_solve_wit_23_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
    | exact proof_of_solver_partial_solve_wit_23_pure_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
    | exact proof_of_solver_partial_solve_wit_23_pure_split_goal_3 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
    | exact proof_of_solver_partial_solve_wit_23_pure_split_goal_4 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
    | exact proof_of_solver_partial_solve_wit_23_pure_split_goal_5 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
    | exact proof_of_solver_partial_solve_wit_23_pure_split_goal_6 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64
    | exact proof_of_solver_partial_solve_wit_23_pure_split_goal_7 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum i_2 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64

theorem proof_of_solver_partial_solve_wit_24_pure_split_goal_1 : solver_partial_solve_wit_24_pure_split_goal_1 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  subst hsize
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_24_pure_split_goal_2 : solver_partial_solve_wit_24_pure_split_goal_2 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  subst hsize
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_24_pure_split_goal_3 : solver_partial_solve_wit_24_pure_split_goal_3 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  subst hsize
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_24_pure_split_goal_4 : solver_partial_solve_wit_24_pure_split_goal_4 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  subst hsize
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  omega

theorem proof_of_solver_partial_solve_wit_24_pure_split_goal_5 : solver_partial_solve_wit_24_pure_split_goal_5 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  assumption

theorem proof_of_solver_partial_solve_wit_24_pure_split_goal_6 : solver_partial_solve_wit_24_pure_split_goal_6 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  have hz := zsum_range_from_znth__solver_hpop_call_pre hl hsize (-600000000000) 4000 (by omega) (fun q hq => PreH61 q (by omega))
  have hb := PreH60 i_3 (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_24_pure_split_goal_7 : solver_partial_solve_wit_24_pure_split_goal_7 := by
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  dump_pre_spatial
  rw [zsum_permutation__solver_hpop_call_pre _ _ PreH24, zsum_cons__solver_hpop_call_pre]
  have hz := zsum_range_from_znth__solver_hpop_call_pre hl hsize (-600000000000) 4000 (by omega) (fun q hq => PreH61 q (by omega))
  have hb := PreH60 i_3 (by omega)
  omega

theorem proof_of_solver_partial_solve_wit_24_pure : solver_partial_solve_wit_24_pure := by
  unfold solver_partial_solve_wit_24_pure
  right
  intro heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
  split_pures
  all_goals first
    | exact proof_of_solver_partial_solve_wit_24_pure_split_goal_1 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_24_pure_split_goal_2 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_24_pure_split_goal_3 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_24_pure_split_goal_4 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_24_pure_split_goal_5 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_24_pure_split_goal_6 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65
    | exact proof_of_solver_partial_solve_wit_24_pure_split_goal_7 heap_pre cand_base_pre cand_t_pre shifted_pre c_pre b_pre k_pre n_pre values_pre contributions sb st hl cb ct sh hsum hsize i_3 best j W l1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_proof_manual
