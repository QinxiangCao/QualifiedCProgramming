import SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_goal
import SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open kings_game_goal kings_game_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem hands_from_forall (ps : List minister)
    (hl : Forall (fun x : Int => 1 ≤ x) (ps.map minister_left))
    (hu : Forall (fun x : Int => x ≤ 10) (ps.map minister_left))
    (hr : Forall (fun x : Int => 1 ≤ x) (ps.map minister_right))
    (hv : Forall (fun x : Int => x ≤ 10) (ps.map minister_right)) : MinisterHandsBound ps := by
  apply Forall.iff_forall_mem.mpr
  intro p hp
  exact ⟨⟨hl.mem (List.mem_map.mpr ⟨p, hp, rfl⟩), hu.mem (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩,
    ⟨hr.mem (List.mem_map.mpr ⟨p, hp, rfl⟩), hv.mem (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩⟩

private theorem hands_to_forall (ps : List minister) (h : MinisterHandsBound ps) :
    Forall (fun x : Int => 1 ≤ x) (ps.map minister_left) ∧
    Forall (fun x : Int => x ≤ 10) (ps.map minister_left) ∧
    Forall (fun x : Int => 1 ≤ x) (ps.map minister_right) ∧
    Forall (fun x : Int => x ≤ 10) (ps.map minister_right) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply Forall.iff_forall_mem.mpr
  all_goals intro x hx
  all_goals obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  · exact (h.mem hp).1.1
  · exact (h.mem hp).1.2
  · exact (h.mem hp).2.1
  · exact (h.mem hp).2.2

theorem proof_of_swap_ministers_return_wit_1_split_goal_1 : swap_ministers_return_wit_1_split_goal_1 := by
  unfold swap_ministers_return_wit_1_split_goal_1
  intro ps flat n_pre i_pre j_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 fresh13 fresh14 fresh15 fresh16
  have PreH9 : (MinisterHandsBound ps) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  exact minister_swap_permutation__flat_bubble ps i_pre j_pre ⟨PreH1, by omega⟩ ⟨PreH3, by omega⟩

theorem proof_of_swap_ministers_return_wit_1_split_goal_2 : swap_ministers_return_wit_1_split_goal_2 := by
  pre_process
  exact flat_ministers_swap__flat_bubble flat ps i_pre j_pre PreH8 ⟨PreH1, by omega⟩ ⟨PreH3, by omega⟩

theorem proof_of_swap_ministers_return_wit_1_split_goal_3 : swap_ministers_return_wit_1_split_goal_3 := by
  pre_process
  exact minister_swap_flat_preprocess_form__flat_bubble flat n_pre i_pre j_pre
    (by rw [flat_ministers_Zlength__flat_bubble flat ps PreH8, PreH7]) ⟨PreH1, PreH2⟩ ⟨PreH3, PreH4⟩

theorem proof_of_swap_ministers_return_wit_1 : swap_ministers_return_wit_1 := by
  unfold swap_ministers_return_wit_1
  right
  pre_process
  have hp := minister_swap_permutation__flat_bubble ps i_pre j_pre ⟨PreH1, by omega⟩ ⟨PreH3, by omega⟩
  have hf := flat_ministers_swap__flat_bubble flat ps i_pre j_pre PreH8 ⟨PreH1, by omega⟩ ⟨PreH3, by omega⟩
  have he := minister_swap_flat_preprocess_form__flat_bubble flat n_pre i_pre j_pre
    (by rw [flat_ministers_Zlength__flat_bubble flat ps PreH8, PreH7]) ⟨PreH1, PreH2⟩ ⟨PreH3, PreH4⟩
  entailer!

theorem proof_of_kings_game_safety_wit_28_split_goal_1 : kings_game_safety_wit_28_split_goal_1 := by
  unfold kings_game_safety_wit_28_split_goal_1
  intro input input_flat ministers_pre n_pre king_left_pre king_right_pre ans_pre j pass flat_cur cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh20 fresh21 fresh22 fresh23 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 fresh30 fresh31 fresh32 fresh33 PreH18 PreH19 PreH20
  have PreH10 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH17 : (MinisterHandsBound cur) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hb := flat_minister_product_bounds__flat_bubble flat_cur cur (j+1) PreH16 PreH17 ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_kings_game_safety_wit_28_split_goal_2 : kings_game_safety_wit_28_split_goal_2 := by
  unfold kings_game_safety_wit_28_split_goal_2
  intro input input_flat ministers_pre n_pre king_left_pre king_right_pre ans_pre j pass flat_cur cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh20 fresh21 fresh22 fresh23 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 fresh30 fresh31 fresh32 fresh33 PreH18 PreH19 PreH20
  have PreH10 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH17 : (MinisterHandsBound cur) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hb := flat_minister_product_bounds__flat_bubble flat_cur cur (j+1) PreH16 PreH17 ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_kings_game_safety_wit_28 : kings_game_safety_wit_28 := by
  unfold kings_game_safety_wit_28
  right
  intro input input_flat ministers_pre n_pre king_left_pre king_right_pre ans_pre j pass flat_cur cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh20 fresh21 fresh22 fresh23 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 fresh30 fresh31 fresh32 fresh33 PreH18 PreH19 PreH20
  have PreH10 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH17 : (MinisterHandsBound cur) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hb := flat_minister_product_bounds__flat_bubble flat_cur cur (j+1) PreH16 PreH17 ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_kings_game_safety_wit_29_split_goal_1 : kings_game_safety_wit_29_split_goal_1 := by
  unfold kings_game_safety_wit_29_split_goal_1
  intro input input_flat ministers_pre n_pre king_left_pre king_right_pre ans_pre j pass flat_cur cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh20 fresh21 fresh22 fresh23 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 fresh30 fresh31 fresh32 fresh33 PreH18 PreH19 PreH20
  have PreH10 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH17 : (MinisterHandsBound cur) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hb := flat_minister_product_bounds__flat_bubble flat_cur cur j PreH16 PreH17 ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_kings_game_safety_wit_29_split_goal_2 : kings_game_safety_wit_29_split_goal_2 := by
  unfold kings_game_safety_wit_29_split_goal_2
  intro input input_flat ministers_pre n_pre king_left_pre king_right_pre ans_pre j pass flat_cur cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh20 fresh21 fresh22 fresh23 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 fresh30 fresh31 fresh32 fresh33 PreH18 PreH19 PreH20
  have PreH10 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH17 : (MinisterHandsBound cur) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hb := flat_minister_product_bounds__flat_bubble flat_cur cur j PreH16 PreH17 ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_kings_game_safety_wit_29 : kings_game_safety_wit_29 := by
  unfold kings_game_safety_wit_29
  right
  intro input input_flat ministers_pre n_pre king_left_pre king_right_pre ans_pre j pass flat_cur cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh20 fresh21 fresh22 fresh23 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 fresh30 fresh31 fresh32 fresh33 PreH18 PreH19 PreH20
  have PreH10 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH17 : (MinisterHandsBound cur) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hb := flat_minister_product_bounds__flat_bubble flat_cur cur j PreH16 PreH17 ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_kings_game_entail_wit_1_split_goal_1 : kings_game_entail_wit_1_split_goal_1 := by
  unfold kings_game_entail_wit_1_split_goal_1
  intro input input_flat n_pre king_left_pre king_right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 fresh13 fresh14 fresh15 fresh16
  have PreH9 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  rw [flat_ministers_Zlength__flat_bubble input_flat input PreH8, PreH7]

theorem proof_of_kings_game_entail_wit_1_split_goal_2 : kings_game_entail_wit_1_split_goal_2 := by
  unfold kings_game_entail_wit_1_split_goal_2
  intro input input_flat n_pre king_left_pre king_right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 fresh13 fresh14 fresh15 fresh16
  have PreH9 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  rfl

theorem proof_of_kings_game_entail_wit_1 : kings_game_entail_wit_1 := by
  unfold kings_game_entail_wit_1
  right
  intro input input_flat n_pre king_left_pre king_right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 fresh13 fresh14 fresh15 fresh16
  have PreH9 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (apply (proof_of_kings_game_entail_wit_1_split_goal_1 input input_flat n_pre king_left_pre king_right_pre) <;> first | assumption | omega)
      | (apply (proof_of_kings_game_entail_wit_1_split_goal_2 input input_flat n_pre king_left_pre king_right_pre) <;> first | assumption | omega)

theorem proof_of_kings_game_entail_wit_2_split_goal_1 : kings_game_entail_wit_2_split_goal_1 := by
  unfold kings_game_entail_wit_2_split_goal_1
  intro input input_flat n_pre king_left_pre king_right_pre k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 fresh16 fresh17 fresh18 fresh19 PreH12 PreH13
  have PreH11 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  rw [sublist_split 0 (k+1) k input_flat ⟨by omega, PreH12⟩ ⟨by omega, by omega⟩,
    sublist_single 0 k input_flat ⟨PreH12, by omega⟩]

theorem proof_of_kings_game_entail_wit_2 : kings_game_entail_wit_2 := by
  unfold kings_game_entail_wit_2
  right
  intro input input_flat n_pre king_left_pre king_right_pre k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 fresh16 fresh17 fresh18 fresh19 PreH12 PreH13
  have PreH11 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (apply (proof_of_kings_game_entail_wit_2_split_goal_1 input input_flat n_pre king_left_pre king_right_pre k) <;> first | assumption | omega)

theorem proof_of_kings_game_entail_wit_3 : kings_game_entail_wit_3 := by
  unfold kings_game_entail_wit_3
  right
  intro input input_flat n_pre king_left_pre king_right_pre k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 fresh17 fresh18 fresh19 fresh20 PreH12 PreH13
  have PreH11 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have he : k = 2*n_pre := by omega
  have hs := bubble_outer_initial__flat_bubble input n_pre PreH8
  refine Automation.exp_right_rule (CRules := naive_C_Rules) input ?_
  rw [sublist_self input_flat k (by omega), PreH8]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact List.Perm.refl _ | omega

theorem proof_of_kings_game_entail_wit_4 : kings_game_entail_wit_4 := by
  unfold kings_game_entail_wit_4
  right
  intro input input_flat n_pre king_left_pre king_right_pre flat_cur_2 cur_2 pass PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh17 fresh18 fresh19 fresh20 PreH11 PreH12 PreH13 PreH14 fresh25 fresh26 fresh27 fresh28 PreH16 PreH17
  have PreH10 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH15 : (MinisterHandsBound cur_2) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hscan := bubble_scan_initial__flat_bubble cur_2 n_pre pass (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cur_2 ?_
  rw [PreH8]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_kings_game_entail_wit_5_1 : kings_game_entail_wit_5_1 := by
  unfold kings_game_entail_wit_5_1
  right
  intro input input_flat n_pre king_left_pre king_right_pre j pass flat_cur_2 cur_2 PreH2 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 fresh21 fresh22 fresh23 fresh24 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 fresh31 fresh32 fresh33 fresh34 PreH23 PreH24 PreH25
  have PreH15 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH22 : (MinisterHandsBound cur_2) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hj : 0 ≤ j ∧ j < Zlength cur_2 := ⟨PreH18, by omega⟩
  have hj1 : 0 ≤ j+1 ∧ j+1 < Zlength cur_2 := ⟨by omega, by omega⟩
  have PreH3 := minister_swap_hands_bound__flat_bubble cur_2 j (j+1) PreH22 hj hj1
  obtain ⟨swl, swu, swr, swv⟩ := hands_to_forall _ PreH3
  have PreH1 : Zlength (minister_swap cur_2 j (j+1)) = n_pre := by
    rw [minister_swap_Zlength__flat_bubble]; exact PreH20
  have hprod := flat_minister_product_eq__flat_bubble flat_cur_2 cur_2 j PreH21 hj
  have hprod1 := flat_minister_product_eq__flat_bubble flat_cur_2 cur_2 (j+1) PreH21 hj1
  have hkey : MinisterProductLe (Znth (j+1) cur_2 default_minister) (Znth j cur_2 default_minister) := by
    unfold MinisterProductLe; rw [← hprod, ← hprod1]; omega
  have houter := bubble_outer_swap_prefix__flat_bubble cur_2 n_pre pass j PreH20 PreH16 PreH18 (by omega) PreH24
  have hscan := bubble_scan_step_swap__flat_bubble cur_2 n_pre pass j PreH20 PreH16 PreH18 (by omega) PreH25 hkey
  have hperm : MinisterPermutation input (minister_swap cur_2 j (j+1)) := PreH23.trans PreH4
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (minister_swap cur_2 j (j+1)) ?_
  rw [PreH1]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simpa only [PreH13] using hscan) | (simpa only [PreH13] using houter)

theorem proof_of_kings_game_entail_wit_5_2 : kings_game_entail_wit_5_2 := by
  unfold kings_game_entail_wit_5_2
  right
  intro input input_flat n_pre king_left_pre king_right_pre j pass flat_cur_2 cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 fresh19 fresh20 fresh21 fresh22 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 fresh29 fresh30 fresh31 fresh32 PreH19 PreH20 PreH21
  have PreH11 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH18 : (MinisterHandsBound cur_2) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hj : 0 ≤ j ∧ j < Zlength cur_2 := ⟨PreH14, by omega⟩
  have hj1 : 0 ≤ j+1 ∧ j+1 < Zlength cur_2 := ⟨by omega, by omega⟩
  have hprod := flat_minister_product_eq__flat_bubble flat_cur_2 cur_2 j PreH17 hj
  have hprod1 := flat_minister_product_eq__flat_bubble flat_cur_2 cur_2 (j+1) PreH17 hj1
  have hkey : MinisterProductLe (Znth j cur_2 default_minister) (Znth (j+1) cur_2 default_minister) := by
    unfold MinisterProductLe; rw [← hprod, ← hprod1]; exact PreH1
  have hscan := bubble_scan_step_no_swap__flat_bubble cur_2 n_pre pass j PreH16 (by omega) PreH21 hkey
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cur_2 ?_
  rw [PreH9]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_kings_game_entail_wit_6 : kings_game_entail_wit_6 := by
  unfold kings_game_entail_wit_6
  right
  intro input input_flat n_pre king_left_pre king_right_pre flat_cur_2 cur_2 j pass PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh18 fresh19 fresh20 fresh21 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 fresh28 fresh29 fresh30 fresh31 PreH18 PreH19 PreH20
  have PreH10 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH17 : (MinisterHandsBound cur_2) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have houter := bubble_outer_finish_pass__flat_bubble cur_2 n_pre pass j (by omega) PreH19 PreH20
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cur_2 ?_
  rw [PreH8]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_kings_game_return_wit_1 : kings_game_return_wit_1 := by
  unfold kings_game_return_wit_1
  right
  intro input input_flat n_pre king_left_pre king_right_pre flat_cur cur pass PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh17 fresh18 fresh19 fresh20 PreH11 PreH12 PreH13 PreH14 fresh25 fresh26 fresh27 fresh28 PreH16 PreH17
  have PreH10 : (MinisterHandsBound input) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have PreH15 : (MinisterHandsBound cur) := hands_from_forall _ (by assumption) (by assumption) (by assumption) (by assumption)
  have hs := bubble_outer_final_sorted__greedy_optimum cur n_pre pass PreH1 PreH12 PreH17
  have hresult := positive_sorted_realizes_kings_optimum__greedy_optimum input cur king_left_pre
    (by omega) (by omega) PreH15 hs PreH16
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cur ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

end SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_proof_manual
