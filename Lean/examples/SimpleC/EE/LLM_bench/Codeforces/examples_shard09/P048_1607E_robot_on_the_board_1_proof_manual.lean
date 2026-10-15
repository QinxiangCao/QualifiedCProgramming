import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_goal
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro col_pre row_pre m_pre n_pre moves PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  unfold WindowFits;omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro col_pre row_pre m_pre n_pre moves PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  exact prefix_window_zero__initialization moves

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro col_pre row_pre m_pre n_pre moves PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  exact PreH9

theorem proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial := by
  intro col_pre row_pre m_pre n_pre moves PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  change naive_C_Rules.derivable1 (naive_C_Rules.sepcon (row_pre # Int |-> (1 : Int)) (col_pre # Int |-> (1 : Int))) (naive_C_Rules.sepcon (intArray.full row_pre 1 ([1] : List Int)) (intArray.full col_pre 1 ([1] : List Int)))
  rel_rw [intArray.full_unfold row_pre 1 ([] : List Int) (1 : Int),intArray.full_unfold col_pre 1 ([] : List Int) (1 : Int),intArray.seg_empty row_pre 1,intArray.seg_empty col_pre 1]
  entailer!
  all_goals try simp only [Int.zero_mul,Int.add_zero] at *
  all_goals first | assumption | exact naive_C_Rules.toContext.derivable1_refl _

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro col_pre row_pre m_pre n_pre moves PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · exact proof_of_solver_entail_wit_1_split_goal_spatial col_pre row_pre m_pre n_pre moves PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  · split_pures
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 col_pre row_pre m_pre n_pre moves PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_solver_entail_wit_1_split_goal_2 col_pre row_pre m_pre n_pre moves PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_solver_entail_wit_1_split_goal_3 col_pre row_pre m_pre n_pre moves PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_1_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_2_1_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_2_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_2_2_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hi := nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30
    
  rw [Znth_app_left__down_new_max moves [0] 0 i ⟨PreH12,hi⟩] at PreH31
  apply prefix_window_step_up_new_min__up_new_min moves i r c minr maxr minc maxc ⟨PreH12,hi⟩ PreH31.symm PreH28
  all_goals omega

theorem proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_3_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_2_3_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_2_4_split_goal_1 : solver_entail_wit_2_4_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_4_split_goal_2 : solver_entail_wit_2_4_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_4_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_2_4_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_2_5_split_goal_1 : solver_entail_wit_2_5_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_5_split_goal_2 : solver_entail_wit_2_5_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_5_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_2_5_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_2_6_split_goal_1 : solver_entail_wit_2_6_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_6_split_goal_2 : solver_entail_wit_2_6_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_6 : solver_entail_wit_2_6 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_6_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_2_6_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_2_7_split_goal_1 : solver_entail_wit_2_7_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_7_split_goal_2 : solver_entail_wit_2_7_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_7 : solver_entail_wit_2_7 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_7_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_2_7_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_2_8_split_goal_1 : solver_entail_wit_2_8_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_8_split_goal_2 : solver_entail_wit_2_8_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_8 : solver_entail_wit_2_8 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_8_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_2_8_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_2_9_split_goal_1 : solver_entail_wit_2_9_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hi := nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30
    
  rw [Znth_app_left__down_new_max moves [0] 0 i ⟨PreH12,hi⟩] at PreH31
  apply prefix_window_step_up_inside__up_inside moves i r c minr maxr minc maxc ⟨PreH12,hi⟩ PreH31.symm PreH28
  all_goals omega

theorem proof_of_solver_entail_wit_2_9_split_goal_2 : solver_entail_wit_2_9_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_9 : solver_entail_wit_2_9 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_9_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_2_9_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_2_10_split_goal_1 : solver_entail_wit_2_10_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_10_split_goal_2 : solver_entail_wit_2_10_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_10 : solver_entail_wit_2_10 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_10_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
      | exact proof_of_solver_entail_wit_2_10_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32

theorem proof_of_solver_entail_wit_2_11_split_goal_1 : solver_entail_wit_2_11_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_11_split_goal_2 : solver_entail_wit_2_11_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_11 : solver_entail_wit_2_11 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_11_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
      | exact proof_of_solver_entail_wit_2_11_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32

theorem proof_of_solver_entail_wit_2_12_split_goal_1 : solver_entail_wit_2_12_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_12_split_goal_2 : solver_entail_wit_2_12_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_12 : solver_entail_wit_2_12 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_12_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
      | exact proof_of_solver_entail_wit_2_12_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32

theorem proof_of_solver_entail_wit_2_13_split_goal_1 : solver_entail_wit_2_13_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_13_split_goal_2 : solver_entail_wit_2_13_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_13 : solver_entail_wit_2_13 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_13_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
      | exact proof_of_solver_entail_wit_2_13_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32

theorem proof_of_solver_entail_wit_2_14_split_goal_1 : solver_entail_wit_2_14_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_14_split_goal_2 : solver_entail_wit_2_14_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_14 : solver_entail_wit_2_14 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_14_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
      | exact proof_of_solver_entail_wit_2_14_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32

theorem proof_of_solver_entail_wit_2_15_split_goal_1 : solver_entail_wit_2_15_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hi := nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30
    
  rw [Znth_app_left__down_new_max moves [0] 0 i ⟨PreH12,hi⟩] at PreH32
  apply prefix_window_step_down_new_max__down_new_max moves i r c minr maxr minc maxc ⟨PreH12,hi⟩ PreH32.symm PreH28
  all_goals omega

theorem proof_of_solver_entail_wit_2_15_split_goal_2 : solver_entail_wit_2_15_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_15 : solver_entail_wit_2_15 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_15_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
      | exact proof_of_solver_entail_wit_2_15_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32

theorem proof_of_solver_entail_wit_2_16_split_goal_1 : solver_entail_wit_2_16_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_16_split_goal_2 : solver_entail_wit_2_16_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_16 : solver_entail_wit_2_16 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_16_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
      | exact proof_of_solver_entail_wit_2_16_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32

theorem proof_of_solver_entail_wit_2_17_split_goal_1 : solver_entail_wit_2_17_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_17_split_goal_2 : solver_entail_wit_2_17_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_17 : solver_entail_wit_2_17 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_17_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
      | exact proof_of_solver_entail_wit_2_17_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32

theorem proof_of_solver_entail_wit_2_18_split_goal_1 : solver_entail_wit_2_18_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hi := nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30
    
  rw [Znth_app_left__down_new_max moves [0] 0 i ⟨PreH12,hi⟩] at PreH32
  apply prefix_window_step_down_inside__down_inside moves i r c minr maxr minc maxc ⟨PreH12,hi⟩ PreH32.symm PreH28
  all_goals omega

theorem proof_of_solver_entail_wit_2_18_split_goal_2 : solver_entail_wit_2_18_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_18 : solver_entail_wit_2_18 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_18_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
      | exact proof_of_solver_entail_wit_2_18_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32

theorem proof_of_solver_entail_wit_2_19_split_goal_1 : solver_entail_wit_2_19_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_19_split_goal_2 : solver_entail_wit_2_19_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_19 : solver_entail_wit_2_19 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_19_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_19_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_20_split_goal_1 : solver_entail_wit_2_20_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_20_split_goal_2 : solver_entail_wit_2_20_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_20 : solver_entail_wit_2_20 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_20_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_20_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_21_split_goal_1 : solver_entail_wit_2_21_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_21_split_goal_2 : solver_entail_wit_2_21_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_21 : solver_entail_wit_2_21 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_21_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_21_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_22_split_goal_1 : solver_entail_wit_2_22_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_22_split_goal_2 : solver_entail_wit_2_22_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_22 : solver_entail_wit_2_22 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_22_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_22_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_23_split_goal_1 : solver_entail_wit_2_23_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_23_split_goal_2 : solver_entail_wit_2_23_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_23 : solver_entail_wit_2_23 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_23_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_23_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_24_split_goal_1 : solver_entail_wit_2_24_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_24_split_goal_2 : solver_entail_wit_2_24_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_24 : solver_entail_wit_2_24 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_24_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_24_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_25_split_goal_1 : solver_entail_wit_2_25_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hi := nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30
  rw [Znth_app_left__down_new_max moves [0] 0 i ⟨PreH12,hi⟩] at PreH33
  have hh := prefix_window_step_left_cases__left_valid_row moves i r c minr maxr minc maxc ⟨PreH12,hi⟩ PreH33.symm PreH28
  rw [min_eq_right (by omega)] at hh
  exact hh

theorem proof_of_solver_entail_wit_2_25_split_goal_2 : solver_entail_wit_2_25_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_25 : solver_entail_wit_2_25 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_25_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_25_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_26_split_goal_1 : solver_entail_wit_2_26_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_26_split_goal_2 : solver_entail_wit_2_26_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_26 : solver_entail_wit_2_26 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_26_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_26_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_27_split_goal_1 : solver_entail_wit_2_27_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hi := nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30
  rw [Znth_app_left__down_new_max moves [0] 0 i ⟨PreH12,hi⟩] at PreH33
  have hh := prefix_window_step_left_cases__left_valid_row moves i r c minr maxr minc maxc ⟨PreH12,hi⟩ PreH33.symm PreH28
  rw [min_eq_left (by omega)] at hh
  exact hh

theorem proof_of_solver_entail_wit_2_27_split_goal_2 : solver_entail_wit_2_27_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_27 : solver_entail_wit_2_27 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_27_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_27_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_28_split_goal_1 : solver_entail_wit_2_28_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_28_split_goal_2 : solver_entail_wit_2_28_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_28 : solver_entail_wit_2_28 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_28_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_28_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_29_split_goal_1 : solver_entail_wit_2_29_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_29_split_goal_2 : solver_entail_wit_2_29_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_29 : solver_entail_wit_2_29 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_29_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_29_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_30_split_goal_1 : solver_entail_wit_2_30_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_30_split_goal_2 : solver_entail_wit_2_30_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_30 : solver_entail_wit_2_30 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_30_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_30_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_31_split_goal_1 : solver_entail_wit_2_31_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_31_split_goal_2 : solver_entail_wit_2_31_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_31 : solver_entail_wit_2_31 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_31_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_31_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_32_split_goal_1 : solver_entail_wit_2_32_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_32_split_goal_2 : solver_entail_wit_2_32_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_32 : solver_entail_wit_2_32 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_32_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_32_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_33_split_goal_1 : solver_entail_wit_2_33_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_33_split_goal_2 : solver_entail_wit_2_33_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_33 : solver_entail_wit_2_33 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_33_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_33_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_34_split_goal_1 : solver_entail_wit_2_34_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rcases PreH28 with ⟨hq,hr,hc,hzr,hzc,hall,hext⟩
  have hb := hall i (by omega)
  omega

theorem proof_of_solver_entail_wit_2_34_split_goal_2 : solver_entail_wit_2_34_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_34 : solver_entail_wit_2_34 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_34_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_34_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_35_split_goal_1 : solver_entail_wit_2_35_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hi := nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30
  simp only [Znth_app_left__down_new_max moves [0] 0 i ⟨PreH12,hi⟩] at PreH31 PreH32 PreH33
  have halpha := PreH11 i ⟨PreH12,hi⟩
  have hcmd : Znth i moves 0=82 := by omega
  exact (prefix_window_step_right_cases__right_valid_row moves i r c minr maxr minc maxc PreH28 hi hcmd (by omega)).1 (by omega)

theorem proof_of_solver_entail_wit_2_35_split_goal_2 : solver_entail_wit_2_35_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_35 : solver_entail_wit_2_35 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_35_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_35_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_2_36_split_goal_1 : solver_entail_wit_2_36_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hi := nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30
  simp only [Znth_app_left__down_new_max moves [0] 0 i ⟨PreH12,hi⟩] at PreH31 PreH32 PreH33
  have halpha := PreH11 i ⟨PreH12,hi⟩
  have hcmd : Znth i moves 0=82 := by omega
  exact (prefix_window_step_right_cases__right_valid_row moves i r c minr maxr minc maxc PreH28 hi hcmd (by omega)).2 (by omega)

theorem proof_of_solver_entail_wit_2_36_split_goal_2 : solver_entail_wit_2_36_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact nonzero_Znth_sentinel_lt__left_valid_row moves i ⟨PreH12,PreH13⟩ PreH30

theorem proof_of_solver_entail_wit_2_36 : solver_entail_wit_2_36 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_36_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
      | exact proof_of_solver_entail_wit_2_36_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  unfold WindowFits;omega

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  intro m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  first | assumption | omega

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  right
  intro m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_3_split_goal_1 m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
      | exact proof_of_solver_entail_wit_3_split_goal_2 m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36

theorem proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hi : i=Zlength moves := by
    by_contra hn
    have hil : 0≤i ∧ i<Zlength moves := by omega
    rw [Znth_app_left__down_new_max moves [0] 0 i hil] at PreH26
    have hc := PreH7 i hil
    omega
  exact optimal_prefix_at_end__termination_optimality n_pre m_pre moves i r c minr maxr minc maxc hi PreH24 PreH25

theorem proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2 := by
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  first | assumption | omega

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  right
  intro m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_1_split_goal_1 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
      | exact proof_of_solver_entail_wit_4_1_split_goal_2 m_pre n_pre moves bc br maxc minc maxr minr c r i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1 := by
  intro m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact optimal_prefix_before_overflow__termination_optimality n_pre m_pre moves i oldr oldc r c minr maxr minc maxc nminr nmaxr nminc nmaxc PreH33 PreH34 PreH35 (by omega)

theorem proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2 := by
  intro m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  first | assumption | omega

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  right
  intro m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_2_split_goal_1 m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
      | exact proof_of_solver_entail_wit_4_2_split_goal_2 m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35

theorem proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1 := by
  intro m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  exact optimal_prefix_before_overflow__termination_optimality n_pre m_pre moves i oldr oldc r c minr maxr minc maxc nminr nmaxr nminc nmaxc PreH34 PreH35 PreH36 (by omega)

theorem proof_of_solver_entail_wit_4_3_split_goal_2 : solver_entail_wit_4_3_split_goal_2 := by
  intro m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  first | assumption | omega

theorem proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3 := by
  right
  intro m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_3_split_goal_1 m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
      | exact proof_of_solver_entail_wit_4_3_split_goal_2 m_pre n_pre moves oldr oldc i r c minr maxr minc maxc nminr nmaxr nminc nmaxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro col_pre row_pre m_pre n_pre moves r c minr maxr minc maxc br bc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  Exists ((1-minr,1-minc) : Int×Int)
  simp only [fst,snd]
  split_pure_spatial
  · rel_rw [intArray.full_unfold row_pre 1 [] (1-minr),intArray.full_unfold col_pre 1 [] (1-minc),intArray.seg_empty row_pre 1,intArray.seg_empty col_pre 1]
    entailer!
    all_goals try simp only [Int.zero_mul,Int.add_zero] at *
    all_goals first | assumption | exact naive_C_Rules.toContext.derivable1_refl _
  · dump_pre_spatial
    exact optimal_window_realizes_spec__final_result n_pre m_pre moves minr maxr minc maxc PreH26

theorem proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1 := by
  left
  intro row col
  change naive_C_Rules.derivable1 (naive_C_Rules.sepcon (intArray.undef_full row (0+1)) (intArray.undef_full col (0+1))) (naive_C_Rules.sepcon (row # Int |->_) (col # Int |->_))
  rel_rw [intArray.undef_full_unfold row 0 ([] : List Int) (by omega),intArray.undef_full_unfold col 0 ([] : List Int) (by omega)]
  simp only [Int.zero_add]
  rel_rw [intArray.undef_seg_empty row 1,intArray.undef_seg_empty col 1]
  entailer!
  all_goals try simp only [Int.zero_mul,Int.add_zero] at *
  all_goals first | assumption | exact naive_C_Rules.toContext.derivable1_refl _

theorem proof_of_solver_which_implies_wit_2_split_goal_spatial : solver_which_implies_wit_2_split_goal_spatial := by
  intro row col
  change naive_C_Rules.derivable1 (naive_C_Rules.sepcon (intArray.full row 1 ([1] : List Int)) (intArray.full col 1 ([1] : List Int))) (naive_C_Rules.sepcon (row # Int |-> (1 : Int)) (col # Int |-> (1 : Int)))
  rel_rw [intArray.full_unfold row 1 ([] : List Int) (1 : Int),intArray.full_unfold col 1 ([] : List Int) (1 : Int),intArray.seg_empty row 1,intArray.seg_empty col 1]
  entailer!
  all_goals try simp only [Int.zero_mul,Int.add_zero] at *
  all_goals first | assumption | exact naive_C_Rules.toContext.derivable1_refl _

theorem proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2 := by
  right
  intro row col
  exact proof_of_solver_which_implies_wit_2_split_goal_spatial row col

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_proof_manual
