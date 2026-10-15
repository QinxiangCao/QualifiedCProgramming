import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array

theorem proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hx := PreH10 i (by omega)
  have hc := PreH11 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hx := PreH10 i (by omega)
  have hc := PreH11 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_11 : solver_safety_wit_11 := by
  unfold solver_safety_wit_11
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_11_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_solver_safety_wit_11_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hx := PreH10 i (by omega)
  have hc := PreH11 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hx := PreH10 i (by omega)
  have hc := PreH11 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_13 : solver_safety_wit_13 := by
  unfold solver_safety_wit_13
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_13_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_solver_safety_wit_13_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  have hd := PreH23 (Znth i prog 0) (by omega)
  simp only [DP_INF] at hd
  omega

theorem proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  have hd := PreH23 (Znth i prog 0) (by omega)
  simp only [DP_INF] at hd
  omega

theorem proof_of_solver_safety_wit_17 : solver_safety_wit_17 := by
  unfold solver_safety_wit_17
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_17_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_safety_wit_17_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  have hd := PreH23 (Znth i prog 0) (by omega)
  simp only [DP_INF] at hd
  omega

theorem proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  have hd := PreH23 (Znth i prog 0) (by omega)
  simp only [DP_INF] at hd
  omega

theorem proof_of_solver_safety_wit_19 : solver_safety_wit_19 := by
  unfold solver_safety_wit_19
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_19_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_safety_wit_19_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_safety_wit_21_split_goal_1 : solver_safety_wit_21_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_21_split_goal_2 : solver_safety_wit_21_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_21 : solver_safety_wit_21 := by
  unfold solver_safety_wit_21
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_21_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    | exact proof_of_solver_safety_wit_21_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_safety_wit_22_split_goal_1 : solver_safety_wit_22_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_22_split_goal_2 : solver_safety_wit_22_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_22 : solver_safety_wit_22 := by
  unfold solver_safety_wit_22
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_22_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    | exact proof_of_solver_safety_wit_22_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_23 : solver_safety_wit_23 := by
  unfold solver_safety_wit_23
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_23_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    | exact proof_of_solver_safety_wit_23_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_24 : solver_safety_wit_24 := by
  unfold solver_safety_wit_24
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_24_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    | exact proof_of_solver_safety_wit_24_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_25 : solver_safety_wit_25 := by
  unfold solver_safety_wit_25
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_25_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_safety_wit_25_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_safety_wit_26_split_goal_1 : solver_safety_wit_26_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_26_split_goal_2 : solver_safety_wit_26_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_26 : solver_safety_wit_26 := by
  unfold solver_safety_wit_26
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_26_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_safety_wit_26_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_safety_wit_28_split_goal_1 : solver_safety_wit_28_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hd := PreH24 (Znth i prog 0) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_28_split_goal_2 : solver_safety_wit_28_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hd := PreH24 (Znth i prog 0) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_28 : solver_safety_wit_28 := by
  unfold solver_safety_wit_28
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_28_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    | exact proof_of_solver_safety_wit_28_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_safety_wit_29_split_goal_1 : solver_safety_wit_29_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hd := PreH24 (Znth i prog 0) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_29_split_goal_2 : solver_safety_wit_29_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hd := PreH24 (Znth i prog 0) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_29 : solver_safety_wit_29 := by
  unfold solver_safety_wit_29
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_29_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    | exact proof_of_solver_safety_wit_29_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_safety_wit_31_split_goal_1 : solver_safety_wit_31_split_goal_1 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= 9223372036854775807)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_31_split_goal_2 : solver_safety_wit_31_split_goal_2 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hc := PreH12 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_safety_wit_31 : solver_safety_wit_31 := by
  unfold solver_safety_wit_31
  right
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_31_split_goal_1 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_safety_wit_31_split_goal_2 d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  intro q hq
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rfl

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact PreH6

theorem proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4 := by
  intro k_pre n_pre hot_costs cold_costs prog PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact PreH5

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro k_pre n_pre hot_costs cold_costs prog PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 k_pre n_pre hot_costs cold_costs prog PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_solver_entail_wit_1_split_goal_2 k_pre n_pre hot_costs cold_costs prog PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_solver_entail_wit_1_split_goal_3 k_pre n_pre hot_costs cold_costs prog PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_solver_entail_wit_1_split_goal_4 k_pre n_pre hot_costs cold_costs prog PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog initialized_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro k_pre n_pre hot_costs cold_costs prog initialized_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 k_pre n_pre hot_costs cold_costs prog initialized_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  left
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog initialized j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hj : j=k_pre+1 := by omega
  have hlen : Zlength initialized=k_pre+1 := by omega
  rw [hj]
  have hp := PreH9 0 (by omega)
  have hcost := PreH10 (Znth 0 prog 0-1) (by omega)
  have hcold := Znth_cons 0 (Znth 0 prog 0) 0 cold_costs (by omega)
  have hdlen := Zlength_replace_Znth initialized 0 (0:Int)
  have hd0 := Znth_replace_Znth_Same 0 initialized 0 (0:Int) (by omega)
  have hdr : ∀ q, (0 ≤ q ∧ q ≤ k_pre) → Znth q (replace_Znth 0 0 initialized) 0 = DP_INF ∨ (-1)*1000000000 ≤ Znth q (replace_Znth 0 0 initialized) 0 ∧ Znth q (replace_Znth 0 0 initialized) 0 ≤ 1*1000000000 := by
    intro q hq
    by_cases he : q=0
    · subst q; rw [hd0]; right; omega
    · left
      rw [Znth_replace_Znth_Diff 0 initialized 0 q 0 (by omega) (by omega) (Ne.symm he)]
      exact PreH14 q (by omega)
  have hstate := normalized_schedule_state_initial__initialization prog cold_costs hot_costs initialized n_pre k_pre PreH2 PreH6 PreH4 PreH7 PreH8 PreH9 PreH10 hlen (fun q hq => PreH14 q (by omega))
  Exists (replace_Znth 0 0 initialized)
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals solve | trivial | assumption | (simp only [hcold,DP_INF] at *; omega)

theorem proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  intro hcond
  have hx := PreH12 i (by omega)
  have hy := PreH12 (i-1) (by omega)
  generalize hxdef : Znth i prog 0 = x at *
  generalize hydef : Znth (i-1) prog 0 = y at *
  have hc := PreH13 (x-1) (by omega)
  have hhot := Znth_cons 0 x 0 hot_costs (by omega)
  have hcold := Znth_cons 0 x 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hd := Znth_indep dp x DP_INF 0 (by omega)
  have hm := normalized_schedule_state_min_le__state_transitions prog cold_costs hot_costs i dp off mind x PreH25 (by omega) (by rw [hd]; exact PreH2)
  rw [hd] at hm
  apply normalized_schedule_state_step__state_transitions prog cold_costs hot_costs i dp off mind x y (Znth (x-1) hot_costs 0) (Znth x dp 0+off+Znth (x-1) hot_costs 0) (Znth x dp 0) dp mind
  · omega
  · exact hxdef.symm
  · exact hydef.symm
  · omega
  · omega
  · omega
  · intro q hq; have hq' := PreH12 q (by omega); omega
  · exact hc.1.2
  · exact PreH25
  · simp only [if_pos PreH3]
  · omega
  · simpa only [DP_INF] using PreH2
  · omega
  · intro hf; rw [hd]
  · right; rw [hd]; exact ⟨by simpa only [DP_INF] using PreH2,rfl⟩
  · right
    rw [← PreH3,hd]
    exact ⟨le_refl _,rfl⟩
  · exact Or.inr ⟨hm,rfl⟩

theorem proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simpa only [Int.add_sub_cancel] using PreH25

theorem proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hd := Znth_indep dp (Znth i prog 0) DP_INF 0 (by omega)
  have hm := normalized_schedule_state_min_le__state_transitions prog cold_costs hot_costs i dp off mind (Znth i prog 0) PreH25 (by omega) (by rw [hd]; exact PreH2)
  rw [hd] at hm
  omega

theorem proof_of_solver_entail_wit_4_1_split_goal_4 : solver_entail_wit_4_1_split_goal_4 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_1_split_goal_5 : solver_entail_wit_4_1_split_goal_5 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  assumption

theorem proof_of_solver_entail_wit_4_1_split_goal_6 : solver_entail_wit_4_1_split_goal_6 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_1_split_goal_7 : solver_entail_wit_4_1_split_goal_7 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_1_split_goal_8 : solver_entail_wit_4_1_split_goal_8 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_1_split_goal_9 : solver_entail_wit_4_1_split_goal_9 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_1_split_goal_10 : solver_entail_wit_4_1_split_goal_10 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact PreH13

theorem proof_of_solver_entail_wit_4_1_split_goal_11 : solver_entail_wit_4_1_split_goal_11 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact PreH12

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  unfold solver_entail_wit_4_1
  right
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_1_split_goal_1 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_2 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_3 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_4 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_5 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_6 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_7 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_8 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_9 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_10 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_1_split_goal_11 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  intro hcond
  have hx := PreH12 i (by omega)
  have hy := PreH12 (i-1) (by omega)
  generalize hxdef : Znth i prog 0 = x at *
  generalize hydef : Znth (i-1) prog 0 = y at *
  have hc := PreH13 (x-1) (by omega)
  have hhot := Znth_cons 0 x 0 hot_costs (by omega)
  have hcold := Znth_cons 0 x 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hb := normalized_unequal_transition_branches__state_transitions prog cold_costs hot_costs i dp off mind x y (by omega) hxdef.symm hydef.symm (by omega) (by omega) (by omega) (fun q hq => by have h := PreH12 q (by omega); omega) hc.1.2 PreH25 PreH3 (by simpa only [DP_INF] using PreH2) PreH1
  exact hb.1 (by omega)

theorem proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  intro hcond
  have hx := PreH12 i (by omega)
  have hy := PreH12 (i-1) (by omega)
  generalize hxdef : Znth i prog 0 = x at *
  generalize hydef : Znth (i-1) prog 0 = y at *
  have hc := PreH13 (x-1) (by omega)
  have hhot := Znth_cons 0 x 0 hot_costs (by omega)
  have hcold := Znth_cons 0 x 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hb := normalized_unequal_transition_branches__state_transitions prog cold_costs hot_costs i dp off mind x y (by omega) hxdef.symm hydef.symm (by omega) (by omega) (by omega) (fun q hq => by have h := PreH12 q (by omega); omega) hc.1.2 PreH25 PreH3 (by simpa only [DP_INF] using PreH2) PreH1
  have he : Znth x dp 0+off+Znth (x-1) hot_costs 0-(off+Znth (x-1) cold_costs 0)=Znth x dp 0+Znth (x-1) hot_costs 0-Znth (x-1) cold_costs 0 := by omega
  rw [he] at hcond ⊢
  exact hb.2.1 hcond

theorem proof_of_solver_entail_wit_4_2_split_goal_3 : solver_entail_wit_4_2_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simpa only [Int.add_sub_cancel] using PreH25

theorem proof_of_solver_entail_wit_4_2_split_goal_4 : solver_entail_wit_4_2_split_goal_4 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hd := Znth_indep dp (Znth i prog 0) DP_INF 0 (by omega)
  have hm := normalized_schedule_state_min_le__state_transitions prog cold_costs hot_costs i dp off mind (Znth i prog 0) PreH25 (by omega) (by rw [hd]; exact PreH2)
  rw [hd] at hm
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_5 : solver_entail_wit_4_2_split_goal_5 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_6 : solver_entail_wit_4_2_split_goal_6 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hb := PreH24 (Znth i prog 0) (by omega)
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_7 : solver_entail_wit_4_2_split_goal_7 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_8 : solver_entail_wit_4_2_split_goal_8 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_9 : solver_entail_wit_4_2_split_goal_9 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_10 : solver_entail_wit_4_2_split_goal_10 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_11 : solver_entail_wit_4_2_split_goal_11 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hc := PreH13 (Znth i prog 0-1) (by omega)
  have hhot := Znth_cons 0 (Znth i prog 0) 0 hot_costs (by omega)
  have hcold := Znth_cons 0 (Znth i prog 0) 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_12 : solver_entail_wit_4_2_split_goal_12 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact PreH13

theorem proof_of_solver_entail_wit_4_2_split_goal_13 : solver_entail_wit_4_2_split_goal_13 := by
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact PreH12

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  unfold solver_entail_wit_4_2
  right
  intro k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_2_split_goal_1 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_2 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_3 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_4 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_5 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_6 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_7 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_8 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_9 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_10 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_11 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_12 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_solver_entail_wit_4_2_split_goal_13 k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hy := PreH12 (i-1) (by omega)
  generalize hxdef : Znth i prog 0 = x at *
  generalize hydef : Znth (i-1) prog 0 = y at *
  have hc := PreH13 (x-1) (by omega)
  have hhot := Znth_cons 0 x 0 hot_costs (by omega)
  have hcold := Znth_cons 0 x 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hbase : mind+off+Znth (x-1) cold_costs 0 ≤ Znth x dp_2 0+off+Znth (x-1) hot_costs 0 := by omega
  have hb := normalized_baseline_transition_branches__state_transitions prog cold_costs hot_costs i dp_2 off mind x y (Znth (x-1) hot_costs 0) (by omega) hxdef.symm hydef.symm (by omega) (by omega) (by omega) (fun q hq => by have h := PreH12 q (by omega); omega) hc.1.2 PreH25 (if_pos PreH3).symm (by omega) hc.2 PreH21 hbase
  have hny : mind+off+Znth (x-1) cold_costs 0-(off+Znth (x-1) hot_costs 0)=mind+Znth (x-1) cold_costs 0-Znth (x-1) hot_costs 0 := by omega
  Left
  Exists dp_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals try simp only [hny,Int.add_sub_cancel]
    all_goals solve
      | trivial
      | assumption
      | omega
      | exact hb.1
      | exact hb.2.1
      | exact hb.2.2

theorem proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hx := PreH12 i (by omega)
  have hy := PreH12 (i-1) (by omega)
  generalize hxdef : Znth i prog 0 = x at *
  generalize hydef : Znth (i-1) prog 0 = y at *
  have hc := PreH13 (x-1) (by omega)
  have hhot := Znth_cons 0 x 0 hot_costs (by omega)
  have hcold := Znth_cons 0 x 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hbase : mind+off+Znth (x-1) cold_costs 0 ≤ Znth x dp_2 0+off+Znth (x-1) hot_costs 0 := by omega
  have hb := normalized_baseline_transition_branches__state_transitions prog cold_costs hot_costs i dp_2 off mind x y (Znth (x-1) cold_costs 0) (by omega) hxdef.symm hydef.symm (by omega) (by omega) (by omega) (fun q hq => by have h := PreH12 q (by omega); omega) hc.1.2 PreH25 (if_neg PreH3).symm (by omega) hc.2 PreH21 hbase
  dsimp only at hb
  simp only [Int.add_sub_cancel] at hb
  have hny : mind+off+Znth (x-1) cold_costs 0-(off+Znth (x-1) cold_costs 0)=mind+Znth (x-1) cold_costs 0-Znth (x-1) cold_costs 0 := by omega
  Left
  Exists dp_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals try simp only [hny,Int.add_sub_cancel]
    all_goals solve
      | trivial
      | assumption
      | omega
      | exact hb.1
      | exact hb.2.1
      | exact hb.2.2

theorem proof_of_solver_entail_wit_4_5 : solver_entail_wit_4_5 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hy := PreH11 (i-1) (by omega)
  generalize hxdef : Znth i prog 0 = x at *
  generalize hydef : Znth (i-1) prog 0 = y at *
  have hc := PreH12 (x-1) (by omega)
  have hhot := Znth_cons 0 x 0 hot_costs (by omega)
  have hcold := Znth_cons 0 x 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hbase : mind+off+Znth (x-1) cold_costs 0 ≤ Znth x dp_2 0+off+Znth (x-1) hot_costs 0 := by omega
  have hb := normalized_baseline_transition_branches__state_transitions prog cold_costs hot_costs i dp_2 off mind x y (Znth (x-1) hot_costs 0) (by omega) hxdef.symm hydef.symm (by omega) (by omega) (by omega) (fun q hq => by have h := PreH11 q (by omega); omega) hc.1.2 PreH24 (if_pos PreH2).symm (by omega) hc.2 PreH20 hbase
  have hny : mind+off+Znth (x-1) cold_costs 0-(off+Znth (x-1) hot_costs 0)=mind+Znth (x-1) cold_costs 0-Znth (x-1) hot_costs 0 := by omega
  Left
  Exists dp_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals try simp only [hny,Int.add_sub_cancel]
    all_goals solve
      | trivial
      | assumption
      | omega
      | exact hb.1
      | exact hb.2.1
      | exact hb.2.2

theorem proof_of_solver_entail_wit_4_6 : solver_entail_wit_4_6 := by
  intro d_pre hot_pre cold_pre k_pre n_pre a_pre hot_costs cold_costs prog mind off dp_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hx := PreH11 i (by omega)
  have hy := PreH11 (i-1) (by omega)
  generalize hxdef : Znth i prog 0 = x at *
  generalize hydef : Znth (i-1) prog 0 = y at *
  have hc := PreH12 (x-1) (by omega)
  have hhot := Znth_cons 0 x 0 hot_costs (by omega)
  have hcold := Znth_cons 0 x 0 cold_costs (by omega)
  simp only [hhot,hcold] at *
  have hbase : mind+off+Znth (x-1) cold_costs 0 ≤ Znth x dp_2 0+off+Znth (x-1) hot_costs 0 := by omega
  have hb := normalized_baseline_transition_branches__state_transitions prog cold_costs hot_costs i dp_2 off mind x y (Znth (x-1) cold_costs 0) (by omega) hxdef.symm hydef.symm (by omega) (by omega) (by omega) (fun q hq => by have h := PreH11 q (by omega); omega) hc.1.2 PreH24 (if_neg PreH2).symm (by omega) hc.2 PreH20 hbase
  dsimp only at hb
  simp only [Int.add_sub_cancel] at hb
  have hny : mind+off+Znth (x-1) cold_costs 0-(off+Znth (x-1) cold_costs 0)=mind+Znth (x-1) cold_costs 0-Znth (x-1) cold_costs 0 := by omega
  Left
  Exists dp_2
  split_pure_spatial
  · Intros; cancel
  · Intros
    split_pures <;> dump_pre_spatial
    all_goals try simp only [hny,Int.add_sub_cancel]
    all_goals solve
      | trivial
      | assumption
      | omega
      | exact hb.1
      | exact hb.2.1
      | exact hb.2.2

theorem proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  apply replace_Znth_dp_bounds__state_write_update
  all_goals solve | assumption | omega

theorem proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  apply Znth_zero_replace_positive__state_write_update
  · omega
  · exact PreH25

theorem proof_of_solver_entail_wit_5_1_split_goal_3 : solver_entail_wit_5_1_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  simpa only [Zlength_replace_Znth] using PreH24

theorem proof_of_solver_entail_wit_5_1_split_goal_4 : solver_entail_wit_5_1_split_goal_4 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  assumption

theorem proof_of_solver_entail_wit_5_1_split_goal_5 : solver_entail_wit_5_1_split_goal_5 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  assumption

theorem proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1 := by
  unfold solver_entail_wit_5_1
  right
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_1_split_goal_1 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_1_split_goal_2 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_1_split_goal_3 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_1_split_goal_4 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_1_split_goal_5 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45

theorem proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  apply replace_Znth_dp_bounds__state_write_update
  all_goals solve | assumption | omega

theorem proof_of_solver_entail_wit_5_2_split_goal_2 : solver_entail_wit_5_2_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  apply Znth_zero_replace_positive__state_write_update
  · omega
  · exact PreH25

theorem proof_of_solver_entail_wit_5_2_split_goal_3 : solver_entail_wit_5_2_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  simpa only [Zlength_replace_Znth] using PreH24

theorem proof_of_solver_entail_wit_5_2_split_goal_4 : solver_entail_wit_5_2_split_goal_4 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  assumption

theorem proof_of_solver_entail_wit_5_2_split_goal_5 : solver_entail_wit_5_2_split_goal_5 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  assumption

theorem proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2 := by
  unfold solver_entail_wit_5_2
  right
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_2_split_goal_1 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
      | exact proof_of_solver_entail_wit_5_2_split_goal_2 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
      | exact proof_of_solver_entail_wit_5_2_split_goal_3 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
      | exact proof_of_solver_entail_wit_5_2_split_goal_4 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
      | exact proof_of_solver_entail_wit_5_2_split_goal_5 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46

theorem proof_of_solver_entail_wit_5_3_split_goal_1 : solver_entail_wit_5_3_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  apply replace_Znth_dp_bounds__state_write_update
  all_goals solve | assumption | omega

theorem proof_of_solver_entail_wit_5_3_split_goal_2 : solver_entail_wit_5_3_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  apply Znth_zero_replace_positive__state_write_update
  · omega
  · exact PreH25

theorem proof_of_solver_entail_wit_5_3_split_goal_3 : solver_entail_wit_5_3_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  simpa only [Zlength_replace_Znth] using PreH24

theorem proof_of_solver_entail_wit_5_3_split_goal_4 : solver_entail_wit_5_3_split_goal_4 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  assumption

theorem proof_of_solver_entail_wit_5_3_split_goal_5 : solver_entail_wit_5_3_split_goal_5 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  assumption

theorem proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3 := by
  unfold solver_entail_wit_5_3
  right
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_3_split_goal_1 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_3_split_goal_2 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_3_split_goal_3 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_3_split_goal_4 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_3_split_goal_5 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45

theorem proof_of_solver_entail_wit_5_4_split_goal_1 : solver_entail_wit_5_4_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  apply replace_Znth_dp_bounds__state_write_update
  all_goals solve | assumption | omega

theorem proof_of_solver_entail_wit_5_4_split_goal_2 : solver_entail_wit_5_4_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  apply Znth_zero_replace_positive__state_write_update
  · omega
  · exact PreH25

theorem proof_of_solver_entail_wit_5_4_split_goal_3 : solver_entail_wit_5_4_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  simpa only [Zlength_replace_Znth] using PreH24

theorem proof_of_solver_entail_wit_5_4_split_goal_4 : solver_entail_wit_5_4_split_goal_4 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  assumption

theorem proof_of_solver_entail_wit_5_4_split_goal_5 : solver_entail_wit_5_4_split_goal_5 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  assumption

theorem proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4 := by
  unfold solver_entail_wit_5_4
  right
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_4_split_goal_1 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_4_split_goal_2 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_4_split_goal_3 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_4_split_goal_4 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_4_split_goal_5 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45

theorem proof_of_solver_entail_wit_5_5_split_goal_1 : solver_entail_wit_5_5_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  apply replace_Znth_dp_bounds__state_write_update
  all_goals solve | assumption | omega

theorem proof_of_solver_entail_wit_5_5_split_goal_2 : solver_entail_wit_5_5_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  apply Znth_zero_replace_positive__state_write_update
  · omega
  · exact PreH25

theorem proof_of_solver_entail_wit_5_5_split_goal_3 : solver_entail_wit_5_5_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  simpa only [Zlength_replace_Znth] using PreH24

theorem proof_of_solver_entail_wit_5_5_split_goal_4 : solver_entail_wit_5_5_split_goal_4 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  assumption

theorem proof_of_solver_entail_wit_5_5_split_goal_5 : solver_entail_wit_5_5_split_goal_5 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  assumption

theorem proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5 := by
  unfold solver_entail_wit_5_5
  right
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_5_split_goal_1 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
      | exact proof_of_solver_entail_wit_5_5_split_goal_2 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
      | exact proof_of_solver_entail_wit_5_5_split_goal_3 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
      | exact proof_of_solver_entail_wit_5_5_split_goal_4 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
      | exact proof_of_solver_entail_wit_5_5_split_goal_5 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46

theorem proof_of_solver_entail_wit_5_6_split_goal_1 : solver_entail_wit_5_6_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  intro q hq
  have hb := PreH33 q hq
  rcases hb with he | hb
  · exact Or.inl he
  · right; omega

theorem proof_of_solver_entail_wit_5_6_split_goal_2 : solver_entail_wit_5_6_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  exact PreH10

theorem proof_of_solver_entail_wit_5_6_split_goal_3 : solver_entail_wit_5_6_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  exact PreH9

theorem proof_of_solver_entail_wit_5_6 : solver_entail_wit_5_6 := by
  unfold solver_entail_wit_5_6
  right
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_6_split_goal_1 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
      | exact proof_of_solver_entail_wit_5_6_split_goal_2 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
      | exact proof_of_solver_entail_wit_5_6_split_goal_3 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44

theorem proof_of_solver_entail_wit_5_7_split_goal_1 : solver_entail_wit_5_7_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  intro q hq
  have hb := PreH33 q hq
  rcases hb with he | hb
  · exact Or.inl he
  · right; omega

theorem proof_of_solver_entail_wit_5_7_split_goal_2 : solver_entail_wit_5_7_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  exact PreH10

theorem proof_of_solver_entail_wit_5_7_split_goal_3 : solver_entail_wit_5_7_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  exact PreH9

theorem proof_of_solver_entail_wit_5_7 : solver_entail_wit_5_7 := by
  unfold solver_entail_wit_5_7
  right
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_7_split_goal_1 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_7_split_goal_2 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_7_split_goal_3 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45

theorem proof_of_solver_entail_wit_5_8_split_goal_1 : solver_entail_wit_5_8_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  intro q hq
  have hb := PreH33 q hq
  rcases hb with he | hb
  · exact Or.inl he
  · right; omega

theorem proof_of_solver_entail_wit_5_8_split_goal_2 : solver_entail_wit_5_8_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  exact PreH10

theorem proof_of_solver_entail_wit_5_8_split_goal_3 : solver_entail_wit_5_8_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  exact PreH9

theorem proof_of_solver_entail_wit_5_8 : solver_entail_wit_5_8 := by
  unfold solver_entail_wit_5_8
  right
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_8_split_goal_1 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
      | exact proof_of_solver_entail_wit_5_8_split_goal_2 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
      | exact proof_of_solver_entail_wit_5_8_split_goal_3 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44

theorem proof_of_solver_entail_wit_5_9_split_goal_1 : solver_entail_wit_5_9_split_goal_1 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  intro q hq
  have hb := PreH33 q hq
  rcases hb with he | hb
  · exact Or.inl he
  · right; omega

theorem proof_of_solver_entail_wit_5_9_split_goal_2 : solver_entail_wit_5_9_split_goal_2 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  exact PreH10

theorem proof_of_solver_entail_wit_5_9_split_goal_3 : solver_entail_wit_5_9_split_goal_3 := by
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  exact PreH9

theorem proof_of_solver_entail_wit_5_9 : solver_entail_wit_5_9 := by
  unfold solver_entail_wit_5_9
  right
  intro k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_9_split_goal_1 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_9_split_goal_2 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
      | exact proof_of_solver_entail_wit_5_9_split_goal_3 k_pre n_pre hot_costs cold_costs prog dp_2 i x y costA off mind candB ny PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro d_pre k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  dump_pre_spatial
  have he : i=Zlength prog := by omega
  rw [he] at PreH22
  have h := normalized_schedule_state_full_spec prog cold_costs hot_costs dp off mind PreH22
  simpa only [Int.add_comm] using h

theorem proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial := by
  intro d_pre k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  sep_apply (int64Array.full_to_full_shape d_pre (k_pre+1) dp)
  cancel

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro d_pre k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · exact proof_of_solver_return_wit_1_split_goal_spatial d_pre k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  · exact proof_of_solver_return_wit_1_split_goal_1 d_pre k_pre n_pre hot_costs cold_costs prog mind off dp i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_proof_manual
