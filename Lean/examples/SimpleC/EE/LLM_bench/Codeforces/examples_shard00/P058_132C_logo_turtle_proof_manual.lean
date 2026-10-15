import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_goal
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev charArray := naive_C_Rules.CharArray

private theorem cell_bound_le (limit f d w s : Int) (hc : f*2+d+1≤(limit+1)*2) (hw : 0≤w) (hs : s≤w) :
    (f*2+d)*w+s≤((limit+1)*2)*w := by
  have hm:=mul_le_mul_of_nonneg_right hc hw
  nlinarith only [hm,hs]
private theorem cell_bound_lt (limit f d w s : Int) (hc : f*2+d+1≤(limit+1)*2) (hw : 0≤w) (hs : s<w) :
    (f*2+d)*w+s<((limit+1)*2)*w := by
  have hm:=mul_le_mul_of_nonneg_right hc hw
  nlinarith only [hm,hs]

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro changes_pre commands n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [PreH4]
  simpa only [TurtleWidth,SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,AUXLib.«repeat»,Int.zero_mul,Int.zero_add,Int.mul_zero] using turtle_layer_zero_table__init_layer commands changes_pre ((changes_pre+1)*2*TurtleWidth commands) PreH5 (by omega) rfl

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro changes_pre commands n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  simp only [Zlength_replace_Znth,SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,Zlength,List.length_replicate,Int.ofNat_eq_coe]
  have hnonneg : 0≤(changes_pre+1)*2*(2*retval+1) := by nlinarith
  omega

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro changes_pre commands n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [Zlength_replace_Znth]
  simp only [SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,Zlength,List.length_replicate,Int.ofNat_eq_coe]
  have hp : 0≤(changes_pre+1)*2*(2*retval+1) := by
    have hc : 0≤changes_pre+1 := by omega
    have hr : 0≤2*retval+1 := by omega
    exact mul_nonneg (mul_nonneg hc (by omega)) hr
  omega

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro changes_pre commands n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 changes_pre commands n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_solver_entail_wit_1_split_goal_2 changes_pre commands n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_solver_entail_wit_1_split_goal_3 changes_pre commands n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro changes_pre commands n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  simpa only [SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,AUXLib.«repeat»,Int.zero_mul,Int.mul_zero] using turtle_next_zero_table__init_layer commands i changes_pre ((changes_pre+1)*2*(2*O+1))

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro changes_pre commands n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  simp only [Zlength_replace_Znth,SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,Zlength,List.length_replicate,Int.ofNat_eq_coe]
  have hnonneg : 0≤(changes_pre+1)*2*(2*O+1) := by nlinarith
  omega

theorem proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3 := by
  intro changes_pre commands n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  first | assumption | omega

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  right
  intro changes_pre commands n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 changes_pre commands n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_solver_entail_wit_2_split_goal_2 changes_pre commands n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_solver_entail_wit_2_split_goal_3 changes_pre commands n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have he : (2 * (((c * 2) + (0 : Int)) * ((2 * O) + 1)))=((4 * c) * W) := by nlinarith
  rw [he]
  exact PreH22

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  first | assumption | omega

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  right
  intro changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_3_split_goal_1 changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_solver_entail_wit_3_split_goal_2 changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have he : (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (0 : Int)))=(2 * (((c * 2) + dir) * W)) := by nlinarith
  rw [he]
  exact PreH23

theorem proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply cell_bound_le changes_pre c dir (2*O+1) 0
  all_goals omega

theorem proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first | assumption | omega

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  right
  intro changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_split_goal_1 changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_4_split_goal_2 changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_4_split_goal_3 changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  intro changes_pre commands n next_table current_table ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  apply cell_bound_lt changes_pre c dir (2*O+1) pos
  all_goals omega

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  right
  intro changes_pre commands n next_table current_table ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_split_goal_1 changes_pre commands n next_table current_table ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have he : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (0 : Int))=(2 * ((((c * 2) + dir) * W) + pos)) := by nlinarith
  rw [he]
  exact PreH36

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  first | assumption | omega

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  right
  intro changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_6_split_goal_1 changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
      | exact proof_of_solver_entail_wit_6_split_goal_2 changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37

theorem proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  rw [binary_lxor_one__direction_bit dir (by omega)]
  omega

theorem proof_of_solver_entail_wit_7_1_split_goal_2 : solver_entail_wit_7_1_split_goal_2 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  rw [binary_lxor_one__direction_bit dir (by omega)]
  omega

theorem proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1 := by
  right
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_7_1_split_goal_1 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
      | exact proof_of_solver_entail_wit_7_1_split_goal_2 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51

theorem proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  rw [binary_lxor_one__direction_bit dir (by omega)]
  omega

theorem proof_of_solver_entail_wit_7_2_split_goal_2 : solver_entail_wit_7_2_split_goal_2 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  rw [binary_lxor_one__direction_bit dir (by omega)]
  omega

theorem proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2 := by
  right
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_7_2_split_goal_1 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
      | exact proof_of_solver_entail_wit_7_2_split_goal_2 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51

theorem proof_of_solver_entail_wit_8_1_split_goal_1 : solver_entail_wit_8_1_split_goal_1 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  apply binary_destination_bound__direction_bit
  all_goals omega

theorem proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1 := by
  right
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_1_split_goal_1 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_8_2_split_goal_1 : solver_entail_wit_8_2_split_goal_1 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  apply binary_destination_bound__direction_bit
  all_goals omega

theorem proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2 := by
  right
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_2_split_goal_1 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_8_3_split_goal_1 : solver_entail_wit_8_3_split_goal_1 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  apply cell_bound_lt changes_pre (c+flip) dir (2*O+1) (pos+(-1))
  all_goals omega

theorem proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3 := by
  right
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_3_split_goal_1 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57

theorem proof_of_solver_entail_wit_8_4_split_goal_1 : solver_entail_wit_8_4_split_goal_1 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  apply cell_bound_lt changes_pre (c+flip) 0 (2*O+1) (pos+1)
  all_goals omega

theorem proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4 := by
  right
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_4_split_goal_1 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57

theorem proof_of_solver_entail_wit_8_5_split_goal_1 : solver_entail_wit_8_5_split_goal_1 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  apply cell_bound_lt changes_pre (c+0) dir (2*O+1) (pos+(-1))
  all_goals omega

theorem proof_of_solver_entail_wit_8_5 : solver_entail_wit_8_5 := by
  right
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_5_split_goal_1 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57

theorem proof_of_solver_entail_wit_8_6_split_goal_1 : solver_entail_wit_8_6_split_goal_1 := by
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  apply cell_bound_lt changes_pre (c+0) 0 (2*O+1) (pos+1)
  all_goals omega

theorem proof_of_solver_entail_wit_8_6 : solver_entail_wit_8_6 := by
  right
  intro changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_6_split_goal_1 changes_pre commands n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57

theorem proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH55
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    try ring
  rw [hdone]
  have hidx : ((((((c + flip) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos))=TurtleCellIndex commands (c+flip) (Z.lxor dir 1) pos := by
    unfold TurtleCellIndex
    rw [hw]
    rw [ho]
    try ring
  rw [hidx]
  have hmeaning:=PreH54 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH48
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH37 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH26
  apply turtle_next_prefix_write_transition__next_update_core commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 84 (c+flip) (Z.lxor dir 1) pos
  · exact hnext
  · simpa only [hw] using PreH53
  · exact hsrc
  · exact hdr
  · exact hpos
  · exact hflip
  · rfl
  · exact hreach
  · rfl
  · omega
  · unfold FlippedCommand
    rcases hc with hc | hc <;> omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    unfold TurtleEncodedStep
    omega
  · omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    omega
  · rw [hw];omega

theorem proof_of_solver_entail_wit_9_1_split_goal_2 : solver_entail_wit_9_1_split_goal_2 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_1_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
      | exact proof_of_solver_entail_wit_9_1_split_goal_2 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  have hflip0 : flip=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH55
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hflip0]
    try ring
  rw [hdone]
  have hidx : ((((((c + (0 : Int)) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos))=TurtleCellIndex commands (c+flip) (Z.lxor dir 1) pos := by
    unfold TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hflip0]
    try ring
  rw [hidx]
  have hmeaning:=PreH54 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH48
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH37 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH26
  apply turtle_next_prefix_write_transition__next_update_core commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 84 (c+flip) (Z.lxor dir 1) pos
  · exact hnext
  · simpa only [hw] using PreH53
  · exact hsrc
  · exact hdr
  · exact hpos
  · exact hflip
  · rfl
  · exact hreach
  · rfl
  · omega
  · unfold FlippedCommand
    rcases hc with hc | hc <;> omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    unfold TurtleEncodedStep
    omega
  · omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    omega
  · rw [hw];omega

theorem proof_of_solver_entail_wit_9_2_split_goal_2 : solver_entail_wit_9_2_split_goal_2 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_2_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
      | exact proof_of_solver_entail_wit_9_2_split_goal_2 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_9_3_split_goal_1 : solver_entail_wit_9_3_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH58
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    try ring
  rw [hdone]
  have hidx : ((((((c + flip) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1))))=TurtleCellIndex commands (c+flip) dir (pos-1) := by
    unfold TurtleCellIndex
    rw [hw]
    rw [ho]
    try ring
  rw [hidx]
  have hmeaning:=PreH57 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH51
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH40 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH29
  apply turtle_next_prefix_write_transition__next_update_core commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 70 (c+flip) dir (pos-1)
  · exact hnext
  · simpa only [hw] using PreH56
  · exact hsrc
  · exact hdr
  · exact hpos
  · exact hflip
  · rfl
  · exact hreach
  · rfl
  · omega
  · unfold FlippedCommand
    rcases hc with hc | hc <;> omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    unfold TurtleEncodedStep
    omega
  · omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    omega
  · rw [hw];omega

theorem proof_of_solver_entail_wit_9_3_split_goal_2 : solver_entail_wit_9_3_split_goal_2 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_3_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
      | exact proof_of_solver_entail_wit_9_3_split_goal_2 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59

theorem proof_of_solver_entail_wit_9_4_split_goal_1 : solver_entail_wit_9_4_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  have hdir0 : dir=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH58
  have hdone : ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + (flip + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hdir0]
    try ring
  rw [hdone]
  have hidx : ((((((c + flip) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1)))=TurtleCellIndex commands (c+flip) dir (pos+1) := by
    unfold TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hdir0]
    try ring
  rw [hidx]
  have hmeaning:=PreH57 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH51
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH40 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH29
  apply turtle_next_prefix_write_transition__next_update_core commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 70 (c+flip) dir (pos+1)
  · exact hnext
  · simpa only [hw] using PreH56
  · exact hsrc
  · exact hdr
  · exact hpos
  · exact hflip
  · rfl
  · exact hreach
  · rfl
  · omega
  · unfold FlippedCommand
    rcases hc with hc | hc <;> omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    unfold TurtleEncodedStep
    omega
  · omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    omega
  · rw [hw];omega

theorem proof_of_solver_entail_wit_9_4_split_goal_2 : solver_entail_wit_9_4_split_goal_2 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_4 : solver_entail_wit_9_4 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_4_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
      | exact proof_of_solver_entail_wit_9_4_split_goal_2 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59

theorem proof_of_solver_entail_wit_9_5_split_goal_1 : solver_entail_wit_9_5_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  have hflip0 : flip=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH58
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hflip0]
    try ring
  rw [hdone]
  have hidx : ((((((c + (0 : Int)) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1))))=TurtleCellIndex commands (c+flip) dir (pos-1) := by
    unfold TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hflip0]
    try ring
  rw [hidx]
  have hmeaning:=PreH57 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH51
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH40 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH29
  apply turtle_next_prefix_write_transition__next_update_core commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 70 (c+flip) dir (pos-1)
  · exact hnext
  · simpa only [hw] using PreH56
  · exact hsrc
  · exact hdr
  · exact hpos
  · exact hflip
  · rfl
  · exact hreach
  · rfl
  · omega
  · unfold FlippedCommand
    rcases hc with hc | hc <;> omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    unfold TurtleEncodedStep
    omega
  · omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    omega
  · rw [hw];omega

theorem proof_of_solver_entail_wit_9_5_split_goal_2 : solver_entail_wit_9_5_split_goal_2 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_5 : solver_entail_wit_9_5 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_5_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
      | exact proof_of_solver_entail_wit_9_5_split_goal_2 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59

theorem proof_of_solver_entail_wit_9_6_split_goal_1 : solver_entail_wit_9_6_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  have hflip0 : flip=0 := by omega
  have hdir0 : dir=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH58
  have hdone : ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hdir0, hflip0]
    try ring
  rw [hdone]
  have hidx : ((((((c + (0 : Int)) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1)))=TurtleCellIndex commands (c+flip) dir (pos+1) := by
    unfold TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hdir0, hflip0]
    try ring
  rw [hidx]
  have hmeaning:=PreH57 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH51
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH40 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH29
  apply turtle_next_prefix_write_transition__next_update_core commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 70 (c+flip) dir (pos+1)
  · exact hnext
  · simpa only [hw] using PreH56
  · exact hsrc
  · exact hdr
  · exact hpos
  · exact hflip
  · rfl
  · exact hreach
  · rfl
  · omega
  · unfold FlippedCommand
    rcases hc with hc | hc <;> omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    unfold TurtleEncodedStep
    omega
  · omega
  · have hx:=binary_lxor_one__direction_bit dir hdr
    omega
  · rw [hw];omega

theorem proof_of_solver_entail_wit_9_6_split_goal_2 : solver_entail_wit_9_6_split_goal_2 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_6 : solver_entail_wit_9_6 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_6_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59
      | exact proof_of_solver_entail_wit_9_6_split_goal_2 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59

theorem proof_of_solver_entail_wit_9_7_split_goal_1 : solver_entail_wit_9_7_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  have hflip0 : flip=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH55
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hflip0]
    try ring
  rw [hdone]
  have hc:=PreH37 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH26
  apply turtle_next_prefix_skip_rank__next_noop commands i changes_pre _ next_table_2 hnext
  intro f d s b e nf nd ns hf hd hs hb hr hp hnf hlim he hstep hnb
  have hid:=turtle_transition_rank_injective__next_noop commands f d s b c dir pos flip hd hs hb hdr hpos hflip hr
  obtain ⟨hf',hd',hs',hb'⟩:=hid
  simp only [hf',hd',hs',hb'] at hnf he hstep
  unfold FlippedCommand at he
  unfold TurtleEncodedStep at hstep
  rw [hw] at hnb
  rcases he with ⟨he1,he2⟩ | ⟨he1,⟨he2,he3⟩ | ⟨he2,he3⟩⟩ <;>
    rcases hstep with ⟨ht1,ht2,ht3⟩ | ⟨ht1,ht2,⟨ht3,ht4⟩ | ⟨ht3,ht4⟩⟩ <;> omega

theorem proof_of_solver_entail_wit_9_7 : solver_entail_wit_9_7 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_7_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_9_8_split_goal_1 : solver_entail_wit_9_8_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH55
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    try ring
  rw [hdone]
  have hc:=PreH37 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH26
  apply turtle_next_prefix_skip_rank__next_noop commands i changes_pre _ next_table_2 hnext
  intro f d s b e nf nd ns hf hd hs hb hr hp hnf hlim he hstep hnb
  have hid:=turtle_transition_rank_injective__next_noop commands f d s b c dir pos flip hd hs hb hdr hpos hflip hr
  obtain ⟨hf',hd',hs',hb'⟩:=hid
  simp only [hf',hd',hs',hb'] at hnf he hstep
  unfold FlippedCommand at he
  unfold TurtleEncodedStep at hstep
  rw [hw] at hnb
  rcases he with ⟨he1,he2⟩ | ⟨he1,⟨he2,he3⟩ | ⟨he2,he3⟩⟩ <;>
    rcases hstep with ⟨ht1,ht2,ht3⟩ | ⟨ht1,ht2,⟨ht3,ht4⟩ | ⟨ht3,ht4⟩⟩ <;> omega

theorem proof_of_solver_entail_wit_9_8 : solver_entail_wit_9_8 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_8_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_9_9_split_goal_1 : solver_entail_wit_9_9_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  have hdir0 : dir=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH56
  have hdone : ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + (flip + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hdir0]
    try ring
  rw [hdone]
  have hc:=PreH38 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH27
  apply turtle_next_prefix_skip_rank__next_noop commands i changes_pre _ next_table_2 hnext
  intro f d s b e nf nd ns hf hd hs hb hr hp hnf hlim he hstep hnb
  have hid:=turtle_transition_rank_injective__next_noop commands f d s b c dir pos flip hd hs hb hdr hpos hflip hr
  obtain ⟨hf',hd',hs',hb'⟩:=hid
  simp only [hf',hd',hs',hb'] at hnf he hstep
  unfold FlippedCommand at he
  unfold TurtleEncodedStep at hstep
  rw [hw] at hnb
  rcases he with ⟨he1,he2⟩ | ⟨he1,⟨he2,he3⟩ | ⟨he2,he3⟩⟩ <;>
    rcases hstep with ⟨ht1,ht2,ht3⟩ | ⟨ht1,ht2,⟨ht3,ht4⟩ | ⟨ht3,ht4⟩⟩ <;> omega

theorem proof_of_solver_entail_wit_9_9 : solver_entail_wit_9_9 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_9_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57

theorem proof_of_solver_entail_wit_9_10_split_goal_1 : solver_entail_wit_9_10_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  have hflip0 : flip=0 := by omega
  have hdir0 : dir=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH56
  have hdone : ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hdir0, hflip0]
    try ring
  rw [hdone]
  have hc:=PreH38 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH27
  apply turtle_next_prefix_skip_rank__next_noop commands i changes_pre _ next_table_2 hnext
  intro f d s b e nf nd ns hf hd hs hb hr hp hnf hlim he hstep hnb
  have hid:=turtle_transition_rank_injective__next_noop commands f d s b c dir pos flip hd hs hb hdr hpos hflip hr
  obtain ⟨hf',hd',hs',hb'⟩:=hid
  simp only [hf',hd',hs',hb'] at hnf he hstep
  unfold FlippedCommand at he
  unfold TurtleEncodedStep at hstep
  rw [hw] at hnb
  rcases he with ⟨he1,he2⟩ | ⟨he1,⟨he2,he3⟩ | ⟨he2,he3⟩⟩ <;>
    rcases hstep with ⟨ht1,ht2,ht3⟩ | ⟨ht1,ht2,⟨ht3,ht4⟩ | ⟨ht3,ht4⟩⟩ <;> omega

theorem proof_of_solver_entail_wit_9_10 : solver_entail_wit_9_10 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_10_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57

theorem proof_of_solver_entail_wit_9_11_split_goal_1 : solver_entail_wit_9_11_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤changes_pre := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH29
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    try ring
  rw [hdone]
  apply turtle_next_prefix_skip_rank__next_noop commands i changes_pre _ next_table_2 hnext
  intro f d s b e nf nd ns hf hd hs hb hr hp hnf hlim he hstep hnb
  have hid:=turtle_transition_rank_injective__next_noop commands f d s b c dir pos flip hd hs hb hdr hpos hflip hr
  obtain ⟨hf',hd',hs',hb'⟩:=hid
  simp only [hf',hd',hs',hb'] at hnf he hstep
  omega

theorem proof_of_solver_entail_wit_9_11 : solver_entail_wit_9_11 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_11_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29

theorem proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have he : (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (pos + 1)))=((2 * ((((c * 2) + dir) * W) + pos)) + flip) := by nlinarith
  rw [he]
  exact PreH28

theorem proof_of_solver_entail_wit_10_1_split_goal_2 : solver_entail_wit_10_1_split_goal_2 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  apply cell_bound_le changes_pre c dir (2*O+1) (pos+1)
  all_goals omega

theorem proof_of_solver_entail_wit_10_1_split_goal_3 : solver_entail_wit_10_1_split_goal_3 := by
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  first | assumption | omega

theorem proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1 := by
  right
  intro changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_10_1_split_goal_1 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | exact proof_of_solver_entail_wit_10_1_split_goal_2 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | exact proof_of_solver_entail_wit_10_1_split_goal_3 changes_pre commands n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hd : 0≤dir ∧ dir<2 := by omega
  have hs : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hzero : Znth (TurtleCellIndex commands c dir pos) current_table_2 0=0 := by
    simpa only [TurtleCellIndex,hw] using PreH37
  have skip : ∀ b, (0≤b ∧ b<2) → ∀ table, TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos b) table → TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos b+1) table := by
    intro b hb table hn
    apply turtle_next_prefix_skip_rank__next_noop commands i changes_pre _ table hn
    intro f dr s b' e nf nd ns hf hdr hslot hbit hr hp hnf hlim he hstep hnb
    have hid:=turtle_transition_rank_injective__next_noop commands f dr s b' c dir pos b hdr hslot hbit hd hs hb hr
    obtain ⟨hfc,hdc,hsc,_⟩:=hid
    have hone:=(PreH35 f dr s hf hdr hslot).2.mpr hp
    rw [hfc,hdc,hsc,hzero] at hone
    omega
  have h0 : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos 0) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw,Int.add_zero] using PreH36
  have h1:=skip 0 (by omega) next_table_2 h0
  have h1' : TurtleNextPrefix commands i changes_pre (TurtleTransitionRank commands c dir pos 1) next_table_2 := by
    simpa only [TurtleTransitionRank,Int.add_zero] using h1
  have h2:=skip 1 (by omega) next_table_2 h1'
  have he : 2*((c*2+dir)*(2*O+1)+(pos+1))=TurtleTransitionRank commands c dir pos 1+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    ring
  rw [he]
  exact h2

theorem proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2 := by
  right
  intro changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_10_2_split_goal_1 changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37

theorem proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have he : (2 * (((c * 2) + (dir + 1)) * ((2 * O) + 1)))=(2 * ((((c * 2) + dir) * W) + pos)) := by nlinarith
  rw [he]
  exact PreH27

theorem proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  first | assumption | omega

theorem proof_of_solver_entail_wit_11 : solver_entail_wit_11 := by
  right
  intro changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_11_split_goal_1 changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
      | exact proof_of_solver_entail_wit_11_split_goal_2 changes_pre commands n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have he : ((4 * (c + 1)) * ((2 * O) + 1))=(2 * (((c * 2) + dir) * W)) := by nlinarith
  rw [he]
  exact PreH23

theorem proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first | assumption | omega

theorem proof_of_solver_entail_wit_12 : solver_entail_wit_12 := by
  right
  intro changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_12_split_goal_1 changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_12_split_goal_2 changes_pre commands n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have he : ((((changes_pre + 1) * 2) * ((2 * O) + 1)) * 2)=((4 * c) * W) := by nlinarith
  rw [he]
  exact PreH22

theorem proof_of_solver_entail_wit_13_split_goal_2 : solver_entail_wit_13_split_goal_2 := by
  intro changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  first | assumption | omega

theorem proof_of_solver_entail_wit_13 : solver_entail_wit_13 := by
  right
  intro changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_13_split_goal_1 changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_solver_entail_wit_13_split_goal_2 changes_pre commands n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_solver_entail_wit_14_split_goal_1 : solver_entail_wit_14_split_goal_1 := by
  intro changes_pre commands n current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply turtle_next_complete_layer__layer_swap commands i changes_pre next_table (by omega) (by omega)
  · intro k hk;exact PreH9 k (by omega)
  · have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
    rw [hw]
    exact PreH17

theorem proof_of_solver_entail_wit_14_split_goal_2 : solver_entail_wit_14_split_goal_2 := by
  intro changes_pre commands n current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  first | assumption | omega

theorem proof_of_solver_entail_wit_14 : solver_entail_wit_14 := by
  right
  intro changes_pre commands n current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_14_split_goal_1 changes_pre commands n current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_solver_entail_wit_14_split_goal_2 changes_pre commands n current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1 := by
  intro changes_pre commands n spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have he : O=i := by nlinarith
  rw [he]
  exact PreH19

theorem proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2 := by
  intro changes_pre commands n spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  first | assumption | omega

theorem proof_of_solver_entail_wit_15 : solver_entail_wit_15 := by
  right
  intro changes_pre commands n spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_15_split_goal_1 changes_pre commands n spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_solver_entail_wit_15_split_goal_2 changes_pre commands n spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_solver_entail_wit_16_split_goal_1 : solver_entail_wit_16_split_goal_1 := by
  intro changes_pre commands n final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  simpa only [Int.zero_mul,Int.mul_zero] using turtle_answer_prefix_zero__answer_init commands changes_pre

theorem proof_of_solver_entail_wit_16_split_goal_2 : solver_entail_wit_16_split_goal_2 := by
  intro changes_pre commands n final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  first | assumption | omega

theorem proof_of_solver_entail_wit_16 : solver_entail_wit_16 := by
  right
  intro changes_pre commands n final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_16_split_goal_1 changes_pre commands n final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_solver_entail_wit_16_split_goal_2 changes_pre commands n final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_17_split_goal_1 : solver_entail_wit_17_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have he : (((c * 2) + (0 : Int)) * ((2 * O) + 1))=((c * 2) * W) := by nlinarith
  rw [he]
  exact PreH21

theorem proof_of_solver_entail_wit_17_split_goal_2 : solver_entail_wit_17_split_goal_2 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  first | assumption | omega

theorem proof_of_solver_entail_wit_17 : solver_entail_wit_17 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_17_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_solver_entail_wit_17_split_goal_2 changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_18_split_goal_1 : solver_entail_wit_18_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have he : ((((c * 2) + d) * ((2 * O) + 1)) + (0 : Int))=(((c * 2) + d) * W) := by nlinarith
  rw [he]
  exact PreH23

theorem proof_of_solver_entail_wit_18_split_goal_2 : solver_entail_wit_18_split_goal_2 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply cell_bound_le changes_pre c d (2*O+1) 0
  all_goals omega

theorem proof_of_solver_entail_wit_18_split_goal_3 : solver_entail_wit_18_split_goal_3 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first | assumption | omega

theorem proof_of_solver_entail_wit_18 : solver_entail_wit_18 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_18_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_18_split_goal_2 changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_18_split_goal_3 changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_19_split_goal_1 : solver_entail_wit_19_split_goal_1 := by
  intro changes_pre commands n spare_table final_table ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  apply cell_bound_lt changes_pre c d (2*O+1) p
  all_goals omega

theorem proof_of_solver_entail_wit_19 : solver_entail_wit_19 := by
  right
  intro changes_pre commands n spare_table final_table ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_19_split_goal_1 changes_pre commands n spare_table final_table ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43

theorem proof_of_solver_entail_wit_20_1_split_goal_1 : solver_entail_wit_20_1_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : O=Zlength commands := by omega
  have hnext : ((c*2+d)*(2*O+1)+(p+1))=TurtleCellIndex commands c d p+1 := by
    unfold TurtleCellIndex
    rw [hw]
    have hwo : 2*O+1=W := by omega
    rw [hwo]
    ring
  rw [hnext]
  have ha : TurtleAnswerPrefix commands changes_pre (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH39
  apply turtle_answer_prefix_consume_cell__answer_position commands changes_pre _ ans (p-O) ha
  · omega
  · intro f dr slot ht he
    have heq:=turtle_cell_index_same_slot__answer_position commands f dr slot c d p (by unfold TurtleWidth;have := Zlength_nonneg commands;omega) ht.2.2.1 (by rw [hw];omega) he
    rw [heq]
    rw [(Z.abs_eq_iff _).mpr (by omega : 0≤p-Zlength commands)]
    omega
  · right
    refine ⟨c,d,p,?_,rfl,?_⟩
    · apply turtle_layer_nonzero_terminal__answer_position commands changes_pre final_table_2 c d p
      · simpa only [show len=Zlength commands by omega] using PreH38
      · omega
      · omega
      · rw [hw];omega
      · exact land_one_zero_even__answer_position _ PreH29
      · simpa only [TurtleCellIndex,hw] using PreH40
    · rw [(Z.abs_eq_iff _).mpr (by omega : 0≤p-Zlength commands)]
      omega

theorem proof_of_solver_entail_wit_20_1 : solver_entail_wit_20_1 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_1_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_solver_entail_wit_20_2_split_goal_1 : solver_entail_wit_20_2_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : O=Zlength commands := by omega
  have habs : Z.abs (p-Zlength commands)= -(p-Zlength commands) := by
    calc
      Z.abs (p-Zlength commands) = Z.abs (-(p-Zlength commands)) := (Z.abs_neg _).symm
      _ = -(p-Zlength commands) := (Z.abs_eq_iff _).mpr (by omega)
  have hnext : ((c*2+d)*(2*O+1)+(p+1))=TurtleCellIndex commands c d p+1 := by
    unfold TurtleCellIndex
    rw [hw]
    have hwo : 2*O+1=W := by omega
    rw [hwo]
    ring
  rw [hnext]
  have ha : TurtleAnswerPrefix commands changes_pre (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH39
  apply turtle_answer_prefix_consume_cell__answer_position commands changes_pre _ ans (-(p-O)) ha
  · omega
  · intro f dr slot ht he
    have heq:=turtle_cell_index_same_slot__answer_position commands f dr slot c d p (by unfold TurtleWidth;have := Zlength_nonneg commands;omega) ht.2.2.1 (by rw [hw];omega) he
    rw [heq]
    rw [habs]
    omega
  · right
    refine ⟨c,d,p,?_,rfl,?_⟩
    · apply turtle_layer_nonzero_terminal__answer_position commands changes_pre final_table_2 c d p
      · simpa only [show len=Zlength commands by omega] using PreH38
      · omega
      · omega
      · rw [hw];omega
      · exact land_one_zero_even__answer_position _ PreH29
      · simpa only [TurtleCellIndex,hw] using PreH40
    · rw [habs]
      omega

theorem proof_of_solver_entail_wit_20_2 : solver_entail_wit_20_2 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_2_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_solver_entail_wit_20_3_split_goal_1 : solver_entail_wit_20_3_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : O=Zlength commands := by omega
  have hnext : ((c*2+d)*(2*O+1)+(p+1))=TurtleCellIndex commands c d p+1 := by
    unfold TurtleCellIndex
    rw [hw]
    have hwo : 2*O+1=W := by omega
    rw [hwo]
    ring
  rw [hnext]
  have ha : TurtleAnswerPrefix commands changes_pre (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH39
  apply turtle_answer_prefix_consume_cell__answer_position commands changes_pre _ ans ans ha
  · omega
  · intro f dr slot ht he
    have heq:=turtle_cell_index_same_slot__answer_position commands f dr slot c d p (by unfold TurtleWidth;have := Zlength_nonneg commands;omega) ht.2.2.1 (by rw [hw];omega) he
    rw [heq]
    rw [(Z.abs_eq_iff _).mpr (by omega : 0≤p-Zlength commands)]
    omega
  · exact Or.inl rfl

theorem proof_of_solver_entail_wit_20_3 : solver_entail_wit_20_3 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_3_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_solver_entail_wit_20_4_split_goal_1 : solver_entail_wit_20_4_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : O=Zlength commands := by omega
  have habs : Z.abs (p-Zlength commands)= -(p-Zlength commands) := by
    calc
      Z.abs (p-Zlength commands) = Z.abs (-(p-Zlength commands)) := (Z.abs_neg _).symm
      _ = -(p-Zlength commands) := (Z.abs_eq_iff _).mpr (by omega)
  have hnext : ((c*2+d)*(2*O+1)+(p+1))=TurtleCellIndex commands c d p+1 := by
    unfold TurtleCellIndex
    rw [hw]
    have hwo : 2*O+1=W := by omega
    rw [hwo]
    ring
  rw [hnext]
  have ha : TurtleAnswerPrefix commands changes_pre (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH39
  apply turtle_answer_prefix_consume_cell__answer_position commands changes_pre _ ans ans ha
  · omega
  · intro f dr slot ht he
    have heq:=turtle_cell_index_same_slot__answer_position commands f dr slot c d p (by unfold TurtleWidth;have := Zlength_nonneg commands;omega) ht.2.2.1 (by rw [hw];omega) he
    rw [heq]
    rw [habs]
    omega
  · exact Or.inl rfl

theorem proof_of_solver_entail_wit_20_4 : solver_entail_wit_20_4 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_4_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_solver_entail_wit_20_5_split_goal_1 : solver_entail_wit_20_5_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : O=Zlength commands := by omega
  have hnext : ((c*2+d)*(2*O+1)+(p+1))=TurtleCellIndex commands c d p+1 := by
    unfold TurtleCellIndex
    rw [hw]
    have hwo : 2*O+1=W := by omega
    rw [hwo]
    ring
  rw [hnext]
  have ha : TurtleAnswerPrefix commands changes_pre (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH36
  apply turtle_answer_prefix_consume_cell__answer_position commands changes_pre _ ans ans ha
  · omega
  · intro f dr slot ht he
    have hl : TurtleLayerMeaning commands (Zlength commands) changes_pre final_table_2 := by
      simpa only [show len=Zlength commands by omega] using PreH35
    have hone:=turtle_terminal_cell_one__answer_position commands changes_pre final_table_2 f dr slot hl ht
    rw [he] at hone
    have hz : Znth (TurtleCellIndex commands c d p) final_table_2 0=0 := by simpa only [TurtleCellIndex,hw] using PreH37
    omega
  · exact Or.inl rfl

theorem proof_of_solver_entail_wit_20_5 : solver_entail_wit_20_5 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_5_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37

theorem proof_of_solver_entail_wit_21_split_goal_1 : solver_entail_wit_21_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have he : (((c * 2) + (d + 1)) * ((2 * O) + 1))=((((c * 2) + d) * W) + p) := by nlinarith
  rw [he]
  exact PreH27

theorem proof_of_solver_entail_wit_21_split_goal_2 : solver_entail_wit_21_split_goal_2 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  first | assumption | omega

theorem proof_of_solver_entail_wit_21 : solver_entail_wit_21 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_21_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
      | exact proof_of_solver_entail_wit_21_split_goal_2 changes_pre commands n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_entail_wit_22_1_split_goal_1 : solver_entail_wit_22_1_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have he : (((c + 1) * 2) * ((2 * O) + 1))=(((c * 2) + d) * W) := by nlinarith
  rw [he]
  exact PreH23

theorem proof_of_solver_entail_wit_22_1_split_goal_2 : solver_entail_wit_22_1_split_goal_2 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first | assumption | omega

theorem proof_of_solver_entail_wit_22_1 : solver_entail_wit_22_1 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_22_1_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_22_1_split_goal_2 changes_pre commands n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_22_2_split_goal_1 : solver_entail_wit_22_2_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have hO : 2*O+1=W := by omega
  rw [hO]
  have hh := turtle_answer_prefix_skip_ineligible__answer_loop_exits commands changes_pre c ans (by omega) (by omega) (by unfold TurtleWidth;omega) PreH1 (by simpa only [hw] using PreH21)
  simpa only [hw] using hh

theorem proof_of_solver_entail_wit_22_2 : solver_entail_wit_22_2 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_22_2_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_23_split_goal_1 : solver_entail_wit_23_split_goal_1 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  apply turtle_answer_complete_spec__final_spec commands changes_pre final_table_2 ans
  · refine ⟨by omega,by omega,?_⟩
    apply command_alphabet_from_Znth__final_spec
    intro k hk;exact PreH10 k (by omega)
  · simpa only [PreH3] using PreH19
  · have he : ((changes_pre+1)*2)*TurtleWidth commands=c*2*W := by unfold TurtleWidth;nlinarith
    rw [he];exact PreH20

theorem proof_of_solver_entail_wit_23_split_goal_2 : solver_entail_wit_23_split_goal_2 := by
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first | assumption | omega

theorem proof_of_solver_entail_wit_23 : solver_entail_wit_23 := by
  right
  intro changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_23_split_goal_1 changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_solver_entail_wit_23_split_goal_2 changes_pre commands n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial := by
  intro changes_pre s_pre commands n final_table spare_table len W O ans dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  rw [PreH3]
  exact naive_C_Rules.toContext.derivable1_refl _

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro changes_pre s_pre commands n final_table spare_table len W O ans dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact proof_of_solver_return_wit_1_split_goal_spatial changes_pre s_pre commands n final_table spare_table len W O ans dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1 := by
  intro changes_pre s_pre commands n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  first | assumption | omega

theorem proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure := by
  right
  intro changes_pre s_pre commands n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  exact PreH8

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_proof_manual
