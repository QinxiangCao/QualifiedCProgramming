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
  intro commands n changes_pre retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  subst changes_pre
  have PreH9 : n = n := rfl
  have previous_PreH3 : ((0 : Int) <= Zlength commands + 1) := by omega
  rw [PreH3]
  simpa only [TurtleWidth,SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,AUXLib.«repeat»,Int.zero_mul,Int.zero_add,Int.mul_zero] using turtle_layer_zero_table__init_layer commands n ((n+1)*2*TurtleWidth commands) PreH4 (by omega) rfl

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro commands n changes_pre retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  subst changes_pre
  have PreH9 : n = n := rfl
  have previous_PreH3 : ((0 : Int) <= Zlength commands + 1) := by omega
  simp only [Zlength_replace_Znth,SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,Zlength,List.length_replicate,Int.ofNat_eq_coe]
  have hnonneg : 0≤(n+1)*2*(2*retval+1) := by nlinarith
  omega

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro commands n changes_pre retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  subst changes_pre
  have PreH9 : n = n := rfl
  have previous_PreH3 : ((0 : Int) <= Zlength commands + 1) := by omega
  rw [Zlength_replace_Znth]
  simp only [SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,Zlength,List.length_replicate,Int.ofNat_eq_coe]
  have hp : 0≤(n+1)*2*(2*retval+1) := by
    have hc : 0≤n+1 := by omega
    have hr : 0≤2*retval+1 := by omega
    exact mul_nonneg (mul_nonneg hc (by omega)) hr
  omega

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro commands n changes_pre retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  subst changes_pre
  have PreH9 : n = n := rfl
  have previous_PreH3 : ((0 : Int) <= Zlength commands + 1) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 commands n n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_solver_entail_wit_1_split_goal_2 commands n n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_solver_entail_wit_1_split_goal_3 commands n n retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro commands n changes_pre spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  subst changes_pre
  have PreH3 : n = n := rfl
  have previous_PreH2 : ((0:Int)<=(len+1)) := by omega
  simpa only [SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,AUXLib.«repeat»,Int.zero_mul,Int.mul_zero] using turtle_next_zero_table__init_layer commands i n ((n+1)*2*(2*O+1))

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro commands n changes_pre spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  subst changes_pre
  have PreH3 : n = n := rfl
  have previous_PreH2 : ((0:Int)<=(len+1)) := by omega
  simp only [Zlength_replace_Znth,SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,Zlength,List.length_replicate,Int.ofNat_eq_coe]
  have hnonneg : 0≤(n+1)*2*(2*O+1) := by nlinarith
  omega

theorem proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3 := by
  intro commands n changes_pre spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  subst changes_pre
  have PreH3 : n = n := rfl
  have previous_PreH2 : ((0:Int)<=(len+1)) := by omega
  first | assumption | omega

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  right
  intro commands n changes_pre spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  subst changes_pre
  have PreH3 : n = n := rfl
  have previous_PreH2 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 commands n n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_solver_entail_wit_2_split_goal_2 commands n n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_solver_entail_wit_2_split_goal_3 commands n n spare_table current_table_2 ndp dp i O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : (2 * (((c * 2) + (0 : Int)) * ((2 * O) + 1)))=((4 * c) * W) := by nlinarith
  rw [he]
  exact PreH22

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  right
  intro commands n changes_pre next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_3_split_goal_1 commands n n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_solver_entail_wit_3_split_goal_2 commands n n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (0 : Int)))=(2 * (((c * 2) + dir) * W)) := by nlinarith
  rw [he]
  exact PreH23

theorem proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  apply cell_bound_le n c dir (2*O+1) 0
  all_goals omega

theorem proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  right
  intro commands n changes_pre next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_split_goal_1 commands n n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_4_split_goal_2 commands n n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_4_split_goal_3 commands n n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  intro commands n changes_pre next_table current_table ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  subst changes_pre
  have PreH18 : n = n := rfl
  apply cell_bound_lt n c dir (2*O+1) pos
  all_goals omega

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  right
  intro commands n changes_pre next_table current_table ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  subst changes_pre
  have PreH18 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_split_goal_1 commands n n next_table current_table ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  subst changes_pre
  have PreH10 : n = n := rfl
  have previous_PreH9 : ((0:Int)<=(len+1)) := by omega
  have he : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (0 : Int))=(2 * ((((c * 2) + dir) * W) + pos)) := by nlinarith
  rw [he]
  exact PreH35

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  subst changes_pre
  have PreH10 : n = n := rfl
  have previous_PreH9 : ((0:Int)<=(len+1)) := by omega
  first | assumption | omega

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  right
  intro commands n changes_pre next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  subst changes_pre
  have PreH10 : n = n := rfl
  have previous_PreH9 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_6_split_goal_1 commands n n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH1 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
      | exact proof_of_solver_entail_wit_6_split_goal_2 commands n n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH1 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36

theorem proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  subst changes_pre
  have PreH24 : n = n := rfl
  rw [binary_lxor_one__direction_bit dir (by omega)]
  omega

theorem proof_of_solver_entail_wit_7_1_split_goal_2 : solver_entail_wit_7_1_split_goal_2 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  subst changes_pre
  have PreH24 : n = n := rfl
  rw [binary_lxor_one__direction_bit dir (by omega)]
  omega

theorem proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1 := by
  right
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  subst changes_pre
  have PreH24 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_7_1_split_goal_1 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
      | exact proof_of_solver_entail_wit_7_1_split_goal_2 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51

theorem proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  subst changes_pre
  have PreH24 : n = n := rfl
  rw [binary_lxor_one__direction_bit dir (by omega)]
  omega

theorem proof_of_solver_entail_wit_7_2_split_goal_2 : solver_entail_wit_7_2_split_goal_2 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  subst changes_pre
  have PreH24 : n = n := rfl
  rw [binary_lxor_one__direction_bit dir (by omega)]
  omega

theorem proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2 := by
  right
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  subst changes_pre
  have PreH24 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_7_2_split_goal_1 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
      | exact proof_of_solver_entail_wit_7_2_split_goal_2 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51

theorem proof_of_solver_entail_wit_8_1_split_goal_1 : solver_entail_wit_8_1_split_goal_1 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  apply binary_destination_bound__direction_bit
  all_goals omega

theorem proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1 := by
  right
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_1_split_goal_1 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH3 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55

theorem proof_of_solver_entail_wit_8_2_split_goal_1 : solver_entail_wit_8_2_split_goal_1 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  apply binary_destination_bound__direction_bit
  all_goals omega

theorem proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2 := by
  right
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_2_split_goal_1 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH3 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55

theorem proof_of_solver_entail_wit_8_3_split_goal_1 : solver_entail_wit_8_3_split_goal_1 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  apply cell_bound_lt n (c+flip) dir (2*O+1) (pos+(-1))
  all_goals omega

theorem proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3 := by
  right
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_3_split_goal_1 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH3 PreH4 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_8_4_split_goal_1 : solver_entail_wit_8_4_split_goal_1 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  apply cell_bound_lt n (c+flip) 0 (2*O+1) (pos+1)
  all_goals omega

theorem proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4 := by
  right
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_4_split_goal_1 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH3 PreH4 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_8_5_split_goal_1 : solver_entail_wit_8_5_split_goal_1 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  apply cell_bound_lt n (c+0) dir (2*O+1) (pos+(-1))
  all_goals omega

theorem proof_of_solver_entail_wit_8_5 : solver_entail_wit_8_5 := by
  right
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_5_split_goal_1 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH3 PreH4 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_8_6_split_goal_1 : solver_entail_wit_8_6_split_goal_1 := by
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  apply cell_bound_lt n (c+0) 0 (2*O+1) (pos+1)
  all_goals omega

theorem proof_of_solver_entail_wit_8_6 : solver_entail_wit_8_6 := by
  right
  intro commands n changes_pre next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_6_split_goal_1 commands n n next_table ndp dp current_table flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH3 PreH4 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH54
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
  have hmeaning:=PreH53 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH47
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH36 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH25
  apply turtle_next_prefix_write_transition__next_update_core commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 84 (c+flip) (Z.lxor dir 1) pos
  · exact hnext
  · simpa only [hw] using PreH52
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1 := by
  right
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_1_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH3 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
      | exact proof_of_solver_entail_wit_9_1_split_goal_2 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH3 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55

theorem proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  have hflip0 : flip=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH54
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
  have hmeaning:=PreH53 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH47
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH36 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH25
  apply turtle_next_prefix_write_transition__next_update_core commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 84 (c+flip) (Z.lxor dir 1) pos
  · exact hnext
  · simpa only [hw] using PreH52
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2 := by
  right
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_2_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH3 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
      | exact proof_of_solver_entail_wit_9_2_split_goal_2 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH3 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55

theorem proof_of_solver_entail_wit_9_3_split_goal_1 : solver_entail_wit_9_3_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH57
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
  have hmeaning:=PreH56 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH50
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH39 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH28
  apply turtle_next_prefix_write_transition__next_update_core commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 70 (c+flip) dir (pos-1)
  · exact hnext
  · simpa only [hw] using PreH55
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3 := by
  right
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_3_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH5 PreH6 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
      | exact proof_of_solver_entail_wit_9_3_split_goal_2 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH5 PreH6 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58

theorem proof_of_solver_entail_wit_9_4_split_goal_1 : solver_entail_wit_9_4_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  have hdir0 : dir=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH57
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
  have hmeaning:=PreH56 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH50
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH39 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH28
  apply turtle_next_prefix_write_transition__next_update_core commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 70 (c+flip) dir (pos+1)
  · exact hnext
  · simpa only [hw] using PreH55
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_4 : solver_entail_wit_9_4 := by
  right
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_4_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH5 PreH6 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
      | exact proof_of_solver_entail_wit_9_4_split_goal_2 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH5 PreH6 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58

theorem proof_of_solver_entail_wit_9_5_split_goal_1 : solver_entail_wit_9_5_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  have hflip0 : flip=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH57
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
  have hmeaning:=PreH56 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH50
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH39 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH28
  apply turtle_next_prefix_write_transition__next_update_core commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 70 (c+flip) dir (pos-1)
  · exact hnext
  · simpa only [hw] using PreH55
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_5 : solver_entail_wit_9_5 := by
  right
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_5_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH5 PreH6 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
      | exact proof_of_solver_entail_wit_9_5_split_goal_2 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH5 PreH6 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58

theorem proof_of_solver_entail_wit_9_6_split_goal_1 : solver_entail_wit_9_6_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  have hflip0 : flip=0 := by omega
  have hdir0 : dir=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH57
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
  have hmeaning:=PreH56 c dir pos hsrc hdr hpos
  have hv : Znth (TurtleCellIndex commands c dir pos) current_table_2 0≠0 := by
    simpa only [TurtleCellIndex,hw] using PreH50
  have hreach : PrefixReachable commands i c dir pos := by
    apply hmeaning.2.mp
    obtain hz | hone:=hmeaning.1
    · exact False.elim (hv hz)
    · exact hone
  have hc:=PreH39 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH28
  apply turtle_next_prefix_write_transition__next_update_core commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 c dir pos flip 70 (c+flip) dir (pos+1)
  · exact hnext
  · simpa only [hw] using PreH55
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  rw [Zlength_replace_Znth]
  have ho : 2*O+1=W := by omega
  rw [ho]
  assumption

theorem proof_of_solver_entail_wit_9_6 : solver_entail_wit_9_6 := by
  right
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
  subst changes_pre
  have PreH31 : n = n := rfl
  have previous_PreH27 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_6_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH5 PreH6 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58
      | exact proof_of_solver_entail_wit_9_6_split_goal_2 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH5 PreH6 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58

theorem proof_of_solver_entail_wit_9_7_split_goal_1 : solver_entail_wit_9_7_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH24 : ((0:Int)<=(len+1)) := by omega
  have hflip0 : flip=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH54
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hflip0]
    try ring
  rw [hdone]
  have hc:=PreH36 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH25
  apply turtle_next_prefix_skip_rank__next_noop commands i n _ next_table_2 hnext
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH24 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_7_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH2 PreH3 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55

theorem proof_of_solver_entail_wit_9_8_split_goal_1 : solver_entail_wit_9_8_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH24 : ((0:Int)<=(len+1)) := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH54
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    try ring
  rw [hdone]
  have hc:=PreH36 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH25
  apply turtle_next_prefix_skip_rank__next_noop commands i n _ next_table_2 hnext
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  subst changes_pre
  have PreH28 : n = n := rfl
  have previous_PreH24 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_8_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH2 PreH3 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55

theorem proof_of_solver_entail_wit_9_9_split_goal_1 : solver_entail_wit_9_9_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  have hdir0 : dir=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH55
  have hdone : ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + (flip + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hdir0]
    try ring
  rw [hdone]
  have hc:=PreH37 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH26
  apply turtle_next_prefix_skip_rank__next_noop commands i n _ next_table_2 hnext
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_9_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH3 PreH4 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_9_10_split_goal_1 : solver_entail_wit_9_10_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  have hflip0 : flip=0 := by omega
  have hdir0 : dir=0 := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH55
  have hdone : ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    simp only [hdir0, hflip0]
    try ring
  rw [hdone]
  have hc:=PreH37 i (by omega)
  rw [Znth_app_left__next_noop commands [0] i 0 (by omega)] at PreH26
  apply turtle_next_prefix_skip_rank__next_noop commands i n _ next_table_2 hnext
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
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  subst changes_pre
  have PreH29 : n = n := rfl
  have previous_PreH25 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_10_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH3 PreH4 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56

theorem proof_of_solver_entail_wit_9_11_split_goal_1 : solver_entail_wit_9_11_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  subst changes_pre
  have PreH3 : n = n := rfl
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hsrc : 0≤c ∧ c≤n := by omega
  have hdr : 0≤dir ∧ dir<2 := by omega
  have hpos : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hflip : 0≤flip ∧ flip<2 := by omega
  have hnext : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos flip) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw] using PreH29
  have hdone : ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1))=TurtleTransitionRank commands c dir pos flip+1 := by
    unfold TurtleTransitionRank TurtleCellIndex
    rw [hw]
    rw [ho]
    try ring
  rw [hdone]
  apply turtle_next_prefix_skip_rank__next_noop commands i n _ next_table_2 hnext
  intro f d s b e nf nd ns hf hd hs hb hr hp hnf hlim he hstep hnb
  have hid:=turtle_transition_rank_injective__next_noop commands f d s b c dir pos flip hd hs hb hdr hpos hflip hr
  obtain ⟨hf',hd',hs',hb'⟩:=hid
  simp only [hf',hd',hs',hb'] at hnf he hstep
  omega

theorem proof_of_solver_entail_wit_9_11 : solver_entail_wit_9_11 := by
  right
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  subst changes_pre
  have PreH3 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_11_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29

theorem proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (pos + 1)))=((2 * ((((c * 2) + dir) * W) + pos)) + flip) := by nlinarith
  rw [he]
  exact PreH28

theorem proof_of_solver_entail_wit_10_1_split_goal_2 : solver_entail_wit_10_1_split_goal_2 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  subst changes_pre
  have PreH2 : n = n := rfl
  apply cell_bound_le n c dir (2*O+1) (pos+1)
  all_goals omega

theorem proof_of_solver_entail_wit_10_1_split_goal_3 : solver_entail_wit_10_1_split_goal_3 := by
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1 := by
  right
  intro commands n changes_pre next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_10_1_split_goal_1 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | exact proof_of_solver_entail_wit_10_1_split_goal_2 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | exact proof_of_solver_entail_wit_10_1_split_goal_3 commands n n next_table_2 ndp dp current_table_2 flip pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  subst changes_pre
  have PreH10 : n = n := rfl
  have previous_PreH9 : ((0:Int)<=(len+1)) := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : 2*O+1=W := by omega
  have hd : 0≤dir ∧ dir<2 := by omega
  have hs : 0≤pos ∧ pos<TurtleWidth commands := by rw [hw];omega
  have hzero : Znth (TurtleCellIndex commands c dir pos) current_table_2 0=0 := by
    simpa only [TurtleCellIndex,hw] using PreH36
  have skip : ∀ b, (0≤b ∧ b<2) → ∀ table, TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos b) table → TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos b+1) table := by
    intro b hb table hn
    apply turtle_next_prefix_skip_rank__next_noop commands i n _ table hn
    intro f dr s b' e nf nd ns hf hdr hslot hbit hr hp hnf hlim he hstep hnb
    have hid:=turtle_transition_rank_injective__next_noop commands f dr s b' c dir pos b hdr hslot hbit hd hs hb hr
    obtain ⟨hfc,hdc,hsc,_⟩:=hid
    have hone:=(PreH34 f dr s hf hdr hslot).2.mpr hp
    rw [hfc,hdc,hsc,hzero] at hone
    omega
  have h0 : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos 0) next_table_2 := by
    simpa only [TurtleTransitionRank,TurtleCellIndex,hw,Int.add_zero] using PreH35
  have h1:=skip 0 (by omega) next_table_2 h0
  have h1' : TurtleNextPrefix commands i n (TurtleTransitionRank commands c dir pos 1) next_table_2 := by
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
  intro commands n changes_pre next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  subst changes_pre
  have PreH10 : n = n := rfl
  have previous_PreH9 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_10_2_split_goal_1 commands n n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH1 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36

theorem proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : (2 * (((c * 2) + (dir + 1)) * ((2 * O) + 1)))=(2 * ((((c * 2) + dir) * W) + pos)) := by nlinarith
  rw [he]
  exact PreH27

theorem proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_11 : solver_entail_wit_11 := by
  right
  intro commands n changes_pre next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_11_split_goal_1 commands n n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
      | exact proof_of_solver_entail_wit_11_split_goal_2 commands n n next_table_2 current_table_2 ndp dp pos dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : ((4 * (c + 1)) * ((2 * O) + 1))=(2 * (((c * 2) + dir) * W)) := by nlinarith
  rw [he]
  exact PreH23

theorem proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_12 : solver_entail_wit_12 := by
  right
  intro commands n changes_pre next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_12_split_goal_1 commands n n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_12_split_goal_2 commands n n next_table_2 current_table_2 ndp dp dir c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : ((((n + 1) * 2) * ((2 * O) + 1)) * 2)=((4 * c) * W) := by nlinarith
  rw [he]
  exact PreH22

theorem proof_of_solver_entail_wit_13_split_goal_2 : solver_entail_wit_13_split_goal_2 := by
  intro commands n changes_pre next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_13 : solver_entail_wit_13 := by
  right
  intro commands n changes_pre next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_13_split_goal_1 commands n n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_solver_entail_wit_13_split_goal_2 commands n n next_table_2 current_table_2 ndp dp c i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_solver_entail_wit_14_split_goal_1 : solver_entail_wit_14_split_goal_1 := by
  intro commands n changes_pre current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  subst changes_pre
  have PreH1 : n = n := rfl
  apply turtle_next_complete_layer__layer_swap commands i n next_table (by omega) (by omega)
  · intro k hk;exact PreH9 k (by omega)
  · have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
    rw [hw]
    exact PreH17

theorem proof_of_solver_entail_wit_14_split_goal_2 : solver_entail_wit_14_split_goal_2 := by
  intro commands n changes_pre current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  subst changes_pre
  have PreH1 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_14 : solver_entail_wit_14 := by
  right
  intro commands n changes_pre current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  subst changes_pre
  have PreH1 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_14_split_goal_1 commands n n current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_solver_entail_wit_14_split_goal_2 commands n n current_table_2 next_table len W O i dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1 := by
  intro commands n changes_pre spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : O=i := by nlinarith
  rw [he]
  exact PreH19

theorem proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2 := by
  intro commands n changes_pre spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_15 : solver_entail_wit_15 := by
  right
  intro commands n changes_pre spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_15_split_goal_1 commands n n spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_solver_entail_wit_15_split_goal_2 commands n n spare_table_2 current_table ndp dp i O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_solver_entail_wit_16_split_goal_1 : solver_entail_wit_16_split_goal_1 := by
  intro commands n changes_pre final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  subst changes_pre
  have PreH1 : n = n := rfl
  simpa only [Int.zero_mul,Int.mul_zero] using turtle_answer_prefix_zero__answer_init commands n

theorem proof_of_solver_entail_wit_16_split_goal_2 : solver_entail_wit_16_split_goal_2 := by
  intro commands n changes_pre final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  subst changes_pre
  have PreH1 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_16 : solver_entail_wit_16 := by
  right
  intro commands n changes_pre final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  subst changes_pre
  have PreH1 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_16_split_goal_1 commands n n final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_solver_entail_wit_16_split_goal_2 commands n n final_table_2 spare_table_2 len W O dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_17_split_goal_1 : solver_entail_wit_17_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  subst changes_pre
  have PreH3 : n = n := rfl
  have he : (((c * 2) + (0 : Int)) * ((2 * O) + 1))=((c * 2) * W) := by nlinarith
  rw [he]
  exact PreH21

theorem proof_of_solver_entail_wit_17_split_goal_2 : solver_entail_wit_17_split_goal_2 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  subst changes_pre
  have PreH3 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_17 : solver_entail_wit_17 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  subst changes_pre
  have PreH3 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_17_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_solver_entail_wit_17_split_goal_2 commands n n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_18_split_goal_1 : solver_entail_wit_18_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : ((((c * 2) + d) * ((2 * O) + 1)) + (0 : Int))=(((c * 2) + d) * W) := by nlinarith
  rw [he]
  exact PreH23

theorem proof_of_solver_entail_wit_18_split_goal_2 : solver_entail_wit_18_split_goal_2 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  apply cell_bound_le n c d (2*O+1) 0
  all_goals omega

theorem proof_of_solver_entail_wit_18_split_goal_3 : solver_entail_wit_18_split_goal_3 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_18 : solver_entail_wit_18 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_18_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_18_split_goal_2 commands n n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_18_split_goal_3 commands n n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_19_split_goal_1 : solver_entail_wit_19_split_goal_1 := by
  intro commands n changes_pre spare_table final_table ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  subst changes_pre
  have PreH18 : n = n := rfl
  apply cell_bound_lt n c d (2*O+1) p
  all_goals omega

theorem proof_of_solver_entail_wit_19 : solver_entail_wit_19 := by
  right
  intro commands n changes_pre spare_table final_table ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  subst changes_pre
  have PreH18 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_19_split_goal_1 commands n n spare_table final_table ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43

theorem proof_of_solver_entail_wit_20_1_split_goal_1 : solver_entail_wit_20_1_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst changes_pre
  have PreH13 : n = n := rfl
  have previous_PreH12 : ((0:Int)<=(len+1)) := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : O=Zlength commands := by omega
  have hnext : ((c*2+d)*(2*O+1)+(p+1))=TurtleCellIndex commands c d p+1 := by
    unfold TurtleCellIndex
    rw [hw]
    have hwo : 2*O+1=W := by omega
    rw [hwo]
    ring
  rw [hnext]
  have ha : TurtleAnswerPrefix commands n (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH38
  apply turtle_answer_prefix_consume_cell__answer_position commands n _ ans (p-O) ha
  · omega
  · intro f dr slot ht he
    have heq:=turtle_cell_index_same_slot__answer_position commands f dr slot c d p (by unfold TurtleWidth;have := Zlength_nonneg commands;omega) ht.2.2.1 (by rw [hw];omega) he
    rw [heq]
    rw [(Z.abs_eq_iff _).mpr (by omega : 0≤p-Zlength commands)]
    omega
  · right
    refine ⟨c,d,p,?_,rfl,?_⟩
    · apply turtle_layer_nonzero_terminal__answer_position commands n final_table_2 c d p
      · simpa only [show len=Zlength commands by omega] using PreH37
      · omega
      · omega
      · rw [hw];omega
      · exact land_one_zero_even__answer_position _ PreH28
      · simpa only [TurtleCellIndex,hw] using PreH39
    · rw [(Z.abs_eq_iff _).mpr (by omega : 0≤p-Zlength commands)]
      omega

theorem proof_of_solver_entail_wit_20_1 : solver_entail_wit_20_1 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst changes_pre
  have PreH13 : n = n := rfl
  have previous_PreH12 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_1_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH4 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39

theorem proof_of_solver_entail_wit_20_2_split_goal_1 : solver_entail_wit_20_2_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst changes_pre
  have PreH13 : n = n := rfl
  have previous_PreH12 : ((0:Int)<=(len+1)) := by omega
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
  have ha : TurtleAnswerPrefix commands n (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH38
  apply turtle_answer_prefix_consume_cell__answer_position commands n _ ans (-(p-O)) ha
  · omega
  · intro f dr slot ht he
    have heq:=turtle_cell_index_same_slot__answer_position commands f dr slot c d p (by unfold TurtleWidth;have := Zlength_nonneg commands;omega) ht.2.2.1 (by rw [hw];omega) he
    rw [heq]
    rw [habs]
    omega
  · right
    refine ⟨c,d,p,?_,rfl,?_⟩
    · apply turtle_layer_nonzero_terminal__answer_position commands n final_table_2 c d p
      · simpa only [show len=Zlength commands by omega] using PreH37
      · omega
      · omega
      · rw [hw];omega
      · exact land_one_zero_even__answer_position _ PreH28
      · simpa only [TurtleCellIndex,hw] using PreH39
    · rw [habs]
      omega

theorem proof_of_solver_entail_wit_20_2 : solver_entail_wit_20_2 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst changes_pre
  have PreH13 : n = n := rfl
  have previous_PreH12 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_2_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH4 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39

theorem proof_of_solver_entail_wit_20_3_split_goal_1 : solver_entail_wit_20_3_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst changes_pre
  have PreH13 : n = n := rfl
  have previous_PreH12 : ((0:Int)<=(len+1)) := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : O=Zlength commands := by omega
  have hnext : ((c*2+d)*(2*O+1)+(p+1))=TurtleCellIndex commands c d p+1 := by
    unfold TurtleCellIndex
    rw [hw]
    have hwo : 2*O+1=W := by omega
    rw [hwo]
    ring
  rw [hnext]
  have ha : TurtleAnswerPrefix commands n (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH38
  apply turtle_answer_prefix_consume_cell__answer_position commands n _ ans ans ha
  · omega
  · intro f dr slot ht he
    have heq:=turtle_cell_index_same_slot__answer_position commands f dr slot c d p (by unfold TurtleWidth;have := Zlength_nonneg commands;omega) ht.2.2.1 (by rw [hw];omega) he
    rw [heq]
    rw [(Z.abs_eq_iff _).mpr (by omega : 0≤p-Zlength commands)]
    omega
  · exact Or.inl rfl

theorem proof_of_solver_entail_wit_20_3 : solver_entail_wit_20_3 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst changes_pre
  have PreH13 : n = n := rfl
  have previous_PreH12 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_3_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH4 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39

theorem proof_of_solver_entail_wit_20_4_split_goal_1 : solver_entail_wit_20_4_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst changes_pre
  have PreH13 : n = n := rfl
  have previous_PreH12 : ((0:Int)<=(len+1)) := by omega
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
  have ha : TurtleAnswerPrefix commands n (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH38
  apply turtle_answer_prefix_consume_cell__answer_position commands n _ ans ans ha
  · omega
  · intro f dr slot ht he
    have heq:=turtle_cell_index_same_slot__answer_position commands f dr slot c d p (by unfold TurtleWidth;have := Zlength_nonneg commands;omega) ht.2.2.1 (by rw [hw];omega) he
    rw [heq]
    rw [habs]
    omega
  · exact Or.inl rfl

theorem proof_of_solver_entail_wit_20_4 : solver_entail_wit_20_4 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst changes_pre
  have PreH13 : n = n := rfl
  have previous_PreH12 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_4_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans p d c O W len retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH4 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39

theorem proof_of_solver_entail_wit_20_5_split_goal_1 : solver_entail_wit_20_5_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  subst changes_pre
  have PreH10 : n = n := rfl
  have previous_PreH9 : ((0:Int)<=(len+1)) := by omega
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have ho : O=Zlength commands := by omega
  have hnext : ((c*2+d)*(2*O+1)+(p+1))=TurtleCellIndex commands c d p+1 := by
    unfold TurtleCellIndex
    rw [hw]
    have hwo : 2*O+1=W := by omega
    rw [hwo]
    ring
  rw [hnext]
  have ha : TurtleAnswerPrefix commands n (TurtleCellIndex commands c d p) ans := by
    simpa only [TurtleCellIndex,hw] using PreH35
  apply turtle_answer_prefix_consume_cell__answer_position commands n _ ans ans ha
  · omega
  · intro f dr slot ht he
    have hl : TurtleLayerMeaning commands (Zlength commands) n final_table_2 := by
      simpa only [show len=Zlength commands by omega] using PreH34
    have hone:=turtle_terminal_cell_one__answer_position commands n final_table_2 f dr slot hl ht
    rw [he] at hone
    have hz : Znth (TurtleCellIndex commands c d p) final_table_2 0=0 := by simpa only [TurtleCellIndex,hw] using PreH36
    omega
  · exact Or.inl rfl

theorem proof_of_solver_entail_wit_20_5 : solver_entail_wit_20_5 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  subst changes_pre
  have PreH10 : n = n := rfl
  have previous_PreH9 : ((0:Int)<=(len+1)) := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_20_5_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH1 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36

theorem proof_of_solver_entail_wit_21_split_goal_1 : solver_entail_wit_21_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : (((c * 2) + (d + 1)) * ((2 * O) + 1))=((((c * 2) + d) * W) + p) := by nlinarith
  rw [he]
  exact PreH27

theorem proof_of_solver_entail_wit_21_split_goal_2 : solver_entail_wit_21_split_goal_2 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_21 : solver_entail_wit_21 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_21_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
      | exact proof_of_solver_entail_wit_21_split_goal_2 commands n n spare_table_2 final_table_2 ndp dp ans p d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_entail_wit_22_1_split_goal_1 : solver_entail_wit_22_1_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  have he : (((c + 1) * 2) * ((2 * O) + 1))=(((c * 2) + d) * W) := by nlinarith
  rw [he]
  exact PreH23

theorem proof_of_solver_entail_wit_22_1_split_goal_2 : solver_entail_wit_22_1_split_goal_2 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_22_1 : solver_entail_wit_22_1 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_22_1_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_22_1_split_goal_2 commands n n spare_table_2 final_table_2 ndp dp ans d c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_22_2_split_goal_1 : solver_entail_wit_22_2_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  subst changes_pre
  have PreH3 : n = n := rfl
  have hw : TurtleWidth commands=W := by unfold TurtleWidth;omega
  have hO : 2*O+1=W := by omega
  rw [hO]
  have hh := turtle_answer_prefix_skip_ineligible__answer_loop_exits commands n c ans (by omega) (by omega) (by unfold TurtleWidth;omega) PreH1 (by simpa only [hw] using PreH21)
  simpa only [hw] using hh

theorem proof_of_solver_entail_wit_22_2 : solver_entail_wit_22_2 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  subst changes_pre
  have PreH3 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_22_2_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_23_split_goal_1 : solver_entail_wit_23_split_goal_1 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  subst changes_pre
  have PreH2 : n = n := rfl
  apply turtle_answer_complete_spec__final_spec commands n final_table_2 ans
  · refine ⟨by omega,by omega,?_⟩
    apply command_alphabet_from_Znth__final_spec
    intro k hk;exact PreH10 k (by omega)
  · simpa only [PreH3] using PreH19
  · have he : ((n+1)*2)*TurtleWidth commands=c*2*W := by unfold TurtleWidth;nlinarith
    rw [he];exact PreH20

theorem proof_of_solver_entail_wit_23_split_goal_2 : solver_entail_wit_23_split_goal_2 := by
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  subst changes_pre
  have PreH2 : n = n := rfl
  first | assumption | omega

theorem proof_of_solver_entail_wit_23 : solver_entail_wit_23 := by
  right
  intro commands n changes_pre spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  subst changes_pre
  have PreH2 : n = n := rfl
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_23_split_goal_1 commands n n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_solver_entail_wit_23_split_goal_2 commands n n spare_table_2 final_table_2 ndp dp ans c O W len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial := by
  intro commands n s_pre changes_pre final_table spare_table len W O ans dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  subst changes_pre
  have PreH1 : n = n := rfl
  have previous_PreH1 : ((0:Int)<=(len+1)) := by omega
  rw [PreH2]
  exact naive_C_Rules.toContext.derivable1_refl _

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro commands n s_pre changes_pre final_table spare_table len W O ans dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  subst changes_pre
  have PreH1 : n = n := rfl
  have previous_PreH1 : ((0:Int)<=(len+1)) := by omega
  exact proof_of_solver_return_wit_1_split_goal_spatial commands n s_pre n final_table spare_table len W O ans dp ndp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1 := by
  intro commands n s_pre changes_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  subst changes_pre
  have PreH8 : n = n := rfl
  have previous_PreH3 : ((0 : Int) <= Zlength commands + 1) := by omega
  dump_pre_spatial
  first | assumption | omega

theorem proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure := by
  right
  intro commands n s_pre changes_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  subst changes_pre
  have PreH8 : n = n := rfl
  have previous_PreH3 : ((0 : Int) <= Zlength commands + 1) := by omega
  dump_pre_spatial
  exact PreH7

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_proof_manual
