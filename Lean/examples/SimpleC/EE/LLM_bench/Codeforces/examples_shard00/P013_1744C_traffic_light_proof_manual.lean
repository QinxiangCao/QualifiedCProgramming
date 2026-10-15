import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_proof_auto
import ListLib.General.Length

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P013_1744C_traffic_light_goal P013_1744C_traffic_light_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem app_left (l r : List Int) (i : Int) (h : 0≤i ∧ i<Zlength l) :
    Znth i (l++r) 0=Znth i l 0 := ListLib.app_Znth1 0 l r i h

private theorem cyclic_read (l : List Int) (i n : Int) (hn : n=Zlength l) (hi : 0≤i) (hp : 0<n) :
    Znth (Z.rem i n) (l++[0]) 0=DoubledTrafficChar l i := by
  have hr := AUXLib.rem_nonneg_bounds i n hi hp
  rw [app_left l [0] (Z.rem i n) ⟨hr.1,by omega⟩]
  unfold DoubledTrafficChar
  rw [← hn,AUXLib.rem_eq_mod i n hi hp]

private theorem cyclic_small (l : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength l) :
    DoubledTrafficChar l i=Znth i l 0 := by
  unfold DoubledTrafficChar
  have he : Z.modulo i (Zlength l)=i%Zlength l := Int.fmod_eq_emod_of_nonneg i (Zlength_nonneg l)
  rw [he,Int.emod_eq_of_lt hi.1 hi.2]

theorem proof_of_solver_entail_wit_1_red_split_goal_1 : solver_entail_wit_1_red_split_goal_1 := by
  unfold solver_entail_wit_1_red_split_goal_1
  intro c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  rw [PreH2]
  exact traffic_scan_state_initial__initialization 114 lights PreH3

theorem proof_of_solver_entail_wit_1_red_split_goal_2 : solver_entail_wit_1_red_split_goal_2 := by
  unfold solver_entail_wit_1_red_split_goal_2
  intro c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  intro idx hidx
  apply PreH6 idx
  omega

theorem proof_of_solver_entail_wit_1_red : solver_entail_wit_1_red := by
  unfold solver_entail_wit_1_red
  right
  intro c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_1_red_split_goal_1 c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)
      | exact (proof_of_solver_entail_wit_1_red_split_goal_2 c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)

theorem proof_of_solver_entail_wit_2_yellow_split_goal_1 : solver_entail_wit_2_yellow_split_goal_1 := by
  unfold solver_entail_wit_2_yellow_split_goal_1
  intro c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  rw [PreH2]
  exact traffic_scan_state_initial__initialization 121 lights PreH3

theorem proof_of_solver_entail_wit_2_yellow_split_goal_2 : solver_entail_wit_2_yellow_split_goal_2 := by
  unfold solver_entail_wit_2_yellow_split_goal_2
  intro c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  intro idx hidx
  apply PreH6 idx
  omega

theorem proof_of_solver_entail_wit_2_yellow : solver_entail_wit_2_yellow := by
  unfold solver_entail_wit_2_yellow
  right
  intro c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_2_yellow_split_goal_1 c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)
      | exact (proof_of_solver_entail_wit_2_yellow_split_goal_2 c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)

theorem proof_of_solver_entail_wit_3_red_split_goal_1 : solver_entail_wit_3_red_split_goal_1 := by
  unfold solver_entail_wit_3_red_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := AUXLib.rem_nonneg_bounds i n (by omega) (by omega)
  exact hr.2

theorem proof_of_solver_entail_wit_3_red_split_goal_2 : solver_entail_wit_3_red_split_goal_2 := by
  unfold solver_entail_wit_3_red_split_goal_2
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := AUXLib.rem_nonneg_bounds i n (by omega) (by omega)
  exact hr.1

theorem proof_of_solver_entail_wit_3_red : solver_entail_wit_3_red := by
  unfold solver_entail_wit_3_red
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_3_red_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
      | exact (proof_of_solver_entail_wit_3_red_split_goal_2 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_solver_entail_wit_4_yellow_split_goal_1 : solver_entail_wit_4_yellow_split_goal_1 := by
  unfold solver_entail_wit_4_yellow_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := AUXLib.rem_nonneg_bounds i n (by omega) (by omega)
  exact hr.2

theorem proof_of_solver_entail_wit_4_yellow_split_goal_2 : solver_entail_wit_4_yellow_split_goal_2 := by
  unfold solver_entail_wit_4_yellow_split_goal_2
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := AUXLib.rem_nonneg_bounds i n (by omega) (by omega)
  exact hr.1

theorem proof_of_solver_entail_wit_4_yellow : solver_entail_wit_4_yellow := by
  unfold solver_entail_wit_4_yellow
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_4_yellow_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
      | exact (proof_of_solver_entail_wit_4_yellow_split_goal_2 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_solver_entail_wit_5_1_red_split_goal_1 : solver_entail_wit_5_1_red_split_goal_1 := by
  unfold solver_entail_wit_5_1_red_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 114 lights i ans next_green := by rw [← PreH15]; exact PreH24
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH4
  have hc : DoubledTrafficChar lights i=114 := by rw [← hr,← PreH15]; exact PreH2
  have hpre : Pre 114 lights := by rw [← PreH15]; exact PreH17
  have hstep := traffic_scan_step_current_raise__current_max_update 114 lights i ans next_green hpre ⟨by omega,by omega⟩ (by decide) hc hs (by omega) (by omega)
  exact hstep.1

theorem proof_of_solver_entail_wit_5_1_red_split_goal_2 : solver_entail_wit_5_1_red_split_goal_2 := by
  unfold solver_entail_wit_5_1_red_split_goal_2
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 114 lights i ans next_green := by rw [← PreH15]; exact PreH24
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH4
  have hc : DoubledTrafficChar lights i=114 := by rw [← hr,← PreH15]; exact PreH2
  have hpre : Pre 114 lights := by rw [← PreH15]; exact PreH17
  have hstep := traffic_scan_step_current_raise__current_max_update 114 lights i ans next_green hpre ⟨by omega,by omega⟩ (by decide) hc hs (by omega) (by omega)
  omega

theorem proof_of_solver_entail_wit_5_1_red : solver_entail_wit_5_1_red := by
  unfold solver_entail_wit_5_1_red
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_1_red_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32)
      | exact (proof_of_solver_entail_wit_5_1_red_split_goal_2 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32)

theorem proof_of_solver_entail_wit_5_2_red_split_goal_1 : solver_entail_wit_5_2_red_split_goal_1 := by
  unfold solver_entail_wit_5_2_red_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 114 lights i ans next_green := by rw [← PreH14]; exact PreH23
  have hn : Znth i lights 0≠114 := by
    rw [← cyclic_small lights i ⟨by omega,by omega⟩,← hr,← PreH14]
    exact PreH1
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH3
  exact traffic_scan_step_noncurrent_nongreen__stable_transition 114 lights i ans next_green ⟨by omega,by omega⟩ hn hg hs

theorem proof_of_solver_entail_wit_5_2_red : solver_entail_wit_5_2_red := by
  unfold solver_entail_wit_5_2_red
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_2_red_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31)

theorem proof_of_solver_entail_wit_5_3_red_split_goal_1 : solver_entail_wit_5_3_red_split_goal_1 := by
  unfold solver_entail_wit_5_3_red_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 114 lights i ans next_green := by rw [← PreH14]; exact PreH23
  have hn : Znth i lights 0≠114 := by
    rw [← cyclic_small lights i ⟨by omega,by omega⟩,← hr,← PreH14]
    exact PreH1
  have hg : DoubledTrafficChar lights i=103 := by rw [← hr]; exact PreH3
  exact traffic_scan_step_green_noncurrent__green_transition 114 lights i ans next_green ⟨by omega,by omega⟩ hg hn hs

theorem proof_of_solver_entail_wit_5_3_red : solver_entail_wit_5_3_red := by
  unfold solver_entail_wit_5_3_red
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_3_red_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31)

theorem proof_of_solver_entail_wit_5_4_red_split_goal_1 : solver_entail_wit_5_4_red_split_goal_1 := by
  unfold solver_entail_wit_5_4_red_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 114 lights i ans next_green := by rw [← PreH13]; exact PreH22
  have hg : DoubledTrafficChar lights i=103 := by rw [← hr]; exact PreH2
  exact traffic_scan_step_green_outside_original__green_transition 114 lights i ans next_green ⟨by omega,by omega⟩ hg hs

theorem proof_of_solver_entail_wit_5_4_red : solver_entail_wit_5_4_red := by
  unfold solver_entail_wit_5_4_red
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_4_red_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_solver_entail_wit_5_5_red_split_goal_1 : solver_entail_wit_5_5_red_split_goal_1 := by
  unfold solver_entail_wit_5_5_red_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 114 lights i ans next_green := by rw [← PreH13]; exact PreH22
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH2
  exact traffic_scan_step_nongreen_outside_original__stable_transition 114 lights i ans next_green (by omega) hg hs

theorem proof_of_solver_entail_wit_5_5_red : solver_entail_wit_5_5_red := by
  unfold solver_entail_wit_5_5_red
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_5_red_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_solver_entail_wit_5_6_red_split_goal_1 : solver_entail_wit_5_6_red_split_goal_1 := by
  unfold solver_entail_wit_5_6_red_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 114 lights i ans next_green := by rw [← PreH15]; exact PreH24
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH4
  exact traffic_scan_step_current_keep__stable_transition 114 lights i ans next_green ⟨by omega,by omega⟩ hg PreH1 hs

theorem proof_of_solver_entail_wit_5_6_red : solver_entail_wit_5_6_red := by
  unfold solver_entail_wit_5_6_red
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_6_red_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32)

theorem proof_of_solver_entail_wit_6_1_yellow_split_goal_1 : solver_entail_wit_6_1_yellow_split_goal_1 := by
  unfold solver_entail_wit_6_1_yellow_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 121 lights i ans next_green := by rw [← PreH15]; exact PreH24
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH4
  have hc : DoubledTrafficChar lights i=121 := by rw [← hr,← PreH15]; exact PreH2
  have hpre : Pre 121 lights := by rw [← PreH15]; exact PreH17
  have hstep := traffic_scan_step_current_raise__current_max_update 121 lights i ans next_green hpre ⟨by omega,by omega⟩ (by decide) hc hs (by omega) (by omega)
  exact hstep.1

theorem proof_of_solver_entail_wit_6_1_yellow_split_goal_2 : solver_entail_wit_6_1_yellow_split_goal_2 := by
  unfold solver_entail_wit_6_1_yellow_split_goal_2
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 121 lights i ans next_green := by rw [← PreH15]; exact PreH24
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH4
  have hc : DoubledTrafficChar lights i=121 := by rw [← hr,← PreH15]; exact PreH2
  have hpre : Pre 121 lights := by rw [← PreH15]; exact PreH17
  have hstep := traffic_scan_step_current_raise__current_max_update 121 lights i ans next_green hpre ⟨by omega,by omega⟩ (by decide) hc hs (by omega) (by omega)
  omega

theorem proof_of_solver_entail_wit_6_1_yellow : solver_entail_wit_6_1_yellow := by
  unfold solver_entail_wit_6_1_yellow
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_6_1_yellow_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32)
      | exact (proof_of_solver_entail_wit_6_1_yellow_split_goal_2 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32)

theorem proof_of_solver_entail_wit_6_2_yellow_split_goal_1 : solver_entail_wit_6_2_yellow_split_goal_1 := by
  unfold solver_entail_wit_6_2_yellow_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 121 lights i ans next_green := by rw [← PreH14]; exact PreH23
  have hn : Znth i lights 0≠121 := by
    rw [← cyclic_small lights i ⟨by omega,by omega⟩,← hr,← PreH14]
    exact PreH1
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH3
  exact traffic_scan_step_noncurrent_nongreen__stable_transition 121 lights i ans next_green ⟨by omega,by omega⟩ hn hg hs

theorem proof_of_solver_entail_wit_6_2_yellow : solver_entail_wit_6_2_yellow := by
  unfold solver_entail_wit_6_2_yellow
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_6_2_yellow_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31)

theorem proof_of_solver_entail_wit_6_3_yellow_split_goal_1 : solver_entail_wit_6_3_yellow_split_goal_1 := by
  unfold solver_entail_wit_6_3_yellow_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 121 lights i ans next_green := by rw [← PreH14]; exact PreH23
  have hn : Znth i lights 0≠121 := by
    rw [← cyclic_small lights i ⟨by omega,by omega⟩,← hr,← PreH14]
    exact PreH1
  have hg : DoubledTrafficChar lights i=103 := by rw [← hr]; exact PreH3
  exact traffic_scan_step_green_noncurrent__green_transition 121 lights i ans next_green ⟨by omega,by omega⟩ hg hn hs

theorem proof_of_solver_entail_wit_6_3_yellow : solver_entail_wit_6_3_yellow := by
  unfold solver_entail_wit_6_3_yellow
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_6_3_yellow_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31)

theorem proof_of_solver_entail_wit_6_4_yellow_split_goal_1 : solver_entail_wit_6_4_yellow_split_goal_1 := by
  unfold solver_entail_wit_6_4_yellow_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 121 lights i ans next_green := by rw [← PreH13]; exact PreH22
  have hg : DoubledTrafficChar lights i=103 := by rw [← hr]; exact PreH2
  exact traffic_scan_step_green_outside_original__green_transition 121 lights i ans next_green ⟨by omega,by omega⟩ hg hs

theorem proof_of_solver_entail_wit_6_4_yellow : solver_entail_wit_6_4_yellow := by
  unfold solver_entail_wit_6_4_yellow
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_6_4_yellow_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_solver_entail_wit_6_5_yellow_split_goal_1 : solver_entail_wit_6_5_yellow_split_goal_1 := by
  unfold solver_entail_wit_6_5_yellow_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 121 lights i ans next_green := by rw [← PreH13]; exact PreH22
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH2
  exact traffic_scan_step_nongreen_outside_original__stable_transition 121 lights i ans next_green (by omega) hg hs

theorem proof_of_solver_entail_wit_6_5_yellow : solver_entail_wit_6_5_yellow := by
  unfold solver_entail_wit_6_5_yellow
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_6_5_yellow_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_solver_entail_wit_6_6_yellow_split_goal_1 : solver_entail_wit_6_6_yellow_split_goal_1 := by
  unfold solver_entail_wit_6_6_yellow_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hr := cyclic_read lights i n (by omega) (by omega) (by omega)
  have hs : TrafficScanState 121 lights i ans next_green := by rw [← PreH15]; exact PreH24
  have hg : DoubledTrafficChar lights i≠103 := by rw [← hr]; exact PreH4
  exact traffic_scan_step_current_keep__stable_transition 121 lights i ans next_green ⟨by omega,by omega⟩ hg PreH1 hs

theorem proof_of_solver_entail_wit_6_6_yellow : solver_entail_wit_6_6_yellow := by
  unfold solver_entail_wit_6_6_yellow
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_6_6_yellow_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32)

theorem proof_of_solver_return_wit_1_red_split_goal_1 : solver_return_wit_1_red_split_goal_1 := by
  unfold solver_return_wit_1_red_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hc : c=114 := by assumption
  have hp : Pre 114 lights := by rw [← hc]; exact PreH7
  have hs : TrafficScanState 114 lights i ans next_green := by rw [← hc]; exact PreH14
  exact traffic_scan_exit_implies_spec__final_results 114 lights i ans next_green ⟨by omega,by omega⟩ hp hs

theorem proof_of_solver_return_wit_1_red : solver_return_wit_1_red := by
  unfold solver_return_wit_1_red
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_return_wit_1_red_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_solver_return_wit_2_yellow_split_goal_1 : solver_return_wit_2_yellow_split_goal_1 := by
  unfold solver_return_wit_2_yellow_split_goal_1
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hc : c=121 := by assumption
  have hp : Pre 121 lights := by rw [← hc]; exact PreH7
  have hs : TrafficScanState 121 lights i ans next_green := by rw [← hc]; exact PreH14
  exact traffic_scan_exit_implies_spec__final_results 121 lights i ans next_green ⟨by omega,by omega⟩ hp hs

theorem proof_of_solver_return_wit_2_yellow : solver_return_wit_2_yellow := by
  unfold solver_return_wit_2_yellow
  right
  intro c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_return_wit_2_yellow_split_goal_1 c_pre n_pre lights next_green ans i c n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_solver_return_wit_3_green_split_goal_1 : solver_return_wit_3_green_split_goal_1 := by
  unfold solver_return_wit_3_green_split_goal_1
  intro c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  apply green_current_spec_zero__final_results lights
  rw [← PreH1]
  exact PreH7

theorem proof_of_solver_return_wit_3_green : solver_return_wit_3_green := by
  unfold solver_return_wit_3_green
  right
  intro c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_return_wit_3_green_split_goal_1 c_pre n_pre lights PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_proof_manual
