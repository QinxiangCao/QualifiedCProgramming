import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 600
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P053_1393C_pinkie_pie_eats_patty_cakes_goal P053_1393C_pinkie_pie_eats_patty_cakes_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1 := by
  unfold solver_safety_wit_13_split_goal_1
  intro n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  dump_pre_spatial
  have ht := terminal_frequency_bounds__terminal_result values counts n_pre i mx c PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hnum : 0≤n_pre-c := by omega
  have hden : 0<mx-1 := by omega
  have hd : Z.quot (n_pre-c) (mx-1)=(n_pre-c)/(mx-1) := Int.tdiv_eq_ediv_of_nonneg hnum
  rw [hd]
  have h0 := Int.ediv_nonneg hnum (by omega : 0≤mx-1)
  have h1 := Int.ediv_le_self (mx-1) hnum
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2 := by
  unfold solver_safety_wit_13_split_goal_2
  intro n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  dump_pre_spatial
  have ht := terminal_frequency_bounds__terminal_result values counts n_pre i mx c PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hnum : 0≤n_pre-c := by omega
  have hden : 0<mx-1 := by omega
  have hd : Z.quot (n_pre-c) (mx-1)=(n_pre-c)/(mx-1) := Int.tdiv_eq_ediv_of_nonneg hnum
  rw [hd]
  have h0 := Int.ediv_nonneg hnum (by omega : 0≤mx-1)
  have h1 := Int.ediv_le_self (mx-1) hnum
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_solver_safety_wit_13 : solver_safety_wit_13 := by
  unfold solver_safety_wit_13
  right
  intro n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pures
  · exact proof_of_solver_safety_wit_13_split_goal_1 n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  · exact proof_of_solver_safety_wit_13_split_goal_2 n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_solver_safety_wit_14_split_goal_1 : solver_safety_wit_14_split_goal_1 := by
  unfold solver_safety_wit_14_split_goal_1
  intro n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  dump_pre_spatial
  have ht := terminal_frequency_bounds__terminal_result values counts n_pre i mx c PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  right
  omega

theorem proof_of_solver_safety_wit_14_split_goal_2 : solver_safety_wit_14_split_goal_2 := by
  unfold solver_safety_wit_14_split_goal_2
  intro n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  dump_pre_spatial
  have ht := terminal_frequency_bounds__terminal_result values counts n_pre i mx c PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  omega

theorem proof_of_solver_safety_wit_14 : solver_safety_wit_14 := by
  unfold solver_safety_wit_14
  right
  intro n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pures
  · exact proof_of_solver_safety_wit_14_split_goal_1 n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  · exact proof_of_solver_safety_wit_14_split_goal_2 n_pre a_pre values counts c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  unfold solver_entail_wit_1_split_goal_1
  intro n_pre values retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  intro k hk
  unfold SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z
  rw [Znth_repeat]
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  unfold solver_entail_wit_1_split_goal_2
  intro n_pre values retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  constructor
  · unfold SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z
    simp only [Zlength,List.length_replicate,Int.ofNat_eq_coe] at PreH6 ⊢
    omega
  · intro v hv
    unfold SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z
    rw [Znth_repeat,Zsublist_nil _ 0 0 (le_refl _)]
    rfl

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  unfold solver_entail_wit_1_split_goal_3
  intro n_pre values retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact PreH4

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n_pre values retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre values retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre values retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | exact proof_of_solver_entail_wit_1_split_goal_3 n_pre values retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  unfold solver_entail_wit_2_split_goal_1
  intro n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hv := PreH8 i (by omega)
  exact count_prefix_step__counting_invariant values counts_2 i (by omega) (by omega) PreH12

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  unfold solver_entail_wit_3_split_goal_1
  intro n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  intro k hk
  have h := PreH13 k hk
  omega

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  unfold solver_entail_wit_3_split_goal_2
  intro n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hl := PreH12.1
  exact maximum_frequency_prefix_zero__counting_invariant counts_2 (by omega)

theorem proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3 := by
  unfold solver_entail_wit_3_split_goal_3
  intro n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have he : n_pre=i := by omega
  rw [he]
  exact PreH12

theorem proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4 := by
  unfold solver_entail_wit_3_split_goal_4
  intro n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH8

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_3_split_goal_1 n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_solver_entail_wit_3_split_goal_2 n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_solver_entail_wit_3_split_goal_3 n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_solver_entail_wit_3_split_goal_4 n_pre values counts_2 i c mx cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1 := by
  unfold solver_entail_wit_4_1_split_goal_1
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hl := PreH15.1
  exact maximum_frequency_prefix_raise__frequency_transitions counts_2 i mx c PreH9 (by omega) PreH16 PreH1

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  unfold solver_entail_wit_4_1
  right
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_1_split_goal_1 n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1 := by
  unfold solver_entail_wit_4_2_split_goal_1
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hl := PreH16.1
  exact maximum_frequency_prefix_tie__frequency_transitions counts_2 i mx c PreH10 (by omega) PreH17 PreH1

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  unfold solver_entail_wit_4_2
  right
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_2_split_goal_1 n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1 := by
  unfold solver_entail_wit_4_3_split_goal_1
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hl := PreH16.1
  have hv := PreH18 i (by omega)
  exact maximum_frequency_prefix_below__frequency_transitions counts_2 i mx c PreH10 (by omega) PreH17 hv.1 PreH2 PreH1

theorem proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3 := by
  unfold solver_entail_wit_4_3
  right
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_3_split_goal_1 n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  unfold solver_entail_wit_5_split_goal_1
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have ht := terminal_frequency_bounds__terminal_result values counts_2 n_pre i mx c PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hd : Z.quot (n_pre-c) (mx-1)=Z.div (n_pre-c) (mx-1) := (Int.fdiv_eq_tdiv_of_nonneg (by omega) (by omega)).symm
  rw [hd,PreH3]
  apply terminal_frequency_summary_implies_Spec values counts_2 mx c
  · rw [←PreH3]; exact PreH14
  · rw [←PreH3,←ht.1]; exact PreH15

theorem proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2 := by
  unfold solver_entail_wit_5_split_goal_2
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he:i=n_pre+1 := by omega
  rw [←he]
  exact PreH15

theorem proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3 := by
  unfold solver_entail_wit_5_split_goal_3
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have ht := terminal_frequency_bounds__terminal_result values counts_2 n_pre i mx c PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact ht.2.2.1

theorem proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4 := by
  unfold solver_entail_wit_5_split_goal_4
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have ht := terminal_frequency_bounds__terminal_result values counts_2 n_pre i mx c PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact ht.2.1.1

theorem proof_of_solver_entail_wit_5_split_goal_5 : solver_entail_wit_5_split_goal_5 := by
  unfold solver_entail_wit_5_split_goal_5
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH6

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  right
  intro n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_split_goal_1 n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_solver_entail_wit_5_split_goal_2 n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_solver_entail_wit_5_split_goal_3 n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_solver_entail_wit_5_split_goal_4 n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_solver_entail_wit_5_split_goal_5 n_pre values counts_2 c mx i cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual
