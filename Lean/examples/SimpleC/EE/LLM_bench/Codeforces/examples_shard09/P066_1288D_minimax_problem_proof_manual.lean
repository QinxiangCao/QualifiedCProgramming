import Mathlib.Tactic.IntervalCases
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_proof_auto
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial

set_option maxHeartbeats 4000000
set_option maxRecDepth 600
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P066_1288D_minimax_problem_goal P066_1288D_minimax_problem_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev matrix := naive_C_Rules.IntArray2

private theorem shift_one (w : Int) (hw : 0≤w) : Z.shiftl 1 w=Z.pow 2 w := by
  obtain ⟨w,rfl⟩ := Int.eq_ofNat_of_zero_le hw
  change (1:Int) <<< w=(2:Int)^w
  simp only [Int.shiftLeft_eq,one_mul]

private theorem signed_shift (j : Int) (hj : 0≤j ∧ j≤8) : signed_last_nbits (Z.shiftl 1 j) 32=Z.pow 2 j := by
  rcases hj with ⟨hj0,hj8⟩
  interval_cases j <;> decide

private theorem pow_mono (a b : Int) (ha : 0≤a) (hab : a≤b) : Z.pow 2 a≤Z.pow 2 b := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤b by omega)
  change (2:Int)^a≤(2:Int)^b
  exact pow_le_pow_right₀ (by omega) (by omega)

private theorem cell_to_singleton (p v : Int) :
    (p # Int |-> v) |-- intArray.full p 1 [v] :=
  P066_1288D_minimax_problem_manual_spatial.cell_to_singleton p v

private theorem rotate_resources (P Q R : naive_C_Rules.expr) :
    (P ** Q ** R) |-- (R ** P ** Q) := by
  cancel

private theorem cells_frame_to_full (bi bj vi vj : Int) (R S : naive_C_Rules.expr)
    (hrs : R |-- S) :
    ((bi # Int |-> vi) ** (bj # Int |-> vj) ** R) |--
      (S ** intArray.full bi 1 [vi] ** intArray.full bj 1 [vj]) := by
  apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ (rotate_resources _ _ _)
  exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
    (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ (cell_to_singleton bi vi) (cell_to_singleton bj vj)) hrs

theorem proof_of_feasible_safety_wit_1_split_goal_1 : feasible_safety_wit_1_split_goal_1 := by
  unfold feasible_safety_wit_1_split_goal_1
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have h0 : 0≤m_pre := by omega
  have h8 : m_pre≤8 := by omega
  interval_cases m_pre <;> decide

theorem proof_of_feasible_safety_wit_1_split_goal_2 : feasible_safety_wit_1_split_goal_2 := by
  unfold feasible_safety_wit_1_split_goal_2
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have h0 : 0≤m_pre := by omega
  have h8 : m_pre≤8 := by omega
  interval_cases m_pre <;> decide

theorem proof_of_feasible_safety_wit_1 : feasible_safety_wit_1 := by
  unfold feasible_safety_wit_1
  right
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pures
  · exact proof_of_feasible_safety_wit_1_split_goal_1 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_feasible_safety_wit_1_split_goal_2 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_feasible_safety_wit_2_split_goal_1 : feasible_safety_wit_2_split_goal_1 := by
  unfold feasible_safety_wit_2_split_goal_1
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have h0 : 0≤m_pre := by omega
  have h8 : m_pre≤8 := by omega
  interval_cases m_pre <;> decide

theorem proof_of_feasible_safety_wit_2_split_goal_2 : feasible_safety_wit_2_split_goal_2 := by
  unfold feasible_safety_wit_2_split_goal_2
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have h0 : 0≤m_pre := by omega
  have h8 : m_pre≤8 := by omega
  interval_cases m_pre <;> decide

theorem proof_of_feasible_safety_wit_2_split_goal_3 : feasible_safety_wit_2_split_goal_3 := by
  unfold feasible_safety_wit_2_split_goal_3
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  omega

theorem proof_of_feasible_safety_wit_2_split_goal_4 : feasible_safety_wit_2_split_goal_4 := by
  unfold feasible_safety_wit_2_split_goal_4
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  omega

theorem proof_of_feasible_safety_wit_2 : feasible_safety_wit_2 := by
  unfold feasible_safety_wit_2
  right
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pures
  · exact proof_of_feasible_safety_wit_2_split_goal_1 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_feasible_safety_wit_2_split_goal_2 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_feasible_safety_wit_2_split_goal_3 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_feasible_safety_wit_2_split_goal_4 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_feasible_safety_wit_14_split_goal_1 : feasible_safety_wit_14_split_goal_1 := by
  unfold feasible_safety_wit_14_split_goal_1
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows reps mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  have h0 : 0≤j := by omega
  have h8 : j≤8 := by omega
  interval_cases j <;> decide

theorem proof_of_feasible_safety_wit_14_split_goal_2 : feasible_safety_wit_14_split_goal_2 := by
  unfold feasible_safety_wit_14_split_goal_2
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows reps mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  have h0 : 0≤j := by omega
  have h8 : j≤8 := by omega
  interval_cases j <;> decide

theorem proof_of_feasible_safety_wit_14_split_goal_3 : feasible_safety_wit_14_split_goal_3 := by
  unfold feasible_safety_wit_14_split_goal_3
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows reps mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  omega

theorem proof_of_feasible_safety_wit_14_split_goal_4 : feasible_safety_wit_14_split_goal_4 := by
  unfold feasible_safety_wit_14_split_goal_4
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows reps mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  omega

theorem proof_of_feasible_safety_wit_14 : feasible_safety_wit_14 := by
  unfold feasible_safety_wit_14
  right
  intro bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows reps mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pures
  · exact proof_of_feasible_safety_wit_14_split_goal_1 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows reps mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  · exact proof_of_feasible_safety_wit_14_split_goal_2 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows reps mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  · exact proof_of_feasible_safety_wit_14_split_goal_3 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows reps mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  · exact proof_of_feasible_safety_wit_14_split_goal_4 bj_pre bi_pre rep_pre x_pre m_pre n_pre a_pre old_bj old_bi rows reps mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_feasible_entail_wit_1 : feasible_entail_wit_1 := by
  unfold feasible_entail_wit_1
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_feasible_entail_wit_1

theorem proof_of_feasible_entail_wit_2_split_goal_1 : feasible_entail_wit_2_split_goal_1 := by
  unfold feasible_entail_wit_2_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  omega

theorem proof_of_feasible_entail_wit_2 : feasible_entail_wit_2 := by
  unfold feasible_entail_wit_2
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_2_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_2_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)

theorem proof_of_feasible_entail_wit_3_split_goal_1 : feasible_entail_wit_3_split_goal_1 := by
  unfold feasible_entail_wit_3_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  intro q hq
  have h:=PreH19 q (by omega)
  omega

theorem proof_of_feasible_entail_wit_3_split_goal_2 : feasible_entail_wit_3_split_goal_2 := by
  unfold feasible_entail_wit_3_split_goal_2
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [shift_one m_pre (by omega)] at PreH13
  intro mask hm
  refine Or.inl ⟨?_,fun row hr=>by omega⟩
  rw [Znth_indep reps_2 mask (-1) 0 (by omega)]
  exact PreH19 mask (by omega)

theorem proof_of_feasible_entail_wit_3 : feasible_entail_wit_3 := by
  unfold feasible_entail_wit_3
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_3_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_3_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact proof_of_feasible_entail_wit_3_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_3_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)

theorem proof_of_feasible_entail_wit_4_split_goal_1 : feasible_entail_wit_4_split_goal_1 := by
  unfold feasible_entail_wit_4_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro q hq
  exact PreH20 q (by omega)

theorem proof_of_feasible_entail_wit_4_split_goal_2 : feasible_entail_wit_4_split_goal_2 := by
  unfold feasible_entail_wit_4_split_goal_2
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact ⟨by change 0≤(0:Int) ∧ 0<1; omega,fun c hc=>by omega⟩

theorem proof_of_feasible_entail_wit_4_split_goal_3 : feasible_entail_wit_4_split_goal_3 := by
  unfold feasible_entail_wit_4_split_goal_3
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  nlinarith

theorem proof_of_feasible_entail_wit_4 : feasible_entail_wit_4 := by
  unfold feasible_entail_wit_4
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_4_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_4_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
      | exact proof_of_feasible_entail_wit_4_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_4_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
      | exact proof_of_feasible_entail_wit_4_split_goal_3 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_4_split_goal_3 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)

theorem proof_of_feasible_entail_wit_5_1_split_goal_1 : feasible_entail_wit_5_1_split_goal_1 := by
  unfold feasible_entail_wit_5_1_split_goal_1
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  dump_pre_spatial
  rw [signed_shift j (by omega)]
  rw [Znth_indep rows i __default__List_Z [] (by omega)] at PreH3
  exact row_mask_set_next__row_mask_step rows x_pre i j mask (by omega) PreH29 PreH3

theorem proof_of_feasible_entail_wit_5_1_split_goal_2 : feasible_entail_wit_5_1_split_goal_2 := by
  unfold feasible_entail_wit_5_1_split_goal_2
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  dump_pre_spatial
  rw [signed_shift j (by omega)]
  rw [Znth_indep rows i __default__List_Z [] (by omega)] at PreH3
  have hn := row_mask_set_next__row_mask_step rows x_pre i j mask (by omega) PreH29 PreH3
  have hb:=hn.1
  have hm:=pow_mono (j+1) m_pre (by omega) (by omega)
  rw [shift_one m_pre (by omega)]
  omega

theorem proof_of_feasible_entail_wit_5_1_split_goal_3 : feasible_entail_wit_5_1_split_goal_3 := by
  unfold feasible_entail_wit_5_1_split_goal_3
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  dump_pre_spatial
  rw [signed_shift j (by omega)]
  rw [Znth_indep rows i __default__List_Z [] (by omega)] at PreH3
  exact (row_mask_set_next__row_mask_step rows x_pre i j mask (by omega) PreH29 PreH3).1.1

theorem proof_of_feasible_entail_wit_5_1_split_goal_4 : feasible_entail_wit_5_1_split_goal_4 := by
  unfold feasible_entail_wit_5_1_split_goal_4
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  dump_pre_spatial
  nlinarith

theorem proof_of_feasible_entail_wit_5_1_split_goal_spatial : feasible_entail_wit_5_1_split_goal_spatial := by
  unfold feasible_entail_wit_5_1_split_goal_spatial
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_feasible_entail_wit_5_1_split_goal_spatial

theorem proof_of_feasible_entail_wit_5_1 : feasible_entail_wit_5_1 := by
  unfold feasible_entail_wit_5_1
  right
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · exact proof_of_feasible_entail_wit_5_1_split_goal_spatial x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_5_1_split_goal_1 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_5_1_split_goal_1 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
      | exact proof_of_feasible_entail_wit_5_1_split_goal_2 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_5_1_split_goal_2 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
      | exact proof_of_feasible_entail_wit_5_1_split_goal_3 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_5_1_split_goal_3 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
      | exact proof_of_feasible_entail_wit_5_1_split_goal_4 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_5_1_split_goal_4 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_feasible_entail_wit_5_2_split_goal_1 : feasible_entail_wit_5_2_split_goal_1 := by
  unfold feasible_entail_wit_5_2_split_goal_1
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  dump_pre_spatial
  rw [Znth_indep rows i __default__List_Z [] (by omega)] at PreH3
  exact row_mask_clear_next__row_mask_step rows x_pre i j mask (by omega) PreH29 PreH3

theorem proof_of_feasible_entail_wit_5_2_split_goal_2 : feasible_entail_wit_5_2_split_goal_2 := by
  unfold feasible_entail_wit_5_2_split_goal_2
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  dump_pre_spatial
  nlinarith

theorem proof_of_feasible_entail_wit_5_2_split_goal_spatial : feasible_entail_wit_5_2_split_goal_spatial := by
  unfold feasible_entail_wit_5_2_split_goal_spatial
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_feasible_entail_wit_5_2_split_goal_spatial

theorem proof_of_feasible_entail_wit_5_2 : feasible_entail_wit_5_2 := by
  unfold feasible_entail_wit_5_2
  right
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · exact proof_of_feasible_entail_wit_5_2_split_goal_spatial x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_5_2_split_goal_1 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_5_2_split_goal_1 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
      | exact proof_of_feasible_entail_wit_5_2_split_goal_2 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_5_2_split_goal_2 x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_feasible_entail_wit_6_1_split_goal_1 : feasible_entail_wit_6_1_split_goal_1 := by
  unfold feasible_entail_wit_6_1_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  intro q hq
  by_cases he:q=mask
  · subst q
    rw [Znth_replace_Znth_Same 0 reps_2 mask i (by omega)]
    omega
  · rw [Znth_replace_Znth_Diff 0 reps_2 mask q i (by omega) (by omega) (Ne.symm he)]
    have h:=PreH28 q hq
    omega

theorem proof_of_feasible_entail_wit_6_1_split_goal_2 : feasible_entail_wit_6_1_split_goal_2 := by
  unfold feasible_entail_wit_6_1_split_goal_2
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  rw [shift_one m_pre (by omega)] at PreH14
  apply representative_insert__representative_update rows x_pre m_pre i reps_2 mask (by omega) (by omega) (by omega) (by omega) PreH26
  · rw [Znth_indep reps_2 mask (-1) 0 (by omega)]
    have h:=PreH28 mask (by omega)
    omega
  · have he:j=m_pre := by omega
    rw [←he]; exact PreH27

theorem proof_of_feasible_entail_wit_6_1_split_goal_3 : feasible_entail_wit_6_1_split_goal_3 := by
  unfold feasible_entail_wit_6_1_split_goal_3
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  rw [Zlength_replace_Znth]
  exact PreH25

theorem proof_of_feasible_entail_wit_6_1 : feasible_entail_wit_6_1 := by
  unfold feasible_entail_wit_6_1
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_6_1_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_6_1_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28)
      | exact proof_of_feasible_entail_wit_6_1_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_6_1_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28)
      | exact proof_of_feasible_entail_wit_6_1_split_goal_3 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_6_1_split_goal_3 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28)

theorem proof_of_feasible_entail_wit_6_2_split_goal_1 : feasible_entail_wit_6_2_split_goal_1 := by
  unfold feasible_entail_wit_6_2_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  intro q hq
  have h:=PreH28 q hq
  omega

theorem proof_of_feasible_entail_wit_6_2_split_goal_2 : feasible_entail_wit_6_2_split_goal_2 := by
  unfold feasible_entail_wit_6_2_split_goal_2
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  rw [shift_one m_pre (by omega)] at PreH14
  apply representative_skip__representative_update rows x_pre m_pre i reps_2 mask (by omega) (by omega) PreH26
  · rw [Znth_indep reps_2 mask (-1) 0 (by omega)]; omega
  · have he:j=m_pre := by omega
    rw [←he]; exact PreH27

theorem proof_of_feasible_entail_wit_6_2 : feasible_entail_wit_6_2 := by
  unfold feasible_entail_wit_6_2
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_6_2_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_6_2_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28)
      | exact proof_of_feasible_entail_wit_6_2_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_6_2_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28)

theorem proof_of_feasible_entail_wit_7_split_goal_1 : feasible_entail_wit_7_split_goal_1 := by
  unfold feasible_entail_wit_7_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro q hq
  have h:=PreH20 q hq
  omega

theorem proof_of_feasible_entail_wit_7_split_goal_2 : feasible_entail_wit_7_split_goal_2 := by
  unfold feasible_entail_wit_7_split_goal_2
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro s u hs hu hb hsr hur
  rcases hb with hb|hb <;> omega

theorem proof_of_feasible_entail_wit_7_split_goal_3 : feasible_entail_wit_7_split_goal_3 := by
  unfold feasible_entail_wit_7_split_goal_3
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have he:i=n_pre := by omega
  rw [←he]
  exact PreH19

theorem proof_of_feasible_entail_wit_7 : feasible_entail_wit_7 := by
  unfold feasible_entail_wit_7
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_7_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_7_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
      | exact proof_of_feasible_entail_wit_7_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_7_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
      | exact proof_of_feasible_entail_wit_7_split_goal_3 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_7_split_goal_3 x_pre m_pre n_pre old_bj old_bi rows reps_2 i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)

theorem proof_of_feasible_entail_wit_8_split_goal_1 : feasible_entail_wit_8_split_goal_1 := by
  unfold feasible_entail_wit_8_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact PreH22

theorem proof_of_feasible_entail_wit_8 : feasible_entail_wit_8 := by
  unfold feasible_entail_wit_8
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_8_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_8_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_feasible_entail_wit_9_1_split_goal_1 : feasible_entail_wit_9_1_split_goal_1 := by
  unfold feasible_entail_wit_9_1_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact PreH25

theorem proof_of_feasible_entail_wit_9_1_split_goal_2 : feasible_entail_wit_9_1_split_goal_2 := by
  unfold feasible_entail_wit_9_1_split_goal_2
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rw [←PreH13]
  exact no_cover_outer_missing__cover_search reps_2 full s u PreH24 (Or.inl (by omega))

theorem proof_of_feasible_entail_wit_9_1 : feasible_entail_wit_9_1 := by
  unfold feasible_entail_wit_9_1
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_9_1_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_9_1_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)
      | exact proof_of_feasible_entail_wit_9_1_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_9_1_split_goal_2 x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)

theorem proof_of_feasible_entail_wit_9_2_split_goal_1 : feasible_entail_wit_9_2_split_goal_1 := by
  unfold feasible_entail_wit_9_2_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [←PreH14]
  apply no_cover_outer_missing__cover_search reps_2 full s 0 PreH21
  right
  rw [Znth_indep reps_2 s (-1) 0 (by omega)]
  exact PreH1

theorem proof_of_feasible_entail_wit_9_2 : feasible_entail_wit_9_2 := by
  unfold feasible_entail_wit_9_2
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_9_2_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_9_2_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_feasible_entail_wit_10_1_split_goal_1 : feasible_entail_wit_10_1_split_goal_1 := by
  unfold feasible_entail_wit_10_1_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  rw [←PreH14]
  apply no_cover_inner_missing__cover_search reps_2 full s u PreH25
  rw [Znth_indep reps_2 u (-1) 0 (by omega)]
  exact PreH1

theorem proof_of_feasible_entail_wit_10_1 : feasible_entail_wit_10_1 := by
  unfold feasible_entail_wit_10_1
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_10_1_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_10_1_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26)

theorem proof_of_feasible_entail_wit_10_2_split_goal_1 : feasible_entail_wit_10_2_split_goal_1 := by
  unfold feasible_entail_wit_10_2_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  rw [←PreH15]
  exact no_cover_inner_noncover__cover_search reps_2 full s u PreH26 PreH1

theorem proof_of_feasible_entail_wit_10_2 : feasible_entail_wit_10_2 := by
  unfold feasible_entail_wit_10_2
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_entail_wit_10_2_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
      | (dump_pre_spatial; exact proof_of_feasible_entail_wit_10_2_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_feasible_return_wit_1_split_goal_1 : feasible_return_wit_1_split_goal_1 := by
  unfold feasible_return_wit_1_split_goal_1
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply completed_no_cover_excludes_feasible__feasible_outcomes rows x_pre m_pre n_pre reps_2 s full (by omega) PreH9
  · rw [Znth_indep rows 0 [] __default__List_Z (by omega)]; exact PreH10
  · exact PreH13
  · exact PreH19
  · exact PreH20
  · exact PreH1

theorem proof_of_feasible_return_wit_1 : feasible_return_wit_1 := by
  unfold feasible_return_wit_1
  right
  intro x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact proof_of_feasible_return_wit_1_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | (dump_pre_spatial; exact proof_of_feasible_return_wit_1_split_goal_1 x_pre m_pre n_pre old_bj old_bi rows reps_2 s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_feasible_return_wit_2 : feasible_return_wit_2 := by
  unfold feasible_return_wit_2
  right
  intro bj_pre bi_pre x_pre m_pre n_pre old_bj old_bi rows reps_2 u s full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hfull := PreH19
  rw [shift_one m_pre (by omega)] at hfull
  have hsidx : 0≤s ∧ s<Zlength reps_2 := by omega
  have huidx : 0≤u ∧ u<Zlength reps_2 := by omega
  have hsrep := PreH29 s (by omega)
  have hurep := PreH29 u (by omega)
  rw [Znth_indep reps_2 s (-1) 0 hsidx] at hsrep
  rw [Znth_indep reps_2 u (-1) 0 huidx] at hurep
  rcases hsrep with ⟨hempty,_⟩|⟨ri,hri,heri,hsmask⟩
  · omega
  rcases hurep with ⟨hempty,_⟩|⟨rj,hrj,herj,humask⟩
  · omega
  subst ri
  subst rj
  have hw : m_pre=Zlength (Znth 0 rows []) := by
    rw [Znth_indep rows 0 [] __default__List_Z (by omega)]
    exact PreH16
  have hp := row_masks_cover_pair__feasible_outcomes rows x_pre m_pre (Znth s reps_2 0) (Znth u reps_2 0) s u hw (by omega) (by omega) hsmask humask (by omega)
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) (Znth s reps_2 0) ?_
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) (Znth u reps_2 0) ?_
  split_pure_spatial
  · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ (cell_to_singleton bi_pre _) (cell_to_singleton bj_pre _)
  · split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_feasible_which_implies_wit_1 : feasible_which_implies_wit_1 := by
  unfold feasible_which_implies_wit_1
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_feasible_which_implies_wit_1

theorem proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1 := by
  unfold solver_safety_wit_4_split_goal_1
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dump_pre_spatial
  have hp := half_positive__solver_semantics (hi-lo+1) (by omega)
  have hl := half_less_than_input__solver_semantics (hi-lo+1) (by omega)
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2 := by
  unfold solver_safety_wit_4_split_goal_2
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dump_pre_spatial
  have hp := half_positive__solver_semantics (hi-lo+1) (by omega)
  have hl := half_less_than_input__solver_semantics (hi-lo+1) (by omega)
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_solver_safety_wit_4 : solver_safety_wit_4 := by
  unfold solver_safety_wit_4
  right
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  · exact proof_of_solver_safety_wit_4_split_goal_1 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  · exact proof_of_solver_safety_wit_4_split_goal_2 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1 := by
  unfold solver_safety_wit_12_split_goal_1
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  have hp := half_positive__solver_semantics (hi-lo+1) (by omega)
  have hl := half_less_than_input__solver_semantics (hi-lo+1) (by omega)
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2 := by
  unfold solver_safety_wit_12_split_goal_2
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  have hp := half_positive__solver_semantics (hi-lo+1) (by omega)
  have hl := half_less_than_input__solver_semantics (hi-lo+1) (by omega)
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_solver_safety_wit_12 : solver_safety_wit_12 := by
  unfold solver_safety_wit_12
  right
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pures
  · exact proof_of_solver_safety_wit_12_split_goal_1 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  · exact proof_of_solver_safety_wit_12_split_goal_2 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro bj_pre bi_pre rep_pre m_pre n_pre rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hm := PreH6 0 (by omega)
  have he := matrix_entries_bounded_from_flat__solver_semantics rows n_pre m_pre __default__List_Z PreH3 (by omega) PreH8 PreH9 PreH7
  have hp := pair_at_least_zero__solver_semantics rows PreH3 he (by omega)
  obtain ⟨best,ho⟩ := optimal_pair_score_exists__solver_semantics rows PreH3 he (by omega)
  have hb := optimal_pair_score_bounds__solver_semantics rows best PreH3 he ho
  have meaning : SolverSearchMeaning rows 0 1000000000 0 0 := ⟨best,ho,hb,hp⟩
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) 0 ?_
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) 0 ?_
  split_pure_spatial
  · exact cells_frame_to_full bi_pre bj_pre 1 1 _ _ (naive_C_Rules.toContext.derivable1_refl _)
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  unfold solver_entail_wit_4_1
  right
  intro bj_pre bi_pre rep_pre m_pre n_pre rows cur_j_2 cur_i_2 hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have he := matrix_entries_bounded_from_flat__solver_semantics rows n_pre m_pre __default__List_Z PreH11 (by omega) PreH16 PreH17 PreH18
  rcases PreH26 with ⟨best,ho,hb,hcur⟩
  have hmid := (feasible_threshold_optimal_bound__solver_semantics rows best (lo+Z.quot (hi-lo+1) 2) PreH11 he ho).1 ⟨i,j,PreH7⟩
  have hp := half_positive__solver_semantics (hi-lo+1) (by omega)
  have hl := half_less_than_input__solver_semantics (hi-lo+1) (by omega)
  have hir := PreH7.1
  have hjr := PreH7.2.1
  have meaning : SolverSearchMeaning rows (lo+Z.quot (hi-lo+1) 2) hi i j := ⟨best,ho,⟨hmid,hb.2⟩,PreH7⟩
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) j ?_
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) i ?_
  split_pure_spatial
  · exact cells_frame_to_full bi_pre bj_pre (i+1) (j+1) _ _ (intArray.full_to_full_shape rep_pre 256 reps)
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  unfold solver_entail_wit_4_2
  right
  intro rep_pre m_pre n_pre rows cur_j_2 cur_i_2 hi lo cj_cells ci_cells reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have he := matrix_entries_bounded_from_flat__solver_semantics rows n_pre m_pre __default__List_Z PreH7 (by omega) PreH12 PreH13 PreH14
  rcases PreH22 with ⟨best,ho,hb,hcur⟩
  have hmid := (feasible_threshold_optimal_bound__solver_semantics rows best (lo+Z.quot (hi-lo+1) 2) PreH7 he ho).2 PreH3
  have hp := half_positive__solver_semantics (hi-lo+1) (by omega)
  have hl := half_less_than_input__solver_semantics (hi-lo+1) (by omega)
  have meaning : SolverSearchMeaning rows lo (lo+Z.quot (hi-lo+1) 2-1) cur_i_2 cur_j_2 := ⟨best,ho,⟨hb.1,by omega⟩,hcur⟩
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) cur_j_2 ?_
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) cur_i_2 ?_
  split_pure_spatial
  · exact intArray.full_to_full_shape rep_pre 256 reps
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro rep_pre m_pre n_pre rows cur_j cur_i hi lo bj_cells bi_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have he := matrix_entries_bounded_from_flat__solver_semantics rows n_pre m_pre __default__List_Z PreH8 (by omega) PreH13 PreH14 PreH15
  rcases PreH23 with ⟨best,ho,hb,hcur⟩
  have hbest : best=0 := by omega
  subst best
  have hs := optimal_pair_to_spec__solver_semantics rows 0 i j PreH8 he ho PreH3
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) (i+1,j+1) ?_
  split_pure_spatial
  · exact intArray.full_to_full_shape rep_pre 256 reps
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro bj_pre bi_pre rep_pre m_pre n_pre rows cur_j cur_i hi lo bj_cells bi_cells reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have he := matrix_entries_bounded_from_flat__solver_semantics rows n_pre m_pre __default__List_Z PreH8 (by omega) PreH13 PreH14 PreH15
  exact False.elim (PreH3 ⟨0,0,pair_at_least_zero__solver_semantics rows PreH8 he (by omega)⟩)

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro m_pre n_pre rows cur_j cur_i hi lo __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have he := matrix_entries_bounded_from_flat__solver_semantics rows n_pre m_pre __default__List_Z PreH3 (by omega) PreH8 PreH9 PreH10
  rcases PreH18 with ⟨best,ho,hb,hcur⟩
  have hbest : best=lo := by omega
  subst best
  have hs := optimal_pair_to_spec__solver_semantics rows lo cur_i cur_j PreH3 he ho hcur
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) (cur_i+1,cur_j+1) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl

theorem proof_of_solver_partial_solve_wit_3_pure_split_goal_1 : solver_partial_solve_wit_3_pure_split_goal_1 := by
  unfold solver_partial_solve_wit_3_pure_split_goal_1
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  dump_pre_spatial
  have hp := half_positive__solver_semantics (hi-lo+1) (by omega)
  have hl := half_less_than_input__solver_semantics (hi-lo+1) (by omega)
  first | assumption | omega

theorem proof_of_solver_partial_solve_wit_3_pure_split_goal_2 : solver_partial_solve_wit_3_pure_split_goal_2 := by
  unfold solver_partial_solve_wit_3_pure_split_goal_2
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  dump_pre_spatial
  have hp := half_positive__solver_semantics (hi-lo+1) (by omega)
  have hl := half_less_than_input__solver_semantics (hi-lo+1) (by omega)
  first | assumption | omega

theorem proof_of_solver_partial_solve_wit_3_pure_split_goal_3 : solver_partial_solve_wit_3_pure_split_goal_3 := by
  unfold solver_partial_solve_wit_3_pure_split_goal_3
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  dump_pre_spatial
  have hp := half_positive__solver_semantics (hi-lo+1) (by omega)
  have hl := half_less_than_input__solver_semantics (hi-lo+1) (by omega)
  first | assumption | omega

theorem proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure := by
  unfold solver_partial_solve_wit_3_pure
  right
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  split_pures
  · exact proof_of_solver_partial_solve_wit_3_pure_split_goal_1 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  · exact proof_of_solver_partial_solve_wit_3_pure_split_goal_2 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  · exact proof_of_solver_partial_solve_wit_3_pure_split_goal_3 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29

theorem proof_of_solver_partial_solve_wit_4_pure_split_goal_1 : solver_partial_solve_wit_4_pure_split_goal_1 := by
  unfold solver_partial_solve_wit_4_pure_split_goal_1
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  dump_pre_spatial
  try simp only [Zlength_cons,Zlength_nil]
  first | assumption | omega | nlinarith

theorem proof_of_solver_partial_solve_wit_4_pure_split_goal_2 : solver_partial_solve_wit_4_pure_split_goal_2 := by
  unfold solver_partial_solve_wit_4_pure_split_goal_2
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  dump_pre_spatial
  try simp only [Zlength_cons,Zlength_nil]
  first | assumption | omega | nlinarith

theorem proof_of_solver_partial_solve_wit_4_pure_split_goal_3 : solver_partial_solve_wit_4_pure_split_goal_3 := by
  unfold solver_partial_solve_wit_4_pure_split_goal_3
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  dump_pre_spatial
  try simp only [Zlength_cons,Zlength_nil]
  first | assumption | omega | nlinarith

theorem proof_of_solver_partial_solve_wit_4_pure_split_goal_4 : solver_partial_solve_wit_4_pure_split_goal_4 := by
  unfold solver_partial_solve_wit_4_pure_split_goal_4
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  dump_pre_spatial
  try simp only [Zlength_cons,Zlength_nil]
  first | assumption | omega | nlinarith

theorem proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure := by
  unfold solver_partial_solve_wit_4_pure
  right
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pures
  · exact proof_of_solver_partial_solve_wit_4_pure_split_goal_1 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  · exact proof_of_solver_partial_solve_wit_4_pure_split_goal_2 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  · exact proof_of_solver_partial_solve_wit_4_pure_split_goal_3 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  · exact proof_of_solver_partial_solve_wit_4_pure_split_goal_4 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo cj_cells ci_cells i j reps retval __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33

theorem proof_of_solver_partial_solve_wit_7_pure_split_goal_1 : solver_partial_solve_wit_7_pure_split_goal_1 := by
  unfold solver_partial_solve_wit_7_pure_split_goal_1
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo bj_cells bi_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  dump_pre_spatial
  try simp only [Zlength_cons,Zlength_nil]
  first | assumption | omega | nlinarith

theorem proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure := by
  unfold solver_partial_solve_wit_7_pure
  right
  intro bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo bj_cells bi_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pures
  · exact proof_of_solver_partial_solve_wit_7_pure_split_goal_1 bj_pre bi_pre rep_pre m_pre n_pre a_pre rows cur_j cur_i hi lo bj_cells bi_cells __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1 := by
  unfold solver_which_implies_wit_1
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_1

theorem proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2 := by
  unfold solver_which_implies_wit_2
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_2

theorem proof_of_solver_which_implies_wit_3_split_goal_spatial : solver_which_implies_wit_3_split_goal_spatial := by
  unfold solver_which_implies_wit_3_split_goal_spatial
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_3_split_goal_spatial

theorem proof_of_solver_which_implies_wit_3 : solver_which_implies_wit_3 := by
  unfold solver_which_implies_wit_3
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_3

theorem proof_of_solver_which_implies_wit_4 : solver_which_implies_wit_4 := by
  unfold solver_which_implies_wit_4
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_4

theorem proof_of_solver_which_implies_wit_5 : solver_which_implies_wit_5 := by
  unfold solver_which_implies_wit_5
  exact P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_5

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_proof_manual
