import SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_goal
import SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open minimal_representation_goal minimal_representation_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg


-- Preserve the source SL tactics and generated residual VCs. The current
-- Goal_apply needs explicit arguments; pure propositions additionally require
-- dump_spatial_left, while spatial split lemmas retain their heap assertions.
theorem proof_of_minimal_representation_entail_wit_1_split_goal_1 : minimal_representation_entail_wit_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_1_split_goal_1
  intro best l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dump_pre_spatial
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_1_split_goal_spatial : minimal_representation_entail_wit_1_split_goal_spatial := by
  unfold minimal_representation_entail_wit_1_split_goal_spatial
  intro best l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  change _ |-- naive_C_Rules.IntArray.undef_seg (&("b")) 0 n_pre **
    naive_C_Rules.IntArray.seg (&("b")) n_pre (n_pre+0) ([] : List Int) **
    naive_C_Rules.IntArray.undef_seg (&("b")) (n_pre+0) (2*n_pre) **
    naive_C_Rules.IntArray.undef_seg (&("b")) (2*n_pre) 2000
  simp only [Int.add_zero]
  sep_apply_l_atomic (naive_C_Rules.IntArray.undef_full_split_to_undef_seg (&("b")) (2*n_pre) 2000 (by omega))
  sep_apply_l_atomic (naive_C_Rules.IntArray.undef_seg_to_undef_full (&("b")) 0 (2*n_pre))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply_l_atomic (naive_C_Rules.IntArray.undef_full_split_to_undef_seg (&("b")) n_pre (2*n_pre) (by omega))
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.seg_empty (&("b")) n_pre n_pre)).2)
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    rfl

theorem proof_of_minimal_representation_entail_wit_1 : minimal_representation_entail_wit_1 := by
  unfold minimal_representation_entail_wit_1
  right
  intro best l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_1_split_goal_1 best l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_1_split_goal_spatial best l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
    | exact (proof_of_minimal_representation_entail_wit_1_split_goal_1 best l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_minimal_representation_entail_wit_1_split_goal_spatial best l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_minimal_representation_entail_wit_2_split_goal_1 : minimal_representation_entail_wit_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_2_split_goal_1
  intro best l n_pre p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  rw [sublist_split 0 (p+1) p l (by omega) (by omega), sublist_single 0 p l (by omega)]

theorem proof_of_minimal_representation_entail_wit_2_split_goal_spatial : minimal_representation_entail_wit_2_split_goal_spatial := by
  unfold minimal_representation_entail_wit_2_split_goal_spatial
  intro best l n_pre p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rw [sublist_split 0 (p+1) p l (by omega) (by omega), sublist_single 0 p l (by omega)]
  rw [show n_pre+(p+1) = n_pre+p+1 by omega]
  cancel

theorem proof_of_minimal_representation_entail_wit_2 : minimal_representation_entail_wit_2 := by
  unfold minimal_representation_entail_wit_2
  right
  intro best l n_pre p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_2_split_goal_1 best l n_pre p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_2_split_goal_spatial best l n_pre p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_minimal_representation_entail_wit_2_split_goal_1 best l n_pre p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | exact (proof_of_minimal_representation_entail_wit_2_split_goal_spatial best l n_pre p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_minimal_representation_entail_wit_4_1_split_goal_1 : minimal_representation_entail_wit_4_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_4_1_split_goal_1
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro offset ho
  omega

theorem proof_of_minimal_representation_entail_wit_4_1 : minimal_representation_entail_wit_4_1 := by
  unfold minimal_representation_entail_wit_4_1
  right
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_4_1_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_4_1_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_4_2_split_goal_1 : minimal_representation_entail_wit_4_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_4_2_split_goal_1
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro offset ho
  omega

theorem proof_of_minimal_representation_entail_wit_4_2 : minimal_representation_entail_wit_4_2 := by
  unfold minimal_representation_entail_wit_4_2
  right
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_4_2_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_4_2_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_5_split_goal_1 : minimal_representation_entail_wit_5_split_goal_1 := by
  unfold minimal_representation_entail_wit_5_split_goal_1
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro offset ho
  by_cases hk : offset < k
  · exact PreH17 offset (by omega)
  · have heq : offset = k := by omega
    subst offset
    exact PreH1

theorem proof_of_minimal_representation_entail_wit_5 : minimal_representation_entail_wit_5 := by
  unfold minimal_representation_entail_wit_5
  right
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_5_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_5_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_6_1 : minimal_representation_entail_wit_6_1 := by
  unfold minimal_representation_entail_wit_6_1
  intro best l a_pre n_pre out_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best (i+k+2) j := by
    have ht := MRCandidateState_advance_left__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.1 (by omega)
  Right
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_6_2 : minimal_representation_entail_wit_6_2 := by
  unfold minimal_representation_entail_wit_6_2
  intro best l a_pre n_pre out_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best (i+k+1) j := by
    have ht := MRCandidateState_advance_left__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.2 (by omega)
  Right
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_6_3 : minimal_representation_entail_wit_6_3 := by
  unfold minimal_representation_entail_wit_6_3
  intro best l a_pre n_pre out_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best i (j+k+2) := by
    have ht := MRCandidateState_advance_right__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.1 (by omega)
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_6_4 : minimal_representation_entail_wit_6_4 := by
  unfold minimal_representation_entail_wit_6_4
  intro best l a_pre n_pre out_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best i (j+k+1) := by
    have ht := MRCandidateState_advance_right__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.2 (by omega)
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_7_1_split_goal_1 : minimal_representation_entail_wit_7_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_7_1_split_goal_1
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  intro h
  rcases PreH16 with hb | hb | ⟨hf, _⟩ <;> omega

theorem proof_of_minimal_representation_entail_wit_7_1 : minimal_representation_entail_wit_7_1 := by
  unfold minimal_representation_entail_wit_7_1
  right
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_7_1_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_minimal_representation_entail_wit_7_1_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

theorem proof_of_minimal_representation_entail_wit_7_2_split_goal_1 : minimal_representation_entail_wit_7_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_7_2_split_goal_1
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro h
  rcases PreH17 with hb | hb | ⟨hf, _⟩ <;> omega

theorem proof_of_minimal_representation_entail_wit_7_2 : minimal_representation_entail_wit_7_2 := by
  unfold minimal_representation_entail_wit_7_2
  right
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_7_2_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_7_2_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_7_3 : minimal_representation_entail_wit_7_3 := by
  unfold minimal_representation_entail_wit_7_3
  intro best l a_pre n_pre out_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hi : MRValidStart l i := by constructor <;> omega
  have hj : MRValidStart l j := by constructor <;> omega
  have heq : MRRotationEq l i j := by
    unfold MRRotationEq
    rw [PreH5, ← PreH1]
    exact PreH17
  obtain ⟨hlt, hge⟩ := MRCandidateState_equal_exit__candidate_boundaries l best i j hi hj PreH12 PreH15 PreH16 heq
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega

theorem proof_of_minimal_representation_entail_wit_8_1_split_goal_1 : minimal_representation_entail_wit_8_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_8_1_split_goal_1
  intro best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_8_1 : minimal_representation_entail_wit_8_1 := by
  unfold minimal_representation_entail_wit_8_1
  right
  intro best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_8_1_split_goal_1 best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_8_1_split_goal_1 best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_8_2_split_goal_1 : minimal_representation_entail_wit_8_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_8_2_split_goal_1
  intro best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_8_2 : minimal_representation_entail_wit_8_2 := by
  unfold minimal_representation_entail_wit_8_2
  right
  intro best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_8_2_split_goal_1 best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_8_2_split_goal_1 best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_8_3_split_goal_1 : minimal_representation_entail_wit_8_3_split_goal_1 := by
  unfold minimal_representation_entail_wit_8_3_split_goal_1
  intro best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_8_3 : minimal_representation_entail_wit_8_3 := by
  unfold minimal_representation_entail_wit_8_3
  right
  intro best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_8_3_split_goal_1 best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_8_3_split_goal_1 best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_8_4_split_goal_1 : minimal_representation_entail_wit_8_4_split_goal_1 := by
  unfold minimal_representation_entail_wit_8_4_split_goal_1
  intro best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_8_4 : minimal_representation_entail_wit_8_4 := by
  unfold minimal_representation_entail_wit_8_4
  right
  intro best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_8_4_split_goal_1 best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_8_4_split_goal_1 best l n_pre i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_9_split_goal_1 : minimal_representation_entail_wit_9_split_goal_1 := by
  unfold minimal_representation_entail_wit_9_split_goal_1
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hs : MRValidStart l best := by constructor <;> omega
  have hn := MRRotation_Zlength__output_finalization l best hs
  rw [← MRRotation_Znth__output_finalization l best k hs (by omega),
    sublist_split 0 (k+1) k (MRRotation l best) (by omega) (by omega),
    sublist_single 0 k (MRRotation l best) (by omega)]

theorem proof_of_minimal_representation_entail_wit_9 : minimal_representation_entail_wit_9 := by
  unfold minimal_representation_entail_wit_9
  right
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_9_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_minimal_representation_entail_wit_9_split_goal_1 best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

theorem proof_of_minimal_representation_entail_wit_10_split_goal_spatial : minimal_representation_entail_wit_10_split_goal_spatial := by
  unfold minimal_representation_entail_wit_10_split_goal_spatial
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  sep_apply (naive_C_Rules.IntArray.full_to_undef_full (&("b")) (2*n_pre) (l++l))
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg (&("b")) (2*n_pre))
  sep_apply (naive_C_Rules.IntArray.undef_seg_merge_to_undef_full (&("b")) 0 (2*n_pre) 2000 ⟨by omega, by omega⟩)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

theorem proof_of_minimal_representation_entail_wit_10 : minimal_representation_entail_wit_10 := by
  unfold minimal_representation_entail_wit_10
  right
  intro best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hs : MRValidStart l best := by constructor <;> omega
  have hn := MRRotation_Zlength__output_finalization l best hs
  have hk : k = n_pre := by omega
  split_pure_spatial
  · exact proof_of_minimal_representation_entail_wit_10_split_goal_spatial best l n_pre k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  · dump_pre_spatial
    rw [hk, sublist_self (MRRotation l best) n_pre (by omega)]

theorem proof_of_minimal_representation_entail_wit_3 : minimal_representation_entail_wit_3 := by
  unfold minimal_representation_entail_wit_3
  intro best l a n out p hp hn hnmax hl hb hbmax hp0 hpn hminimal
  have he : p = n := by omega
  rw [he, sublist_self l n hl.symm, show n+n = 2*n by omega]
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.undef_seg_empty (&("b")) n)).1)
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.undef_seg_empty (&("b")) (2*n))).1)
  sep_apply (naive_C_Rules.IntArray.seg_merge_to_full (&("b")) 0 n (2*n) l l (by omega))
  have hstate := MRCandidateState_initial__candidate_boundaries l best (by omega) hminimal
  Left
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | trivial | omega

end SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_proof_manual
