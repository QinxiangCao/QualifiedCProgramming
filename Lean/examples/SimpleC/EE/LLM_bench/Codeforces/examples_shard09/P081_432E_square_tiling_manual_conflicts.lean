import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_goal
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo

 theorem p081_signed_byte (flat : List Int) (index : Int) (hc : CanonicalGrid flat) (hi : 0≤index ∧ index<Zlength flat) :
    signed_last_nbits (Znth index flat 0) 8=Znth index flat 0 := by
  apply signed_last_nbits_eq _ 8 (by decide)
  change -128≤Znth index flat 0 ∧ Znth index flat 0<128
  rcases hc index hi with hz | hr <;> omega

theorem proof_of_conflicts_entail_wit_1_split_goal_1 : conflicts_entail_wit_1_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  intro h
  constructor <;> nlinarith

theorem proof_of_conflicts_entail_wit_1_split_goal_2 : conflicts_entail_wit_1_split_goal_2 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  intro h
  constructor <;> nlinarith

theorem proof_of_conflicts_entail_wit_1_split_goal_3 : conflicts_entail_wit_1_split_goal_3 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  intro h
  constructor <;> nlinarith

theorem proof_of_conflicts_entail_wit_1_split_goal_4 : conflicts_entail_wit_1_split_goal_4 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  intro h
  constructor <;> nlinarith

theorem proof_of_conflicts_entail_wit_1 : conflicts_entail_wit_1 := by
  unfold conflicts_entail_wit_1
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_entail_wit_1_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_conflicts_entail_wit_1_split_goal_2 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_conflicts_entail_wit_1_split_goal_3 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_conflicts_entail_wit_1_split_goal_4 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_conflicts_return_wit_1_split_goal_1 : conflicts_return_wit_1_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_1 : conflicts_return_wit_1 := by
  unfold conflicts_return_wit_1
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_1_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_2_split_goal_1 : conflicts_return_wit_2_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_2 : conflicts_return_wit_2 := by
  unfold conflicts_return_wit_2
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_2_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_3_split_goal_1 : conflicts_return_wit_3_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_3 : conflicts_return_wit_3 := by
  unfold conflicts_return_wit_3
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_3_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_4_split_goal_1 : conflicts_return_wit_4_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_4 : conflicts_return_wit_4 := by
  unfold conflicts_return_wit_4
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_4_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_5_split_goal_1 : conflicts_return_wit_5_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_5 : conflicts_return_wit_5 := by
  unfold conflicts_return_wit_5
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_5_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_6_split_goal_1 : conflicts_return_wit_6_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH24 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_6 : conflicts_return_wit_6 := by
  unfold conflicts_return_wit_6
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_6_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_7_split_goal_1 : conflicts_return_wit_7_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_7 : conflicts_return_wit_7 := by
  unfold conflicts_return_wit_7
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_7_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_8_split_goal_1 : conflicts_return_wit_8_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_8 : conflicts_return_wit_8 := by
  unfold conflicts_return_wit_8
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_8_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_9_split_goal_1 : conflicts_return_wit_9_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_9 : conflicts_return_wit_9 := by
  unfold conflicts_return_wit_9
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_9_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_10_split_goal_1 : conflicts_return_wit_10_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_10 : conflicts_return_wit_10 := by
  unfold conflicts_return_wit_10
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_10_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_11_split_goal_1 : conflicts_return_wit_11_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_11 : conflicts_return_wit_11 := by
  unfold conflicts_return_wit_11
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_11_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_12_split_goal_1 : conflicts_return_wit_12_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_12 : conflicts_return_wit_12 := by
  unfold conflicts_return_wit_12
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_12_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_13_split_goal_1 : conflicts_return_wit_13_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_13 : conflicts_return_wit_13 := by
  unfold conflicts_return_wit_13
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_13_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_14_split_goal_1 : conflicts_return_wit_14_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_14 : conflicts_return_wit_14 := by
  unfold conflicts_return_wit_14
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_14_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_15_split_goal_1 : conflicts_return_wit_15_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_15 : conflicts_return_wit_15 := by
  unfold conflicts_return_wit_15
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_15_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_conflicts_return_wit_16_split_goal_1 : conflicts_return_wit_16_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH27 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_16 : conflicts_return_wit_16 := by
  unfold conflicts_return_wit_16
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_16_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_conflicts_return_wit_17_split_goal_1 : conflicts_return_wit_17_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_17 : conflicts_return_wit_17 := by
  unfold conflicts_return_wit_17
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_17_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_18_split_goal_1 : conflicts_return_wit_18_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_18 : conflicts_return_wit_18 := by
  unfold conflicts_return_wit_18
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_18_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_19_split_goal_1 : conflicts_return_wit_19_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_19 : conflicts_return_wit_19 := by
  unfold conflicts_return_wit_19
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_19_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_conflicts_return_wit_20_split_goal_1 : conflicts_return_wit_20_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_20 : conflicts_return_wit_20 := by
  unfold conflicts_return_wit_20
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_20_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_21_split_goal_1 : conflicts_return_wit_21_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_21 : conflicts_return_wit_21 := by
  unfold conflicts_return_wit_21
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_21_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_22_split_goal_1 : conflicts_return_wit_22_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_22 : conflicts_return_wit_22 := by
  unfold conflicts_return_wit_22
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_22_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_23_split_goal_1 : conflicts_return_wit_23_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_23 : conflicts_return_wit_23 := by
  unfold conflicts_return_wit_23
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_23_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_24_split_goal_1 : conflicts_return_wit_24_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_24 : conflicts_return_wit_24 := by
  unfold conflicts_return_wit_24
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_24_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_25_split_goal_1 : conflicts_return_wit_25_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_25 : conflicts_return_wit_25 := by
  unfold conflicts_return_wit_25
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_25_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_26_split_goal_1 : conflicts_return_wit_26_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_26 : conflicts_return_wit_26 := by
  unfold conflicts_return_wit_26
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_26_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_27_split_goal_1 : conflicts_return_wit_27_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_27 : conflicts_return_wit_27 := by
  unfold conflicts_return_wit_27
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_27_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_conflicts_return_wit_28_split_goal_1 : conflicts_return_wit_28_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_28 : conflicts_return_wit_28 := by
  unfold conflicts_return_wit_28
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_28_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_29_split_goal_1 : conflicts_return_wit_29_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_29 : conflicts_return_wit_29 := by
  unfold conflicts_return_wit_29
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_29_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_30_split_goal_1 : conflicts_return_wit_30_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_30 : conflicts_return_wit_30 := by
  unfold conflicts_return_wit_30
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_30_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_31_split_goal_1 : conflicts_return_wit_31_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_31 : conflicts_return_wit_31 := by
  unfold conflicts_return_wit_31
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_31_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_32_split_goal_1 : conflicts_return_wit_32_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩)))

theorem proof_of_conflicts_return_wit_32 : conflicts_return_wit_32 := by
  unfold conflicts_return_wit_32
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_32_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_33_split_goal_1 : conflicts_return_wit_33_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_33 : conflicts_return_wit_33 := by
  unfold conflicts_return_wit_33
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_33_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_34_split_goal_1 : conflicts_return_wit_34_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_34 : conflicts_return_wit_34 := by
  unfold conflicts_return_wit_34
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_34_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_35_split_goal_1 : conflicts_return_wit_35_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_35 : conflicts_return_wit_35 := by
  unfold conflicts_return_wit_35
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_35_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_36_split_goal_1 : conflicts_return_wit_36_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_36 : conflicts_return_wit_36 := by
  unfold conflicts_return_wit_36
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_36_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_37_split_goal_1 : conflicts_return_wit_37_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_37 : conflicts_return_wit_37 := by
  unfold conflicts_return_wit_37
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_37_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_38_split_goal_1 : conflicts_return_wit_38_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH24 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_38 : conflicts_return_wit_38 := by
  unfold conflicts_return_wit_38
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_38_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_39_split_goal_1 : conflicts_return_wit_39_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_39 : conflicts_return_wit_39 := by
  unfold conflicts_return_wit_39
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_39_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_40_split_goal_1 : conflicts_return_wit_40_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_40 : conflicts_return_wit_40 := by
  unfold conflicts_return_wit_40
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_40_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_41_split_goal_1 : conflicts_return_wit_41_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_41 : conflicts_return_wit_41 := by
  unfold conflicts_return_wit_41
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_41_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_42_split_goal_1 : conflicts_return_wit_42_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_42 : conflicts_return_wit_42 := by
  unfold conflicts_return_wit_42
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_42_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_43_split_goal_1 : conflicts_return_wit_43_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_43 : conflicts_return_wit_43 := by
  unfold conflicts_return_wit_43
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_43_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_44_split_goal_1 : conflicts_return_wit_44_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH25 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_44 : conflicts_return_wit_44 := by
  unfold conflicts_return_wit_44
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_44_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_conflicts_return_wit_45_split_goal_1 : conflicts_return_wit_45_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_45 : conflicts_return_wit_45 := by
  unfold conflicts_return_wit_45
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_45_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_46_split_goal_1 : conflicts_return_wit_46_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH26 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_46 : conflicts_return_wit_46 := by
  unfold conflicts_return_wit_46
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_46_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_conflicts_return_wit_47_split_goal_1 : conflicts_return_wit_47_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_47 : conflicts_return_wit_47 := by
  unfold conflicts_return_wit_47
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_47_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_conflicts_return_wit_48_split_goal_1 : conflicts_return_wit_48_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hbyte := p081_signed_byte flat (i_pre*m_pre+j_pre-1) PreH27 (by constructor <;> nlinarith)
  rw [hbyte] at PreH1
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_48 : conflicts_return_wit_48 := by
  unfold conflicts_return_wit_48
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_48_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_conflicts_return_wit_49_split_goal_1 : conflicts_return_wit_49_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_49 : conflicts_return_wit_49 := by
  unfold conflicts_return_wit_49
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_49_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_conflicts_return_wit_50_split_goal_1 : conflicts_return_wit_50_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_50 : conflicts_return_wit_50 := by
  unfold conflicts_return_wit_50
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_50_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_conflicts_return_wit_51_split_goal_1 : conflicts_return_wit_51_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_51 : conflicts_return_wit_51 := by
  unfold conflicts_return_wit_51
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_51_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_conflicts_return_wit_52_split_goal_1 : conflicts_return_wit_52_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_52 : conflicts_return_wit_52 := by
  unfold conflicts_return_wit_52
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_52_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_conflicts_return_wit_53_split_goal_1 : conflicts_return_wit_53_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_53 : conflicts_return_wit_53 := by
  unfold conflicts_return_wit_53
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_53_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_conflicts_return_wit_54_split_goal_1 : conflicts_return_wit_54_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_54 : conflicts_return_wit_54 := by
  unfold conflicts_return_wit_54
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_54_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_conflicts_return_wit_55_split_goal_1 : conflicts_return_wit_55_split_goal_1 := by
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simp only [NeighborConflict]
  split_ifs <;> omega

theorem proof_of_conflicts_return_wit_55 : conflicts_return_wit_55 := by
  unfold conflicts_return_wit_55
  right
  intro left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_conflicts_return_wit_55_split_goal_1 left_override_pre c_pre j_pre i_pre m_pre n_pre flat PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_proof_manual
