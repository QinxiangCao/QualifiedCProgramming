import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_proof_manual

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P004_2008B_square_or_not_goal P004_2008B_square_or_not_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem equal_square_sides {q r : Int} (hq : 1 ≤ q) (hr : 1 ≤ r)
    (heq : q * q = r * r) : q = r := by
  nlinarith [sq_nonneg (q - r)]

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre bits PreH1 PreH2 PreH3 PreH4 PreH5
  exact PreH4

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro n_pre bits r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 x y h
  omega

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  intro n_pre bits r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact PreH6

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  intro n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 y h
  omega

theorem proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2 := by
  intro n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH12

theorem proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3 := by
  intro n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH5

theorem proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  nlinarith

theorem proof_of_solver_entail_wit_5_3_split_goal_1 : solver_entail_wit_5_3_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  nlinarith

theorem proof_of_solver_entail_wit_5_4_split_goal_1 : solver_entail_wit_5_4_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  nlinarith

theorem proof_of_solver_entail_wit_5_5_split_goal_1 : solver_entail_wit_5_5_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  nlinarith

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 x y h
  by_cases hx : x < i
  · exact PreH14 x y ⟨⟨⟨h.1.1.1, hx⟩, h.1.2⟩, h.2⟩
  · have heq : x = i := by omega
    subst x
    exact PreH15 y ⟨h.1.2, by omega⟩

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH5

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  left
  refine ⟨rfl, r, PreH7, PreH7, by omega, ?_⟩
  intro x y hx hy
  have hc := PreH12 x y ⟨⟨⟨hx.1, by omega⟩, hy.1⟩, hy.2⟩
  simpa only [OnBorder, not_or, or_assoc, and_assoc] using hc

theorem proof_of_solver_return_wit_7_split_goal_1 : solver_return_wit_7_split_goal_1 := by
  intro n_pre bits r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  right
  refine ⟨rfl, ?_⟩
  rintro ⟨q, hq, _, hlen, _⟩
  by_cases hqr : q ≤ r
  · have := mul_self_le_mul_self (by omega : (0 : Int) ≤ q) hqr
    omega
  · have := mul_self_le_mul_self (by omega : (0 : Int) ≤ r + 1) (by omega : r + 1 ≤ q)
    nlinarith

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  right
  refine ⟨rfl, ?_⟩
  rintro ⟨q, hq, _, hlen, hcells⟩
  have hqr : q = r := equal_square_sides hq PreH15 (by omega)
  subst q
  have hc := hcells i j ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  rcases hc with ⟨hb, hv⟩ | ⟨hb, hv⟩
  · exact PreH1 hv
  · apply hb
    unfold OnBorder
    tauto

theorem proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  right
  refine ⟨rfl, ?_⟩
  rintro ⟨q, hq, _, hlen, hcells⟩
  have hqr : q = r := equal_square_sides hq PreH13 (by omega)
  subst q
  have hc := hcells i j ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  rcases hc with ⟨hb, hv⟩ | ⟨hb, hv⟩
  · exact PreH1 hv
  · apply hb
    unfold OnBorder
    tauto

theorem proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  right
  refine ⟨rfl, ?_⟩
  rintro ⟨q, hq, _, hlen, hcells⟩
  have hqr : q = r := equal_square_sides hq PreH14 (by omega)
  subst q
  have hc := hcells i j ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  rcases hc with ⟨hb, hv⟩ | ⟨hb, hv⟩
  · exact PreH1 hv
  · apply hb
    unfold OnBorder
    tauto

theorem proof_of_solver_return_wit_5_split_goal_1 : solver_return_wit_5_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  right
  refine ⟨rfl, ?_⟩
  rintro ⟨q, hq, _, hlen, hcells⟩
  have hqr : q = r := equal_square_sides hq PreH16 (by omega)
  subst q
  have hc := hcells i j ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  rcases hc with ⟨hb, hv⟩ | ⟨hb, hv⟩
  · exact PreH1 hv
  · apply hb
    unfold OnBorder
    tauto

theorem proof_of_solver_return_wit_6_split_goal_1 : solver_return_wit_6_split_goal_1 := by
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  right
  refine ⟨rfl, ?_⟩
  rintro ⟨q, hq, _, hlen, hcells⟩
  have hqr : q = r := equal_square_sides hq PreH16 (by omega)
  subst q
  have hc := hcells i j ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  rcases hc with ⟨hb, hv⟩ | ⟨hb, hv⟩
  · simp only [OnBorder] at hb
    tauto
  · exact PreH1 hv

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n_pre bits PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_1_split_goal_1 n_pre bits PreH1 PreH2 PreH3 PreH4 PreH5

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro n_pre bits r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_solver_entail_wit_3_split_goal_1 n_pre bits r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    · exact proof_of_solver_entail_wit_3_split_goal_2 n_pre bits r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_solver_entail_wit_4_split_goal_3 n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    · exact proof_of_solver_entail_wit_4_split_goal_1 n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    · exact proof_of_solver_entail_wit_4_split_goal_2 n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1 := by
  unfold solver_entail_wit_5_1
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_5_1_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3 := by
  unfold solver_entail_wit_5_3
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_5_3_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4 := by
  unfold solver_entail_wit_5_4
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_5_4_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29

theorem proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5 := by
  unfold solver_entail_wit_5_5
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_5_5_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_solver_entail_wit_6_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    · exact proof_of_solver_entail_wit_6_split_goal_2 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_1_split_goal_1 n_pre bits i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_2_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_3_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_return_wit_4 : solver_return_wit_4 := by
  unfold solver_return_wit_4
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_4_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_solver_return_wit_5 : solver_return_wit_5 := by
  unfold solver_return_wit_5
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_5_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_return_wit_6 : solver_return_wit_6 := by
  unfold solver_return_wit_6
  right
  intro n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_6_split_goal_1 n_pre bits j i r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_return_wit_7 : solver_return_wit_7 := by
  unfold solver_return_wit_7
  right
  intro n_pre bits r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_7_split_goal_1 n_pre bits r PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_proof_manual
