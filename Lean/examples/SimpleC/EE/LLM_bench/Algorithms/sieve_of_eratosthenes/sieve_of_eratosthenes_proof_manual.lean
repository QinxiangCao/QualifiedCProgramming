import SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_goal
import SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_proof_auto

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open sieve_of_eratosthenes_goal sieve_of_eratosthenes_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- The generated residual branch uses real SL preprocessing and Goal_apply.
-- This library version needs explicit arguments and pure-context extraction.
private noncomputable abbrev intArray := naive_C_Rules.IntArray

-- Historical pure helpers remain proved and audited after VC regrouping.
private noncomputable def legacy_solve_entail_wit_6_split_goal_1 : Prop :=

  forall (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  (SieveMarkState n_pre i (j + i) (replace_Znth ((j - 1)) ((0 : Int)) (current_2)))


private noncomputable def legacy_solve_entail_wit_6 : Prop :=

  (
forall (f_pre : Int) (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((j - 1)) ((0 : Int)) (current_2)))
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((2 * i) <= (j + i)) ” &&
  “ ((j + i) <= (n_pre + i)) ” &&
  “ (SieveMarkState n_pre i (j + i) current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  TT && emp 
|--
  “ (SieveMarkState n_pre i (j + i) (replace_Znth ((j - 1)) ((0 : Int)) (current_2))) ”
  &&  emp
)


private noncomputable def legacy_solve_entail_wit_7_split_goal_1 : Prop :=

  forall (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  (SieveStage n_pre (i + 1) current_2)


private noncomputable def legacy_solve_entail_wit_7 : Prop :=

  (
forall (f_pre : Int) (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current_2)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (SieveStage n_pre (i + 1) current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  TT && emp 
|--
  “ (SieveStage n_pre (i + 1) current_2) ”
  &&  emp
)


private noncomputable def legacy_solve_entail_wit_8_2_split_goal_1 : Prop :=

  forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current_2 (0 : Int)) ≠ 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current_2)) ,
  (SieveStage n_pre (i + 1) current_2)


private noncomputable def legacy_solve_entail_wit_8_2 : Prop :=

  (
forall (f_pre : Int) (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current_2 (0 : Int)) ≠ 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current_2)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current_2)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (SieveStage n_pre (i + 1) current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current_2 (0 : Int)) ≠ 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current_2)) ,
  TT && emp 
|--
  “ (SieveStage n_pre (i + 1) current_2) ”
  &&  emp
)


private noncomputable def legacy_solve_entail_wit_10_split_goal_1 : Prop :=

  forall (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveStage n_pre i current)) ,
  (PrimeIndicatorList n_pre current)


private noncomputable def legacy_solve_entail_wit_10 : Prop :=

  (
forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveStage n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  EX result : (List Int),
  “ (PrimeIndicatorList n_pre result) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) result)
) \/
(
forall (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveStage n_pre i current)) ,
  TT && emp 
|--
  “ (PrimeIndicatorList n_pre current) ”
  &&  emp
)


theorem proof_of_solve_entail_wit_1_split_goal_1 : solve_entail_wit_1_split_goal_1 := by
  unfold solve_entail_wit_1_split_goal_1
  intro n_pre initial PreH1 PreH2 PreH3
  apply SieveInitPrefix_start__sieve_invariants
  all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_1 : solve_entail_wit_1 := by
  unfold solve_entail_wit_1
  right
  intro n_pre initial PreH1 PreH2 PreH3
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | exact proof_of_solve_entail_wit_1_split_goal_1 n_pre initial PreH1 PreH2 PreH3
    | Goal_apply (proof_of_solve_entail_wit_1_split_goal_1 n_pre initial PreH1 PreH2 PreH3)

theorem proof_of_solve_entail_wit_2_split_goal_1 : solve_entail_wit_2_split_goal_1 := by
  unfold solve_entail_wit_2_split_goal_1
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  apply SieveInitPrefix_step__sieve_invariants
  all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_2 : solve_entail_wit_2 := by
  unfold solve_entail_wit_2
  right
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | exact proof_of_solve_entail_wit_2_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    | Goal_apply (proof_of_solve_entail_wit_2_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_solve_entail_wit_3_split_goal_1 : solve_entail_wit_3_split_goal_1 := by
  unfold solve_entail_wit_3_split_goal_1
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  apply SieveInitPrefix_finish__sieve_invariants
  all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_3 : solve_entail_wit_3 := by
  unfold solve_entail_wit_3
  right
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | exact proof_of_solve_entail_wit_3_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    | Goal_apply (proof_of_solve_entail_wit_3_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_solve_entail_wit_5_split_goal_1 : solve_entail_wit_5_split_goal_1 := by
  unfold solve_entail_wit_5_split_goal_1
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  apply SieveMarkState_step__sieve_invariants
  all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_5 : solve_entail_wit_5 := by
  unfold solve_entail_wit_5
  right
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | exact proof_of_solve_entail_wit_5_split_goal_1 n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    | Goal_apply (proof_of_solve_entail_wit_5_split_goal_1 n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_solve_entail_wit_6_split_goal_1 : legacy_solve_entail_wit_6_split_goal_1 := by
  unfold legacy_solve_entail_wit_6_split_goal_1
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  exact SieveMarkState_step__sieve_invariants n_pre i j current_2 PreH1 PreH8

theorem proof_of_solve_entail_wit_6 : legacy_solve_entail_wit_6 := by
  unfold legacy_solve_entail_wit_6
  right
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_6_split_goal_1 n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_solve_entail_wit_7_split_goal_1 : legacy_solve_entail_wit_7_split_goal_1 := by
  unfold legacy_solve_entail_wit_7_split_goal_1
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  exact SieveMarkState_finish__sieve_invariants n_pre i j current_2 PreH1 PreH8

theorem proof_of_solve_entail_wit_7 : legacy_solve_entail_wit_7 := by
  unfold legacy_solve_entail_wit_7
  right
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_7_split_goal_1 n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_solve_entail_wit_8_2_split_goal_1 : legacy_solve_entail_wit_8_2_split_goal_1 := by
  unfold legacy_solve_entail_wit_8_2_split_goal_1
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact SieveStage_skip_composite__sieve_invariants n_pre i current_2 PreH5 PreH2 PreH1 PreH7

theorem proof_of_solve_entail_wit_8_2 : legacy_solve_entail_wit_8_2 := by
  unfold legacy_solve_entail_wit_8_2
  left
  intro f_pre n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  Exists current_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact SieveStage_skip_composite__sieve_invariants n_pre i current_2 PreH5 PreH2 PreH1 PreH7

theorem proof_of_solve_entail_wit_10_split_goal_1 : legacy_solve_entail_wit_10_split_goal_1 := by
  unfold legacy_solve_entail_wit_10_split_goal_1
  intro n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact SieveStage_implies_PrimeIndicatorList n_pre i current PreH1 PreH6

theorem proof_of_solve_entail_wit_10 : legacy_solve_entail_wit_10 := by
  unfold legacy_solve_entail_wit_10
  right
  intro n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_10_split_goal_1 n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
theorem proof_of_solve_entail_wit_4_split_goal_1 : solve_entail_wit_4_split_goal_1 := by
  unfold solve_entail_wit_4_split_goal_1
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  apply SieveStage_mark_start__sieve_invariants
  all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_4 : solve_entail_wit_4 := by
  unfold solve_entail_wit_4
  right
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | exact proof_of_solve_entail_wit_4_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    | Goal_apply (proof_of_solve_entail_wit_4_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)

theorem proof_of_solve_entail_wit_6_1_split_goal_1 : solve_entail_wit_6_1_split_goal_1 := by
  unfold solve_entail_wit_6_1_split_goal_1
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  apply SieveMarkState_finish__sieve_invariants
  all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_6_1 : solve_entail_wit_6_1 := by
  unfold solve_entail_wit_6_1
  right
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | exact proof_of_solve_entail_wit_6_1_split_goal_1 n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    | Goal_apply (proof_of_solve_entail_wit_6_1_split_goal_1 n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_solve_entail_wit_6_2_split_goal_1 : solve_entail_wit_6_2_split_goal_1 := by
  unfold solve_entail_wit_6_2_split_goal_1
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  apply SieveStage_skip_composite__sieve_invariants
  all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_6_2 : solve_entail_wit_6_2 := by
  unfold solve_entail_wit_6_2
  right
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | exact proof_of_solve_entail_wit_6_2_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    | Goal_apply (proof_of_solve_entail_wit_6_2_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)

theorem proof_of_solve_return_wit_1_split_goal_1 : solve_return_wit_1_split_goal_1 := by
  unfold solve_return_wit_1_split_goal_1
  intro n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  apply SieveStage_implies_PrimeIndicatorList
  all_goals first | assumption | omega

theorem proof_of_solve_return_wit_1 : solve_return_wit_1 := by
  unfold solve_return_wit_1
  right
  intro n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | exact proof_of_solve_return_wit_1_split_goal_1 n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    | Goal_apply (proof_of_solve_return_wit_1_split_goal_1 n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)


end SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_proof_manual
