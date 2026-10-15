import SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_goal
import SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open integer_divide_goal integer_divide_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_divide_entail_wit_1 : divide_entail_wit_1 := by
  unfold divide_entail_wit_1
  right
  intro p n original heq ho hb
  Exists ([] : List Int)
  split_pure_spatial
  · sep_apply (naive_C_Rules.IntArray.undef_full_split_to_undef_seg p 1 original (by omega))
    simp only [Int.add_zero]
    sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (naive_C_Rules.IntArray.seg_empty p 1 1)).2)
    split_pure_spatial
    · cancel
    · dump_pre_spatial
      rfl
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (exact ⟨by simpa using heq, .nil, .Sorted_nil, .nil,
          fun d hd => by omega⟩)
      | (solve | simp [Zlength])
      | omega
      | int_auto

theorem proof_of_divide_entail_wit_3_1 : divide_entail_wit_3_1 := by
  unfold divide_entail_wit_3_1
  intro p original factors cnt i n hm ho hb hn hno hi hio h1 hc hco hl hp
  have hrem : Z.rem n i = 1 := by
    subst n
    exact Int.tmod_eq_of_lt (by decide) (by omega)
  omega

theorem proof_of_divide_entail_wit_3_2 : divide_entail_wit_3_2 := by
  unfold divide_entail_wit_3_2
  intro p original factors cnt i n hm ho hb hn hno hi hio hin hc hco hl hp
  have hroom := factorization_progress_room__progress_transitions original factors n i hi hin hp
  Right
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | (simp only [INT_MIN]; omega) | int_auto

theorem proof_of_divide_entail_wit_4_1 : divide_entail_wit_4_1 := by
  unfold divide_entail_wit_4_1
  intro p original factors cnt i n hroom hib hnb hii hni hm ho hb hn hno hi hio h1 hc hco hl hp
  have hrem : Z.rem n i = 1 := by
    subst n
    exact Int.tmod_eq_of_lt (by decide) (by omega)
  omega

theorem proof_of_divide_entail_wit_4_2 : divide_entail_wit_4_2 := by
  unfold divide_entail_wit_4_2
  intro p original factors cnt i n hroom hib hnb hii hni hm ho hb hn hno hi hio hin hc hco hl hp
  obtain ⟨hprogress, hcases⟩ :=
    factorization_progress_extract__progress_transitions original factors n i hn hi hin hm hp
  have hqpos : 1 ≤ Z.quot n i := Z.quot_le_lower_bound n i 1 (by omega) (by omega)
  have hqupper : Z.quot n i ≤ original :=
    Z.quot_le_upper_bound n i original (by omega) (by
      have hm := Int.mul_le_mul_of_nonneg_right (show 1 ≤ i by omega) (show 0 ≤ original by omega)
      omega)
  have hlen : Zlength (factors ++ [i]) = cnt + 1 := by
    simp only [Zlength_app, Zlength_cons, Zlength_nil, hl]
    omega
  rcases hcases with h1 | hlarge
  · Left
    Exists (factors ++ [i])
    simp only [Int.add_assoc]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial <;> first | assumption | omega | (simp only [INT_MIN]; omega) | int_auto
  · Right
    Exists (factors ++ [i])
    simp only [Int.add_assoc]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial <;> first | assumption | omega | (simp only [INT_MIN]; omega) | int_auto

theorem proof_of_divide_entail_wit_5_split_goal_1 : divide_entail_wit_5_split_goal_1 := by
  unfold divide_entail_wit_5_split_goal_1
  intro original factors cnt i n hcb hib hnb hci hii hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp
  have hne : i ≠ n := by
    intro heq
    subst n
    exact hm Int.tmod_self
  omega

theorem proof_of_divide_entail_wit_5 : divide_entail_wit_5 := by
  unfold divide_entail_wit_5
  right
  intro original factors cnt i n hcb hib hnb hci hii hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_divide_entail_wit_5_split_goal_1 original factors cnt i n
      hcb hib hnb hci hii hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp

theorem proof_of_divide_entail_wit_6_split_goal_1 : divide_entail_wit_6_split_goal_1 := by
  unfold divide_entail_wit_6_split_goal_1
  intro original factors cnt i n hib hcb hnb hci hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp
  exact factorization_progress_advance__progress_transitions original factors n i hi hm hp

theorem proof_of_divide_entail_wit_6 : divide_entail_wit_6 := by
  unfold divide_entail_wit_6
  right
  intro original factors cnt i n hib hcb hnb hci hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_divide_entail_wit_6_split_goal_1 original factors cnt i n
      hib hcb hnb hci hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp

theorem proof_of_divide_return_wit_1 : divide_return_wit_1 := by
  unfold divide_return_wit_1
  right
  intro p original factors cnt i n hin ho hb hn hno hi hib hio hc hco hl hp
  Exists factors
  rw [hl]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact factorization_progress_complete__final_result original factors n i hn (.inr hin) hp
      | omega

theorem proof_of_divide_return_wit_2 : divide_return_wit_2 := by
  unfold divide_return_wit_2
  right
  intro p original factors cnt i n h1 hm ho hb hn hno hi hio h11 hc hco hl hp
  Exists factors
  rw [hl]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact factorization_progress_complete__final_result original factors n i hn (.inl h1) hp
      | omega

end SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_proof_manual
