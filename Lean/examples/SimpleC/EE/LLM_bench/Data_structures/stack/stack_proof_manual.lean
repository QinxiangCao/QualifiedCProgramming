import SimpleC.EE.LLM_bench.Data_structures.stack.stack_goal
import SimpleC.EE.LLM_bench.Data_structures.stack.stack_proof_auto
import ListLib.Base.Positional

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Data_structures.stack.stack_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open stack_goal stack_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩



theorem proof_of_push_return_wit_1_split_goal_spatial : push_return_wit_1_split_goal_spatial := by
  unfold push_return_wit_1_split_goal_spatial
  intro before p n x hxmax hxmin hn hc
  unfold store_stack
  Intros concrete
  have hr : stack_representation before concrete n := by assumption
  Exists (concrete ++ [x])
  sep_apply (naive_C_Rules.IntArray.seg_single p n x)
  sep_apply (naive_C_Rules.IntArray.full_to_seg p n concrete)
  sep_apply (naive_C_Rules.IntArray.seg_merge_to_full p 0 n (n + 1) concrete [x] (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact stack_representation_push__push_state before concrete n x hr hc

theorem proof_of_push_return_wit_1 : push_return_wit_1 := by
  unfold push_return_wit_1
  right
  exact proof_of_push_return_wit_1_split_goal_spatial

theorem proof_of_pop_entail_wit_1 : pop_entail_wit_1 := by
  unfold pop_entail_wit_1
  right
  intro rest top p n hn hc
  unfold store_stack
  Intros concrete
  have hr : stack_representation (sll_cons top rest) concrete n := by assumption
  Exists concrete
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | exact hr | exact hn | exact hc

theorem proof_of_pop_return_wit_1_split_goal_1 : pop_return_wit_1_split_goal_1 := by
  unfold pop_return_wit_1_split_goal_1
  intro rest top p n concrete hn hc hr
  dump_pre_spatial
  exact (stack_representation_pop__pop_state top rest concrete n hn hr).2.2.2

theorem proof_of_pop_return_wit_1_split_goal_spatial : pop_return_wit_1_split_goal_spatial := by
  unfold pop_return_wit_1_split_goal_spatial
  intro rest top p n concrete hn hc hr
  obtain ⟨hconcrete, hlen, hrest, htop⟩ :=
    stack_representation_pop__pop_state top rest concrete n hn hr
  have hpfx : sublist 0 (n - 1) concrete = rest.reverse := by
    rw [hconcrete, ← hlen]
    exact sublist_app_exact1 rest.reverse [top]
  unfold store_stack
  Exists rest.reverse
  sep_apply (naive_C_Rules.IntArray.full_split_to_seg p (n - 1) n concrete (by omega))
  rw [hpfx]
  sep_apply (naive_C_Rules.IntArray.seg_to_full p 0 (n - 1) rest.reverse)
  sep_apply (naive_C_Rules.IntArray.seg_to_undef_seg p (n - 1) n (sublist (n - 1) n concrete))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact hrest

theorem proof_of_pop_return_wit_1 : pop_return_wit_1 := by
  unfold pop_return_wit_1
  right
  intro rest top p n concrete hn hc hr
  split_pure_spatial
  · exact proof_of_pop_return_wit_1_split_goal_spatial rest top p n concrete hn hc hr
  · exact proof_of_pop_return_wit_1_split_goal_1 rest top p n concrete hn hc hr

theorem proof_of_build_entail_wit_1 : build_entail_wit_1 := by
  unfold build_entail_wit_1
  intro input p n hn hc
  prop_apply (naive_C_Rules.IntArray.full_Zlength p n input)
  Intros_p hl
  by_cases hz : n = 0
  · Left
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial <;> first | assumption | rfl
  · Right
    have hp := stack_representation_prefix__build_loop input 1 (by omega) (by omega)
    sep_apply (naive_C_Rules.IntArray.full_split_to_seg p 1 n input (by omega))
    Exists (sll_from_array (sublist 0 1 input))
    unfold store_stack
    Exists (sublist 0 1 input)
    sep_apply (naive_C_Rules.IntArray.seg_to_full p 0 1 (sublist 0 1 input))
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial <;> first | assumption | rfl | omega

theorem proof_of_build_entail_wit_2 : build_entail_wit_2 := by
  unfold build_entail_wit_2
  right
  intro input p n pfx i hi hn hc hi0 hin hl hp
  Exists pfx
  sep_apply (naive_C_Rules.IntArray.seg_split_to_seg p i (i + 1) n
    (sublist i n input) (by omega))
  sep_apply (naive_C_Rules.IntArray.seg_to_undef_seg p i (i + 1)
    (sublist 0 (i + 1 - i) (sublist i n input)))
  have htail : sublist (i + 1 - i) (n - i) (sublist i n input) =
      sublist (i + 1) n input := by
    have h := ListLib.Zsublist_Zsublist (n - i) n (i + 1 - i) i input
      (by omega) (by omega) (by omega)
    simpa only [ListLib.sublist, Int.sub_add_cancel] using h
  rw [htail]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> try assumption
    rw [Znth_sublist 0 i (i - i) n input (by omega) (by omega)]
    congr 1 <;> omega

theorem proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1 := by
  unfold build_entail_wit_3_split_goal_1
  intro input n pfx i x hn hc hi hin hx hl hp
  exact build_stack_prefix_succ__build_loop pfx input i x (by omega) hp hx

theorem proof_of_build_entail_wit_3 : build_entail_wit_3 := by
  unfold build_entail_wit_3
  right
  intro input n pfx i x hn hc hi hin hx hl hp
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_build_entail_wit_3_split_goal_1 input n pfx i x hn hc hi hin hx hl hp



theorem proof_of_build_return_wit_1_split_goal_spatial : build_return_wit_1_split_goal_spatial := by
  unfold build_return_wit_1_split_goal_spatial
  intro input p n i hin hz hi
  prop_apply (naive_C_Rules.IntArray.full_Zlength p n input)
  Intros_p hl
  subst n
  have he : input = [] := by
    change (input.length : Int) = 0 at hl
    cases input with
    | nil => rfl
    | cons x xs => simp at hl; omega
  subst input
  unfold store_stack
  Exists ([] : List Int)
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    simp [stack_representation, sll_from_array, stack_capacity, Zlength]

theorem proof_of_build_return_wit_1 : build_return_wit_1 := by
  unfold build_return_wit_1
  right
  exact proof_of_build_return_wit_1_split_goal_spatial

theorem proof_of_build_return_wit_2_split_goal_spatial : build_return_wit_2_split_goal_spatial := by
  unfold build_return_wit_2_split_goal_spatial
  intro input p n pfx i hin hn hc hi hle hl hp
  obtain ⟨he, hpfx⟩ := build_stack_prefix_complete__build_completion pfx input i n hin hle hl hp
  subst i
  subst pfx
  rw [Zsublist_nil input n n (by omega)]
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.seg_empty p n n)).1)
  Intros_p hempty
  cancel

theorem proof_of_build_return_wit_2 : build_return_wit_2 := by
  unfold build_return_wit_2
  right
  exact proof_of_build_return_wit_2_split_goal_spatial

end SimpleC.EE.LLM_bench.Data_structures.stack.stack_proof_manual
