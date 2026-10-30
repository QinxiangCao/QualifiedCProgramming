import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_goal
import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_proof_auto

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open container_with_most_water_linear_goal container_with_most_water_linear_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Previously proved auxiliary statements retained for proof audits.
private theorem annotation_Forall_nth (P : Int → Prop) (l : List Int) (i d : Int)
    (h : Forall P l) (hd : P d) : P (Znth i l d) := by
  by_cases hi : i.toNat < l.length
  · have hp := h.mem (List.getElem_mem (l := l) hi)
    simpa only [Znth, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some] using hp
  · simpa only [Znth, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : l.length ≤ i.toNat), Option.getD_none] using hd

private theorem annotation_Forall_nth_in (P : Int → Prop) (l : List Int) (i d : Int)
    (h : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  have hin : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have hp := h.mem (List.getElem_mem (l := l) hin)
  simpa only [Znth, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hin, Option.getD_some] using hp


private theorem rectangle_bounds (l : List Int) (n left right : Int)
    (hn : n ≤ 100000) (hle : 0 ≤ left) (hlr : left < right) (hrn : right < n)
    (hlow : Forall (fun x : Int => 0 ≤ x) l)
    (hhigh : Forall (fun x : Int => x ≤ 10000) l) (idx : Int) :
    0 ≤ (right-left)*Znth idx l 0 ∧ (right-left)*Znth idx l 0 ≤ 999990000 := by
  have low := annotation_Forall_nth _ l idx 0 hlow (by omega)
  have high := annotation_Forall_nth _ l idx 0 hhigh (by omega)
  have width : right-left ≤ 99999 := by omega
  have a := Int.mul_le_mul_of_nonneg_right width low
  have b := Int.mul_le_mul_of_nonneg_left high (by decide : (0 : Int) ≤ 99999)
  exact ⟨Int.mul_nonneg (by omega) low, by omega⟩


theorem aux_maxAreaLinear_entail_wit_1_split_goal_1 : (forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre ≠ (0 : Int))) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre ≠ (0 : Int))) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < heightSize_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) := by

  intro heightSize_pre height_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact PreH7

theorem proof_of_maxAreaLinear_entail_wit_1_split_goal_1 : maxAreaLinear_entail_wit_1_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_1_split_goal_1
  intro l height_pre heightSize_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    refine ⟨Or.inl rfl, ?_⟩
    intro i j hp
    exact Or.inr ⟨i, j, ⟨hp, hp.1, by have := hp.2.2; omega⟩, Int.le_refl _⟩

  -- Pure residual VCs use the generated right branch. Explicitly discard its empty
  -- spatial context before Goal_apply, then supply the Coq split lemma arguments.

theorem proof_of_maxAreaLinear_entail_wit_1 : maxAreaLinear_entail_wit_1 := by
  unfold maxAreaLinear_entail_wit_1
  right
  intro l height_pre heightSize_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have PreH1 : (heightSize_pre >= 2) := NewPreH1
  have PreH2 : (height_pre ≠ (0 : Int)) := NewPreH2
  have PreH3 : (2 <= heightSize_pre) := NewPreH3
  have PreH4 : (heightSize_pre <= 100000) := NewPreH4
  have PreH5 : (height_pre ≠ (0 : Int)) := NewPreH2
  have PreH6 : ((Zlength (l)) = heightSize_pre) := NewPreH6
  have PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000))) := by
    intro k_2 hindex
    have value_PreH7 := annotation_Forall_nth _ l k_2 0 NewPreH7 (by omega)
    have value_PreH8 := annotation_Forall_nth _ l k_2 0 NewPreH8 (by omega)
    omega
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | Goal_apply (aux_maxAreaLinear_entail_wit_1_split_goal_1 heightSize_pre height_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_1_split_goal_1 l height_pre heightSize_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8)

theorem proof_of_maxAreaLinear_entail_wit_2_1_split_goal_1 : maxAreaLinear_entail_wit_2_1_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_2_1_split_goal_1
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (((right - left) * (Znth left l (0 : Int))) > maximumArea) := NewPreH1
    have PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int))) := NewPreH2
    have PreH3 : (left < right) := NewPreH3
    have PreH7 : ((0 : Int) <= left) := NewPreH7
    have PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea) := NewPreH12
    have heq : LinearContainerArea l left right = (right-left) * Znth left l 0 := by
      simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_left (Int.le_of_lt PreH2)]
    rw [← heq]
    apply linear_container_invariant_update_best__best_update l left right maximumArea PreH12
    · exact ⟨PreH7, PreH3, by omega⟩
    · rw [heq]; exact PreH1

theorem proof_of_maxAreaLinear_entail_wit_2_1_split_goal_3 : maxAreaLinear_entail_wit_2_1_split_goal_3 := by
  unfold maxAreaLinear_entail_wit_2_1_split_goal_3
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int))) := NewPreH2
    simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_left (Int.le_of_lt PreH2)]

theorem proof_of_maxAreaLinear_entail_wit_2_1 : maxAreaLinear_entail_wit_2_1 := by
  unfold maxAreaLinear_entail_wit_2_1
  right
  intro l n best right left hbest hcmp hlr hn0 hn hlen hl0 hle hrn hb0 hb hinv hlow hhigh
  have low := annotation_Forall_nth _ l left 0 hlow (by omega)
  have high := annotation_Forall_nth _ l left 0 hhigh (by omega)
  have bounds := rectangle_bounds l n left right hn hl0 hlr hrn hlow hhigh left
  have height : Znth left l 0 = LinearContainerHeight l left right := by
    simp only [LinearContainerHeight, Int.min_eq_left (Int.le_of_lt hcmp)]
  have area : (right-left)*Znth left l 0 = LinearContainerArea l left right := by
    simp only [LinearContainerArea, ← height]
  have next := linear_container_invariant_update_best__best_update l left right best hinv
    (show LinearContainerPair l left right from ⟨hl0,hlr,by omega⟩) (by omega : best < LinearContainerArea l left right)
  rw [← area] at next
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_maxAreaLinear_entail_wit_2_2_split_goal_1 : maxAreaLinear_entail_wit_2_2_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_2_2_split_goal_1
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (((right - left) * (Znth right l (0 : Int))) > maximumArea) := NewPreH1
    have PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int))) := NewPreH2
    have PreH3 : (left < right) := NewPreH3
    have PreH7 : ((0 : Int) <= left) := NewPreH7
    have PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea) := NewPreH12
    have heq : LinearContainerArea l left right = (right-left) * Znth right l 0 := by
      simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_right PreH2]
    rw [← heq]
    apply linear_container_invariant_update_best__best_update l left right maximumArea PreH12
    · exact ⟨PreH7, PreH3, by omega⟩
    · rw [heq]; exact PreH1

theorem proof_of_maxAreaLinear_entail_wit_2_2_split_goal_3 : maxAreaLinear_entail_wit_2_2_split_goal_3 := by
  unfold maxAreaLinear_entail_wit_2_2_split_goal_3
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int))) := NewPreH2
    simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_right PreH2]

theorem proof_of_maxAreaLinear_entail_wit_2_2 : maxAreaLinear_entail_wit_2_2 := by
  unfold maxAreaLinear_entail_wit_2_2
  right
  intro l n best right left hbest hcmp hlr hn0 hn hlen hl0 hle hrn hb0 hb hinv hlow hhigh
  have low := annotation_Forall_nth _ l right 0 hlow (by omega)
  have high := annotation_Forall_nth _ l right 0 hhigh (by omega)
  have bounds := rectangle_bounds l n left right hn hl0 hlr hrn hlow hhigh right
  have height : Znth right l 0 = LinearContainerHeight l left right := by
    simp only [LinearContainerHeight, Int.min_eq_right hcmp]
  have area : (right-left)*Znth right l 0 = LinearContainerArea l left right := by
    simp only [LinearContainerArea, ← height]
  have next := linear_container_invariant_update_best__best_update l left right best hinv
    (show LinearContainerPair l left right from ⟨hl0,hlr,by omega⟩) (by omega : best < LinearContainerArea l left right)
  rw [← area] at next
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_maxAreaLinear_entail_wit_2_3_split_goal_1 : maxAreaLinear_entail_wit_2_3_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_2_3_split_goal_1
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000))) := by
      intro k_2 hindex
      have value_PreH13 := annotation_Forall_nth _ l k_2 0 NewPreH13 (by omega)
      have value_PreH14 := annotation_Forall_nth _ l k_2 0 NewPreH14 (by omega)
      omega
    have hn := (PreH13 left (by omega)).1
    exact Int.mul_nonneg (by omega) hn

theorem proof_of_maxAreaLinear_entail_wit_2_3_split_goal_2 : maxAreaLinear_entail_wit_2_3_split_goal_2 := by
  unfold maxAreaLinear_entail_wit_2_3_split_goal_2
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int))) := NewPreH2
    simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_left (Int.le_of_lt PreH2)]

theorem proof_of_maxAreaLinear_entail_wit_2_3 : maxAreaLinear_entail_wit_2_3 := by
  unfold maxAreaLinear_entail_wit_2_3
  right
  intro l n best right left hbest hcmp hlr hn0 hn hlen hl0 hle hrn hb0 hb hinv hlow hhigh
  have low := annotation_Forall_nth _ l left 0 hlow (by omega)
  have high := annotation_Forall_nth _ l left 0 hhigh (by omega)
  have bounds := rectangle_bounds l n left right hn hl0 hlr hrn hlow hhigh left
  have height : Znth left l 0 = LinearContainerHeight l left right := by
    simp only [LinearContainerHeight, Int.min_eq_left (Int.le_of_lt hcmp)]
  have area : (right-left)*Znth left l 0 = LinearContainerArea l left right := by
    simp only [LinearContainerArea, ← height]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_maxAreaLinear_entail_wit_2_4_split_goal_1 : maxAreaLinear_entail_wit_2_4_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_2_4_split_goal_1
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000))) := by
      intro k_2 hindex
      have value_PreH13 := annotation_Forall_nth _ l k_2 0 NewPreH13 (by omega)
      have value_PreH14 := annotation_Forall_nth _ l k_2 0 NewPreH14 (by omega)
      omega
    have hn := (PreH13 right (by omega)).1
    exact Int.mul_nonneg (by omega) hn

theorem proof_of_maxAreaLinear_entail_wit_2_4_split_goal_2 : maxAreaLinear_entail_wit_2_4_split_goal_2 := by
  unfold maxAreaLinear_entail_wit_2_4_split_goal_2
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int))) := NewPreH2
    simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_right PreH2]

theorem proof_of_maxAreaLinear_entail_wit_2_4 : maxAreaLinear_entail_wit_2_4 := by
  unfold maxAreaLinear_entail_wit_2_4
  right
  intro l n best right left hbest hcmp hlr hn0 hn hlen hl0 hle hrn hb0 hb hinv hlow hhigh
  have low := annotation_Forall_nth _ l right 0 hlow (by omega)
  have high := annotation_Forall_nth _ l right 0 hhigh (by omega)
  have bounds := rectangle_bounds l n left right hn hl0 hlr hrn hlow hhigh right
  have height : Znth right l 0 = LinearContainerHeight l left right := by
    simp only [LinearContainerHeight, Int.min_eq_right hcmp]
  have area : (right-left)*Znth right l 0 = LinearContainerArea l left right := by
    simp only [LinearContainerArea, ← height]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem aux_maxAreaLinear_entail_wit_3_1_split_goal_1 : (forall (heightSize_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < heightSize_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) := by

  intro heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact PreH20

theorem proof_of_maxAreaLinear_entail_wit_3_1_split_goal_1 : maxAreaLinear_entail_wit_3_1_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_3_1_split_goal_1
  intro l heightSize_pre left right width shorterHeight area maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int))) := NewPreH1
    have PreH5 : ((0 : Int) <= left) := NewPreH5
    have PreH6 : (left < right) := NewPreH6
    have PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea) := NewPreH19
    have PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000))) := by
      intro k_2 hindex
      have value_PreH20 := annotation_Forall_nth _ l k_2 0 NewPreH20 (by omega)
      have value_PreH21 := annotation_Forall_nth _ l k_2 0 NewPreH21 (by omega)
      omega
    apply linear_container_invariant_advance_left__pointer_transitions l left right maximumArea
    · intro k hk
      exact (PreH20 k (by omega)).1
    · exact ⟨PreH5, PreH6, by omega⟩
    · exact PreH1
    · omega
    · exact PreH19

theorem proof_of_maxAreaLinear_entail_wit_3_1 : maxAreaLinear_entail_wit_3_1 := by
  unfold maxAreaLinear_entail_wit_3_1
  right
  intro l heightSize_pre left right width shorterHeight area maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21
  have PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int))) := NewPreH1
  have PreH2 : (2 <= heightSize_pre) := NewPreH2
  have PreH3 : (heightSize_pre <= 100000) := NewPreH3
  have PreH4 : ((Zlength (l)) = heightSize_pre) := NewPreH4
  have PreH5 : ((0 : Int) <= left) := NewPreH5
  have PreH6 : (left < right) := NewPreH6
  have PreH7 : (right < heightSize_pre) := NewPreH7
  have PreH8 : (width = (right - left)) := NewPreH8
  have PreH9 : (1 <= width) := NewPreH9
  have PreH10 : (width <= 99999) := NewPreH10
  have PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right))) := NewPreH11
  have PreH12 : ((0 : Int) <= shorterHeight) := NewPreH12
  have PreH13 : (shorterHeight <= 10000) := NewPreH13
  have PreH14 : (area = (LinearContainerArea (l) (left) (right))) := NewPreH14
  have PreH15 : ((0 : Int) <= area) := NewPreH15
  have PreH16 : (area <= maximumArea) := NewPreH16
  have PreH17 : ((0 : Int) <= maximumArea) := NewPreH17
  have PreH18 : (maximumArea <= 999990000) := NewPreH18
  have PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea) := NewPreH19
  have PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000))) := by
    intro k_2 hindex
    have value_PreH20 := annotation_Forall_nth _ l k_2 0 NewPreH20 (by omega)
    have value_PreH21 := annotation_Forall_nth _ l k_2 0 NewPreH21 (by omega)
    omega
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | Goal_apply (aux_maxAreaLinear_entail_wit_3_1_split_goal_1 heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_3_1_split_goal_1 l heightSize_pre left right width shorterHeight area maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21)

theorem aux_maxAreaLinear_entail_wit_3_2_split_goal_1 : (forall (heightSize_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < heightSize_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) := by

  intro heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact PreH20

theorem proof_of_maxAreaLinear_entail_wit_3_2_split_goal_1 : maxAreaLinear_entail_wit_3_2_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_3_2_split_goal_1
  intro l heightSize_pre left right width shorterHeight area maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int))) := NewPreH1
    have PreH5 : ((0 : Int) <= left) := NewPreH5
    have PreH6 : (left < right) := NewPreH6
    have PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea) := NewPreH19
    have PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000))) := by
      intro k_2 hindex
      have value_PreH20 := annotation_Forall_nth _ l k_2 0 NewPreH20 (by omega)
      have value_PreH21 := annotation_Forall_nth _ l k_2 0 NewPreH21 (by omega)
      omega
    apply linear_container_invariant_retreat_right__pointer_transitions l left right maximumArea
    · intro k hk
      exact (PreH20 k (by omega)).1
    · exact ⟨PreH5, PreH6, by omega⟩
    · exact PreH1
    · omega
    · exact PreH19

theorem proof_of_maxAreaLinear_entail_wit_3_2 : maxAreaLinear_entail_wit_3_2 := by
  unfold maxAreaLinear_entail_wit_3_2
  right
  intro l heightSize_pre left right width shorterHeight area maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21
  have PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int))) := NewPreH1
  have PreH2 : (2 <= heightSize_pre) := NewPreH2
  have PreH3 : (heightSize_pre <= 100000) := NewPreH3
  have PreH4 : ((Zlength (l)) = heightSize_pre) := NewPreH4
  have PreH5 : ((0 : Int) <= left) := NewPreH5
  have PreH6 : (left < right) := NewPreH6
  have PreH7 : (right < heightSize_pre) := NewPreH7
  have PreH8 : (width = (right - left)) := NewPreH8
  have PreH9 : (1 <= width) := NewPreH9
  have PreH10 : (width <= 99999) := NewPreH10
  have PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right))) := NewPreH11
  have PreH12 : ((0 : Int) <= shorterHeight) := NewPreH12
  have PreH13 : (shorterHeight <= 10000) := NewPreH13
  have PreH14 : (area = (LinearContainerArea (l) (left) (right))) := NewPreH14
  have PreH15 : ((0 : Int) <= area) := NewPreH15
  have PreH16 : (area <= maximumArea) := NewPreH16
  have PreH17 : ((0 : Int) <= maximumArea) := NewPreH17
  have PreH18 : (maximumArea <= 999990000) := NewPreH18
  have PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea) := NewPreH19
  have PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < heightSize_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000))) := by
    intro k_2 hindex
    have value_PreH20 := annotation_Forall_nth _ l k_2 0 NewPreH20 (by omega)
    have value_PreH21 := annotation_Forall_nth _ l k_2 0 NewPreH21 (by omega)
    omega
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | Goal_apply (aux_maxAreaLinear_entail_wit_3_2_split_goal_1 heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_3_2_split_goal_1 l heightSize_pre left right width shorterHeight area maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21)

theorem proof_of_maxAreaLinear_return_wit_1_split_goal_1 : maxAreaLinear_return_wit_1_split_goal_1 := by
  unfold maxAreaLinear_return_wit_1_split_goal_1
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea) := NewPreH10
    have PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < heightSize_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) := by
      intro k hindex
      have value_PreH11 := annotation_Forall_nth _ l k 0 NewPreH11 (by omega)
      have value_PreH12 := annotation_Forall_nth _ l k 0 NewPreH12 (by omega)
      omega
    apply linear_container_closed_invariant_maximum__final_result l left right maximumArea
    · omega
    · omega
    · intro k hk
      exact (PreH11 k (by omega)).1
    · exact PreH10

theorem proof_of_maxAreaLinear_return_wit_1 : maxAreaLinear_return_wit_1 := by
  unfold maxAreaLinear_return_wit_1
  right
  intro l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
  have PreH1 : (left >= right) := NewPreH1
  have PreH2 : (2 <= heightSize_pre) := NewPreH2
  have PreH3 : (heightSize_pre <= 100000) := NewPreH3
  have PreH4 : ((Zlength (l)) = heightSize_pre) := NewPreH4
  have PreH5 : ((0 : Int) <= left) := NewPreH5
  have PreH6 : (left <= right) := NewPreH6
  have PreH7 : (right < heightSize_pre) := NewPreH7
  have PreH8 : ((0 : Int) <= maximumArea) := NewPreH8
  have PreH9 : (maximumArea <= 999990000) := NewPreH9
  have PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea) := NewPreH10
  have PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < heightSize_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) := by
    intro k hindex
    have value_PreH11 := annotation_Forall_nth _ l k 0 NewPreH11 (by omega)
    have value_PreH12 := annotation_Forall_nth _ l k 0 NewPreH12 (by omega)
    omega
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | Goal_apply (proof_of_maxAreaLinear_return_wit_1_split_goal_1 l heightSize_pre maximumArea right left NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12)

theorem proof_of_maxAreaLinear_safety_wit_10 : maxAreaLinear_safety_wit_10 := by
  unfold maxAreaLinear_safety_wit_10
  right
  intro l addr n best right left hcmp hlr hn0 hn hlen hl0 hle hrn hb0 hb hinv hlow hhigh
  have bounds := rectangle_bounds l n left right hn hl0 hlr hrn hlow hhigh left
  split_pures <;> dump_pre_spatial <;> simp only [INT_MIN, INT_MAX] <;> omega


theorem proof_of_maxAreaLinear_safety_wit_11 : maxAreaLinear_safety_wit_11 := by
  unfold maxAreaLinear_safety_wit_11
  right
  intro l addr n best right left hcmp hlr hn0 hn hlen hl0 hle hrn hb0 hb hinv hlow hhigh
  have bounds := rectangle_bounds l n left right hn hl0 hlr hrn hlow hhigh right
  split_pures <;> dump_pre_spatial <;> simp only [INT_MIN, INT_MAX] <;> omega


end SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_proof_manual
