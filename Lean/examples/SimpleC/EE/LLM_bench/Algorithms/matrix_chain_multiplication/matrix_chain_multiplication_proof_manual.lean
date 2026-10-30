import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_goal
import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_proof_auto

import ListLib.General.Length

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open matrix_chain_multiplication_goal matrix_chain_multiplication_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private theorem candidate_upper (dims table : List Int) (n len l k : Int)
    (hn : n ≤ 8) (hlen : 2 ≤ len) (hl : 0 ≤ l) (hfit : l+len ≤ n)
    (hk : l ≤ k ∧ k < l+len-1)
    (hd : MatrixChainDimensionsBounded dims n)
    (hprogress : MatrixChainLengthsDone dims table n len) :
    Znth (l*n+k) table 0 + Znth ((k+1)*n+(l+len-1)) table 0 +
      Znth l dims 0*Znth (k+1) dims 0*Znth ((l+len-1)+1) dims 0 ≤ 7000000 := by
  have hml := hprogress.2 (k-l+1) l k ⟨by omega, by omega⟩ (by omega) hl (by omega)
  have hmr := hprogress.2 (l+len-1-k) (k+1) (l+len-1) ⟨by omega, by omega⟩
    (by omega) (by omega) (by omega)
  have hb1 := matrix_chain_interval_minimum_upper_bound__candidate_progress
    dims n l k _ hd hl hk.1 (by omega) hml
  have hb2 := matrix_chain_interval_minimum_upper_bound__candidate_progress
    dims n (k+1) (l+len-1) _ hd (by omega) (by omega) (by omega) hmr
  have hb3 := matrix_chain_dimensions_product_bound _ _ _
    (hd.2 l ⟨hl, by omega⟩) (hd.2 (k+1) ⟨by omega, by omega⟩)
    (hd.2 ((l+len-1)+1) ⟨by omega, by omega⟩)
  omega

private theorem matrix_index_injective (n i j k l : Int) (hn : 1 ≤ n)
    (hj : 0 ≤ j ∧ j < n) (hl : 0 ≤ l ∧ l < n)
    (he : i*n+j = k*n+l) : i = k ∧ j = l := by
  have hi : i = k := by
    rcases lt_trichotomy i k with h | h | h
    · have hp : (i+1)*n ≤ k*n := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    · exact h
    · have hp : (k+1)*n ≤ i*n := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
  exact ⟨hi, by rw [hi] at he; omega⟩

private theorem indexed_Forall {A : Type} (P : A → Prop) (l : List A) (d : A) :
    Forall P l ↔ ∀ i, 0 ≤ i ∧ i < Zlength l → P (Znth i l d) := by
  rw [Forall.iff_forall_mem]
  constructor
  · intro h i hi
    have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
    have hm := h l[i.toNat] (List.mem_iff_getElem.mpr ⟨i.toNat, hn, rfl⟩)
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hm
  · intro h v hv
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hv
    have hi : 0 ≤ (n : Int) ∧ (n : Int) < Zlength l := by change 0 ≤ (n : Int) ∧ (n : Int) < (l.length : Int); omega
    have hh := h n hi
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hh

private theorem forall_replace {A : Type} (P : A → Prop) (d x : A) (l : List A)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) (hp : Forall P l) (hx : P x) :
    Forall P (replace_Znth i x l) := by
  apply (indexed_Forall P _ d).mpr
  intro j hj
  rw [Zlength_replace_Znth] at hj
  by_cases he : i = j
  · subst j; rw [Znth_replace_Znth_Same d l i x hi]; exact hx
  · rw [Znth_replace_Znth_Diff d l i j x hi hj he]
    exact (indexed_Forall P l d).mp hp j hj


attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

theorem proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 : matrixChainMinCost_entail_wit_2_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_2_split_goal_1
  intro dimensions_l matrix_count_pre cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  rw [Forall.iff_forall_mem] at PreH11 ⊢
  intro x hx
  rcases List.mem_append.mp hx with hleft | hright
  · exact PreH11 x hleft
  · have he : x = 0 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hright
    exact he.symm

theorem proof_of_matrixChainMinCost_entail_wit_2_split_goal_2 : matrixChainMinCost_entail_wit_2_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_2_split_goal_2
  intro dimensions_l matrix_count_pre cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simp only [Zlength_app, Zlength_cons, Zlength_nil]
  omega

theorem proof_of_matrixChainMinCost_entail_wit_4_split_goal_1 : matrixChainMinCost_entail_wit_4_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_4_split_goal_1
  intro dimensions_l matrix_count_pre chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have PreH9_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH9
  have PreH10_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH10
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH12
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH9_indexed idx (by omega), PreH10_indexed idx (by omega)⟩
  have hlengths : MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length := ⟨by omega, PreH14⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH11_indexed idx hidx, PreH12_indexed idx hidx⟩
  have hlegacy :   (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length (0 : Int)) := by
    exact ⟨hlengths, fun l r hl hr hfit => False.elim (by omega)⟩
  exact ⟨hlegacy.1.2, hlegacy.2⟩

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 : matrixChainMinCost_entail_wit_5_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_1
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  exact (hd.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_2 : matrixChainMinCost_entail_wit_5_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_2
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  exact (hd.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_3 : matrixChainMinCost_entail_wit_5_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_3
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  exact (hd.2 (left+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_4 : matrixChainMinCost_entail_wit_5_split_goal_4 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_4
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  exact (hd.2 (left+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_5 : matrixChainMinCost_entail_wit_5_split_goal_5 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_5
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  exact (hd.2 left ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_6 : matrixChainMinCost_entail_wit_5_split_goal_6 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_6
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  exact (hd.2 left ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_7 : matrixChainMinCost_entail_wit_5_split_goal_7 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_7
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre (left+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (hv ((left+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH5]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_8 : matrixChainMinCost_entail_wit_5_split_goal_8 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_8
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre (left+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (hv ((left+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH5]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_9 : matrixChainMinCost_entail_wit_5_split_goal_9 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_9
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre left left (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (hv (left*matrix_count_pre+left) (by rw [PreH5]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_10 : matrixChainMinCost_entail_wit_5_split_goal_10 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_10
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre left left (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (hv (left*matrix_count_pre+left) (by rw [PreH5]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_11 : matrixChainMinCost_entail_wit_5_split_goal_11 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_11
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre (left+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_12 : matrixChainMinCost_entail_wit_5_split_goal_12 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_12
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre left left (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 : matrixChainMinCost_entail_wit_6_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_1
  intro dimensions_l matrix_count_pre cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have PreH33_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH33
  have PreH34_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH34
  have PreH35_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l (0 : Int)).mp PreH35
  have PreH36_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l (0 : Int)).mp PreH36
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH33_indexed idx (by omega), PreH34_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left := ⟨⟨by omega, PreH38.1⟩, PreH38.2⟩
  have hv : MatrixChainTableValuesBounded cost_l := by
    intro idx hidx
    exact ⟨PreH35_indexed idx hidx, PreH36_indexed idx hidx⟩
  have hlegacy :   (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (left + 1) (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))))) := by
    exact matrix_chain_split_progress_initial__candidate_progress _ _ _ _ _ _ hleft
  exact ⟨⟨hlegacy.1.1.2, hlegacy.1.2⟩, hlegacy.2⟩

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 : matrixChainMinCost_entail_wit_6_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_2
  intro dimensions_l matrix_count_pre cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have PreH33_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH33
  have PreH34_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH34
  have PreH35_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l (0 : Int)).mp PreH35
  have PreH36_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l (0 : Int)).mp PreH36
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH33_indexed idx (by omega), PreH34_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left := ⟨⟨by omega, PreH38.1⟩, PreH38.2⟩
  have hv : MatrixChainTableValuesBounded cost_l := by
    intro idx hidx
    exact ⟨PreH35_indexed idx hidx, PreH36_indexed idx hidx⟩
  exact candidate_upper dimensions_l cost_l matrix_count_pre chain_length left left
    (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ hd hleft.1

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 : matrixChainMinCost_entail_wit_7_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_1
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  exact (hd.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 : matrixChainMinCost_entail_wit_7_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_2
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  exact (hd.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_3 : matrixChainMinCost_entail_wit_7_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_3
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  exact (hd.2 (split+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_4 : matrixChainMinCost_entail_wit_7_split_goal_4 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_4
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  exact (hd.2 (split+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_5 : matrixChainMinCost_entail_wit_7_split_goal_5 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_5
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  exact (hd.2 left ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_6 : matrixChainMinCost_entail_wit_7_split_goal_6 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_6
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  exact (hd.2 left ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_7 : matrixChainMinCost_entail_wit_7_split_goal_7 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_7
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre (split+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (hv ((split+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH16]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_8 : matrixChainMinCost_entail_wit_7_split_goal_8 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_8
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre (split+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (hv ((split+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH16]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_9 : matrixChainMinCost_entail_wit_7_split_goal_9 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_9
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre left split (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (hv (left*matrix_count_pre+split) (by rw [PreH16]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_10 : matrixChainMinCost_entail_wit_7_split_goal_10 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_10
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre left split (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (hv (left*matrix_count_pre+split) (by rw [PreH16]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_11 : matrixChainMinCost_entail_wit_7_split_goal_11 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_11
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre (split+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_12 : matrixChainMinCost_entail_wit_7_split_goal_12 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_12
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  have hb := matrix_chain_index_bounds matrix_count_pre left split (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 : matrixChainMinCost_entail_wit_8_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_1
  intro dimensions_l matrix_count_pre cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have PreH37_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH37
  have PreH38_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH38
  have PreH39_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l (0 : Int)).mp PreH39
  have PreH40_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l (0 : Int)).mp PreH40
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH37_indexed idx (by omega), PreH38_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH42.1.1⟩, PreH42.1.2⟩, PreH42.2⟩
  have hv : MatrixChainTableValuesBounded cost_l := by
    intro idx hidx
    exact ⟨PreH39_indexed idx hidx, PreH40_indexed idx hidx⟩
  rfl

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 : matrixChainMinCost_entail_wit_8_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_2
  intro dimensions_l matrix_count_pre cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have PreH37_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH37
  have PreH38_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH38
  have PreH39_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l (0 : Int)).mp PreH39
  have PreH40_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l (0 : Int)).mp PreH40
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH37_indexed idx (by omega), PreH38_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH42.1.1⟩, PreH42.1.2⟩, PreH42.2⟩
  have hv : MatrixChainTableValuesBounded cost_l := by
    intro idx hidx
    exact ⟨PreH39_indexed idx hidx, PreH40_indexed idx hidx⟩
  exact candidate_upper dimensions_l cost_l matrix_count_pre chain_length left split
    (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ hd hsplit.1.1

theorem proof_of_matrixChainMinCost_entail_wit_9_1_split_goal_1 : matrixChainMinCost_entail_wit_9_1_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_9_1_split_goal_1
  intro dimensions_l matrix_count_pre cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH21
  have PreH22_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH22
  have PreH23_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH23
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH20_indexed idx (by omega), PreH21_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH26.1.1⟩, PreH26.1.2⟩, PreH26.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH22_indexed idx hidx, PreH23_indexed idx hidx⟩
  have hlegacy :   (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) candidate) := by
    rw [PreH8] at PreH24
    exact matrix_chain_split_progress_better__min_update _ _ _ _ _ _ _ _ _
      (by omega) (by omega) PreH24 hsplit
  exact ⟨⟨hlegacy.1.1.2, hlegacy.1.2⟩, hlegacy.2⟩

theorem proof_of_matrixChainMinCost_entail_wit_9_2_split_goal_1 : matrixChainMinCost_entail_wit_9_2_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_9_2_split_goal_1
  intro dimensions_l matrix_count_pre cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH21
  have PreH22_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH22
  have PreH23_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH23
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH20_indexed idx (by omega), PreH21_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH26.1.1⟩, PreH26.1.2⟩, PreH26.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH22_indexed idx hidx, PreH23_indexed idx hidx⟩
  have hlegacy :   (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) best) := by
    rw [PreH8] at PreH24
    exact matrix_chain_split_progress_not_better__min_update _ _ _ _ _ _ _ _ _
      (by omega) (by omega) PreH24 hsplit
  exact ⟨⟨hlegacy.1.1.2, hlegacy.1.2⟩, hlegacy.2⟩

theorem proof_of_matrixChainMinCost_entail_wit_10_split_goal_1 : matrixChainMinCost_entail_wit_10_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_10_split_goal_1
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  apply matrix_chain_split_progress_complete__min_update dimensions_l cost_l_2 matrix_count_pre
    chain_length left (left+chain_length-1) best (by omega) (by omega) rfl (by omega) (by omega)
  convert hsplit using 1 <;> omega

theorem proof_of_matrixChainMinCost_entail_wit_10_split_goal_2 : matrixChainMinCost_entail_wit_10_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_10_split_goal_2
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  have hlegacy :   (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left ((left + chain_length) - 1) best) := by
    convert hsplit using 1 <;> omega
  exact ⟨⟨hlegacy.1.1.2, hlegacy.1.2⟩, hlegacy.2⟩

theorem proof_of_matrixChainMinCost_entail_wit_10_split_goal_3 : matrixChainMinCost_entail_wit_10_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_10_split_goal_3
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH18_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH20
  have PreH21_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH21
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH18_indexed idx (by omega), PreH19_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) := ⟨⟨⟨by omega, PreH23.1.1⟩, PreH23.1.2⟩, PreH23.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH20_indexed idx hidx, PreH21_indexed idx hidx⟩
  exact (matrix_chain_index_bounds matrix_count_pre left (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 : matrixChainMinCost_entail_wit_11_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_1
  intro dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH20
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best) := ⟨⟨⟨by omega, PreH22.1.1⟩, PreH22.1.2⟩, PreH22.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH19_indexed idx hidx, PreH20_indexed idx hidx⟩
  have hlegacy :   (MatrixChainLeftProgress dimensions_l (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)) matrix_count_pre chain_length (left + 1)) := by
    have hcur : 0 ≤ left*matrix_count_pre+(left+chain_length-1) ∧
        left*matrix_count_pre+(left+chain_length-1) < Zlength cost_l_2 := by
      rw [PreH15]
      exact matrix_chain_index_bounds matrix_count_pre left (left+chain_length-1) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have hd := hsplit.1.1
    have hp := hsplit.1.2
    constructor
    · refine ⟨hd.1, ?_⟩
      intro len l r hlen hr hl hfit
      have hidx : 0 ≤ l*matrix_count_pre+r ∧ l*matrix_count_pre+r < Zlength cost_l_2 := by
        rw [PreH15]
        exact matrix_chain_index_bounds matrix_count_pre l r (by omega)
          ⟨hl, by omega⟩ ⟨by omega, by omega⟩
      have hneq : left*matrix_count_pre+(left+chain_length-1) ≠ l*matrix_count_pre+r := by
        intro he
        have hh := matrix_index_injective matrix_count_pre left (left+chain_length-1) l r
          (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
        omega
      rw [Znth_replace_Znth_Diff 0 cost_l_2 _ _ best hcur hidx hneq]
      exact hd.2 len l r hlen hr hl hfit
    · intro l r hl hr hfit
      by_cases he : l = left
      · subst l
        have her : r = left+chain_length-1 := by omega
        subst r
        rw [Znth_replace_Znth_Same 0 cost_l_2 _ best hcur]
        convert PreH23 using 1 <;> omega
      · have hidx : 0 ≤ l*matrix_count_pre+r ∧ l*matrix_count_pre+r < Zlength cost_l_2 := by
          rw [PreH15]
          exact matrix_chain_index_bounds matrix_count_pre l r (by omega)
            ⟨hl.1, by omega⟩ ⟨by omega, by omega⟩
        have hneq : left*matrix_count_pre+(left+chain_length-1) ≠ l*matrix_count_pre+r := by
          intro hi
          have hh := matrix_index_injective matrix_count_pre left (left+chain_length-1) l r
            (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hi
          omega
        rw [Znth_replace_Znth_Diff 0 cost_l_2 _ _ best hcur hidx hneq]
        exact hp l r ⟨hl.1, by omega⟩ hr hfit
  exact ⟨hlegacy.1.2, hlegacy.2⟩

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 : matrixChainMinCost_entail_wit_11_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_2
  intro dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH20
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best) := ⟨⟨⟨by omega, PreH22.1.1⟩, PreH22.1.2⟩, PreH22.2⟩
  apply forall_replace _ 0 best cost_l_2 (left*matrix_count_pre+(left+chain_length-1)) (by omega) PreH20
  omega

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 : matrixChainMinCost_entail_wit_11_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_3
  intro dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH20
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best) := ⟨⟨⟨by omega, PreH22.1.1⟩, PreH22.1.2⟩, PreH22.2⟩
  apply forall_replace _ 0 best cost_l_2 (left*matrix_count_pre+(left+chain_length-1)) (by omega) PreH19
  omega

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_4 : matrixChainMinCost_entail_wit_11_split_goal_4 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_4
  intro dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have PreH17_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH17
  have PreH18_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH18
  have PreH19_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH19
  have PreH20_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH20
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH17_indexed idx (by omega), PreH18_indexed idx (by omega)⟩
  have hsplit : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best) := ⟨⟨⟨by omega, PreH22.1.1⟩, PreH22.1.2⟩, PreH22.2⟩
  simp only [Zlength_replace_Znth]
  omega

theorem proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 : matrixChainMinCost_entail_wit_12_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_12_split_goal_1
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have PreH11_indexed := (indexed_Forall ((LE.le (α := Int)) (1)) dimensions_l (0 : Int)).mp PreH11
  have PreH12_indexed := (indexed_Forall ((GE.ge (α := Int)) (100)) dimensions_l (0 : Int)).mp PreH12
  have PreH13_indexed := (indexed_Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2 (0 : Int)).mp PreH13
  have PreH14_indexed := (indexed_Forall ((GE.ge (α := Int)) (7000000)) cost_l_2 (0 : Int)).mp PreH14
  have hd : MatrixChainDimensionsBounded dimensions_l matrix_count_pre := by
    refine ⟨by omega, ?_⟩
    intro idx hi
    exact ⟨PreH11_indexed idx (by omega), PreH12_indexed idx (by omega)⟩
  have hleft : MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left := ⟨⟨by omega, PreH16.1⟩, PreH16.2⟩
  have hv : MatrixChainTableValuesBounded cost_l_2 := by
    intro idx hidx
    exact ⟨PreH13_indexed idx hidx, PreH14_indexed idx hidx⟩
  have hlegacy :   (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre (chain_length + 1)) := by
    refine ⟨by omega, ?_⟩
    intro len l r hlen hr hl hfit
    by_cases hlt : len < chain_length
    · exact hleft.1.2 len l r ⟨hlen.1, hlt⟩ hr hl hfit
    · have he : len = chain_length := by omega
      subst len
      exact hleft.2 l r ⟨hl, by omega⟩ hr hfit
  exact hlegacy.2

theorem proof_of_matrixChainMinCost_entail_wit_2 : matrixChainMinCost_entail_wit_2 := by
  unfold matrixChainMinCost_entail_wit_2
  right
  intro dimensions_l matrix_count_pre cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 dimensions_l matrix_count_pre cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | exact (proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 dimensions_l matrix_count_pre cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_2_split_goal_2 dimensions_l matrix_count_pre cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | exact (proof_of_matrixChainMinCost_entail_wit_2_split_goal_2 dimensions_l matrix_count_pre cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_4 : matrixChainMinCost_entail_wit_4 := by
  unfold matrixChainMinCost_entail_wit_4
  right
  intro dimensions_l matrix_count_pre chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_4_split_goal_1 dimensions_l matrix_count_pre chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
    | exact (proof_of_matrixChainMinCost_entail_wit_4_split_goal_1 dimensions_l matrix_count_pre chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_5 : matrixChainMinCost_entail_wit_5 := by
  unfold matrixChainMinCost_entail_wit_5
  right
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_2 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_2 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_3 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_3 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_4 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_4 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_5 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_5 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_6 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_6 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_7 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_7 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_8 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_8 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_9 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_9 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_10 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_10 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_11 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_11 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_5_split_goal_12 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_5_split_goal_12 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_6 : matrixChainMinCost_entail_wit_6 := by
  unfold matrixChainMinCost_entail_wit_6
  right
  intro dimensions_l matrix_count_pre cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 dimensions_l matrix_count_pre cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38))
    | exact (proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 dimensions_l matrix_count_pre cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 dimensions_l matrix_count_pre cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38))
    | exact (proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 dimensions_l matrix_count_pre cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_7 : matrixChainMinCost_entail_wit_7 := by
  unfold matrixChainMinCost_entail_wit_7
  right
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_3 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_3 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_4 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_4 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_5 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_5 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_6 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_6 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_7 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_7 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_8 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_8 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_9 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_9 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_10 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_10 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_11 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_11 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_7_split_goal_12 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_7_split_goal_12 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_8 : matrixChainMinCost_entail_wit_8 := by
  unfold matrixChainMinCost_entail_wit_8
  right
  intro dimensions_l matrix_count_pre cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 dimensions_l matrix_count_pre cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42))
    | exact (proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 dimensions_l matrix_count_pre cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 dimensions_l matrix_count_pre cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42))
    | exact (proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 dimensions_l matrix_count_pre cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_9_1 : matrixChainMinCost_entail_wit_9_1 := by
  unfold matrixChainMinCost_entail_wit_9_1
  right
  intro dimensions_l matrix_count_pre cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_9_1_split_goal_1 dimensions_l matrix_count_pre cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | exact (proof_of_matrixChainMinCost_entail_wit_9_1_split_goal_1 dimensions_l matrix_count_pre cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_9_2 : matrixChainMinCost_entail_wit_9_2 := by
  unfold matrixChainMinCost_entail_wit_9_2
  right
  intro dimensions_l matrix_count_pre cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_9_2_split_goal_1 dimensions_l matrix_count_pre cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | exact (proof_of_matrixChainMinCost_entail_wit_9_2_split_goal_1 dimensions_l matrix_count_pre cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_10 : matrixChainMinCost_entail_wit_10 := by
  unfold matrixChainMinCost_entail_wit_10
  right
  intro dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_10_split_goal_1 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_10_split_goal_1 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_10_split_goal_2 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_10_split_goal_2 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_10_split_goal_3 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_10_split_goal_3 dimensions_l matrix_count_pre cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_11 : matrixChainMinCost_entail_wit_11 := by
  unfold matrixChainMinCost_entail_wit_11
  right
  intro dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_11_split_goal_4 dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_matrixChainMinCost_entail_wit_11_split_goal_4 dimensions_l matrix_count_pre cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_12 : matrixChainMinCost_entail_wit_12 := by
  unfold matrixChainMinCost_entail_wit_12
  right
  intro dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 dimensions_l matrix_count_pre left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | assumption
    | omega
    | trivial

theorem proof_of_matrixChainMinCost_entail_wit_1 : matrixChainMinCost_entail_wit_1 := by
  unfold matrixChainMinCost_entail_wit_1
  right
  intro dims n hn hnmax hd hd' hb hu
  split_pure_spatial
  · sep_apply (intArray.undef_full_split_to_undef_seg (&("cost")) (n*n) 64 (by constructor <;> nlinarith))
    cancel
  · split_pures <;> dump_pre_spatial
    · simp [Forall.iff_forall_mem]
    · rfl

theorem proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3 := by
  unfold matrixChainMinCost_entail_wit_3
  right
  intro dims n table i hi hn hnmax hd hi0 hin hd' hb hu hlen hz
  have he : i = n*n := by omega
  have hlength : Zlength table = n*n := by omega
  have hzero : MatrixChainZeroPrefix table (n*n) := by
    refine ⟨hlength, ?_⟩
    intro idx hidx
    exact ((indexed_Forall (Eq (0 : Int)) table 0).mp hz idx (by omega)).symm
  have hdone := matrix_chain_zero_table_lengths_done__initialization dims table n hn hd hzero
  have hlow : Forall (LE.le (0 : Int)) table := by
    rw [Forall.iff_forall_mem] at hz ⊢
    intro v hv
    have he := hz v hv
    omega
  have hhigh : Forall (GE.ge (7000000 : Int)) table := by
    rw [Forall.iff_forall_mem] at hz ⊢
    intro v hv
    have he := hz v hv
    omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | exact hdone.2

theorem proof_of_matrixChainMinCost_entail_wit_13 : matrixChainMinCost_entail_wit_13 := by
  unfold matrixChainMinCost_entail_wit_13
  right
  intro dims n len table hlen hn hnmax hd ht hlen0 hlenn hd' hb hu htb htu hlen1 hdone
  have hc := hdone n 0 (n-1) ⟨hn, hlen⟩ (by omega) (by omega) (by omega)
  have hresult : MatrixChainOptimalCost dims n (Znth (n-1) table 0) := by
    simpa only [Int.zero_mul, Int.zero_add] using hc
  split_pure_spatial
  · sep_apply (intArray.full_to_undef_full (&("cost")) (n*n) table)
    sep_apply (intArray.undef_full_to_undef_seg (&("cost")) (n*n))
    sep_apply (intArray.undef_seg_merge_to_undef_full (&("cost")) 0 (n*n) 64 (by constructor <;> nlinarith))
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    exact naive_C_Rules.toContext.derivable1_refl _
  · dump_pre_spatial
    exact hresult

end SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_proof_manual
