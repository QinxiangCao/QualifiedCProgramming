import SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_goal
import SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open catalan_numbers_goal catalan_numbers_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem sum_cell_int_range (n : Int) (table : List Int) (row col : Int)
    (hn : 0 ≤ n ∧ n ≤ 7) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (hp : StackRowProgress n table row col) :
    INT_MIN ≤ Znth (StackCellIndex n (row - 1) (col + 1)) table 0 +
        Znth (StackCellIndex n row (col - 1)) table 0 ∧
    Znth (StackCellIndex n (row - 1) (col + 1)) table 0 +
        Znth (StackCellIndex n row (col - 1)) table 0 ≤ INT_MAX := by
  have hb := (StackRowProgress_add_step_extend__cell_dp n table row col hn hr hc hp).2.2
  have hl := hp.2.2.2.1.2
  rw [app_Znth2 0 table _ (StackCellIndex n row col) (by change Zlength table ≤ row * (n + 1) + col; omega), hl] at hb
  simp only [StackCellIndex, Int.sub_self] at hb
  exact StackCellBound_int_range__cell_dp row col _ (by omega) (by omega) hb

-- Previously proved auxiliary statements retained for proof audits.
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private theorem prefix_bounds (n : Int) (table : List Int) (written : Int)
    (hp : StackTablePrefix n table written) :
    ∀ r c, ((((0 ≤ r ∧ r ≤ n) ∧ 0 ≤ c) ∧ c ≤ n) ∧ (r*(n+1)+c < written)) →
      0 ≤ Znth (r*(n+1)+c) table 0 ∧ Znth (r*(n+1)+c) table 0 ≤ Z.pow 2 (2*r+c) := by
  intro r c ⟨⟨⟨⟨hr0,hrn⟩,hc0⟩,hcn⟩,hi⟩
  have hi0 : 0 ≤ r*(n+1)+c := Int.add_nonneg
    (Int.mul_nonneg hr0 (by have := hp.1; omega)) hc0
  exact (hp.2.2 r c ⟨hr0,hrn⟩ ⟨hc0,hcn⟩ ⟨hi0,hi⟩).1.2.2


theorem proof_of_solve_safety_wit_10_split_goal_1 : solve_safety_wit_10_split_goal_1 := by
  unfold solve_safety_wit_10_split_goal_1
  intro n_pre table i j retval_3 retval retval_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1))) := NewPreH1
    have PreH4 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1))) := NewPreH2
    have PreH22 : (StackRowProgress n_pre table i j) := by exact ⟨by omega, by omega, by assumption⟩
    dump_pre_spatial
    have h := (sum_cell_int_range n_pre table i j (by omega) (by omega) (by omega) PreH22).2
    simpa only [PreH1, PreH4, Int.sub_zero, StackCellIndex] using h

theorem proof_of_solve_safety_wit_10_split_goal_2 : solve_safety_wit_10_split_goal_2 := by
  unfold solve_safety_wit_10_split_goal_2
  intro n_pre table i j retval_3 retval retval_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1))) := NewPreH1
    have PreH4 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1))) := NewPreH2
    have PreH22 : (StackRowProgress n_pre table i j) := by exact ⟨by omega, by omega, by assumption⟩
    dump_pre_spatial
    have h := (sum_cell_int_range n_pre table i j (by omega) (by omega) (by omega) PreH22).1
    simpa only [PreH1, PreH4, Int.sub_zero, StackCellIndex] using h

theorem proof_of_solve_safety_wit_10 : solve_safety_wit_10 := by
  unfold solve_safety_wit_10
  right
  intro n_pre table i j retval_3 retval retval_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17
  have PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1))) := NewPreH1
  have PreH2 : ((0 : Int) <= retval_2) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1))) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH4 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1))) := NewPreH2
  have PreH5 : ((0 : Int) <= retval) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1))) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH7 : (retval_3 = ((i * (n_pre + 1)) + j)) := NewPreH3
  have PreH8 : ((0 : Int) <= retval_3) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH9 : (retval_3 <= ((n_pre + 1) * (n_pre + 1))) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH10 : ((0 : Int) <= n_pre) := NewPreH4
  have PreH11 : (n_pre <= 7) := NewPreH5
  have PreH12 : (1 <= i) := NewPreH6
  have PreH13 : (i <= n_pre) := NewPreH7
  have PreH14 : (1 <= j) := NewPreH8
  have PreH15 : (j <= n_pre) := NewPreH9
  have PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j)) := NewPreH10
  have PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) := NewPreH11
  have PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) := NewPreH12
  have PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) := NewPreH13
  have PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) := NewPreH14
  have PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) := NewPreH15
  have PreH22 : (StackRowProgress n_pre table i j) := by exact ⟨by omega, by omega, by assumption⟩
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_solve_safety_wit_10_split_goal_1 n_pre table i j retval_3 retval retval_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17
    | exact proof_of_solve_safety_wit_10_split_goal_2 n_pre table i j retval_3 retval retval_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17

theorem proof_of_solve_entail_wit_1 : solve_entail_wit_1 := by
  unfold solve_entail_wit_1
  right
  intro n hn0 hn
  have hsize : 0 ≤ (n+1)*(n+1) ∧ (n+1)*(n+1) ≤ 64 := by
    constructor
    · exact Int.mul_nonneg (by omega) (by omega)
    · nlinarith
  have hp : StackTablePrefix n [] 0 := by
    refine ⟨hn0, ⟨by omega,rfl⟩, ?_⟩
    intro r c hr hc hi
    omega
  have hbounds := prefix_bounds n [] 0 hp
  Exists ([] : List Int)
  simp only [Int.zero_mul]
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg (&("f")) 64)
  sep_apply (naive_C_Rules.IntArray.undef_seg_split_to_undef_seg (&("f")) 0 ((n+1)*(n+1)) 64 hsize)
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.seg_empty (&("f")) 0 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_2 : solve_entail_wit_2 := by
  unfold solve_entail_wit_2
  right
  intro n_pre table_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7
  have PreH4 : ((0 : Int) <= i) := NewPreH4
  have PreH6 : (StackRowsDone n_pre table_2 i) := by exact ⟨by omega, by assumption⟩
  have hp : StackRowProgress n_pre table_2 i 0 :=
    ⟨PreH4, ⟨by omega, by omega⟩, by simpa only [Int.add_zero] using PreH6.2⟩
  Exists table_2
  simp only [Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_solve_entail_wit_3_split_goal_2 : solve_entail_wit_3_split_goal_2 := by
  unfold solve_entail_wit_3_split_goal_2
  intro n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    simp only [Int.sub_mul, Int.one_mul]
    omega

theorem proof_of_solve_entail_wit_3_split_goal_3 : solve_entail_wit_3_split_goal_3 := by
  unfold solve_entail_wit_3_split_goal_3
  intro n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (i <= n_pre) := NewPreH7
    have hm := Int.mul_le_mul_of_nonneg_right PreH7 (show 0 ≤ n_pre + 1 by omega)
    simp only [Int.add_mul, Int.one_mul]
    omega

theorem proof_of_solve_entail_wit_3 : solve_entail_wit_3 := by
  unfold solve_entail_wit_3
  right
  intro n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  have PreH1 : (j = (0 : Int)) := NewPreH1
  have PreH2 : (i ≠ (0 : Int)) := NewPreH2
  have PreH3 : (j <= n_pre) := NewPreH3
  have PreH4 : ((0 : Int) <= n_pre) := NewPreH4
  have PreH5 : (n_pre <= 7) := NewPreH5
  have PreH6 : ((0 : Int) <= i) := NewPreH6
  have PreH7 : (i <= n_pre) := NewPreH7
  have PreH8 : ((0 : Int) <= j) := NewPreH8
  have PreH9 : (j <= (n_pre + 1)) := NewPreH9
  have PreH10 : (StackRowProgress n_pre table_2 i j) := by exact ⟨by omega, by omega, by assumption⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_solve_entail_wit_3_split_goal_2 n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
      | exact proof_of_solve_entail_wit_3_split_goal_3 n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11

theorem proof_of_solve_entail_wit_4_split_goal_2 : solve_entail_wit_4_split_goal_2 := by
  unfold solve_entail_wit_4_split_goal_2
  intro n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    simp only [Int.sub_mul, Int.one_mul]
    omega

theorem proof_of_solve_entail_wit_4_split_goal_3 : solve_entail_wit_4_split_goal_3 := by
  unfold solve_entail_wit_4_split_goal_3
  intro n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (i <= n_pre) := NewPreH7
    have hm := Int.mul_le_mul_of_nonneg_right PreH7 (show 0 ≤ n_pre + 1 by omega)
    simp only [Int.add_mul, Int.one_mul]
    omega

theorem proof_of_solve_entail_wit_4 : solve_entail_wit_4 := by
  unfold solve_entail_wit_4
  right
  intro n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  have PreH1 : (j ≠ (0 : Int)) := NewPreH1
  have PreH2 : (i ≠ (0 : Int)) := NewPreH2
  have PreH3 : (j <= n_pre) := NewPreH3
  have PreH4 : ((0 : Int) <= n_pre) := NewPreH4
  have PreH5 : (n_pre <= 7) := NewPreH5
  have PreH6 : ((0 : Int) <= i) := NewPreH6
  have PreH7 : (i <= n_pre) := NewPreH7
  have PreH8 : ((0 : Int) <= j) := NewPreH8
  have PreH9 : (j <= (n_pre + 1)) := NewPreH9
  have PreH10 : (StackRowProgress n_pre table_2 i j) := by exact ⟨by omega, by omega, by assumption⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_solve_entail_wit_4_split_goal_2 n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
      | exact proof_of_solve_entail_wit_4_split_goal_3 n_pre table_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11

theorem aux_solve_entail_wit_5_1_split_goal_1 : (forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (i = (0 : Int))) (PreH5 : (j <= n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (n_pre + 1))) (PreH12 : (StackRowProgress n_pre table_2 i j)) ,
  (StackRowProgress n_pre (table_2 ++ (1 :: (@List.nil Int))) (0 : Int) (j + 1))) := by

  intro n_pre table_2 j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    subst i
    have h := (StackRowProgress_zero_row_extend__cell_dp n_pre table_2 j (by omega) (by omega) PreH12).1
    simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_1 : solve_entail_wit_5_1 := by
  unfold solve_entail_wit_5_1
  right
  intro n_pre table_2 j i retval NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  have PreH1 : (retval = ((i * (n_pre + 1)) + j)) := NewPreH1
  have PreH2 : ((0 : Int) <= retval) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1))) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH4 : (i = (0 : Int)) := NewPreH2
  have PreH5 : (j <= n_pre) := NewPreH3
  have PreH6 : ((0 : Int) <= n_pre) := NewPreH4
  have PreH7 : (n_pre <= 7) := NewPreH5
  have PreH8 : ((0 : Int) <= i) := NewPreH6
  have PreH9 : (i <= n_pre) := NewPreH7
  have PreH10 : ((0 : Int) <= j) := NewPreH8
  have PreH11 : (j <= (n_pre + 1)) := NewPreH9
  have PreH12 : (StackRowProgress n_pre table_2 i j) := by exact ⟨by omega, by omega, by assumption⟩
  have hnext := aux_solve_entail_wit_5_1_split_goal_1 n_pre table_2 j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hprefix : StackTablePrefix n_pre (table_2 ++ [1]) (i*(n_pre+1)+(j+1)) := by
    simpa only [PreH4] using hnext.2.2
  have hbounds := prefix_bounds _ _ _ hprefix
  Exists (table_2 ++ [1])
  simp only [Int.add_assoc] at hprefix hbounds ⊢
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem aux_solve_entail_wit_5_2_split_goal_1 : (forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = (0 : Int))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH13 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH15 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table_2 i j)) ,
  (StackRowProgress n_pre (table_2 ++ ((Znth ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))) i ((0 : Int) + 1))) := by

  intro n_pre table_2 i j retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    subst j
    have h := (StackRowProgress_copy_boundary_extend__cell_dp n_pre table_2 i (by omega) (by omega) PreH16).1
    simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_2 : solve_entail_wit_5_2 := by
  unfold solve_entail_wit_5_2
  right
  intro n_pre table_2 i j retval retval_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13
  have PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) := NewPreH1
  have PreH2 : ((0 : Int) <= retval_2) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1))) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH4 : (retval = ((i * (n_pre + 1)) + j)) := NewPreH2
  have PreH5 : ((0 : Int) <= retval) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1))) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH7 : ((0 : Int) <= n_pre) := NewPreH3
  have PreH8 : (n_pre <= 7) := NewPreH4
  have PreH9 : (1 <= i) := NewPreH5
  have PreH10 : (i <= n_pre) := NewPreH6
  have PreH11 : (j = (0 : Int)) := NewPreH7
  have PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + j)) := NewPreH8
  have PreH13 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) := NewPreH9
  have PreH14 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) := NewPreH10
  have PreH15 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) := NewPreH11
  have PreH16 : (StackRowProgress n_pre table_2 i j) := by exact ⟨by omega, by omega, by assumption⟩
  have hnext := aux_solve_entail_wit_5_2_split_goal_1 n_pre table_2 i j retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hprefix := hnext.2.2
  have hbounds := prefix_bounds _ _ _ hprefix
  Exists (table_2 ++ [Znth (((i-1)*(n_pre+1))+1) table_2 0])
  simp only [PreH1, PreH11, Int.add_zero, Int.zero_add, Int.sub_zero, Int.add_assoc] at hprefix hbounds ⊢
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem aux_solve_entail_wit_5_3_split_goal_1 : (forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval)) (PreH9 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table_2 i j)) ,
  (StackRowProgress n_pre (table_2 ++ (((Znth ((((i - 1) * (n_pre + 1)) + (j + 1)) - (0 : Int)) table_2 (0 : Int)) + (Znth (((i * (n_pre + 1)) + (j - 1)) - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))) i (j + 1))) := by

  intro n_pre table_2 i j retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have h := (StackRowProgress_add_step_extend__cell_dp n_pre table_2 i j (by omega) (by omega) (by omega) PreH22).1
    simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_3 : solve_entail_wit_5_3 := by
  unfold solve_entail_wit_5_3
  right
  intro n_pre table_2 i j retval retval_2 retval_3 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17
  have PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1))) := NewPreH1
  have PreH2 : ((0 : Int) <= retval_3) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH3 : (retval_3 <= ((n_pre + 1) * (n_pre + 1))) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH4 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) := NewPreH2
  have PreH5 : ((0 : Int) <= retval_2) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH6 : (retval_2 <= ((n_pre + 1) * (n_pre + 1))) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH7 : (retval = ((i * (n_pre + 1)) + j)) := NewPreH3
  have PreH8 : ((0 : Int) <= retval) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH9 : (retval <= ((n_pre + 1) * (n_pre + 1))) := by first | assumption | (simp_all only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> nlinarith)
  have PreH10 : ((0 : Int) <= n_pre) := NewPreH4
  have PreH11 : (n_pre <= 7) := NewPreH5
  have PreH12 : (1 <= i) := NewPreH6
  have PreH13 : (i <= n_pre) := NewPreH7
  have PreH14 : (1 <= j) := NewPreH8
  have PreH15 : (j <= n_pre) := NewPreH9
  have PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j)) := NewPreH10
  have PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) := NewPreH11
  have PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) := NewPreH12
  have PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) := NewPreH13
  have PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) := NewPreH14
  have PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) := NewPreH15
  have PreH22 : (StackRowProgress n_pre table_2 i j) := by exact ⟨by omega, by omega, by assumption⟩
  have hnext := aux_solve_entail_wit_5_3_split_goal_1 n_pre table_2 i j retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hprefix := hnext.2.2
  have hbounds := prefix_bounds _ _ _ hprefix
  Exists (table_2 ++ [Znth (((i-1)*(n_pre+1))+(j+1)) table_2 0 + Znth ((i*(n_pre+1))+(j-1)) table_2 0])
  simp only [PreH1, PreH4, PreH7, Int.sub_zero, Int.add_assoc] at hprefix hbounds ⊢
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_6 : solve_entail_wit_6 := by
  unfold solve_entail_wit_6
  right
  intro n table j i hj hn0 hn hi0 hin hj0 hjn hp hv
  have he : j = n+1 := by omega
  have hp' : StackTablePrefix n table ((i+1)*(n+1)) := by
    simpa only [he, Int.add_mul, Int.one_mul] using hp
  have hb := prefix_bounds n table ((i+1)*(n+1)) hp'
  Exists table
  simp only [he, Int.add_mul, Int.one_mul] at hp' hb ⊢
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_7 : solve_entail_wit_7 := by
  unfold solve_entail_wit_7
  right
  intro n table i hi hn0 hn hi0 hin hp hv
  have he : i = n+1 := by omega
  subst i
  have hm := Int.mul_nonneg hn0 (show 0 ≤ n+1 by omega)
  have hlt : n*(n+1) < (n+1)*(n+1) := by
    simp only [Int.add_mul, Int.one_mul]
    omega
  have hcorrect := (hp.2.2 n 0 (by omega) (by omega) (by
    simpa only [StackCellIndex, Int.add_zero] using And.intro hm hlt)).2
  have hc : StackSequenceCount n (Znth (n*(n+1)) table 0) := by
    apply StackCompletionCount_zero_to_StackSequenceCount
    simpa only [StackCellIndex, Int.add_zero] using hcorrect (by omega)
  Exists table
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.undef_seg_empty (&("f")) ((n+1)*(n+1)))).1)
  sep_apply (naive_C_Rules.IntArray.seg_to_full (&("f")) 0 ((n+1)*(n+1)) table)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solve_entail_wit_8 : solve_entail_wit_8 := by
  unfold solve_entail_wit_8
  left
  intro n table retval he hn0 hn hi0 hib hc
  have hsize : 0 ≤ (n+1)*(n+1) ∧ (n+1)*(n+1) ≤ 64 := by
    constructor
    · exact Int.mul_nonneg (by omega) (by omega)
    · nlinarith
  split_pure_spatial
  · sep_apply (naive_C_Rules.IntArray.full_to_undef_full (&("f")) ((n+1)*(n+1)) table)
    sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg (&("f")) ((n+1)*(n+1)))
    sep_apply (naive_C_Rules.IntArray.undef_seg_merge_to_undef_full (&("f")) 0 ((n+1)*(n+1)) 64 hsize)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    exact naive_C_Rules.toContext.derivable1_refl _
  · dump_pre_spatial
    simpa only [he, Int.add_zero] using hc


end SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_proof_manual
