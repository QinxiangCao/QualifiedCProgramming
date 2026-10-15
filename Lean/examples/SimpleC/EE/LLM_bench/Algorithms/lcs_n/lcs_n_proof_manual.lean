import SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_goal
import SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib
import SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_proof_auto
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open lcs_n_goal lcs_n_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem row_bounds (n r : Int) (hn : 0 ≤ n) (hr : 0 ≤ r ∧ r ≤ n+1) :
    0 ≤ (n+1)*r ∧ (n+1)*r ≤ (n+1)*(n+1) := by
  exact ⟨Int.mul_nonneg (by omega) hr.1, Int.mul_le_mul_of_nonneg_left hr.2 (by omega)⟩

private theorem cell_bounds (n r c : Int) (hn : 0 ≤ n)
    (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n) :
    0 ≤ (n+1)*r+c ∧ (n+1)*r+c < (n+1)*(n+1) := by
  have h0 := Int.mul_nonneg (show 0 ≤ n+1 by omega) hr.1
  have h1 := Int.mul_le_mul_of_nonneg_left hr.2 (show 0 ≤ n+1 by omega)
  grind

private theorem sublist_nested {A : Type} (l : List A) (lo hi a b : Int)
    (hlo : 0 ≤ lo) (ha : 0 ≤ a ∧ a ≤ b) (hb : b ≤ hi-lo) :
    sublist a b (sublist lo hi l) = sublist (a+lo) (b+lo) l := by
  have hmin : lo.toNat+b.toNat ≤ hi.toNat := by omega
  simp only [sublist, List.take_drop, List.take_take, List.drop_drop,
    Nat.min_eq_left hmin]
  congr 2 <;> omega

private theorem append_cell (l : List (Option Int)) (lo k : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ k) (hk : k < Zlength l) :
    sublist lo k l ++ [Znth k l none] = sublist lo (k+1) l := by
  rw [sublist_split lo (k+1) k l hlo ⟨by omega,by omega⟩,
    sublist_single none k l ⟨by omega,hk⟩]

private theorem split_mixed_cell (x lo k hi : Int) (l : List (Option Int))
    (hlo : 0 ≤ lo ∧ lo ≤ k) (hk : k < hi) (hhi : hi ≤ Zlength l) :
    intArray.mixed_seg x lo hi (sublist lo hi l) |--
      intArray.mixed_seg x lo k (sublist lo k l) **
      intArray.mixedstoreA x k (Znth k l none) **
      intArray.mixed_seg x (k+1) hi (sublist (k+1) hi l) := by
  sep_apply (intArray.mixed_seg_split_to_mixed_seg x lo k hi (sublist lo hi l) ⟨hlo.2,by omega⟩)
  rw [sublist_nested l lo hi 0 (k-lo) hlo.1 ⟨by omega,by omega⟩ (by omega),
    sublist_nested l lo hi (k-lo) (hi-lo) hlo.1 ⟨by omega,by omega⟩ (by omega)]
  simp only [Int.zero_add, Int.sub_add_cancel]
  sep_apply (intArray.mixed_seg_split_to_mixed_seg x k (k+1) hi (sublist k hi l) ⟨by omega,by omega⟩)
  rw [sublist_nested l k hi 0 (k+1-k) (by omega) ⟨by omega,by omega⟩ (by omega),
    sublist_nested l k hi (k+1-k) (hi-k) (by omega) ⟨by omega,by omega⟩ (by omega)]
  simp only [Int.zero_add, Int.sub_add_cancel]
  rw [sublist_single none k l ⟨by omega,by omega⟩]
  sep_apply ((intArray.mixed_seg_unfold x k (k+1) ([] : List (Option Int)) (Znth k l none)).1)
  sep_apply ((intArray.mixed_seg_empty x (k+1) (k+1)).1)
  Intros_p he
  cancel


private theorem read_prefix (x k : Int) (l : List (Option Int)) (v : Int)
    (hk : 0 ≤ k ∧ k < Zlength l) (hv : Znth k l none = some v) :
    intArray.mixed_seg x 0 k (sublist 0 k l) **
      ((x + k * sizeof(INT)) # Int |-> v) |--
    intArray.mixed_seg x 0 (k+1) (sublist 0 (k+1) l) := by
  have hs := intArray.mixed_seg_single x k (some v)
  change ((x + k * sizeof(INT)) # Int |-> v) |--
    intArray.mixed_seg x k (k+1) [some v] at hs
  sep_apply hs
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg x 0 k (k+1) (sublist 0 k l) [some v] ⟨hk.1,by omega⟩)
  rw [← hv, append_cell l 0 k ⟨by omega,hk.1⟩ hk.2]
  cancel

private theorem join_written_full (x k total : Int) (l : List (Option Int)) (v : Int)
    (hk : 0 ≤ k ∧ k < total) (hl : Zlength l = total) :
    intArray.mixed_seg x 0 k (sublist 0 k l) **
      ((x + k * sizeof(INT)) # Int |-> v) **
      intArray.mixed_seg x (k+1) total (sublist (k+1) total l) |--
    intArray.mixed_full x total (replace_Znth k (some v) l) := by
  have hs := intArray.mixed_seg_single x k (some v)
  change ((x + k * sizeof(INT)) # Int |-> v) |--
    intArray.mixed_seg x k (k+1) [some v] at hs
  sep_apply hs
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg x 0 k (k+1) (sublist 0 k l) [some v] ⟨hk.1,by omega⟩)
  sep_apply (intArray.mixed_seg_merge_to_mixed_full x 0 (k+1) total
    (sublist 0 k l ++ [some v]) (sublist (k+1) total l) ⟨by omega,by omega⟩)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  have he : (sublist 0 k l ++ [some v]) ++ sublist (k+1) total l = replace_Znth k (some v) l := by
    rw [replace_Znth_sublist__max_write l k (some v) ⟨hk.1,by omega⟩,hl]
    simp only [List.append_assoc,List.singleton_append]
  rw [he]
  cancel


private theorem expose_some (x k v : Int) :
    intArray.mixedstoreA x k (some v) |-- ((x + k * sizeof(INT)) # Int |-> v) := by
  exact naive_C_Rules.toContext.derivable1_refl _

private theorem expose_none (x k : Int) :
    intArray.mixedstoreA x k none |-- intArray.undef_seg x k (k+1) := by
  exact intArray.undef_seg_single x k

private theorem cell_properties (x v : Int) :
    (x # Int |-> v) |-- “(isvalidptr_int x ∧ v ≤ Int.max_signed ∧ v ≥ Int.min_signed)” := by
  exact naive_C_Rules.toContext.derivable1_andp_elim1 _ _


theorem proof_of_longest_common_sequence_entail_wit_1 : longest_common_sequence_entail_wit_1 := by
  unfold longest_common_sequence_entail_wit_1
  right
  intro n_pre ys xs PreH1 PreH2 PreH3 PreH4
  let table_pre : Int := &("table")
  have hp := lcsn_column_progress_zero__column_init_update n_pre PreH1
  have hsq := row_bounds n_pre 0 PreH1 ⟨by omega,by omega⟩
  have hcap : 0 ≤ (n_pre+1)*(n_pre+1) ∧ (n_pre+1)*(n_pre+1) ≤ 1002001 := by
    constructor
    · positivity
    · have h := Int.mul_le_mul_of_nonneg_left (show n_pre+1 ≤ 1001 by omega) (show 0 ≤ n_pre+1 by omega)
      have h' := Int.mul_le_mul_of_nonneg_right (show n_pre+1 ≤ 1001 by omega) (show (0 : Int) ≤ 1001 by decide)
      nlinarith
  Exists (List.replicate ((n_pre+1)*(n_pre+1)).toNat (none : Option Int))
    (List.replicate ((n_pre+1)*(n_pre+1)).toNat (0 : Int))
  split_pure_spatial
  · sep_apply (intArray.undef_full_split_to_undef_seg table_pre ((n_pre+1)*(n_pre+1)) 1002001 hcap)
    sep_apply (intArray.undef_seg_to_undef_full table_pre 0 ((n_pre+1)*(n_pre+1)))
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    sep_apply (intArray.undef_full_to_mixed_full table_pre ((n_pre+1)*(n_pre+1)))
    cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength, List.length_replicate, Int.ofNat_eq_coe, Int.toNat_of_nonneg hcap.1])

theorem proof_of_longest_common_sequence_entail_wit_2_split_goal_1 : longest_common_sequence_entail_wit_2_split_goal_1 := by
  unfold longest_common_sequence_entail_wit_2_split_goal_1
  intro n_pre ys xs mixed_table table_l i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 fresh24 fresh25
  have h := cell_bounds n_pre i 0 (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  omega

theorem proof_of_longest_common_sequence_entail_wit_2 : longest_common_sequence_entail_wit_2 := by
  unfold longest_common_sequence_entail_wit_2
  right
  intro n_pre ys xs mixed_table table_l i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 fresh24 fresh25
  have h := cell_bounds n_pre i 0 (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  aggressive_pre_process
  all_goals try dump_pre_spatial
  all_goals first | omega | int_auto

theorem proof_of_longest_common_sequence_entail_wit_3 : longest_common_sequence_entail_wit_3 := by
  unfold longest_common_sequence_entail_wit_3
  right
  intro n_pre ys xs mixed_table_2 table_l_2 i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 fresh22 fresh23
  have hp := lcsn_column_write_progress__column_init_update mixed_table_2 table_l_2 n_pre i stride PreH6 PreH7 ⟨PreH11,PreH5⟩ PreH15
  have hr := row_bounds n_pre (i+1) PreH7 ⟨by omega,by omega⟩
  Exists (replace_Znth (stride*i) (0 : Int) table_l_2)
  rw [PreH6] at hp
  rw [PreH9,PreH6]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Zlength_replace_Znth] at *
    all_goals first | assumption | omega

theorem proof_of_longest_common_sequence_entail_wit_4 : longest_common_sequence_entail_wit_4 := by
  unfold longest_common_sequence_entail_wit_4
  right
  intro n_pre ys xs mixed_table_2 table_l_2 i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 fresh18 fresh19
  have he : i = n_pre+1 := by omega
  have hp := lcsn_column_complete_boundary_start__boundary_phase mixed_table_2 table_l_2 n_pre PreH3 (by simpa [he] using PreH11)
  Exists table_l_2
  rw [PreH5]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Zlength_replace_Znth] at *
    all_goals first | assumption | omega

theorem proof_of_longest_common_sequence_entail_wit_6 : longest_common_sequence_entail_wit_6 := by
  unfold longest_common_sequence_entail_wit_6
  right
  intro n_pre ys xs mixed_table_2 table_l_2 j stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh16 fresh17
  have he : j = n_pre+1 := by omega
  have hp := lcsn_boundaries_complete_rows_start__row_phase_entry xs ys mixed_table_2 table_l_2 n_pre (by simpa [he] using PreH9)
  have hr := row_bounds n_pre 1 PreH3 ⟨by omega,by omega⟩
  Exists table_l_2
  rw [PreH5]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Zlength_replace_Znth] at *
    all_goals first | assumption | omega

theorem proof_of_longest_common_sequence_entail_wit_7 : longest_common_sequence_entail_wit_7 := by
  unfold longest_common_sequence_entail_wit_7
  right
  intro n_pre ys xs mixed_table_2 table_l_2 i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 fresh18 fresh19
  have hp := lcsn_rows_start_row__row_phase_entry xs ys mixed_table_2 table_l_2 n_pre i PreH1 PreH11
  have hr := cell_bounds n_pre i 1 PreH3 ⟨by omega,PreH1⟩ ⟨by omega,by omega⟩
  Exists table_l_2
  rw [PreH5]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Zlength_replace_Znth] at *
    all_goals first | assumption | omega

theorem proof_of_longest_common_sequence_entail_wit_8_split_goal_1 : longest_common_sequence_entail_wit_8_split_goal_1 := by
  unfold longest_common_sequence_entail_wit_8_split_goal_1
  intro n_pre ys xs j i stride mixed_table table_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 fresh29 fresh30
  have h := cell_bounds n_pre (i - 1) (j) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  omega

theorem proof_of_longest_common_sequence_entail_wit_8_split_goal_2 : longest_common_sequence_entail_wit_8_split_goal_2 := by
  unfold longest_common_sequence_entail_wit_8_split_goal_2
  intro n_pre ys xs j i stride mixed_table table_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 fresh29 fresh30
  have h := cell_bounds n_pre (i - 1) (j - 1) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  omega

theorem proof_of_longest_common_sequence_entail_wit_8_split_goal_3 : longest_common_sequence_entail_wit_8_split_goal_3 := by
  unfold longest_common_sequence_entail_wit_8_split_goal_3
  intro n_pre ys xs j i stride mixed_table table_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 fresh29 fresh30
  have h := cell_bounds n_pre (i) (j) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  omega

theorem proof_of_longest_common_sequence_entail_wit_8 : longest_common_sequence_entail_wit_8 := by
  unfold longest_common_sequence_entail_wit_8
  right
  intro n_pre ys xs j i stride mixed_table table_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 fresh29 fresh30
  have h1 := cell_bounds n_pre (i - 1) (j) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have h2 := cell_bounds n_pre (i - 1) (j - 1) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have h3 := cell_bounds n_pre (i) (j) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  aggressive_pre_process
  all_goals try dump_pre_spatial
  all_goals first | omega | int_auto

theorem proof_of_longest_common_sequence_entail_wit_9_1 : longest_common_sequence_entail_wit_9_1 := by
  unfold longest_common_sequence_entail_wit_9_1
  right
  intro n_pre ys xs j i stride mixed_table_2 table_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 fresh17 fresh18 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 fresh51 fresh52
  let table_pre : Int := &("table")
  subst stride
  rw [PreH33] at PreH1 PreH2 PreH3 PreH4 ⊢
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  let diag := (n_pre+1)*(i-1)+(j-1)
  let value := Znth diag table_l_2 0 + 1
  have hdb := cell_bounds n_pre (i-1) (j-1) PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hdc : diag+1 ≤ current := by dsimp [diag,current]; grind
  have hlen := PreH9.1.1
  have hp := lcsn_equal_write_progress__equal_write_and_row_exit xs ys mixed_table_2 table_l_2 n_pre i j
    PreH31 ⟨PreH5,PreH6⟩ ⟨PreH7,PreH8⟩ PreH14 PreH9
  have hprogress : LCSNRowProgress xs ys (replace_Znth current (some value) mixed_table_2)
      (replace_Znth current value table_l_2) n_pre i (j+1) := by
    simpa only [LCSNCellIndex,Int.mul_comm,current,value,diag] using hp
  sep_apply (read_prefix table_pre diag mixed_table_2 (Znth diag table_l_2 0) ⟨hdb.1,by omega⟩ PreH11)
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg table_pre 0 (diag+1) current
    (sublist 0 (diag+1) mixed_table_2) (sublist (diag+1) current mixed_table_2) ⟨by omega,hdc⟩)
  rw [← sublist_split 0 current (diag+1) mixed_table_2 ⟨by omega,by omega⟩ ⟨hdc,by omega⟩]
  sep_apply (join_written_full table_pre current total mixed_table_2 value hcb hlen)
  Exists (replace_Znth current (some value) mixed_table_2) (replace_Znth current value table_l_2)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Zlength_replace_Znth] at *
    all_goals first | trivial | assumption | omega

theorem proof_of_longest_common_sequence_entail_wit_9_2 : longest_common_sequence_entail_wit_9_2 := by
  unfold longest_common_sequence_entail_wit_9_2
  right
  intro n_pre ys xs j i stride mixed_table_2 table_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 fresh18 fresh19 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 fresh51 fresh52
  let table_pre : Int := &("table")
  subst stride
  rw [PreH33] at PreH1 PreH2 PreH3 PreH4 PreH5 ⊢
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  let above := (n_pre+1)*(i-1)+j
  let left := (n_pre+1)*i+(j-1)
  let value := Znth above table_l_2 0
  have hab := cell_bounds n_pre (i-1) j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hlb := cell_bounds n_pre i (j-1) PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hal : above+1 ≤ left := by dsimp [above,left]; grind
  have hlc : left+1 = current := by dsimp [left,current]; omega
  have hlen := PreH10.1.1
  have hp := lcsn_max_write_progress__max_write xs ys mixed_table_2 table_l_2 n_pre i j
    ⟨PreH6,PreH7⟩ ⟨PreH8,PreH9⟩ PreH10 PreH14
  have hmax : max (Znth above table_l_2 0) (Znth left table_l_2 0) = value := by
    exact Int.max_eq_left PreH5
  have hprogress : LCSNRowProgress xs ys (replace_Znth current (some value) mixed_table_2)
      (replace_Znth current value table_l_2) n_pre i (j+1) := by
    have hp' : LCSNRowProgress xs ys
        (replace_Znth current (some (max (Znth above table_l_2 0) (Znth left table_l_2 0))) mixed_table_2)
        (replace_Znth current (max (Znth above table_l_2 0) (Znth left table_l_2 0)) table_l_2) n_pre i (j+1) := by
      simpa only [LCSNCellIndex,Int.mul_comm,current,above,left] using hp
    simpa only [hmax] using hp'
  sep_apply (read_prefix table_pre above mixed_table_2 (Znth above table_l_2 0) ⟨hab.1,by omega⟩ PreH12)
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg table_pre 0 (above+1) left
    (sublist 0 (above+1) mixed_table_2) (sublist (above+1) left mixed_table_2) ⟨by omega,hal⟩)
  rw [← sublist_split 0 left (above+1) mixed_table_2 ⟨by omega,by omega⟩ ⟨hal,by omega⟩]
  sep_apply (read_prefix table_pre left mixed_table_2 (Znth left table_l_2 0) ⟨hlb.1,by omega⟩ PreH13)
  rw [hlc]
  sep_apply (join_written_full table_pre current total mixed_table_2 value hcb hlen)
  Exists (replace_Znth current (some value) mixed_table_2) (replace_Znth current value table_l_2)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Zlength_replace_Znth] at *
    all_goals first | trivial | assumption | omega

theorem proof_of_longest_common_sequence_entail_wit_9_3 : longest_common_sequence_entail_wit_9_3 := by
  unfold longest_common_sequence_entail_wit_9_3
  right
  intro n_pre ys xs j i stride mixed_table_2 table_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 fresh18 fresh19 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 fresh51 fresh52
  let table_pre : Int := &("table")
  subst stride
  rw [PreH33] at PreH1 PreH2 PreH3 PreH4 PreH5 ⊢
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  let above := (n_pre+1)*(i-1)+j
  let left := (n_pre+1)*i+(j-1)
  let value := Znth left table_l_2 0
  have hab := cell_bounds n_pre (i-1) j PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hlb := cell_bounds n_pre i (j-1) PreH31 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hal : above+1 ≤ left := by dsimp [above,left]; grind
  have hlc : left+1 = current := by dsimp [left,current]; omega
  have hlen := PreH10.1.1
  have hp := lcsn_max_write_progress__max_write xs ys mixed_table_2 table_l_2 n_pre i j
    ⟨PreH6,PreH7⟩ ⟨PreH8,PreH9⟩ PreH10 PreH14
  have hmax : max (Znth above table_l_2 0) (Znth left table_l_2 0) = value := by
    exact Int.max_eq_right (Int.le_of_lt PreH5)
  have hprogress : LCSNRowProgress xs ys (replace_Znth current (some value) mixed_table_2)
      (replace_Znth current value table_l_2) n_pre i (j+1) := by
    have hp' : LCSNRowProgress xs ys
        (replace_Znth current (some (max (Znth above table_l_2 0) (Znth left table_l_2 0))) mixed_table_2)
        (replace_Znth current (max (Znth above table_l_2 0) (Znth left table_l_2 0)) table_l_2) n_pre i (j+1) := by
      simpa only [LCSNCellIndex,Int.mul_comm,current,above,left] using hp
    simpa only [hmax] using hp'
  sep_apply (read_prefix table_pre above mixed_table_2 (Znth above table_l_2 0) ⟨hab.1,by omega⟩ PreH12)
  sep_apply (intArray.mixed_seg_merge_to_mixed_seg table_pre 0 (above+1) left
    (sublist 0 (above+1) mixed_table_2) (sublist (above+1) left mixed_table_2) ⟨by omega,hal⟩)
  rw [← sublist_split 0 left (above+1) mixed_table_2 ⟨by omega,by omega⟩ ⟨hal,by omega⟩]
  sep_apply (read_prefix table_pre left mixed_table_2 (Znth left table_l_2 0) ⟨hlb.1,by omega⟩ PreH13)
  rw [hlc]
  sep_apply (join_written_full table_pre current total mixed_table_2 value hcb hlen)
  Exists (replace_Znth current (some value) mixed_table_2) (replace_Znth current value table_l_2)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Zlength_replace_Znth] at *
    all_goals first | trivial | assumption | omega

theorem proof_of_longest_common_sequence_entail_wit_11 : longest_common_sequence_entail_wit_11 := by
  unfold longest_common_sequence_entail_wit_11
  right
  intro n_pre ys xs mixed_table_2 table_l_2 j i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 fresh21 fresh22
  have hp := lcsn_row_finish_progress__equal_write_and_row_exit xs ys mixed_table_2 table_l_2 n_pre i j PreH3 ⟨PreH7,PreH8⟩ ⟨PreH1,PreH10⟩ PreH13
  have hr := row_bounds n_pre (i+1) PreH3 ⟨by omega,by omega⟩
  Exists table_l_2
  rw [PreH5]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Zlength_replace_Znth] at *
    all_goals first | assumption | omega

theorem proof_of_longest_common_sequence_entail_wit_12 : longest_common_sequence_entail_wit_12 := by
  unfold longest_common_sequence_entail_wit_12
  right
  intro n_pre ys xs mixed_table_2 table_l_2 i stride PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 fresh18 fresh19
  let table_pre : Int := &("table")
  subst stride
  have hi := cell_bounds n_pre n_pre n_pre PreH3 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have he : i = n_pre+1 := by omega
  have hp : LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre (n_pre+1) := by simpa [he] using PreH11
  have hres := lcsn_completed_rows_result__finalize_and_return_index xs ys mixed_table_2 table_l_2 n_pre PreH3 hp
  have hm := lcsn_initialized_mixed_full_to_full__finalize_and_return_index xs ys mixed_table_2 table_l_2 n_pre PreH3 hp
  Exists mixed_table_2 table_l_2
  split_pure_spatial
  · rw [hm]
    sep_apply (intArray.mixed_full_to_full table_pre ((n_pre+1)*(n_pre+1)) table_l_2)
    cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Zlength_replace_Znth] at *
    all_goals first | assumption | omega

private theorem scratch_full_tail_undef (x k cap : Int) (l : List Int)
    (hk : 0 ≤ k ∧ k ≤ cap) :
    intArray.full x k l ** intArray.undef_seg x k cap |-- intArray.undef_full x cap := by
  sep_apply (intArray.full_to_undef_full x k l)
  sep_apply (intArray.undef_full_to_undef_seg x k)
  sep_apply (intArray.undef_seg_merge_to_undef_full x 0 k cap hk)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

theorem proof_of_longest_common_sequence_entail_wit_13_split_goal_1 : longest_common_sequence_entail_wit_13_split_goal_1 := by
  pre_process
  have hp := lcsn_table_length_result xs ys n_pre table_l PreH2 PreH4 PreH5 PreH9
  entailer!

theorem proof_of_longest_common_sequence_entail_wit_13_split_goal_spatial : longest_common_sequence_entail_wit_13_split_goal_spatial := by
  pre_process
  apply scratch_full_tail_undef
  constructor
  · positivity
  · have h := Int.mul_le_mul_of_nonneg_left (show n_pre+1 ≤ 1001 by omega) (show 0 ≤ n_pre+1 by omega)
    have h' := Int.mul_le_mul_of_nonneg_right (show n_pre+1 ≤ 1001 by omega) (show (0 : Int) ≤ 1001 by decide)
    nlinarith

theorem proof_of_longest_common_sequence_entail_wit_13 : longest_common_sequence_entail_wit_13 := by
  unfold longest_common_sequence_entail_wit_13
  right
  pre_process
  have hp := lcsn_table_length_result xs ys n_pre table_l PreH2 PreH4 PreH5 PreH9
  have hk : 0 ≤ (n_pre+1)*(n_pre+1) ∧ (n_pre+1)*(n_pre+1) ≤ 1002001 := by
    constructor
    · positivity
    · have h := Int.mul_le_mul_of_nonneg_left (show n_pre+1 ≤ 1001 by omega) (show 0 ≤ n_pre+1 by omega)
      have h' := Int.mul_le_mul_of_nonneg_right (show n_pre+1 ≤ 1001 by omega) (show (0 : Int) ≤ 1001 by decide)
      nlinarith
  sep_apply (scratch_full_tail_undef &("table") ((n_pre+1)*(n_pre+1)) 1002001 table_l hk)
  entailer!

theorem proof_of_longest_common_sequence_which_implies_wit_1 : longest_common_sequence_which_implies_wit_1 := by
  unfold longest_common_sequence_which_implies_wit_1
  right
  intro n_pre ys xs fresh3 fresh4 i j PreH1 PreH2 PreH3 PreH4 fresh11 fresh12 fresh13
  let table : Int := &("table")
  let mixed_table_2 := fresh3
  let table_l_2 := fresh4
  have PreH5 : LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j := fresh11
  have hn : 0 ≤ n_pre := by omega
  have hlen := PreH5.1.1
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j hn ⟨by omega,PreH2⟩ ⟨by omega,PreH4⟩
  let diag := (n_pre+1)*(i-1)+(j-1)
  have hdb := cell_bounds n_pre (i-1) (j-1) hn ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hdc : diag+1 ≤ current := by dsimp [diag,current]; grind
  have hobs := lcsn_diagonal_observation__read_exposure xs ys mixed_table_2 table_l_2 n_pre i j PreH1 PreH2 PreH3 PreH4 PreH5
  rcases hobs with ⟨hcur,hdiag,hval⟩
  have hcur' : Znth current mixed_table_2 none = none := by
    simpa only [LCSNCellUndefined,LCSNCellIndex,Int.mul_comm,current] using hcur
  have hdiag' : Znth diag mixed_table_2 none = some (Znth diag table_l_2 0) := by
    simpa only [LCSNCellInitialized,LCSNCellIndex,Int.mul_comm,diag] using hdiag
  have hval' : 0 ≤ Znth diag table_l_2 0 ∧ Znth diag table_l_2 0 ≤ n_pre := by
    simpa only [LCSNCellIndex,Int.mul_comm,diag] using hval
  dsimp [diag,current] at hcur' hdiag' hval'
  have hsplit := split_mixed_cell table 0 diag total mixed_table_2 ⟨by omega,hdb.1⟩ hdb.2 (by omega)
  rw [sublist_self mixed_table_2 total (by exact hlen.symm)] at hsplit
  sep_apply (intArray.mixed_full_to_mixed_seg table total mixed_table_2)
  sep_apply hsplit
  sep_apply (split_mixed_cell table (diag+1) current total mixed_table_2 ⟨by omega,hdc⟩ hcb.2 (by omega))
  rw [hdiag',hcur']
  sep_apply (expose_none table current)
  sep_apply (expose_some table diag (Znth diag table_l_2 0))
  prop_apply (cell_properties (table+diag*sizeof(INT)) (Znth diag table_l_2 0))
  Intros_p hprop
  split_pure_spatial
  · pre_process
    all_goals cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try dsimp only [mixed_table_2,table_l_2] at *
    all_goals try assumption
    all_goals try omega

theorem proof_of_longest_common_sequence_which_implies_wit_2 : longest_common_sequence_which_implies_wit_2 := by
  unfold longest_common_sequence_which_implies_wit_2
  right
  intro n_pre ys xs fresh3 fresh4 i j PreH1 PreH2 PreH3 PreH4 fresh11 fresh12 fresh13
  let table : Int := &("table")
  let mixed_table_2 := fresh3
  let table_l_2 := fresh4
  have PreH5 : LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j := fresh11
  have hn : 0 ≤ n_pre := by omega
  have hlen := PreH5.1.1
  let total := (n_pre+1)*(n_pre+1)
  let current := (n_pre+1)*i+j
  have hcb := cell_bounds n_pre i j hn ⟨by omega,PreH2⟩ ⟨by omega,PreH4⟩
  let above := (n_pre+1)*(i-1)+j
  let left := (n_pre+1)*i+(j-1)
  have hab := cell_bounds n_pre (i-1) j hn ⟨by omega,by omega⟩ ⟨by omega,PreH4⟩
  have hlb := cell_bounds n_pre i (j-1) hn ⟨by omega,PreH2⟩ ⟨by omega,by omega⟩
  have hal : above+1 ≤ left := by dsimp [above,left]; grind
  have hlc : left+1 = current := by dsimp [left,current]; omega
  have hobs := lcsn_neighbor_observations__read_exposure xs ys mixed_table_2 table_l_2 n_pre i j PreH1 PreH2 PreH3 PreH4 PreH5
  rcases hobs with ⟨hcur,ha,hl⟩
  have hcur' : Znth current mixed_table_2 none = none := by
    simpa only [LCSNCellUndefined,LCSNCellIndex,Int.mul_comm,current] using hcur
  have ha' : Znth above mixed_table_2 none = some (Znth above table_l_2 0) := by
    simpa only [LCSNCellInitialized,LCSNCellIndex,Int.mul_comm,above] using ha
  have hl' : Znth left mixed_table_2 none = some (Znth left table_l_2 0) := by
    simpa only [LCSNCellInitialized,LCSNCellIndex,Int.mul_comm,left] using hl
  dsimp [above,left,current] at hcur' ha' hl'
  have hsplit := split_mixed_cell table 0 above total mixed_table_2 ⟨by omega,hab.1⟩ hab.2 (by omega)
  rw [sublist_self mixed_table_2 total (by exact hlen.symm)] at hsplit
  sep_apply (intArray.mixed_full_to_mixed_seg table total mixed_table_2)
  sep_apply hsplit
  sep_apply (split_mixed_cell table (above+1) left total mixed_table_2 ⟨by omega,hal⟩ hlb.2 (by omega))
  sep_apply (split_mixed_cell table (left+1) current total mixed_table_2 ⟨by omega,by omega⟩ hcb.2 (by omega))
  rw [ha',hl',hcur',hlc]
  rw [Zsublist_nil mixed_table_2 current current (by omega)]
  sep_apply ((intArray.mixed_seg_empty table current current).1)
  Intros_p he
  sep_apply (expose_none table current)
  sep_apply (expose_some table above (Znth above table_l_2 0))
  sep_apply (expose_some table left (Znth left table_l_2 0))
  prop_apply (cell_properties (table+above*sizeof(INT)) (Znth above table_l_2 0))
  Intros_p haprop
  prop_apply (cell_properties (table+left*sizeof(INT)) (Znth left table_l_2 0))
  Intros_p hlprop
  split_pure_spatial
  · pre_process
    all_goals cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try dsimp only [mixed_table_2,table_l_2] at *
    all_goals try assumption
    all_goals try omega

theorem proof_of_longest_common_sequence_entail_wit_5 : longest_common_sequence_entail_wit_5 := by
  unfold longest_common_sequence_entail_wit_5
  right
  pre_process
  have hp := lcsn_boundary_write_progress__boundary_phase mixed_table_2 table_l_2 n_pre j ⟨PreH7,PreH1⟩ PreH9
  Exists (replace_Znth j (0 : Int) table_l_2)
  rw [PreH5]
  entailer!
  all_goals first | exact hp | (simp only [Zlength_replace_Znth]; assumption)

theorem proof_of_longest_common_sequence_entail_wit_10 : longest_common_sequence_entail_wit_10 := by
  unfold longest_common_sequence_entail_wit_10
  right
  pre_process
  Exists table_l_2
  rw [PreH4]
  entailer!

end SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_proof_manual
