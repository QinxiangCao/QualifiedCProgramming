import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_goal
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array

private theorem first_three (values : List Int) (h : 3 ≤ Zlength values) :
    sublist 0 3 values=[Znth 0 values 0,Znth 1 values 0,Znth 2 values 0] := by
  rw [sublist_split 0 3 1 values (by omega) (by omega),show sublist 0 1 values=[Znth 0 values 0] from sublist_single 0 0 values (by omega),
    sublist_split 1 3 2 values (by omega) (by omega),show sublist 1 2 values=[Znth 1 values 0] from sublist_single 0 1 values (by omega),show sublist 2 3 values=[Znth 2 values 0] from sublist_single 0 2 values (by omega)]
  rfl

private theorem two_cells (out a b : Int) :
    (out # Int64 |-> a) ** ((out+8) # Int64 |-> b) |-- int64Array.full out 2 [a,b] := by
  have hu : int64Array.full out 2 [a,b] =
      ((out # Int64 |-> a) ** (((out+8) # Int64 |-> b) ** int64Array.seg out 2 2 [])) := by
    change (((out+0*8) # Int64 |-> a) ** (((out+1*8) # Int64 |-> b) ** int64Array.seg out 2 2 [])) = _
    simp only [show sizeof(INT64)=(8 : Int) from rfl,Int.zero_mul,Int.add_zero,Int.one_mul,show (2: Int)*8=16 from rfl]
  rw [hu]
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (int64Array.seg_empty out 2 2)).2)
  Intros
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals solve | assumption | trivial | rfl

private theorem three_cells (out a b c : Int) :
    (out # Int64 |-> a) ** ((out+8) # Int64 |-> b) ** ((out+16) # Int64 |-> c)
      |-- int64Array.seg out 0 3 [a,b,c] := by
  have hu : int64Array.seg out 0 3 [a,b,c] =
      ((out # Int64 |-> a) ** (((out+8) # Int64 |-> b) ** (((out+16) # Int64 |-> c) ** int64Array.seg out 3 3 []))) := by
    change (((out+0*8) # Int64 |-> a) ** (((out+1*8) # Int64 |-> b) ** (((out+2*8) # Int64 |-> c) ** int64Array.seg out 3 3 []))) = _
    simp only [show sizeof(INT64)=(8 : Int) from rfl,Int.zero_mul,Int.add_zero,Int.one_mul,show (2: Int)*8=16 from rfl]
  rw [hu]
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (int64Array.seg_empty out 3 3)).2)
  Intros
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals solve | assumption | trivial | rfl

theorem proof_of_llabs_return_wit_1_split_goal_1 : llabs_return_wit_1_split_goal_1 := by
  intro x_pre PreH1 PreH2 PreH3
  rw [← Z.abs_neg]
  exact ((Z.abs_eq_iff (-x_pre)).mpr (by omega)).symm

theorem proof_of_llabs_return_wit_1 : llabs_return_wit_1 := by
  unfold llabs_return_wit_1
  right
  intro x_pre PreH1 PreH2 PreH3
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    all_goals first
      | exact proof_of_llabs_return_wit_1_split_goal_1 x_pre PreH1 PreH2 PreH3

theorem proof_of_llabs_return_wit_2_split_goal_1 : llabs_return_wit_2_split_goal_1 := by
  intro x_pre PreH1 PreH2 PreH3
  exact ((Z.abs_eq_iff x_pre).mpr PreH1).symm

theorem proof_of_llabs_return_wit_2 : llabs_return_wit_2 := by
  unfold llabs_return_wit_2
  right
  intro x_pre PreH1 PreH2 PreH3
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    all_goals first
      | exact proof_of_llabs_return_wit_2_split_goal_1 x_pre PreH1 PreH2 PreH3

theorem proof_of_gcdll_entail_wit_2_split_goal_1 : gcdll_entail_wit_2_split_goal_1 := by
  intro a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  unfold GcdValue at *
  rw [Z.gcd_comm b (Z.rem a b),Z.gcd_rem a b PreH6,Z.gcd_comm b a]
  exact PreH5

theorem proof_of_gcdll_entail_wit_2_split_goal_2 : gcdll_entail_wit_2_split_goal_2 := by
  intro a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hr := Z.rem_bound_pos_pos a b (by omega) (by omega)
  omega

theorem proof_of_gcdll_entail_wit_2_split_goal_3 : gcdll_entail_wit_2_split_goal_3 := by
  intro a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hr := Z.rem_bound_pos_pos a b (by omega) (by omega)
  omega

theorem proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2 := by
  unfold gcdll_entail_wit_2
  right
  intro a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_gcdll_entail_wit_2_split_goal_1 a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | exact proof_of_gcdll_entail_wit_2_split_goal_2 a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | exact proof_of_gcdll_entail_wit_2_split_goal_3 a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6

theorem proof_of_gcdll_return_wit_1_split_goal_1 : gcdll_return_wit_1_split_goal_1 := by
  intro a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  subst b
  unfold GcdValue at *
  rw [Z.gcd_0_r,(Z.abs_eq_iff a).mpr PreH1] at PreH6
  exact PreH6

theorem proof_of_gcdll_return_wit_1 : gcdll_return_wit_1 := by
  unfold gcdll_return_wit_1
  right
  intro a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    all_goals first
      | exact proof_of_gcdll_return_wit_1_split_goal_1 a_pre b_pre b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7

theorem proof_of_pair_fill_safety_wit_2_split_goal_1 : pair_fill_safety_wit_2_split_goal_1 := by
  intro a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  left; omega

theorem proof_of_pair_fill_safety_wit_2_split_goal_2 : pair_fill_safety_wit_2_split_goal_2 := by
  intro a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  unfold GcdValue at PreH1
  rw [PreH1,PreH2,PreH3]
  have hg := gcd_abs_positive__pair_fill a_pre b_pre PreH6 PreH9
  omega

theorem proof_of_pair_fill_safety_wit_2 : pair_fill_safety_wit_2 := by
  unfold pair_fill_safety_wit_2
  right
  intro a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact proof_of_pair_fill_safety_wit_2_split_goal_1 a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_pair_fill_safety_wit_2_split_goal_2 a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_pair_fill_safety_wit_4_split_goal_1 : pair_fill_safety_wit_4_split_goal_1 := by
  intro a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  left; omega

theorem proof_of_pair_fill_safety_wit_4_split_goal_2 : pair_fill_safety_wit_4_split_goal_2 := by
  intro a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  unfold GcdValue at PreH1
  rw [PreH1,PreH2,PreH3]
  have hg := gcd_abs_positive__pair_fill a_pre b_pre PreH6 PreH9
  omega

theorem proof_of_pair_fill_safety_wit_4 : pair_fill_safety_wit_4 := by
  unfold pair_fill_safety_wit_4
  right
  intro a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact proof_of_pair_fill_safety_wit_4_split_goal_1 a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_pair_fill_safety_wit_4_split_goal_2 a_pre b_pre out_pre retval_2 retval_3 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_pair_fill_return_wit_1 : pair_fill_return_wit_1 := by
  left
  intro a_pre b_pre out_pre retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  Exists [Z.quot b_pre retval_3,Z.quot (-a_pre) retval_3]
  simp only [show sizeof(INT64)=(8 : Int) from rfl,Int.zero_mul,Int.add_zero,Int.one_mul,show (2: Int)*8=16 from rfl]
  sep_apply_right (two_cells out_pre (Z.quot b_pre retval_3) (Z.quot (-a_pre) retval_3))
  split_pure_spatial
  · Intros
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals assumption
  · dump_pre_spatial
    rw [PreH1,PreH2,PreH3]
    exact pair_output_prefix__pair_fill a_pre b_pre ⟨PreH4,PreH5⟩ PreH6 ⟨PreH7,PreH8⟩ PreH9

theorem proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_1 : pair_fill_partial_solve_wit_3_pure_split_goal_1 := by
  intro a_pre b_pre out_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have ha := (Z.abs_le_iff a_pre 10000).mpr (by omega)
  have hb := (Z.abs_le_iff b_pre 10000).mpr (by omega)
  have han := (show 0 < Z.abs a_pre from Int.natCast_pos.mpr (Int.natAbs_pos.mpr PreH9))
  have hbn := (show 0 < Z.abs b_pre from Int.natCast_pos.mpr (Int.natAbs_pos.mpr PreH12))
  omega

theorem proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_2 : pair_fill_partial_solve_wit_3_pure_split_goal_2 := by
  intro a_pre b_pre out_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have ha := (Z.abs_le_iff a_pre 10000).mpr (by omega)
  have hb := (Z.abs_le_iff b_pre 10000).mpr (by omega)
  have han := (show 0 < Z.abs a_pre from Int.natCast_pos.mpr (Int.natAbs_pos.mpr PreH9))
  have hbn := (show 0 < Z.abs b_pre from Int.natCast_pos.mpr (Int.natAbs_pos.mpr PreH12))
  omega

theorem proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_3 : pair_fill_partial_solve_wit_3_pure_split_goal_3 := by
  intro a_pre b_pre out_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have ha := (Z.abs_le_iff a_pre 10000).mpr (by omega)
  have hb := (Z.abs_le_iff b_pre 10000).mpr (by omega)
  have han := (show 0 < Z.abs a_pre from Int.natCast_pos.mpr (Int.natAbs_pos.mpr PreH9))
  have hbn := (show 0 < Z.abs b_pre from Int.natCast_pos.mpr (Int.natAbs_pos.mpr PreH12))
  omega

theorem proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_4 : pair_fill_partial_solve_wit_3_pure_split_goal_4 := by
  intro a_pre b_pre out_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have ha := (Z.abs_le_iff a_pre 10000).mpr (by omega)
  have hb := (Z.abs_le_iff b_pre 10000).mpr (by omega)
  have han := (show 0 < Z.abs a_pre from Int.natCast_pos.mpr (Int.natAbs_pos.mpr PreH9))
  have hbn := (show 0 < Z.abs b_pre from Int.natCast_pos.mpr (Int.natAbs_pos.mpr PreH12))
  omega

theorem proof_of_pair_fill_partial_solve_wit_3_pure : pair_fill_partial_solve_wit_3_pure := by
  unfold pair_fill_partial_solve_wit_3_pure
  right
  intro a_pre b_pre out_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pures
  all_goals first
    | exact proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_1 a_pre b_pre out_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    | exact proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_2 a_pre b_pre out_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    | exact proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_3 a_pre b_pre out_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    | exact proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_4 a_pre b_pre out_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1 := by
  intro values a_pre n_pre b_pre start x y z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hx := PreH6 0 (by omega)
  have hz := PreH6 2 (by omega)
  dump_pre_spatial
  change ((x + z) ≠ (-9223372036854775808))
  omega

theorem proof_of_solver_safety_wit_19 : solver_safety_wit_19 := by
  unfold solver_safety_wit_19
  right
  intro values a_pre n_pre b_pre start x y z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  all_goals first
    | exact proof_of_solver_safety_wit_19_split_goal_1 values a_pre n_pre b_pre start x y z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1 := by
  intro values a_pre n_pre b_pre start x y z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hx := PreH6 0 (by omega)
  have hz := PreH6 2 (by omega)
  dump_pre_spatial
  change ((x + z) <= 9223372036854775807)
  omega

theorem proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2 := by
  intro values a_pre n_pre b_pre start x y z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hx := PreH6 0 (by omega)
  have hz := PreH6 2 (by omega)
  dump_pre_spatial
  change ((-9223372036854775808) <= (x + z))
  omega

theorem proof_of_solver_safety_wit_20 : solver_safety_wit_20 := by
  unfold solver_safety_wit_20
  right
  intro values a_pre n_pre b_pre start x y z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_20_split_goal_1 values a_pre n_pre b_pre start x y z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_solver_safety_wit_20_split_goal_2 values a_pre n_pre b_pre start x y z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro values n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  by_cases h : n_pre=2
  · exact False.elim (PreH9 (by rw [h]; rfl))
  · omega

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro values n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 values n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro values n_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  exact PreH10

theorem proof_of_solver_entail_wit_2_split_goal_spatial : solver_entail_wit_2_split_goal_spatial := by
  intro values n_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hn : (n_pre-1).toNat=2+(n_pre-3).toNat := by omega
  unfold SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z
  rw [hn]
  simp only [List.replicate_add,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,Int.zero_mul,Int.add_zero,Int.one_mul,show (2: Int)*8=16 from rfl]
  change int64Array.mixed_seg b_pre 1 n_pre (None :: Some (Znth 1 values (0 : Int)) :: List.replicate (n_pre-3).toNat None) ** (b_pre # Int64 |-> Znth 1 values (0 : Int)) |-- _
  have hu : int64Array.mixed_seg b_pre 1 n_pre (None :: Some (Znth 1 values (0 : Int)) :: List.replicate (n_pre-3).toNat None) =
    (((b_pre+8) # Int64 |->_) ** (((b_pre+16) # Int64 |-> Znth 1 values (0 : Int)) ** int64Array.mixed_seg b_pre 3 n_pre (List.replicate (n_pre-3).toNat None))) := rfl
  rw [hu]
  sep_apply (int64Array.mixed_seg_to_undef_seg b_pre 3 n_pre (List.replicate (n_pre-3).toNat None))
  have hs0 := int64Array.seg_single b_pre 0 (Znth 1 values (0 : Int))
  change (b_pre+0*8 # Int64 |-> Znth 1 values (0 : Int)) |-- int64Array.seg b_pre 0 1 [Znth 1 values (0 : Int)] at hs0
  simp only [Int.zero_mul,Int.add_zero] at hs0
  sep_apply hs0
  have hs1 := int64Array.undef_seg_single b_pre 1
  change ((b_pre+8) # Int64 |->_) |-- int64Array.undef_seg b_pre 1 2 at hs1
  sep_apply hs1
  have hs2 := int64Array.seg_single b_pre 2 (Znth 1 values (0 : Int))
  change ((b_pre+16) # Int64 |-> Znth 1 values (0 : Int)) |-- int64Array.seg b_pre 2 3 [Znth 1 values (0 : Int)] at hs2
  sep_apply hs2
  cancel

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro values n_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · exact proof_of_solver_entail_wit_2_split_goal_spatial values n_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_solver_entail_wit_2_split_goal_1 values n_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1 := by
  left
  intro values a_pre n_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hx := PreH7 0 (by omega)
  have hy := PreH7 1 (by omega)
  have hz := PreH7 2 (by omega)
  have hsub := first_three values (by omega)
  have hp : OutputPrefix (sublist 0 3 values) [Znth 2 values (0 : Int),Znth 2 values (0 : Int),-(Znth 0 values (0 : Int)+Znth 1 values (0 : Int))] 10000 := by
    rw [hsub]
    apply output_prefix_three_case1__solver_initialization
    all_goals omega
  have hm := Z.rem_bound_pos_pos n_pre 2 (by omega) (by omega)
  Exists [Znth 2 values (0 : Int),Znth 2 values (0 : Int),-(Znth 0 values (0 : Int)+Znth 1 values (0 : Int))]
  simp only [show sizeof(INT64)=(8 : Int) from rfl,Int.zero_mul,Int.add_zero,Int.one_mul,show (2: Int)*8=16 from rfl]
  sep_apply_right (three_cells b_pre (Znth 2 values (0 : Int)) (Znth 2 values (0 : Int)) (-(Znth 0 values (0 : Int)+Znth 1 values (0 : Int))))
  split_pure_spatial
  · Intros
    split_pure_spatial
    · simp only [show (1+1+1 : Int)=3 from rfl]; cancel
    · split_pures <;> dump_pre_spatial
      all_goals assumption
  · split_pures <;> dump_pre_spatial
    all_goals solve | assumption | omega | trivial | exact hp | change Z.rem n_pre 2=1; omega

theorem proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2 := by
  left
  intro values a_pre n_pre b_pre start x y z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hx := PreH6 0 (by omega)
  have hy := PreH6 1 (by omega)
  have hz := PreH6 2 (by omega)
  have hsub := first_three values (by omega)
  have hp : OutputPrefix (sublist 0 3 values) [y,-(x+z),y] 10000 := by
    rw [hsub]
    rw [← PreH7,← PreH8,← PreH9]
    apply output_prefix_three_case2__solver_initialization
    all_goals omega
  have hm := Z.rem_bound_pos_pos n_pre 2 (by omega) (by omega)
  Exists [y,-(x+z),y]
  simp only [show (1+1 : Int)=2 from rfl,List.cons_append,List.nil_append]
  sep_apply (int64Array.seg_merge_to_seg b_pre 0 2 3 [y,-(x+z)] [y] (by omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals solve | assumption | omega | trivial | exact hp | change Z.rem n_pre 2=1; omega

theorem proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3 := by
  left
  intro values a_pre n_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hx := PreH8 0 (by omega)
  have hy := PreH8 1 (by omega)
  have hz := PreH8 2 (by omega)
  have hsub := first_three values (by omega)
  have hp : OutputPrefix (sublist 0 3 values) [-(Znth 1 values (0 : Int)+Znth 2 values (0 : Int)),Znth 0 values (0 : Int),Znth 0 values (0 : Int)] 10000 := by
    rw [hsub]
    apply output_prefix_three_case3__solver_initialization
    all_goals omega
  have hm := Z.rem_bound_pos_pos n_pre 2 (by omega) (by omega)
  Exists [-(Znth 1 values (0 : Int)+Znth 2 values (0 : Int)),Znth 0 values (0 : Int),Znth 0 values (0 : Int)]
  have hn : n_pre.toNat=3+(n_pre-3).toNat := by omega
  unfold SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z
  rw [hn]
  simp only [List.replicate_add,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append]
  have hu : int64Array.mixed_full b_pre n_pre (Some (-(Znth 1 values (0 : Int)+Znth 2 values (0 : Int))) :: Some (Znth 0 values (0 : Int)) :: Some (Znth 0 values (0 : Int)) :: List.replicate (n_pre-3).toNat None) =
    ((b_pre # Int64 |-> -(Znth 1 values (0 : Int)+Znth 2 values (0 : Int))) ** (((b_pre+8) # Int64 |-> Znth 0 values (0 : Int)) ** (((b_pre+16) # Int64 |-> Znth 0 values (0 : Int)) ** int64Array.mixed_seg b_pre 3 n_pre (List.replicate (n_pre-3).toNat None)))) := by
    change (((b_pre+0*8) # Int64 |-> -(Znth 1 values (0 : Int)+Znth 2 values (0 : Int))) ** (((b_pre+1*8) # Int64 |-> Znth 0 values (0 : Int)) ** (((b_pre+2*8) # Int64 |-> Znth 0 values (0 : Int)) ** int64Array.mixed_seg b_pre 3 n_pre (List.replicate (n_pre-3).toNat None)))) = _
    simp only [show sizeof(INT64)=(8 : Int) from rfl,Int.zero_mul,Int.add_zero,Int.one_mul,show (2: Int)*8=16 from rfl]
  change int64Array.mixed_full b_pre n_pre (Some (-(Znth 1 values (0 : Int)+Znth 2 values (0 : Int))) :: Some (Znth 0 values (0 : Int)) :: Some (Znth 0 values (0 : Int)) :: List.replicate (n_pre-3).toNat None) ** intArray.full a_pre n_pre values |-- _
  rw [hu]
  sep_apply (int64Array.mixed_seg_to_undef_seg b_pre 3 n_pre (List.replicate (n_pre-3).toNat None))
  sep_apply (three_cells b_pre (-(Znth 1 values (0 : Int)+Znth 2 values (0 : Int))) (Znth 0 values (0 : Int)) (Znth 0 values (0 : Int)))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals solve | assumption | omega | trivial | exact hp | change Z.rem n_pre 2=1; omega

theorem proof_of_solver_entail_wit_3_4_split_goal_1 : solver_entail_wit_3_4_split_goal_1 := by
  intro values n_pre PreH1 PreH2 PreH3 PreH4 PreH5
  simp [OutputPrefix,sublist,Forall.nil,Zlength,Z.quot]

theorem proof_of_solver_entail_wit_3_4_split_goal_2 : solver_entail_wit_3_4_split_goal_2 := by
  intro values n_pre PreH1 PreH2 PreH3 PreH4 PreH5
  exact PreH3

theorem proof_of_solver_entail_wit_3_4 : solver_entail_wit_3_4 := by
  unfold solver_entail_wit_3_4
  right
  intro values n_pre PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_3_4_split_goal_1 values n_pre PreH1 PreH2 PreH3 PreH4 PreH5
      | exact proof_of_solver_entail_wit_3_4_split_goal_2 values n_pre PreH1 PreH2 PreH3 PreH4 PreH5

theorem proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1 := by
  intro values n_pre written_2 start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact PreH4

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  unfold solver_entail_wit_4_1
  right
  intro values n_pre written_2 start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_1_split_goal_1 values n_pre written_2 start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1 := by
  intro values n_pre written_2 start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact PreH4

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  unfold solver_entail_wit_4_2
  right
  intro values n_pre written_2 start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_2_split_goal_1 values n_pre written_2 start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1 := by
  intro values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  exact PreH5

theorem proof_of_solver_entail_wit_5_1_split_goal_spatial : solver_entail_wit_5_1_split_goal_spatial := by
  intro values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  sep_apply (int64Array.undef_seg_split_to_undef_seg b_pre i (i+2) n_pre (by omega))
  sep_apply (int64Array.undef_seg_to_undef_full b_pre i (i+2))
  simp only [show i+2-i=2 by omega,show int64Array.elementStore.sizeA=sizeof(INT64) from rfl]
  cancel
  exact naive_C_Rules.toContext.derivable1_refl _

theorem proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1 := by
  unfold solver_entail_wit_5_1
  right
  intro values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · exact proof_of_solver_entail_wit_5_1_split_goal_spatial values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_solver_entail_wit_5_1_split_goal_1 values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1 := by
  intro values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  exact PreH5

theorem proof_of_solver_entail_wit_5_2_split_goal_spatial : solver_entail_wit_5_2_split_goal_spatial := by
  intro values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  sep_apply (int64Array.undef_seg_split_to_undef_seg b_pre i (i+2) n_pre (by omega))
  sep_apply (int64Array.undef_seg_to_undef_full b_pre i (i+2))
  simp only [show i+2-i=2 by omega,show int64Array.elementStore.sizeA=sizeof(INT64) from rfl]
  cancel
  exact naive_C_Rules.toContext.derivable1_refl _

theorem proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2 := by
  unfold solver_entail_wit_5_2
  right
  intro values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · exact proof_of_solver_entail_wit_5_2_split_goal_spatial values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_solver_entail_wit_5_2_split_goal_1 values n_pre b_pre written_2 i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1 := by
  left
  intro values a_pre n_pre b_pre written_2 start i pair_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hp := output_prefix_append_pair__loop_extension values written_2 pair_out (Z.quot (10000*start) 3) i (by omega) (by omega) PreH12 PreH1
  have hm : Z.rem (i+2-start) 2=0 := by
    simp only [Z.rem,Int.tmod_eq_emod_of_nonneg (by omega : 0≤i-start)] at PreH11
    simp only [Z.rem,Int.tmod_eq_emod_of_nonneg (by omega : 0≤i+2-start)]
    omega
  Exists (written_2++pair_out)
  sep_apply (int64Array.full_to_seg (b_pre+i*sizeof(INT64)) 2 pair_out)
  have hshift : int64Array.seg (b_pre+i*sizeof(INT64)) 0 2 pair_out |--
      int64Array.seg b_pre (i+0) (i+2) pair_out :=
    ((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (int64Array.seg_shift b_pre i 0 2 pair_out)).2
  sep_apply hshift
  simp only [Int.add_zero]
  sep_apply (int64Array.seg_merge_to_seg b_pre 0 i (i+2) written_2 pair_out (by omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals solve | assumption | omega | trivial

theorem proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2 := by
  left
  intro values a_pre n_pre b_pre written_2 start i pair_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hp := output_prefix_append_pair__loop_extension values written_2 pair_out (Z.quot (10000*start) 3) i (by omega) (by omega) PreH12 PreH1
  have hm : Z.rem (i+2-start) 2=0 := by
    simp only [Z.rem,Int.tmod_eq_emod_of_nonneg (by omega : 0≤i-start)] at PreH11
    simp only [Z.rem,Int.tmod_eq_emod_of_nonneg (by omega : 0≤i+2-start)]
    omega
  Exists (written_2++pair_out)
  sep_apply (int64Array.full_to_seg (b_pre+i*sizeof(INT64)) 2 pair_out)
  have hshift : int64Array.seg (b_pre+i*sizeof(INT64)) 0 2 pair_out |--
      int64Array.seg b_pre (i+0) (i+2) pair_out :=
    ((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (int64Array.seg_shift b_pre i 0 2 pair_out)).2
  sep_apply hshift
  simp only [Int.add_zero]
  sep_apply (int64Array.seg_merge_to_seg b_pre 0 i (i+2) written_2 pair_out (by omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals solve | assumption | omega | trivial

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  left
  intro values a_pre n_pre b_pre written i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  obtain ⟨he,hspec⟩ := output_prefix_to_spec_by_parity__final_result n_pre values written i start PreH1 PreH2 PreH3 PreH4 (Or.inl PreH6) PreH8 PreH9 PreH10 PreH11 PreH12
  subst i
  Exists written
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (int64Array.undef_seg_empty b_pre n_pre)).1)
  sep_apply (int64Array.seg_to_full b_pre 0 n_pre written)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact hspec

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  left
  intro values a_pre n_pre b_pre written i start PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  obtain ⟨he,hspec⟩ := output_prefix_to_spec_by_parity__final_result n_pre values written i start PreH1 PreH2 PreH3 PreH4 (Or.inr PreH6) PreH8 PreH9 PreH10 PreH11 PreH12
  subst i
  Exists written
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (int64Array.undef_seg_empty b_pre n_pre)).1)
  sep_apply (int64Array.seg_to_full b_pre 0 n_pre written)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact hspec

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_proof_manual
