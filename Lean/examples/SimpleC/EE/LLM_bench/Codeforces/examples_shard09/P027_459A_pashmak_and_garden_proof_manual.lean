import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P027_459A_pashmak_and_garden_goal P027_459A_pashmak_and_garden_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem four_cells (out a b c d : Int) :
    ((out+3*sizeof(INT)) # Int |-> d) ** ((out+2*sizeof(INT)) # Int |-> c) **
    ((out+1*sizeof(INT)) # Int |-> b) ** ((out+0*sizeof(INT)) # Int |-> a) |--
    intArray.full out 4 [a,b,c,d] := by
  have hu : intArray.full out 4 [a,b,c,d] = (
      ((out+0*sizeof(INT)) # Int |-> a) ** (((out+1*sizeof(INT)) # Int |-> b) **
      (((out+2*sizeof(INT)) # Int |-> c) ** (((out+3*sizeof(INT)) # Int |-> d) **
      intArray.seg out 4 4 [])))) := rfl
  rw [hu]
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.seg_empty out 4 4)).2)
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    rfl

theorem proof_of_iabs_return_wit_1_split_goal_1 : iabs_return_wit_1_split_goal_1 := by
  intro x h1 h2 h3
  simp only [Z.abs,Int.ofNat_eq_coe,Int.natCast_natAbs]
  rw [abs_of_nonpos (by omega)]

theorem proof_of_iabs_return_wit_1 : iabs_return_wit_1 := by
  unfold iabs_return_wit_1
  right
  intro x h1 h2 h3
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_iabs_return_wit_1_split_goal_1 x h1 h2 h3

theorem proof_of_iabs_return_wit_2_split_goal_1 : iabs_return_wit_2_split_goal_1 := by
  intro x h1 h2 h3
  simp only [Z.abs,Int.ofNat_eq_coe,Int.natCast_natAbs]
  rw [abs_of_nonneg (by omega)]

theorem proof_of_iabs_return_wit_2 : iabs_return_wit_2 := by
  unfold iabs_return_wit_2
  right
  intro x h1 h2 h3
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_iabs_return_wit_2_split_goal_1 x h1 h2 h3

theorem proof_of_solver_safety_wit_3_split_goal_1 : solver_safety_wit_3_split_goal_1 := by
  intro out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [abs_diff] at h1
  dump_pre_spatial
  change x1+retval≤2147483647
  split at h1 <;> omega

theorem proof_of_solver_safety_wit_3_split_goal_2 : solver_safety_wit_3_split_goal_2 := by
  intro out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [abs_diff] at h1
  dump_pre_spatial
  change -2147483648≤x1+retval
  split at h1 <;> omega

theorem proof_of_solver_safety_wit_3 : solver_safety_wit_3 := by
  unfold solver_safety_wit_3
  right
  intro out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  split_pures
  · exact proof_of_solver_safety_wit_3_split_goal_1 out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  · exact proof_of_solver_safety_wit_3_split_goal_2 out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1 := by
  intro out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [abs_diff] at h1
  dump_pre_spatial
  change y1+retval≤2147483647
  split at h1 <;> omega

theorem proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2 := by
  intro out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [abs_diff] at h1
  dump_pre_spatial
  change -2147483648≤y1+retval
  split at h1 <;> omega

theorem proof_of_solver_safety_wit_12 : solver_safety_wit_12 := by
  unfold solver_safety_wit_12
  right
  intro out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  split_pures
  · exact proof_of_solver_safety_wit_12_split_goal_1 out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  · exact proof_of_solver_safety_wit_12_split_goal_2 out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro y2 x2 y1 x1 retval retval2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  apply no_completion_of_nonaxis_unequal_abs_diffs__final_results x1 y1 x2 y2 h5 h4
  omega

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro y2 x2 y1 x1 retval retval2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_1_split_goal_1 y2 x2 y1 x1 retval retval2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro out y2 x2 y1 x1 retval retval2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
  Exists x1 y2 x2 y1
  sep_apply (four_cells out x1 y2 x2 y1)
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact completes_square_diagonal__final_results x1 y1 x2 y2 ⟨h14,h15⟩ ⟨h16,h17⟩ ⟨h18,h19⟩ ⟨h20,h21⟩ h22 h13 h12 (by omega)

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
  Exists x1 (y1+retval) x2 (y2+retval)
  sep_apply (four_cells out x1 (y1+retval) x2 (y2+retval))
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact completes_square_horizontal__final_results x1 y1 x2 y2 retval ⟨h12,h13⟩ ⟨h14,h15⟩ ⟨h16,h17⟩ ⟨h18,h19⟩ h20 h10 h11 h9

theorem proof_of_solver_return_wit_4 : solver_return_wit_4 := by
  unfold solver_return_wit_4
  right
  intro out y2 x2 y1 x1 retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
  Exists (x1+retval) y1 (x2+retval) y2
  sep_apply (four_cells out (x1+retval) y1 (x2+retval) y2)
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact completes_square_vertical__final_results x1 y1 x2 y2 retval ⟨h11,h12⟩ ⟨h13,h14⟩ ⟨h15,h16⟩ ⟨h17,h18⟩ h19 h10 h9

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_proof_manual
