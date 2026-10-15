import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P055_276D_little_girl_and_maximum_xor_goal P055_276D_little_girl_and_maximum_xor_lib MaxMinLib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro r l h1 h2 h3 h4
  exact ⟨rfl,fun k hk => False.elim (by omega)⟩

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro r l h1 h2 h3 h4
  apply lxor_u64_bound__bit_scan_transitions l r
  · change 0≤l ∧ l<18446744073709551616
    omega
  · change 0≤r ∧ r<18446744073709551616
    omega

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro r l h1 h2 h3 h4
  have hh := xor_nonneg l r (by omega) (by omega)
  omega

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro r l h1 h2 h3 h4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 r l h1 h2 h3 h4
      | exact proof_of_solver_entail_wit_1_split_goal_2 r l h1 h2 h3 h4
      | exact proof_of_solver_entail_wit_1_split_goal_3 r l h1 h2 h3 h4

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact (highest_bit_scan_zero_step__bit_scan_transitions l r x b
    ⟨h5,by change x<18446744073709551616; omega⟩ ⟨h7,h8⟩ h9 h1).2

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hh := (highest_bit_scan_zero_step__bit_scan_transitions l r x b
    ⟨h5,by change x<18446744073709551616; omega⟩ ⟨h7,h8⟩ h9 h1).1
  omega

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9
      | exact proof_of_solver_entail_wit_2_split_goal_2 r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hm : unsigned_last_nbits (Z.lnot 0) 64=Z.pow 2 (63+1)-1 := by decide
  rw [hm]
  subst b
  exact interval_max_xor_from_scan__interval_maximum l r x 63 ⟨by omega,h4⟩ ⟨by omega,h7⟩ ⟨by omega,by omega⟩ h10 h2

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_1_split_goal_1 r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

private theorem mask_exact (b : Int) (hb : 0≤b ∧ b<63) :
    unsigned_last_nbits (unsigned_last_nbits (Z.shiftl 1 (b+1)) 64-1) 64=Z.pow 2 (b+1)-1 := by
  lift b to Nat using hb.1
  have hn : b+1<64 := by omega
  have hp : 0<(2:Int)^(b+1) := pow_pos (by omega) _
  have hlt : (2:Int)^(b+1)<(2:Int)^64 := pow_lt_pow_right₀ (by omega) hn
  have he : Z.shiftl 1 ((b:Int)+1)=(2:Int)^(b+1) := by
    change (1:Int) <<< (b+1)=(2:Int)^(b+1)
    rw [Int.shiftLeft_eq,one_mul]
  unfold unsigned_last_nbits
  rw [he]
  change (((2:Int)^(b+1)).fmod ((2:Int)^64)-1).fmod ((2:Int)^64)=(2:Int)^(b+1)-1
  rw [Int.fmod_eq_of_lt (by omega) hlt,Int.fmod_eq_of_lt (by omega) (by omega)]

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rw [mask_exact b ⟨h8,by omega⟩]
  exact interval_max_xor_from_scan__interval_maximum l r x b ⟨by omega,h4⟩ ⟨by omega,h7⟩ ⟨h8,h9⟩ h10 h2

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_2_split_goal_1 r l b x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1 := by
  intro r l h1 h2 h3 h4
  have he := (xor_zero_iff l r).mp h1
  subst r
  unfold Spec max_value_of_subset max_object_of_subset
  refine ⟨0,⟨⟨l,l,⟨by omega,by omega⟩,by omega,(P055_276D_little_girl_and_maximum_xor_lib.xor_self l).symm⟩,?_⟩,rfl⟩
  rintro v ⟨a,d,had,hdl,rfl⟩
  have ha : a=l := by omega
  have hd : d=l := by omega
  subst a
  subst d
  change Z.lxor l l≤0
  rw [P055_276D_little_girl_and_maximum_xor_lib.xor_self]

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro r l h1 h2 h3 h4
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_3_split_goal_1 r l h1 h2 h3 h4

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_proof_manual
