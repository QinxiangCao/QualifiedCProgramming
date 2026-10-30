import SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_goal
import SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open sieve_of_euler_goal sieve_of_euler_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev intArray := naive_C_Rules.IntArray
attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

theorem proof_of_get_prime_entail_wit_1 : get_prime_entail_wit_1 := by
  unfold get_prime_entail_wit_1
  right
  intro prime0 n_pre PreH1 PreH2 PreH3
  sep_apply (intArray.undef_full_split_to_undef_seg (&("flag")) (n_pre+1) 46341 ⟨by omega, by omega⟩)
  sep_apply (intArray.undef_seg_split_to_undef_seg (&("flag")) 0 2 (n_pre+1) ⟨by omega, by omega⟩)
  split_pure_spatial
  · cancel
  · dump_pre_spatial; rfl

theorem proof_of_get_prime_entail_wit_2 : get_prime_entail_wit_2 := by
  unfold get_prime_entail_wit_2
  right
  intro prime0 n_pre flag_init_2 z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    simp only [Zlength_app, Zlength_cons, Zlength_nil]
    omega

theorem proof_of_get_prime_entail_wit_3 : get_prime_entail_wit_3 := by
  unfold get_prime_entail_wit_3
  right
  intro prime0 n_pre flag_init z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hi : z = n_pre+1 := by omega
  subst z
  have hs : EulerInitPrefix n_pre 2 flag_init := by intro k hk; omega
  Exists flag_init
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_get_prime_entail_wit_4 : get_prime_entail_wit_4 := by
  unfold get_prime_entail_wit_4
  right
  intro prime0 n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have old : Legacy.EulerInitPrefix n_pre i flag_l_2 := ⟨PreH8, PreH7⟩
  have hs := init_prefix_math _ _ _ (Legacy.EulerInitPrefix_step__core_invariants n_pre i flag_l_2 PreH1 PreH5 old)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_get_prime_entail_wit_5 : get_prime_entail_wit_5 := by
  unfold get_prime_entail_wit_5
  right
  intro prime0 n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have old : Legacy.EulerInitPrefix n_pre i flag_l_2 := ⟨PreH8, PreH7⟩
  have hs := outer_state_math _ _ _ _ _
    (Legacy.EulerInitPrefix_finish_outer__core_invariants n_pre i flag_l_2 prime0 PreH1 PreH3 PreH9 old)
  subst tot
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_get_prime_entail_wit_6_1 : get_prime_entail_wit_6_1 := by
  unfold get_prime_entail_wit_6_1
  right
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have old := (outer_state_facts n_pre i tot flag_l_2 prime_l_2).mpr
    ⟨PreH10, PreH11, ⟨PreH5, PreH6⟩, ⟨PreH7, PreH8⟩, PreH9⟩
  have hp := Legacy.EulerOuterState_self_inner_start__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 old
  have hs := inner_state_math _ _ _ _ _ _ hp
  have hb := Legacy.EulerOuterState_self_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 old
  simp only [show (1 : Int)-1 = 0 from rfl] at *
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_get_prime_entail_wit_6_2 : get_prime_entail_wit_6_2 := by
  unfold get_prime_entail_wit_6_2
  right
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have old := (outer_state_facts n_pre i tot flag_l_2 prime_l_2).mpr
    ⟨PreH10, PreH11, ⟨PreH5, PreH6⟩, ⟨PreH7, PreH8⟩, PreH9⟩
  have hp := Legacy.EulerOuterState_nonself_inner_start__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 old
  have hs := inner_state_math _ _ _ _ _ _ hp
  have hb := Legacy.EulerOuterState_nonself_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 old
  simp only [show (1 : Int)-1 = 0 from rfl] at *
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_get_prime_entail_wit_7 : get_prime_entail_wit_7 := by
  unfold get_prime_entail_wit_7
  right
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have old := (inner_state_facts n_pre i j tot flag_l_2 prime_l_2).mpr
    ⟨PreH14, PreH15, ⟨PreH5, PreH6⟩, ⟨PreH9, PreH10⟩, ⟨by omega, PreH8⟩, PreH16, PreH11⟩
  have hp := Legacy.EulerInnerState_mark_product__core_invariants n_pre i j tot flag_l_2 prime_l_2
    PreH5 PreH6 PreH9 PreH10 PreH2 old
  have hs := marked_state_math _ _ _ _ _ _ hp
  have hf := (marked_state_facts _ _ _ _ _ _).mp hp
  have hnext := hf.2.2.2.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_get_prime_entail_wit_8 : get_prime_entail_wit_8 := by
  unfold get_prime_entail_wit_8
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hd := (Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).1 PreH1
  have hs := PreH11.2.2.2.2.1 hd
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_get_prime_entail_wit_9 : get_prime_entail_wit_9 := by
  unfold get_prime_entail_wit_9
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have old := (marked_state_facts n_pre i j tot flag_l_2 prime_l_2).mpr
    ⟨PreH14, PreH15, ⟨PreH4, PreH5⟩, ⟨PreH8, PreH9⟩, ⟨by omega, PreH7⟩,
      PreH16, PreH10, PreH17, PreH11⟩
  have hn : ¬ Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hp := old.2.2.2.2.2.2 hn
  have hs := inner_state_math _ _ _ _ _ _ hp
  have hle := hp.2.2.2.2.2.1
  have hb := hp.2.2.2.2.2.2.2.2.2.2.1 (j+1) ⟨by omega, hle⟩
  simp only [Int.add_sub_cancel] at hb
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_get_prime_entail_wit_10 : get_prime_entail_wit_10 := by
  unfold get_prime_entail_wit_10
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> simpa only [Int.add_sub_cancel] using (by assumption)

theorem proof_of_get_prime_entail_wit_11_1 : get_prime_entail_wit_11_1 := by
  unfold get_prime_entail_wit_11_1
  right
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hs := PreH10.2.2.2.2 PreH1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_get_prime_entail_wit_12 : get_prime_entail_wit_12 := by
  unfold get_prime_entail_wit_12
  right
  intro n_pre flag_l prime_l tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hi : i = n_pre+1 := by omega
  have hprefix : PrimePrefixList n_pre tot prime_l := by
    have hp := PreH8.2
    simpa only [hi, Int.add_sub_cancel] using hp
  have hflags : LeastPrimeFlagList n_pre flag_l := by
    intro k hk
    exact (PreH8.1 k hk).1 (by omega)
  have hr : EulerSieveResult n_pre tot flag_l prime_l := ⟨hflags, hprefix⟩
  Exists flag_l
  split_pure_spatial
  · sep_apply (intArray.seg_to_undef_seg (&("flag")) 2 (n_pre+1) flag_l)
    sep_apply (intArray.undef_seg_merge_to_undef_seg (&("flag")) 0 2 (n_pre+1) ⟨by omega, by omega⟩)
    sep_apply (intArray.undef_seg_merge_to_undef_full (&("flag")) 0 (n_pre+1) 46341 ⟨by omega, by omega⟩)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_get_prime_return_wit_1 : get_prime_return_wit_1 := by
  unfold get_prime_return_wit_1
  right
  intro n_pre flag_out prime_out_2 tot PreH1 PreH2 PreH3
  have hp := PreH3.2
  Exists tot
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp only [Zlength_replace_Znth, Zlength_app, Zlength_cons, Zlength_nil]; omega)

end SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_proof_manual
