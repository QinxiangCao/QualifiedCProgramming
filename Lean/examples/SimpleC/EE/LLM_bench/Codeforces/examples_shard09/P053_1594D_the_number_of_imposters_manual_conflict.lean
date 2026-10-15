import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_manual_pop

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
open AUXLib MaxMinLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hr := PreH27 PreH3
  exact scan_conflict_spec__scan_conflict n_pre m_pre comments hs_2 ns_2 ts ws before cs finished (sublist 0 top ks_2) u e c0 c1
    PreH8 ⟨by omega,PreH26⟩ hr.1.1.1 hr.1.1.2 PreH2 PreH1 PreH34 PreH39 PreH40

theorem proof_of_solver_entail_wit_10_1_split_goal_2 : solver_entail_wit_10_1_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hw := (PreH27 PreH3).1.1.2
  have hh := lxor_bit__scan_and_component_closure 0 (Znth e ws 0) (by decide) hw
  omega

theorem proof_of_solver_entail_wit_10_1_split_goal_3 : solver_entail_wit_10_1_split_goal_3 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hw := (PreH27 PreH3).1.1.2
  have hh := lxor_bit__scan_and_component_closure 0 (Znth e ws 0) (by decide) hw
  omega

theorem proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1 := by
  unfold solver_entail_wit_10_1
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_10_1_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
    | exact proof_of_solver_entail_wit_10_1_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
    | exact proof_of_solver_entail_wit_10_1_split_goal_3 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41

theorem proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hr := PreH27 PreH3
  exact scan_conflict_spec__scan_conflict n_pre m_pre comments hs_2 ns_2 ts ws before cs finished (sublist 0 top ks_2) u e c0 c1
    PreH8 ⟨by omega,PreH26⟩ hr.1.1.1 hr.1.1.2 PreH2 PreH1 PreH34 PreH39 PreH40

theorem proof_of_solver_entail_wit_10_2_split_goal_2 : solver_entail_wit_10_2_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hw := (PreH27 PreH3).1.1.2
  have hh := lxor_bit__scan_and_component_closure 1 (Znth e ws 0) (by decide) hw
  omega

theorem proof_of_solver_entail_wit_10_2_split_goal_3 : solver_entail_wit_10_2_split_goal_3 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hw := (PreH27 PreH3).1.1.2
  have hh := lxor_bit__scan_and_component_closure 1 (Znth e ws 0) (by decide) hw
  omega

theorem proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2 := by
  unfold solver_entail_wit_10_2
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_10_2_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
    | exact proof_of_solver_entail_wit_10_2_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
    | exact proof_of_solver_entail_wit_10_2_split_goal_3 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished before ks_2 ns_2 ws ts e c1 c0 top cs u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
