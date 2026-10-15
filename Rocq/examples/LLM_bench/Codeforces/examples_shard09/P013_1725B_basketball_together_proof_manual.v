Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P013_1725B_basketball_together_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P013_1725B_basketball_together_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P013_1725B_basketball_together_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hpower.
  rewrite zdiv_equiv by lia.
  assert (Hdiv_nonnegative : 0 <= d_pre / Znth i sorted 0) by
    (apply Z.div_pos; lia).
  assert (Hdiv_upper : d_pre / Znth i sorted 0 <= d_pre) by
    (apply Z.div_le_upper_bound; nia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hpower.
  rewrite zdiv_equiv by lia.
  assert (Hdiv_nonnegative : 0 <= d_pre / Znth i sorted 0) by
    (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hpower.
  rewrite zdiv_equiv by lia.
  assert (Hdiv_nonnegative : 0 <= d_pre / Znth i sorted 0) by
    (apply Z.div_pos; lia).
  assert (Hdiv_upper : d_pre / Znth i sorted 0 <= d_pre) by
    (apply Z.div_le_upper_bound; nia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH7 i ltac:(lia)) as Hpower.
  rewrite zdiv_equiv by lia.
  assert (Hdiv_nonnegative : 0 <= d_pre / Znth i sorted 0) by
    (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply permutation_preserves_zindexed_bounds__greedy_initialization.
  - exact PreH1.
  - intros i Hi. apply PreH7. rewrite PreH8. exact Hi.
  - split; [lia |].
    rewrite Zlength_correct.
    rewrite <- (Permutation_length PreH1).
    rewrite <- Zlength_correct.
    rewrite <- PreH8.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_correct.
  rewrite <- (Permutation_length PreH1).
  rewrite <- Zlength_correct.
  symmetry.
  exact PreH8.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst wins.
  eapply basketball_greedy_prefix_cutoff_spec__terminal_correctness;
    try eassumption; try lia.
  intros j Hj. specialize (PreH8 j Hj). lia.
  pose proof (PreH8 i ltac:(lia)) as Hipos.
  rewrite Z.quot_div_nonneg in PreH1 by lia.
  unfold TeamNeed. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH8. assumption.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst wins.
  specialize (PreH8 i ltac:(lia)) as [Hpower _].
  rewrite Z.quot_div_nonneg by lia.
  unfold TeamNeed.
  eapply basketball_greedy_prefix_succ__greedy_transition; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst wins.
  specialize (PreH8 i ltac:(lia)) as [Hpower _].
  rewrite Z.quot_div_nonneg by lia.
  assert (Hdiv : 0 <= d_pre / Znth i sorted_2 0) by
    (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst wins.
  assert (i = n_pre) by lia. subst i.
  eapply basketball_greedy_prefix_complete_spec__terminal_correctness;
    try eassumption; try lia.
  intros j Hj. specialize (PreH7 j Hj). lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
