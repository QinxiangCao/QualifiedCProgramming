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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P080_1316E_team_building_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P080_1316E_team_building_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P080_1316E_team_building_lib.
Local Open Scope sac.

Lemma proof_of_popcount_safety_wit_2_split_goal_1 : popcount_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (land_shiftr_one_bit__popcount v 0 ltac:(lia)) as Hbit;
    rewrite Z.shiftr_0_r in Hbit;
    rewrite Hbit;
    destruct (Z.testbit v 0); simpl; lia).
Qed.

Lemma proof_of_popcount_safety_wit_2_split_goal_2 : popcount_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (land_shiftr_one_bit__popcount v 0 ltac:(lia)) as Hbit;
    rewrite Z.shiftr_0_r in Hbit;
    rewrite Hbit;
    destruct (Z.testbit v 0); simpl; lia).
Qed.

Lemma proof_of_popcount_safety_wit_2 : popcount_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_popcount_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_popcount_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_popcount_entail_wit_1_split_goal_1 : popcount_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    unfold BitCountProgress;
    exists 0;
    rewrite Z.shiftr_0_r;
    simpl;
    lia).
Qed.

Lemma proof_of_popcount_entail_wit_1 : popcount_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_popcount_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_popcount_entail_wit_2_split_goal_1 : popcount_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    exact (bitcount_progress_step__popcount v_pre v c
      ltac:(lia) PreH8 PreH7)).
Qed.

Lemma proof_of_popcount_entail_wit_2_split_goal_2 : popcount_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    exact (bitcount_progress_step_bound__popcount v_pre v c
      ltac:(lia) PreH8 PreH7)).
Qed.

Lemma proof_of_popcount_entail_wit_2_split_goal_3 : popcount_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    pose proof (land_shiftr_one_bit__popcount v 0 ltac:(lia)) as Hbit;
    rewrite Z.shiftr_0_r in Hbit;
    rewrite Hbit;
    destruct (Z.testbit v 0); simpl; lia).
Qed.

Lemma proof_of_popcount_entail_wit_2_split_goal_4 : popcount_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    rewrite Z.shiftr_div_pow2 by lia;
    apply Z.div_lt_upper_bound; lia).
Qed.

Lemma proof_of_popcount_entail_wit_2_split_goal_5 : popcount_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(
    rewrite Z.shiftr_div_pow2 by lia;
    apply Z_div_nonneg_nonneg; lia).
Qed.

Lemma proof_of_popcount_entail_wit_2 : popcount_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_popcount_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_popcount_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_popcount_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_popcount_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_popcount_entail_wit_2_split_goal_5.
Qed.

Lemma proof_of_popcount_return_wit_1_split_goal_1 : popcount_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    exact (bitcount_progress_finish__popcount v_pre v c
      ltac:(lia) PreH8 PreH7)).
Qed.

Lemma proof_of_popcount_return_wit_1 : popcount_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_popcount_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sift_people_entail_wit_1_split_goal_1 : sift_people_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  unfold PeopleSiftProgress, PeoplePermutation.
  repeat split; try reflexivity; try assumption.
  left. reflexivity.
Qed.

Lemma proof_of_sift_people_entail_wit_1 : sift_people_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_people_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_sift_people_entail_wit_2_1_split_goal_1 : sift_people_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  unfold PeopleSelectedLargerChild.
  repeat split.
  - right. lia.
  - exact PreH2.
  - intros.
    replace (2 * root + 1 + 1) with (2 * root + 2) by lia.
    replace (2 * root + 1 + 1) with (2 * root + 2) in PreH1 by lia.
    lia.
  - intros.
    replace (2 * root + 1 + 1) with (2 * root + 2) by lia.
    apply Z.le_refl.
Qed.

Lemma proof_of_sift_people_entail_wit_2_1 : sift_people_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_people_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_sift_people_entail_wit_2_2_split_goal_1 : sift_people_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  unfold PeopleSelectedLargerChild.
  repeat split.
  - left. reflexivity.
  - exact PreH2.
  - intros. lia.
  - intros. lia.
Qed.

Lemma proof_of_sift_people_entail_wit_2_2 : sift_people_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_people_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_sift_people_entail_wit_2_3_split_goal_1 : sift_people_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  unfold PeopleSelectedLargerChild.
  repeat split.
  - left. reflexivity.
  - exact PreH3.
  - intros. lia.
  - intros.
    replace (2 * root + 1 + 1) with (2 * root + 2) in PreH1 by lia.
    lia.
Qed.

Lemma proof_of_sift_people_entail_wit_2_3 : sift_people_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_people_entail_wit_2_3_split_goal_1.
Qed.

Lemma proof_of_sift_people_entail_wit_3_split_goal_1 : sift_people_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  eapply people_sift_swap_preserves_progress__sift_transition_exit;
    eauto; lia.
Qed.

Lemma proof_of_sift_people_entail_wit_3_split_goal_2 : sift_people_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(intros).
  unfold PeopleSelectedLargerChild in PreH15.
  destruct PreH15 as [[-> | ->] _]; lia.
Qed.

Lemma proof_of_sift_people_entail_wit_3_split_goal_3 : sift_people_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(intros).
  repeat rewrite ListLib.Zlength_replace_Znth.
  assumption.
Qed.

Lemma proof_of_sift_people_entail_wit_3_split_goal_4 : sift_people_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(intros).
  repeat rewrite ListLib.Zlength_replace_Znth.
  assumption.
Qed.

Lemma proof_of_sift_people_entail_wit_3 : sift_people_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_people_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_sift_people_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_sift_people_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_sift_people_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_sift_people_return_wit_1_split_goal_1 : sift_people_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  unfold PeopleSiftProgress in *.
  tauto.
Qed.

Lemma proof_of_sift_people_return_wit_1_split_goal_2 : sift_people_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  unfold PeopleSiftProgress in *.
  tauto.
Qed.

Lemma proof_of_sift_people_return_wit_1_split_goal_3 : sift_people_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  eapply people_sift_exit_restores_heap__sift_transition_exit.
  - eassumption.
  - right. eexists. split; [eassumption | lia].
Qed.

Lemma proof_of_sift_people_return_wit_1_split_goal_4 : sift_people_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  unfold PeopleSiftProgress in *.
  tauto.
Qed.

Lemma proof_of_sift_people_return_wit_1 : sift_people_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_people_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sift_people_return_wit_1_split_goal_2.
  - Goal_apply proof_of_sift_people_return_wit_1_split_goal_3.
  - Goal_apply proof_of_sift_people_return_wit_1_split_goal_4.
Qed.

Lemma proof_of_sift_people_return_wit_2_split_goal_1 : sift_people_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  unfold PeopleSiftProgress in *.
  tauto.
Qed.

Lemma proof_of_sift_people_return_wit_2_split_goal_2 : sift_people_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  unfold PeopleSiftProgress in *.
  tauto.
Qed.

Lemma proof_of_sift_people_return_wit_2_split_goal_3 : sift_people_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  eapply people_sift_exit_restores_heap__sift_transition_exit.
  - eassumption.
  - left. lia.
Qed.

Lemma proof_of_sift_people_return_wit_2_split_goal_4 : sift_people_return_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  unfold PeopleSiftProgress in *.
  tauto.
Qed.

Lemma proof_of_sift_people_return_wit_2 : sift_people_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_people_return_wit_2_split_goal_1.
  - Goal_apply proof_of_sift_people_return_wit_2_split_goal_2.
  - Goal_apply proof_of_sift_people_return_wit_2_split_goal_3.
  - Goal_apply proof_of_sift_people_return_wit_2_split_goal_4.
Qed.

Lemma proof_of_sort_people_safety_wit_1_split_goal_1 : sort_people_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (0 <= n_pre ÷ 2) by (apply Z.quot_pos; lia).
  assert (n_pre ÷ 2 <= n_pre) by (apply Z.quot_le_upper_bound; lia).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_sort_people_safety_wit_1_split_goal_2 : sort_people_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (0 <= n_pre ÷ 2) by (apply Z.quot_pos; lia).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_sort_people_safety_wit_1 : sort_people_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_people_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_people_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_sort_people_entail_wit_1_split_goal_1 : sort_people_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  rewrite Z.quot_div_nonneg by lia.
  unfold PeopleHeapBuildState.
  split.
  - unfold PeoplePermutation. apply Permutation_refl.
  - unfold PeopleHeapParentsFrom.
    intros child Hchild Hparent.
    pose proof (Z.div_mod n_pre 2 ltac:(lia)) as Hdiv_n.
    pose proof (Z.mod_pos_bound n_pre 2 ltac:(lia)) as Hmod_n.
    pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hdiv_child.
    pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hmod_child.
    exfalso. lia.
Qed.

Lemma proof_of_sort_people_entail_wit_1_split_goal_2 : sort_people_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (0 <= n_pre ÷ 2) by (apply Z.quot_pos; lia).
  lia.
Qed.

Lemma proof_of_sort_people_entail_wit_1 : sort_people_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_people_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_people_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_sort_people_entail_wit_2_split_goal_1 : sort_people_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  unfold PeopleHeapBuildState in PreH10.
  destruct PreH10 as [_ Hparents].
  unfold PeopleHeapOrderedExceptAt, PeopleHeapParentsFrom in *.
  intros child Hchild Hlo Hneq.
  apply Hparents; try lia.
Qed.

Lemma proof_of_sort_people_entail_wit_2 : sort_people_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_people_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_sort_people_entail_wit_3_split_goal_1 : sort_people_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  eapply people_heap_build_step__sort_build; eauto.
Qed.

Lemma proof_of_sort_people_entail_wit_3 : sort_people_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_people_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_sort_people_entail_wit_4_split_goal_1 : sort_people_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  unfold PeopleHeapBuildState in PreH10.
  destruct PreH10 as [Hperm Hparents].
  unfold PeopleHeapSortState.
  repeat split.
  - exact Hperm.
  - replace root with (-1) in Hparents by lia.
    replace (-1 + 1) with 0 in Hparents by lia.
    exact Hparents.
  - replace (n_pre - 1 + 1) with n_pre by lia.
    rewrite <- PreH6.
    rewrite Zsublist_nil by lia.
    constructor.
  - intros left right Hleft Hright. lia.
Qed.

Lemma proof_of_sort_people_entail_wit_4 : sort_people_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_people_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_sort_people_entail_wit_5_split_goal_1 : sort_people_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  now eapply people_heap_extract_cross__sort_extract_final; eauto; lia.
Qed.

Lemma proof_of_sort_people_entail_wit_5_split_goal_2 : sort_people_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  now eapply people_heap_extract_suffix__sort_extract_final; eauto; lia.
Qed.

Lemma proof_of_sort_people_entail_wit_5_split_goal_3 : sort_people_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  now eapply people_heap_extract_except__sort_extract_final; eauto; lia.
Qed.

Lemma proof_of_sort_people_entail_wit_5_split_goal_4 : sort_people_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  destruct PreH10 as [Hparallel _].
  now eapply people_parallel_permutation_swap__sift_transition_exit; eauto; lia.
Qed.

Lemma proof_of_sort_people_entail_wit_5_split_goal_5 : sort_people_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  repeat rewrite Zlength_replace_Znth__sift_transition_exit.
  lia.
Qed.

Lemma proof_of_sort_people_entail_wit_5_split_goal_6 : sort_people_entail_wit_5_split_goal_6.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  repeat rewrite Zlength_replace_Znth__sift_transition_exit.
  lia.
Qed.

Lemma proof_of_sort_people_entail_wit_5 : sort_people_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_people_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_sort_people_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_sort_people_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_sort_people_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_sort_people_entail_wit_5_split_goal_5.
  - Goal_apply proof_of_sort_people_entail_wit_5_split_goal_6.
Qed.

Lemma proof_of_sort_people_entail_wit_6_split_goal_1 : sort_people_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  replace (hi - 1 + 1) with hi in PreH5 by lia.
  refine (people_heap_extract_step__sort_extract_final
    audience_values order_values audience_now_2 order_now_2
    audience_after order_after n_pre hi
    PreH11 PreH12 PreH1 PreH2 ltac:(lia)
    PreH15 PreH3 PreH4 PreH5 PreH17 _).
  intros left right Hleft Hright.
  apply PreH18; lia.
Qed.

Lemma proof_of_sort_people_entail_wit_6 : sort_people_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_people_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_sort_people_return_wit_1_split_goal_1 : sort_people_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  assert (hi = 0) as -> by lia.
  now eapply people_heap_sort_final__sort_extract_final; eauto; lia.
Qed.

Lemma proof_of_sort_people_return_wit_1_split_goal_2 : sort_people_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  destruct PreH10 as [Hparallel _].
  exact Hparallel.
Qed.

Lemma proof_of_sort_people_return_wit_1 : sort_people_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_people_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_people_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_sort_people_partial_solve_wit_1_pure_split_goal_1 : sort_people_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(eauto || lia).
  assert (n_pre ÷ 2 <= n_pre) by
    (apply Z.quot_le_upper_bound; lia).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_sort_people_partial_solve_wit_1_pure : sort_people_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_people_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_1_split_goal_1 : solver_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ p_pre <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ p_pre) 32 = 1 * 2 ^ p_pre).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_1_split_goal_2 : solver_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ p_pre <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ p_pre) 32 = 1 * 2 ^ p_pre).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_1_split_goal_3 : solver_safety_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_1_split_goal_4 : solver_safety_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(auto).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_35_split_goal_1 : solver_safety_wit_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_35_split_goal_2 : solver_safety_wit_35_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_35_split_goal_3 : solver_safety_wit_35_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_35_split_goal_4 : solver_safety_wit_35_split_goal_4.
Proof.
  LLM_pre_process ltac:(auto).
Qed.

Lemma proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_35_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_35_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_35_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_35_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_36_split_goal_1 : solver_safety_wit_36_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_36_split_goal_2 : solver_safety_wit_36_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_36_split_goal_3 : solver_safety_wit_36_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_36_split_goal_4 : solver_safety_wit_36_split_goal_4.
Proof.
  LLM_pre_process ltac:(auto).
Qed.

Lemma proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_36_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_36_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_36_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_36_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_37_split_goal_1 : solver_safety_wit_37_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_37_split_goal_2 : solver_safety_wit_37_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_37_split_goal_3 : solver_safety_wit_37_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_37_split_goal_4 : solver_safety_wit_37_split_goal_4.
Proof.
  LLM_pre_process ltac:(auto).
Qed.

Lemma proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_37_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_37_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_37_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_37_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_38_split_goal_1 : solver_safety_wit_38_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_38_split_goal_2 : solver_safety_wit_38_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_38_split_goal_3 : solver_safety_wit_38_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_38_split_goal_4 : solver_safety_wit_38_split_goal_4.
Proof.
  LLM_pre_process ltac:(auto).
Qed.

Lemma proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_38_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_38_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_38_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_38_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_39_split_goal_1 : solver_safety_wit_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_39_split_goal_2 : solver_safety_wit_39_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_39_split_goal_3 : solver_safety_wit_39_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_39_split_goal_4 : solver_safety_wit_39_split_goal_4.
Proof.
  LLM_pre_process ltac:(auto).
Qed.

Lemma proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_39_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_39_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_39_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_39_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_40_split_goal_1 : solver_safety_wit_40_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_40_split_goal_2 : solver_safety_wit_40_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hpow : 0 <= 2 ^ j <= 128).
  { split.
    - apply Z.pow_nonneg. lia.
    - change 128 with (2 ^ 7).
      apply Z.pow_le_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (1 * 2 ^ j) 32 = 1 * 2 ^ j).
  { apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. lia. }
  rewrite Hsigned.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_40_split_goal_3 : solver_safety_wit_40_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_40_split_goal_4 : solver_safety_wit_40_split_goal_4.
Proof.
  LLM_pre_process ltac:(auto).
Qed.

Lemma proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_40_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_40_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_40_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_40_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_65_split_goal_1 : solver_safety_wit_65_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_65_split_goal_2 : solver_safety_wit_65_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_65_split_goal_3 : solver_safety_wit_65_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_65_split_goal_4 : solver_safety_wit_65_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_65 : solver_safety_wit_65.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_65_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_65_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_65_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_65_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_67_split_goal_1 : solver_safety_wit_67_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_67_split_goal_2 : solver_safety_wit_67_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_67_split_goal_3 : solver_safety_wit_67_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_67_split_goal_4 : solver_safety_wit_67_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_67 : solver_safety_wit_67.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_67_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_67_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_67_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_67_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_69_split_goal_1 : solver_safety_wit_69_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_69_split_goal_2 : solver_safety_wit_69_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_69_split_goal_3 : solver_safety_wit_69_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_69_split_goal_4 : solver_safety_wit_69_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_71_split_goal_1 : solver_safety_wit_71_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_71_split_goal_2 : solver_safety_wit_71_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_71_split_goal_3 : solver_safety_wit_71_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_71_split_goal_4 : solver_safety_wit_71_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_71 : solver_safety_wit_71.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_71_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_71_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_71_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_71_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_73_split_goal_1 : solver_safety_wit_73_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_73_split_goal_2 : solver_safety_wit_73_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_73_split_goal_3 : solver_safety_wit_73_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_73_split_goal_4 : solver_safety_wit_73_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_73 : solver_safety_wit_73.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_73_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_73_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_73_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_73_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_75_split_goal_1 : solver_safety_wit_75_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_75_split_goal_2 : solver_safety_wit_75_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (signed_Lastnbits_range (1 * 2 ^ j) 32 ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_75_split_goal_3 : solver_safety_wit_75_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_75_split_goal_4 : solver_safety_wit_75_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_safety_wit_75 : solver_safety_wit_75.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_75_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_75_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_75_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_75_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply (people_order_bounds__solver_setup aud order_values audience_after
    order_after n_pre); eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply (people_audience_bounds__solver_setup aud order_values audience_after
    order_after n_pre); eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply (sorted_people_state_intro__solver_setup aud order_values
    audience_after order_after n_pre); eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply (skill_concat_length_from_pre__solver_setup aud skill k_pre n_pre
    p_pre __default__List_Z); eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hshape_rec :
    forall (storeA : addr -> Z -> Z -> Assertion) k x lo hi,
      store_undef_array_rec (fun x lo => EX a : Z, storeA x lo a)
        x lo hi k
      |-- EX l : list Z, store_array_rec storeA x lo hi l).
  {
    intros storeA k.
    induction k as [| k IH]; intros x lo hi; simpl.
    - Exists (@nil Z). simpl.
      split_pure_spatial.
      + Intros_p Hlohi. cancel.
      + Intros_p Hlohi. split_pures; dump_pre_spatial; auto.
    - Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      Intros l. Exists (a :: l). simpl. cancel.
  }
  assert (Hshape_full :
    forall x n,
      Int64Array.full_shape x n
      |-- EX l : list Z, Int64Array.full x n l).
  {
    intros x n.
    unfold Int64Array.full_shape, Int64Array.full,
      store_undef_array, store_array.
    apply Hshape_rec.
  }
  sep_apply_l_atomic (Hshape_full dp_pre 128).
  Intros dp_values.
  prop_apply_p (Int64Array.full_Zlength dp_pre 128 dp_values).
  Intros_p Hdp_length.
  assert (Hempty : AllTeamNegInf (sublist 0 0 dp_values)).
  { unfold AllTeamNegInf. rewrite Zsublist_nil by lia. constructor. }
  assert (Hp_cases :
    p_pre = 1 \/ p_pre = 2 \/ p_pre = 3 \/ p_pre = 4 \/
    p_pre = 5 \/ p_pre = 6 \/ p_pre = 7) by lia.
  destruct Hp_cases as
    [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    Exists dp_values order_sorted_2 audience_sorted_2;
    split_pure_spatial.
  all: try (repeat cancel).
  all: split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (-(Z.shiftl 1 60)) with TeamNegInf.
  2: { unfold TeamNegInf. rewrite Z.shiftl_1_l. reflexivity. }
  eapply all_team_neg_inf_replace_extend__solver_setup; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite ListLib.Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (m = full) by lia. subst m.
  rewrite Z.shiftl_1_l in *.
  eapply (bounded_team_dp_zero_bounds__solver_setup dp_values_2 p_pre full);
    eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (m = full) by lia. subst m.
  rewrite Z.shiftl_1_l in *.
  eapply (bounded_team_dp_base_zero__solver_setup aud skill order_sorted_2
    p_pre k_pre dp_values_2 full); eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite ListLib.Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hshape_rec :
    forall (storeA : addr -> Z -> Z -> Assertion) k x lo hi,
      store_undef_array_rec (fun x lo => EX a : Z, storeA x lo a)
        x lo hi k
      |-- EX l : list Z, store_array_rec storeA x lo hi l).
  {
    intros storeA k.
    induction k as [| k IH]; intros x lo hi; simpl.
    - Exists (@nil Z). simpl.
      split_pure_spatial.
      + Intros_p Hlohi. cancel.
      + Intros_p Hlohi. split_pures; dump_pre_spatial; auto.
    - Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      Intros l. Exists (a :: l). simpl. cancel.
  }
  assert (Hshape_full :
    forall x n,
      Int64Array.full_shape x n
      |-- EX l : list Z, Int64Array.full x n l).
  {
    intros x n.
    unfold Int64Array.full_shape, Int64Array.full,
      store_undef_array, store_array.
    apply Hshape_rec.
  }
  sep_apply_l_atomic (Hshape_full ndp_pre 128).
  Intros ndp_values.
  prop_apply_p (Int64Array.full_Zlength ndp_pre 128 ndp_values).
  Intros_p Hndp_length.
  assert (Hempty : AllTeamNegInf (sublist 0 0 ndp_values)).
  { unfold AllTeamNegInf. rewrite Zsublist_nil by lia. constructor. }
  Exists ndp_values dp_values_2 order_sorted_2 audience_sorted_2 aud.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (-(Z.shiftl 1 60)) with TeamNegInf.
  2: { unfold TeamNegInf. rewrite Z.shiftl_1_l. reflexivity. }
  eapply all_team_neg_inf_replace_extend__solver_setup; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite ListLib.Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    specialize (PreH31 q_4 ltac:(lia));
    pose proof (all_team_neg_inf_Znth__solver_row_start
      ndp_values_2 m q_4 0 ltac:(lia) ltac:(lia) PreH26) as Hneg;
    unfold TeamNegInf in Hneg;
    lia).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(apply PreH30; assumption).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(apply PreH29; assumption).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(apply PreH28; assumption).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(apply PreH27; assumption).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_6 : solver_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(
    change (TeamNextRowProgress audience_sorted_2 order_sorted skill
      p_pre k_pre i dp_values_2 ndp_values_2 0);
    eapply team_next_row_empty__solver_row_start with (hi := m);
    [lia | rewrite Z.shiftl_1_l in PreH14; lia | lia | exact PreH26]).
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
  Goal_apply proof_of_solver_entail_wit_8_split_goal_5.
  Goal_apply proof_of_solver_entail_wit_8_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(apply PreH34; assumption).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(apply PreH33; assumption).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(apply PreH32; assumption).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_4 : solver_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(apply PreH31; assumption).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_5 : solver_entail_wit_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(apply PreH30; assumption).
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_9_split_goal_4.
  Goal_apply proof_of_solver_entail_wit_9_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_1 : solver_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec q_8 m) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by
      (rewrite ?ListLib.Zlength_replace_Znth; lia).
    specialize (PreH60 m ltac:(lia)).
    pose proof (PreH56 rank ltac:(lia)) as Hrank_bounds.
    assert (Haud_input : forall chosen,
      ProcessedPerson order_sorted i chosen ->
      0 <= Znth chosen aud_input 0 <= 1000000000).
    {
      intros chosen [step [Hstep ->]].
      unfold SortedPeopleState in PreH53.
      destruct PreH53 as [Haudlen [Horderlen [Hperm [Hinc Hmap]]]].
      specialize (Hmap (Zlength order_sorted - 1 - step) ltac:(lia)).
      specialize (PreH56 (Zlength order_sorted - 1 - step) ltac:(lia)).
      destruct Hmap as [_ Hvalue]. rewrite <- Hvalue. lia.
    }
    assert (Hdpupper_raw :
      Znth m dp_values TeamNegInf <= i * 1000000000).
    {
      eapply (bounded_dp_live_value_upper__solver_role_init
        n_pre p_pre k_pre aud_input __default__List_Z skill order_sorted i
        dp_values m); try eassumption; try lia.
      - rewrite <- Z.shiftl_1_l. lia.
      - intros idx Hidx. specialize (PreH59 idx Hidx). lia.
      - unfold TeamNegInf.
        rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia.
        rewrite <- Z.shiftl_1_l. exact PreH7.
    }
    assert (Hdpupper : Znth m dp_values 0 <= i * 1000000000).
    { rewrite <- (Znth_indep dp_values m TeamNegInf 0) by lia.
      exact Hdpupper_raw. }
    lia.
  - repeat rewrite Znth_replace_Znth_Diff by
      (rewrite ?ListLib.Zlength_replace_Znth; lia).
    apply PreH60. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_2 : solver_entail_wit_11_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  apply PreH59.
  split; lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_3 : solver_entail_wit_11_1_split_goal_3.
Proof. LLM_pre_process ltac:(lia). all: apply PreH58; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_4 : solver_entail_wit_11_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  apply PreH57.
  split; lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_5 : solver_entail_wit_11_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  apply PreH56.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_6 : solver_entail_wit_11_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite replace_Znth_overwrite__solver_role_init.
  pose proof (PreH56 (n_pre - 1 - i) ltac:(split; lia)) as Haudience.
  eapply bounded_team_role_update_init__solver_role_init
    with (used := retval); try eassumption.
  - rewrite <- Z.shiftl_1_l. lia.
  - rewrite <- Z.shiftl_1_l. lia.
  - unfold TeamNegInf.
    rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia.
    rewrite <- Z.shiftl_1_l. exact PreH7.
  - rewrite (Znth_indep ndp_values m TeamNegInf 0) by lia.
    lia.
  - left. repeat split; try lia.
    + rewrite (Znth_indep dp_values m TeamNegInf 0) by lia. lia.
    + repeat rewrite (Znth_indep dp_values m TeamNegInf 0) by lia.
      rewrite PreH34. reflexivity.
    + right. rewrite (Znth_indep dp_values m TeamNegInf 0) by lia.
      rewrite PreH34. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_7 : solver_entail_wit_11_1_split_goal_7.
Proof. LLM_pre_process ltac:(lia).
  repeat rewrite ListLib.Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_4.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_5.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_6.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_1 : solver_entail_wit_11_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec q_8 m) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by lia.
    specialize (PreH60 m ltac:(lia)).
    pose proof (PreH56 rank ltac:(lia)) as Hrank_bounds.
    assert (Haud_input : forall chosen,
      ProcessedPerson order_sorted i chosen ->
      0 <= Znth chosen aud_input 0 <= 1000000000).
    {
      intros chosen [step [Hstep ->]].
      unfold SortedPeopleState in PreH53.
      destruct PreH53 as [Haudlen [Horderlen [Hperm [Hinc Hmap]]]].
      specialize (Hmap (Zlength order_sorted - 1 - step) ltac:(lia)).
      specialize (PreH56 (Zlength order_sorted - 1 - step) ltac:(lia)).
      destruct Hmap as [_ Hvalue]. rewrite <- Hvalue. lia.
    }
    assert (Hdpupper_raw :
      Znth m dp_values TeamNegInf <= i * 1000000000).
    {
      eapply (bounded_dp_live_value_upper__solver_role_init
        n_pre p_pre k_pre aud_input __default__List_Z skill order_sorted i
        dp_values m); try eassumption; try lia.
      - rewrite <- Z.shiftl_1_l. lia.
      - intros idx Hidx. specialize (PreH59 idx Hidx). lia.
      - unfold TeamNegInf.
        rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia.
        rewrite <- Z.shiftl_1_l. exact PreH7.
    }
    assert (Hdpupper : Znth m dp_values 0 <= i * 1000000000).
    { rewrite <- (Znth_indep dp_values m TeamNegInf 0) by lia.
      exact Hdpupper_raw. }
    lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply PreH60. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_2 : solver_entail_wit_11_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  apply PreH59.
  split; lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_3 : solver_entail_wit_11_2_split_goal_3.
Proof. LLM_pre_process ltac:(lia). all: apply PreH58; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_4 : solver_entail_wit_11_2_split_goal_4.
Proof. LLM_pre_process ltac:(lia). all: apply PreH57; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_5 : solver_entail_wit_11_2_split_goal_5.
Proof. LLM_pre_process ltac:(lia). all: apply PreH56; tauto. Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_6 : solver_entail_wit_11_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (PreH56 (n_pre - 1 - i) ltac:(split; lia)) as Haudience.
  eapply bounded_team_role_update_init__solver_role_init
    with (used := retval); try eassumption.
  - rewrite <- Z.shiftl_1_l. lia.
  - rewrite <- Z.shiftl_1_l. lia.
  - unfold TeamNegInf.
    rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia.
    rewrite <- Z.shiftl_1_l. exact PreH7.
  - rewrite (Znth_indep ndp_values m TeamNegInf 0) by lia.
    rewrite <- PreH44. lia.
  - left. repeat split; try lia.
    + rewrite (Znth_indep dp_values m TeamNegInf 0) by lia. lia.
    + repeat rewrite (Znth_indep dp_values m TeamNegInf 0) by lia.
      rewrite PreH34. reflexivity.
    + right. rewrite (Znth_indep dp_values m TeamNegInf 0) by lia.
      rewrite PreH34. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_7 : solver_entail_wit_11_2_split_goal_7.
Proof. LLM_pre_process ltac:(lia).
  repeat rewrite ListLib.Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_4.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_5.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_6.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_1 : solver_entail_wit_11_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec q_8 m) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by lia.
    specialize (PreH60 m ltac:(lia)). lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply PreH60. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_2 : solver_entail_wit_11_3_split_goal_2.
Proof. LLM_pre_process ltac:(lia). all: apply PreH59; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_3 : solver_entail_wit_11_3_split_goal_3.
Proof. LLM_pre_process ltac:(lia). all: apply PreH58; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_4 : solver_entail_wit_11_3_split_goal_4.
Proof. LLM_pre_process ltac:(lia). all: apply PreH57; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_5 : solver_entail_wit_11_3_split_goal_5.
Proof. LLM_pre_process ltac:(lia). all: apply PreH56; tauto. Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_6 : solver_entail_wit_11_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Znth_replace_Znth_Same in PreH1 by lia.
  rewrite PreH44 in PreH1.
  eapply bounded_team_role_update_init__solver_role_init
    with (used := retval); try eassumption.
  - rewrite <- Z.shiftl_1_l. lia.
  - rewrite <- Z.shiftl_1_l. lia.
  - unfold TeamNegInf.
    rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia.
    rewrite <- Z.shiftl_1_l. exact PreH7.
  - rewrite (Znth_indep ndp_values m TeamNegInf 0) by lia. lia.
  - left. repeat split; try lia.
    + rewrite (Znth_indep dp_values m TeamNegInf 0) by lia. lia.
    + repeat rewrite (Znth_indep dp_values m TeamNegInf 0) by lia.
      rewrite PreH34. lia.
    + left. rewrite (Znth_indep dp_values m TeamNegInf 0) by lia.
      reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_7 : solver_entail_wit_11_3_split_goal_7.
Proof. LLM_pre_process ltac:(lia).
  repeat rewrite ListLib.Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_3_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_11_3_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_11_3_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_11_3_split_goal_4.
  Goal_apply proof_of_solver_entail_wit_11_3_split_goal_5.
  Goal_apply proof_of_solver_entail_wit_11_3_split_goal_6.
  Goal_apply proof_of_solver_entail_wit_11_3_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_1 : solver_entail_wit_11_4_split_goal_1.
Proof. LLM_pre_process ltac:(lia). all: apply PreH60; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_2 : solver_entail_wit_11_4_split_goal_2.
Proof. LLM_pre_process ltac:(lia). all: apply PreH59; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_3 : solver_entail_wit_11_4_split_goal_3.
Proof. LLM_pre_process ltac:(lia). all: apply PreH58; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_4 : solver_entail_wit_11_4_split_goal_4.
Proof. LLM_pre_process ltac:(lia). all: apply PreH57; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_5 : solver_entail_wit_11_4_split_goal_5.
Proof. LLM_pre_process ltac:(lia). all: apply PreH56; tauto. Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_6 : solver_entail_wit_11_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite PreH44 in PreH1.
  pose proof (PreH60 m ltac:(split; lia)) as Hbounds.
  eapply bounded_team_role_update_init_skip__solver_role_init
    with (used := retval); try eassumption.
  - rewrite <- Z.shiftl_1_l. lia.
  - unfold TeamNegInf.
    rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia. lia.
  - unfold TeamNegInf.
    rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia.
    rewrite <- Z.shiftl_1_l. exact PreH7.
  - left. repeat split; try lia.
    + rewrite (Znth_indep dp_values m TeamNegInf 0) by lia.
      rewrite (Znth_indep ndp_values m TeamNegInf 0) by lia. lia.
    + rewrite (Znth_indep dp_values m TeamNegInf 0) by lia.
      rewrite (Znth_indep ndp_values m TeamNegInf 0) by lia.
      rewrite PreH34. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_4_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_11_4_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_11_4_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_11_4_split_goal_4.
  Goal_apply proof_of_solver_entail_wit_11_4_split_goal_5.
  Goal_apply proof_of_solver_entail_wit_11_4_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_11_5_split_goal_1 : solver_entail_wit_11_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec q_8 m) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by lia.
    specialize (PreH59 m ltac:(lia)). lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply PreH59. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_5_split_goal_2 : solver_entail_wit_11_5_split_goal_2.
Proof. LLM_pre_process ltac:(lia). all: apply PreH58; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_5_split_goal_3 : solver_entail_wit_11_5_split_goal_3.
Proof. LLM_pre_process ltac:(lia). all: apply PreH57; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_5_split_goal_4 : solver_entail_wit_11_5_split_goal_4.
Proof. LLM_pre_process ltac:(lia). all: apply PreH56; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_5_split_goal_5 : solver_entail_wit_11_5_split_goal_5.
Proof. LLM_pre_process ltac:(lia). all: apply PreH55; tauto. Qed.

Lemma proof_of_solver_entail_wit_11_5_split_goal_6 : solver_entail_wit_11_5_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  eapply bounded_team_role_update_init__solver_role_init
    with (used := retval); try eassumption.
  - rewrite <- Z.shiftl_1_l. lia.
  - rewrite <- Z.shiftl_1_l. lia.
  - unfold TeamNegInf.
    rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia.
    rewrite <- Z.shiftl_1_l. exact PreH6.
  - rewrite (Znth_indep ndp_values m TeamNegInf 0) by lia. lia.
  - right. split; try lia.
    rewrite (Znth_indep dp_values m TeamNegInf 0) by lia. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_11_5_split_goal_7 : solver_entail_wit_11_5_split_goal_7.
Proof. LLM_pre_process ltac:(lia).
  repeat rewrite ListLib.Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_11_5 : solver_entail_wit_11_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_5_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_11_5_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_11_5_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_11_5_split_goal_4.
  Goal_apply proof_of_solver_entail_wit_11_5_split_goal_5.
  Goal_apply proof_of_solver_entail_wit_11_5_split_goal_6.
  Goal_apply proof_of_solver_entail_wit_11_5_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_11_6_split_goal_1 : solver_entail_wit_11_6_split_goal_1.
Proof. LLM_pre_process ltac:(lia). all: apply PreH59; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_6_split_goal_2 : solver_entail_wit_11_6_split_goal_2.
Proof. LLM_pre_process ltac:(lia). all: apply PreH58; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_6_split_goal_3 : solver_entail_wit_11_6_split_goal_3.
Proof. LLM_pre_process ltac:(lia). all: apply PreH57; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_6_split_goal_4 : solver_entail_wit_11_6_split_goal_4.
Proof. LLM_pre_process ltac:(lia). all: apply PreH56; split; lia. Qed.

Lemma proof_of_solver_entail_wit_11_6_split_goal_5 : solver_entail_wit_11_6_split_goal_5.
Proof. LLM_pre_process ltac:(lia). all: apply PreH55; tauto. Qed.

Lemma proof_of_solver_entail_wit_11_6_split_goal_6 : solver_entail_wit_11_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (PreH59 m ltac:(split; lia)) as Hbounds.
  eapply bounded_team_role_update_init_skip__solver_role_init
    with (used := retval); try eassumption.
  - rewrite <- Z.shiftl_1_l. lia.
  - unfold TeamNegInf.
    rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia. lia.
  - unfold TeamNegInf.
    rewrite (Znth_indep dp_values m (- 2 ^ 60) 0) by lia.
    rewrite <- Z.shiftl_1_l. exact PreH6.
  - right. split; try lia.
    rewrite (Znth_indep dp_values m TeamNegInf 0) by lia.
    rewrite (Znth_indep ndp_values m TeamNegInf 0) by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_6 : solver_entail_wit_11_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_6_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_11_6_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_11_6_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_11_6_split_goal_4.
  Goal_apply proof_of_solver_entail_wit_11_6_split_goal_5.
  Goal_apply proof_of_solver_entail_wit_11_6_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_1 : solver_entail_wit_12_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(eapply PreH37; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_2 : solver_entail_wit_12_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(eapply PreH36; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_3 : solver_entail_wit_12_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(eapply PreH35; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_4 : solver_entail_wit_12_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(eapply PreH34; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_5 : solver_entail_wit_12_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(eapply PreH33; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_1 : solver_entail_wit_12_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(eapply PreH37; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_2 : solver_entail_wit_12_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(eapply PreH36; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_3 : solver_entail_wit_12_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(eapply PreH35; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_4 : solver_entail_wit_12_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(eapply PreH34; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_5 : solver_entail_wit_12_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(eapply PreH33; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_2_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_1 : solver_entail_wit_12_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(eapply PreH37; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_2 : solver_entail_wit_12_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(eapply PreH36; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_3 : solver_entail_wit_12_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(eapply PreH35; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_4 : solver_entail_wit_12_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(eapply PreH34; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_5 : solver_entail_wit_12_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(eapply PreH33; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_3_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_1 : solver_entail_wit_12_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(eapply PreH37; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_2 : solver_entail_wit_12_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(eapply PreH36; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_3 : solver_entail_wit_12_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(eapply PreH35; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_4 : solver_entail_wit_12_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(eapply PreH34; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_5 : solver_entail_wit_12_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(eapply PreH33; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_4_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_12_5_split_goal_1 : solver_entail_wit_12_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(eapply PreH37; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_5_split_goal_2 : solver_entail_wit_12_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(eapply PreH36; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_5_split_goal_3 : solver_entail_wit_12_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(eapply PreH35; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_5_split_goal_4 : solver_entail_wit_12_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(eapply PreH34; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_5_split_goal_5 : solver_entail_wit_12_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(eapply PreH33; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_5 : solver_entail_wit_12_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_5_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_5_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_12_6_split_goal_1 : solver_entail_wit_12_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(eapply PreH37; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_6_split_goal_2 : solver_entail_wit_12_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(eapply PreH36; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_6_split_goal_3 : solver_entail_wit_12_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(eapply PreH35; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_6_split_goal_4 : solver_entail_wit_12_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(eapply PreH34; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_6_split_goal_5 : solver_entail_wit_12_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(eapply PreH33; eassumption).
Qed.

Lemma proof_of_solver_entail_wit_12_6 : solver_entail_wit_12_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_6_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_6_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_6_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_13_1_split_goal_1 : solver_entail_wit_13_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||
    (eapply flattened_role_index_bounds__solver_role_index; lia)).
Qed.

Lemma proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_2_split_goal_1 : solver_entail_wit_13_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||
    (eapply flattened_role_index_bounds__solver_role_index; lia)).
Qed.

Lemma proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_3_split_goal_1 : solver_entail_wit_13_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||
    (eapply flattened_role_index_bounds__solver_role_index; lia)).
Qed.

Lemma proof_of_solver_entail_wit_13_3 : solver_entail_wit_13_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_4_split_goal_1 : solver_entail_wit_13_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||
    (eapply flattened_role_index_bounds__solver_role_index; lia)).
Qed.

Lemma proof_of_solver_entail_wit_13_4 : solver_entail_wit_13_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_5_split_goal_1 : solver_entail_wit_13_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||
    (eapply flattened_role_index_bounds__solver_role_index; lia)).
Qed.

Lemma proof_of_solver_entail_wit_13_5 : solver_entail_wit_13_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_6_split_goal_1 : solver_entail_wit_13_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||
    (eapply flattened_role_index_bounds__solver_role_index; lia)).
Qed.

Lemma proof_of_solver_entail_wit_13_6 : solver_entail_wit_13_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_2 j p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_2 j p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_3 j_2 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_2) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_3 j_2 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_2) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_1 : solver_entail_wit_14_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_4 j_3 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_3) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_2 : solver_entail_wit_14_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_4 j_3 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_3) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_4_split_goal_1 : solver_entail_wit_14_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_5 j_4 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_4) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_4_split_goal_2 : solver_entail_wit_14_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_5 j_4 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_4) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_4 : solver_entail_wit_14_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_5_split_goal_1 : solver_entail_wit_14_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_6 j_5 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_5) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_5_split_goal_2 : solver_entail_wit_14_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_6 j_5 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_5) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_5 : solver_entail_wit_14_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_6_split_goal_1 : solver_entail_wit_14_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_7 j_6 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_6) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_6_split_goal_2 : solver_entail_wit_14_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite !Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - pose proof (mask_set_bit_bounds__solver_role_index
      m_7 j_6 p_pre ltac:(lia) ltac:(lia)) as Hmask.
    rewrite !Z.shiftl_1_l in Hmask.
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j_6) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_6 : solver_entail_wit_14_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_15_1_split_goal_1 : solver_entail_wit_15_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = p_pre) as -> by lia.
  apply bounded_team_source_close__solver_source_close.
  - lia.
  - exact PreH38.
Qed.

Lemma proof_of_solver_entail_wit_15_1_split_goal_2 : solver_entail_wit_15_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- PreH110.
  exact PreH111.
Qed.

Lemma proof_of_solver_entail_wit_15_1 : solver_entail_wit_15_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_15_2_split_goal_1 : solver_entail_wit_15_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = p_pre) as -> by lia.
  apply bounded_team_source_close__solver_source_close.
  - lia.
  - exact PreH38.
Qed.

Lemma proof_of_solver_entail_wit_15_2_split_goal_2 : solver_entail_wit_15_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- PreH110.
  exact PreH111.
Qed.

Lemma proof_of_solver_entail_wit_15_2 : solver_entail_wit_15_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_15_3_split_goal_1 : solver_entail_wit_15_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = p_pre) as -> by lia.
  apply bounded_team_source_close__solver_source_close.
  - lia.
  - exact PreH38.
Qed.

Lemma proof_of_solver_entail_wit_15_3_split_goal_2 : solver_entail_wit_15_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- PreH110.
  exact PreH111.
Qed.

Lemma proof_of_solver_entail_wit_15_3 : solver_entail_wit_15_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_15_4_split_goal_1 : solver_entail_wit_15_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = p_pre) as -> by lia.
  apply bounded_team_source_close__solver_source_close.
  - lia.
  - exact PreH38.
Qed.

Lemma proof_of_solver_entail_wit_15_4_split_goal_2 : solver_entail_wit_15_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- PreH110.
  exact PreH111.
Qed.

Lemma proof_of_solver_entail_wit_15_4 : solver_entail_wit_15_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_15_5_split_goal_1 : solver_entail_wit_15_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = p_pre) as -> by lia.
  apply bounded_team_source_close__solver_source_close.
  - lia.
  - exact PreH38.
Qed.

Lemma proof_of_solver_entail_wit_15_5_split_goal_2 : solver_entail_wit_15_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- PreH109.
  exact PreH110.
Qed.

Lemma proof_of_solver_entail_wit_15_5 : solver_entail_wit_15_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_15_6_split_goal_1 : solver_entail_wit_15_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = p_pre) as -> by lia.
  apply bounded_team_source_close__solver_source_close.
  - lia.
  - exact PreH38.
Qed.

Lemma proof_of_solver_entail_wit_15_6_split_goal_2 : solver_entail_wit_15_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- PreH109.
  exact PreH110.
Qed.

Lemma proof_of_solver_entail_wit_15_6 : solver_entail_wit_15_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_15_7_split_goal_1 : solver_entail_wit_15_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmneg : Znth m dp_values_2 TeamNegInf = TeamNegInf).
  {
    rewrite (Znth_indep dp_values_2 m TeamNegInf 0) by lia.
    unfold TeamNegInf.
    rewrite Z.shiftl_1_l in PreH1.
    exact PreH1.
  }
  eapply bounded_team_source_skip__solver_source_close.
  - exact Hmneg.
  - exact PreH49.
Qed.

Lemma proof_of_solver_entail_wit_15_7 : solver_entail_wit_15_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_1_split_goal_1 : solver_entail_wit_16_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hsingle :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    rewrite !Z.shiftl_1_l.
    unfold signed_last_nbits.
    rewrite Z.mod_small.
    - destruct (Coqlib.zlt (2 ^ j) (2 ^ (32 - 1))) as [Hlt | Hnlt];
        [reflexivity | exfalso].
      apply Hnlt. apply Z.pow_lt_mono_r; lia.
    - split.
      + apply Z.pow_nonneg. lia.
      + apply Z.pow_lt_mono_r; lia.
  }
  rewrite Hsingle in *.
  rewrite !Z.shiftl_1_l in *.
  assert (Hbit : Z.testbit m_2 j = false).
  {
    assert (Hlandbit :
      Z.testbit (Z.land m_2 (2 ^ j)) j = false).
    { rewrite PreH24, Z.testbit_0_l. reflexivity. }
    rewrite Z.land_spec in Hlandbit.
    assert (Hsinglebit : Z.testbit (2 ^ j) j = true).
    {
      rewrite <- Z.shiftl_1_l.
      rewrite Z.shiftl_spec by lia.
      replace (j - j) with 0 by lia. reflexivity.
    }
    rewrite Hsinglebit, Bool.andb_true_r in Hlandbit. exact Hlandbit.
  }
  pose proof PreH59 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as
    [Hskill_aud [width [Hwidth_k [Hskill_aud' Hrows]]]].
  assert (Hskill_len : Zlength skill = n_pre) by lia.
  assert (Hrow0 : Zlength (Znth 0 skill __default__List_Z) = width).
  {
    apply (Forall_Znth_local__solver_role_update_b
      _ __default__List_Z skill Hrows).
    rewrite Hskill_len. lia.
  }
  assert (Hwidth_eq : width = p_pre) by lia.
  assert (Hrow_lengths : forall r,
    0 <= r < Zlength skill ->
    Zlength (Znth r skill (@nil Z)) = p_pre).
  {
    intros r Hr.
    pose proof (Forall_Znth_local__solver_role_update_b
      _ (@nil Z) skill Hrows r Hr) as Hrlen.
    rewrite Hwidth_eq in Hrlen. exact Hrlen.
  }
  assert (Hperson_index :
    Znth (Zlength order_sorted_14 - 1 - i_2) order_sorted_14 0 = person_2).
  {
    rewrite PreH55, <- PreH40. symmetry. exact PreH43.
  }
  assert (Hflat :
    Znth (person_2 * p_pre + j) (concat skill) 0 =
    Znth j
      (Znth (Znth (Zlength order_sorted_14 - 1 - i_2)
        order_sorted_14 0) skill (@nil Z)) 0).
  {
    rewrite Hperson_index.
    apply Znth_concat_uniform__solver_role_update_b.
    - rewrite Hskill_len. lia.
    - exact Hrow_lengths.
    - lia.
  }
  eapply bounded_team_role_update_write__solver_role_update_a.
  - lia.
  - reflexivity.
  - exact Hbit.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    rewrite <- Hflat. reflexivity.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    unfold TeamNegInf. exact PreH50.
  - lia.
  - lia.
  - rewrite (Znth_indep ndp_values_14 (Z.lor m_2 (2 ^ j))
      TeamNegInf 0) by lia.
    lia.
  - exact PreH62.
Qed.

Lemma proof_of_solver_entail_wit_16_1_split_goal_2 : solver_entail_wit_16_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite ListLib.Zlength_replace_Znth.
  exact PreH58.
Qed.

Lemma proof_of_solver_entail_wit_16_1 : solver_entail_wit_16_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_16_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_16_2_split_goal_1 : solver_entail_wit_16_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hsingle :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    rewrite !Z.shiftl_1_l.
    unfold signed_last_nbits.
    rewrite Z.mod_small.
    - destruct (Coqlib.zlt (2 ^ j) (2 ^ (32 - 1))) as [Hlt | Hnlt];
        [reflexivity | exfalso].
      apply Hnlt. apply Z.pow_lt_mono_r; lia.
    - split.
      + apply Z.pow_nonneg. lia.
      + apply Z.pow_lt_mono_r; lia.
  }
  rewrite Hsingle in *.
  rewrite !Z.shiftl_1_l in *.
  assert (Hbit : Z.testbit m_2 j = false).
  {
    assert (Hlandbit :
      Z.testbit (Z.land m_2 (2 ^ j)) j = false).
    { rewrite PreH24, Z.testbit_0_l. reflexivity. }
    rewrite Z.land_spec in Hlandbit.
    assert (Hsinglebit : Z.testbit (2 ^ j) j = true).
    {
      rewrite <- Z.shiftl_1_l.
      rewrite Z.shiftl_spec by lia.
      replace (j - j) with 0 by lia. reflexivity.
    }
    rewrite Hsinglebit, Bool.andb_true_r in Hlandbit. exact Hlandbit.
  }
  pose proof PreH59 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as
    [Hskill_aud [width [Hwidth_k [Hskill_aud' Hrows]]]].
  assert (Hskill_len : Zlength skill = n_pre) by lia.
  assert (Hrow0 : Zlength (Znth 0 skill __default__List_Z) = width).
  {
    apply (Forall_Znth_local__solver_role_update_b
      _ __default__List_Z skill Hrows).
    rewrite Hskill_len. lia.
  }
  assert (Hwidth_eq : width = p_pre) by lia.
  assert (Hrow_lengths : forall r,
    0 <= r < Zlength skill ->
    Zlength (Znth r skill (@nil Z)) = p_pre).
  {
    intros r Hr.
    pose proof (Forall_Znth_local__solver_role_update_b
      _ (@nil Z) skill Hrows r Hr) as Hrlen.
    rewrite Hwidth_eq in Hrlen. exact Hrlen.
  }
  assert (Hperson_index :
    Znth (Zlength order_sorted_14 - 1 - i_2) order_sorted_14 0 = person_2).
  {
    rewrite PreH55, <- PreH40. symmetry. exact PreH43.
  }
  assert (Hflat :
    Znth (person_2 * p_pre + j) (concat skill) 0 =
    Znth j
      (Znth (Znth (Zlength order_sorted_14 - 1 - i_2)
        order_sorted_14 0) skill (@nil Z)) 0).
  {
    rewrite Hperson_index.
    apply Znth_concat_uniform__solver_role_update_b.
    - rewrite Hskill_len. lia.
    - exact Hrow_lengths.
    - lia.
  }
  eapply bounded_team_role_update_write__solver_role_update_a.
  - lia.
  - reflexivity.
  - exact Hbit.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    rewrite <- Hflat. reflexivity.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    unfold TeamNegInf. exact PreH50.
  - lia.
  - lia.
  - rewrite (Znth_indep ndp_values_14 (Z.lor m_2 (2 ^ j))
      TeamNegInf 0) by lia.
    lia.
  - exact PreH62.
Qed.

Lemma proof_of_solver_entail_wit_16_2_split_goal_2 : solver_entail_wit_16_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite ListLib.Zlength_replace_Znth.
  exact PreH58.
Qed.

Lemma proof_of_solver_entail_wit_16_2 : solver_entail_wit_16_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_16_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_16_3_split_goal_1 : solver_entail_wit_16_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hsingle :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    rewrite !Z.shiftl_1_l.
    unfold signed_last_nbits.
    rewrite Z.mod_small.
    - destruct (Coqlib.zlt (2 ^ j) (2 ^ (32 - 1))) as [Hlt | Hnlt];
        [reflexivity | exfalso].
      apply Hnlt. apply Z.pow_lt_mono_r; lia.
    - split.
      + apply Z.pow_nonneg. lia.
      + apply Z.pow_lt_mono_r; lia.
  }
  rewrite Hsingle in *.
  rewrite !Z.shiftl_1_l in *.
  assert (Hbit : Z.testbit m_2 j = false).
  {
    assert (Hlandbit :
      Z.testbit (Z.land m_2 (2 ^ j)) j = false).
    { rewrite PreH24, Z.testbit_0_l. reflexivity. }
    rewrite Z.land_spec in Hlandbit.
    assert (Hsinglebit : Z.testbit (2 ^ j) j = true).
    {
      rewrite <- Z.shiftl_1_l.
      rewrite Z.shiftl_spec by lia.
      replace (j - j) with 0 by lia. reflexivity.
    }
    rewrite Hsinglebit, Bool.andb_true_r in Hlandbit. exact Hlandbit.
  }
  pose proof PreH59 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as
    [Hskill_aud [width [Hwidth_k [Hskill_aud' Hrows]]]].
  assert (Hskill_len : Zlength skill = n_pre) by lia.
  assert (Hrow0 : Zlength (Znth 0 skill __default__List_Z) = width).
  {
    apply (Forall_Znth_local__solver_role_update_b
      _ __default__List_Z skill Hrows).
    rewrite Hskill_len. lia.
  }
  assert (Hwidth_eq : width = p_pre) by lia.
  assert (Hrow_lengths : forall r,
    0 <= r < Zlength skill ->
    Zlength (Znth r skill (@nil Z)) = p_pre).
  {
    intros r Hr.
    pose proof (Forall_Znth_local__solver_role_update_b
      _ (@nil Z) skill Hrows r Hr) as Hrlen.
    rewrite Hwidth_eq in Hrlen. exact Hrlen.
  }
  assert (Hperson_index :
    Znth (Zlength order_sorted_14 - 1 - i_2) order_sorted_14 0 = person_2).
  {
    rewrite PreH55, <- PreH40. symmetry. exact PreH43.
  }
  assert (Hflat :
    Znth (person_2 * p_pre + j) (concat skill) 0 =
    Znth j
      (Znth (Znth (Zlength order_sorted_14 - 1 - i_2)
        order_sorted_14 0) skill (@nil Z)) 0).
  {
    rewrite Hperson_index.
    apply Znth_concat_uniform__solver_role_update_b.
    - rewrite Hskill_len. lia.
    - exact Hrow_lengths.
    - lia.
  }
  eapply bounded_team_role_update_write__solver_role_update_a.
  - lia.
  - reflexivity.
  - exact Hbit.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    rewrite <- Hflat. reflexivity.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    unfold TeamNegInf. exact PreH50.
  - lia.
  - lia.
  - rewrite (Znth_indep ndp_values_14 (Z.lor m_2 (2 ^ j))
      TeamNegInf 0) by lia.
    lia.
  - exact PreH62.
Qed.

Lemma proof_of_solver_entail_wit_16_3_split_goal_2 : solver_entail_wit_16_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite ListLib.Zlength_replace_Znth.
  exact PreH58.
Qed.

Lemma proof_of_solver_entail_wit_16_3 : solver_entail_wit_16_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_16_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_16_4_split_goal_1 : solver_entail_wit_16_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hsingle :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    rewrite !Z.shiftl_1_l.
    unfold signed_last_nbits.
    rewrite Z.mod_small.
    - destruct (Coqlib.zlt (2 ^ j) (2 ^ (32 - 1))) as [Hlt | Hnlt];
        [reflexivity | exfalso].
      apply Hnlt. apply Z.pow_lt_mono_r; lia.
    - split.
      + apply Z.pow_nonneg. lia.
      + apply Z.pow_lt_mono_r; lia.
  }
  rewrite Hsingle in *.
  rewrite !Z.shiftl_1_l in *.
  assert (Hbit : Z.testbit m_2 j = false).
  {
    assert (Hlandbit :
      Z.testbit (Z.land m_2 (2 ^ j)) j = false).
    { rewrite PreH24, Z.testbit_0_l. reflexivity. }
    rewrite Z.land_spec in Hlandbit.
    assert (Hsinglebit : Z.testbit (2 ^ j) j = true).
    {
      rewrite <- Z.shiftl_1_l.
      rewrite Z.shiftl_spec by lia.
      replace (j - j) with 0 by lia. reflexivity.
    }
    rewrite Hsinglebit, Bool.andb_true_r in Hlandbit. exact Hlandbit.
  }
  pose proof PreH59 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as
    [Hskill_aud [width [Hwidth_k [Hskill_aud' Hrows]]]].
  assert (Hskill_len : Zlength skill = n_pre) by lia.
  assert (Hrow0 : Zlength (Znth 0 skill __default__List_Z) = width).
  {
    apply (Forall_Znth_local__solver_role_update_b
      _ __default__List_Z skill Hrows).
    rewrite Hskill_len. lia.
  }
  assert (Hwidth_eq : width = p_pre) by lia.
  assert (Hrow_lengths : forall r,
    0 <= r < Zlength skill ->
    Zlength (Znth r skill (@nil Z)) = p_pre).
  {
    intros r Hr.
    pose proof (Forall_Znth_local__solver_role_update_b
      _ (@nil Z) skill Hrows r Hr) as Hrlen.
    rewrite Hwidth_eq in Hrlen. exact Hrlen.
  }
  assert (Hperson_index :
    Znth (Zlength order_sorted_14 - 1 - i_2) order_sorted_14 0 = person_2).
  {
    rewrite PreH55, <- PreH40. symmetry. exact PreH43.
  }
  assert (Hflat :
    Znth (person_2 * p_pre + j) (concat skill) 0 =
    Znth j
      (Znth (Znth (Zlength order_sorted_14 - 1 - i_2)
        order_sorted_14 0) skill (@nil Z)) 0).
  {
    rewrite Hperson_index.
    apply Znth_concat_uniform__solver_role_update_b.
    - rewrite Hskill_len. lia.
    - exact Hrow_lengths.
    - lia.
  }
  eapply bounded_team_role_update_write__solver_role_update_a.
  - lia.
  - reflexivity.
  - exact Hbit.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    rewrite <- Hflat. reflexivity.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    unfold TeamNegInf. exact PreH50.
  - lia.
  - lia.
  - rewrite (Znth_indep ndp_values_14 (Z.lor m_2 (2 ^ j))
      TeamNegInf 0) by lia.
    lia.
  - exact PreH62.
Qed.

Lemma proof_of_solver_entail_wit_16_4_split_goal_2 : solver_entail_wit_16_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite ListLib.Zlength_replace_Znth.
  exact PreH58.
Qed.

Lemma proof_of_solver_entail_wit_16_4 : solver_entail_wit_16_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_16_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_16_5_split_goal_1 : solver_entail_wit_16_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hsingle :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    rewrite !Z.shiftl_1_l.
    unfold signed_last_nbits.
    rewrite Z.mod_small.
    - destruct (Coqlib.zlt (2 ^ j) (2 ^ (32 - 1))) as [Hlt | Hnlt];
        [reflexivity | exfalso].
      apply Hnlt. apply Z.pow_lt_mono_r; lia.
    - split.
      + apply Z.pow_nonneg. lia.
      + apply Z.pow_lt_mono_r; lia.
  }
  rewrite Hsingle in *.
  rewrite !Z.shiftl_1_l in *.
  assert (Hbit : Z.testbit m_2 j = false).
  {
    assert (Hlandbit :
      Z.testbit (Z.land m_2 (2 ^ j)) j = false).
    { rewrite PreH24, Z.testbit_0_l. reflexivity. }
    rewrite Z.land_spec in Hlandbit.
    assert (Hsinglebit : Z.testbit (2 ^ j) j = true).
    {
      rewrite <- Z.shiftl_1_l.
      rewrite Z.shiftl_spec by lia.
      replace (j - j) with 0 by lia. reflexivity.
    }
    rewrite Hsinglebit, Bool.andb_true_r in Hlandbit. exact Hlandbit.
  }
  pose proof PreH59 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as
    [Hskill_aud [width [Hwidth_k [Hskill_aud' Hrows]]]].
  assert (Hskill_len : Zlength skill = n_pre) by lia.
  assert (Hrow0 : Zlength (Znth 0 skill __default__List_Z) = width).
  {
    apply (Forall_Znth_local__solver_role_update_b
      _ __default__List_Z skill Hrows).
    rewrite Hskill_len. lia.
  }
  assert (Hwidth_eq : width = p_pre) by lia.
  assert (Hrow_lengths : forall r,
    0 <= r < Zlength skill ->
    Zlength (Znth r skill (@nil Z)) = p_pre).
  {
    intros r Hr.
    pose proof (Forall_Znth_local__solver_role_update_b
      _ (@nil Z) skill Hrows r Hr) as Hrlen.
    rewrite Hwidth_eq in Hrlen. exact Hrlen.
  }
  assert (Hperson_index :
    Znth (Zlength order_sorted_14 - 1 - i_2) order_sorted_14 0 = person_2).
  {
    rewrite PreH55, <- PreH40. symmetry. exact PreH43.
  }
  assert (Hflat :
    Znth (person_2 * p_pre + j) (concat skill) 0 =
    Znth j
      (Znth (Znth (Zlength order_sorted_14 - 1 - i_2)
        order_sorted_14 0) skill (@nil Z)) 0).
  {
    rewrite Hperson_index.
    apply Znth_concat_uniform__solver_role_update_b.
    - rewrite Hskill_len. lia.
    - exact Hrow_lengths.
    - lia.
  }
  eapply bounded_team_role_update_write__solver_role_update_a.
  - lia.
  - reflexivity.
  - exact Hbit.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    rewrite <- Hflat. reflexivity.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    unfold TeamNegInf. exact PreH50.
  - lia.
  - lia.
  - rewrite (Znth_indep ndp_values_14 (Z.lor m_2 (2 ^ j))
      TeamNegInf 0) by lia.
    lia.
  - exact PreH62.
Qed.

Lemma proof_of_solver_entail_wit_16_5_split_goal_2 : solver_entail_wit_16_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite ListLib.Zlength_replace_Znth.
  exact PreH58.
Qed.

Lemma proof_of_solver_entail_wit_16_5 : solver_entail_wit_16_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_16_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_16_6_split_goal_1 : solver_entail_wit_16_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hsingle :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    rewrite !Z.shiftl_1_l.
    unfold signed_last_nbits.
    rewrite Z.mod_small.
    - destruct (Coqlib.zlt (2 ^ j) (2 ^ (32 - 1))) as [Hlt | Hnlt];
        [reflexivity | exfalso].
      apply Hnlt. apply Z.pow_lt_mono_r; lia.
    - split.
      + apply Z.pow_nonneg. lia.
      + apply Z.pow_lt_mono_r; lia.
  }
  rewrite Hsingle in *.
  rewrite !Z.shiftl_1_l in *.
  assert (Hbit : Z.testbit m_2 j = false).
  {
    assert (Hlandbit :
      Z.testbit (Z.land m_2 (2 ^ j)) j = false).
    { rewrite PreH24, Z.testbit_0_l. reflexivity. }
    rewrite Z.land_spec in Hlandbit.
    assert (Hsinglebit : Z.testbit (2 ^ j) j = true).
    {
      rewrite <- Z.shiftl_1_l.
      rewrite Z.shiftl_spec by lia.
      replace (j - j) with 0 by lia. reflexivity.
    }
    rewrite Hsinglebit, Bool.andb_true_r in Hlandbit. exact Hlandbit.
  }
  pose proof PreH59 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as
    [Hskill_aud [width [Hwidth_k [Hskill_aud' Hrows]]]].
  assert (Hskill_len : Zlength skill = n_pre) by lia.
  assert (Hrow0 : Zlength (Znth 0 skill __default__List_Z) = width).
  {
    apply (Forall_Znth_local__solver_role_update_b
      _ __default__List_Z skill Hrows).
    rewrite Hskill_len. lia.
  }
  assert (Hwidth_eq : width = p_pre) by lia.
  assert (Hrow_lengths : forall r,
    0 <= r < Zlength skill ->
    Zlength (Znth r skill (@nil Z)) = p_pre).
  {
    intros r Hr.
    pose proof (Forall_Znth_local__solver_role_update_b
      _ (@nil Z) skill Hrows r Hr) as Hrlen.
    rewrite Hwidth_eq in Hrlen. exact Hrlen.
  }
  assert (Hperson_index :
    Znth (Zlength order_sorted_14 - 1 - i_2) order_sorted_14 0 = person_2).
  {
    rewrite PreH55, <- PreH40. symmetry. exact PreH43.
  }
  assert (Hflat :
    Znth (person_2 * p_pre + j) (concat skill) 0 =
    Znth j
      (Znth (Znth (Zlength order_sorted_14 - 1 - i_2)
        order_sorted_14 0) skill (@nil Z)) 0).
  {
    rewrite Hperson_index.
    apply Znth_concat_uniform__solver_role_update_b.
    - rewrite Hskill_len. lia.
    - exact Hrow_lengths.
    - lia.
  }
  eapply bounded_team_role_update_write__solver_role_update_a.
  - lia.
  - reflexivity.
  - exact Hbit.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    rewrite <- Hflat. reflexivity.
  - rewrite (Znth_indep dp_values_14 m_2 TeamNegInf 0) by lia.
    unfold TeamNegInf. exact PreH50.
  - lia.
  - lia.
  - rewrite (Znth_indep ndp_values_14 (Z.lor m_2 (2 ^ j))
      TeamNegInf 0) by lia.
    lia.
  - exact PreH62.
Qed.

Lemma proof_of_solver_entail_wit_16_6_split_goal_2 : solver_entail_wit_16_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite ListLib.Zlength_replace_Znth.
  exact PreH58.
Qed.

Lemma proof_of_solver_entail_wit_16_6 : solver_entail_wit_16_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_16_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_16_7_split_goal_1 : solver_entail_wit_16_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros; try int_auto).
  eapply bounded_team_role_update_skip__solver_role_update_b with
    (n := n_pre) (p := p_pre) (k := k_pre) (aud := aud_input)
    (default := __default__List_Z) (skill := skill)
    (sorted_audience := audience_sorted_14)
    (sorted_order := order_sorted_14) (processed := i_2)
    (old_values := dp_values_14) (next_values := ndp_values_14)
    (source := m_2) (role := j) (person := person_2)
    (full := full_2)
    (mask := signed_last_nbits (Z.shiftl 1 j) 32);
    eauto; try lia.
  all: try (rewrite <- PreH40; exact PreH43).
  all: try (apply signed_last_nbits_eq; [lia |];
    rewrite Z.shiftl_1_l;
    split;
    [pose proof (Z.pow_nonneg 2 j ltac:(lia)); lia |
     apply Z.pow_lt_mono_r; lia]).
Qed.

Lemma proof_of_solver_entail_wit_16_7 : solver_entail_wit_16_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_8_split_goal_1 : solver_entail_wit_16_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros; try int_auto).
  eapply bounded_team_role_update_skip__solver_role_update_b with
    (n := n_pre) (p := p_pre) (k := k_pre) (aud := aud_input)
    (default := __default__List_Z) (skill := skill)
    (sorted_audience := audience_sorted_14)
    (sorted_order := order_sorted_14) (processed := i_2)
    (old_values := dp_values_14) (next_values := ndp_values_14)
    (source := m_2) (role := j) (person := person_2)
    (full := full_2)
    (mask := signed_last_nbits (Z.shiftl 1 j) 32);
    eauto; try lia.
  all: try (rewrite <- PreH40; exact PreH43).
  all: try (apply signed_last_nbits_eq; [lia |];
    rewrite Z.shiftl_1_l;
    split;
    [pose proof (Z.pow_nonneg 2 j ltac:(lia)); lia |
     apply Z.pow_lt_mono_r; lia]).
Qed.

Lemma proof_of_solver_entail_wit_16_8 : solver_entail_wit_16_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_8_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_9_split_goal_1 : solver_entail_wit_16_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros; try int_auto).
  eapply bounded_team_role_update_skip__solver_role_update_b with
    (n := n_pre) (p := p_pre) (k := k_pre) (aud := aud_input)
    (default := __default__List_Z) (skill := skill)
    (sorted_audience := audience_sorted_14)
    (sorted_order := order_sorted_14) (processed := i_2)
    (old_values := dp_values_14) (next_values := ndp_values_14)
    (source := m_2) (role := j) (person := person_2)
    (full := full_2)
    (mask := signed_last_nbits (Z.shiftl 1 j) 32);
    eauto; try lia.
  all: try (rewrite <- PreH40; exact PreH43).
  all: try (apply signed_last_nbits_eq; [lia |];
    rewrite Z.shiftl_1_l;
    split;
    [pose proof (Z.pow_nonneg 2 j ltac:(lia)); lia |
     apply Z.pow_lt_mono_r; lia]).
Qed.

Lemma proof_of_solver_entail_wit_16_9 : solver_entail_wit_16_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_9_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_10_split_goal_1 : solver_entail_wit_16_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros; try int_auto).
  eapply bounded_team_role_update_skip__solver_role_update_b with
    (n := n_pre) (p := p_pre) (k := k_pre) (aud := aud_input)
    (default := __default__List_Z) (skill := skill)
    (sorted_audience := audience_sorted_14)
    (sorted_order := order_sorted_14) (processed := i_2)
    (old_values := dp_values_14) (next_values := ndp_values_14)
    (source := m_2) (role := j) (person := person_2)
    (full := full_2)
    (mask := signed_last_nbits (Z.shiftl 1 j) 32);
    eauto; try lia.
  all: try (rewrite <- PreH40; exact PreH43).
  all: try (apply signed_last_nbits_eq; [lia |];
    rewrite Z.shiftl_1_l;
    split;
    [pose proof (Z.pow_nonneg 2 j ltac:(lia)); lia |
     apply Z.pow_lt_mono_r; lia]).
Qed.

Lemma proof_of_solver_entail_wit_16_10 : solver_entail_wit_16_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_10_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_11_split_goal_1 : solver_entail_wit_16_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros; try int_auto).
  eapply bounded_team_role_update_skip__solver_role_update_b with
    (n := n_pre) (p := p_pre) (k := k_pre) (aud := aud_input)
    (default := __default__List_Z) (skill := skill)
    (sorted_audience := audience_sorted_14)
    (sorted_order := order_sorted_14) (processed := i_2)
    (old_values := dp_values_14) (next_values := ndp_values_14)
    (source := m_2) (role := j) (person := person_2)
    (full := full_2)
    (mask := signed_last_nbits (Z.shiftl 1 j) 32);
    eauto; try lia.
  all: try (rewrite <- PreH40; exact PreH43).
  all: try (apply signed_last_nbits_eq; [lia |];
    rewrite Z.shiftl_1_l;
    split;
    [pose proof (Z.pow_nonneg 2 j ltac:(lia)); lia |
     apply Z.pow_lt_mono_r; lia]).
Qed.

Lemma proof_of_solver_entail_wit_16_11 : solver_entail_wit_16_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_11_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_12_split_goal_1 : solver_entail_wit_16_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros; try int_auto).
  eapply bounded_team_role_update_skip__solver_role_update_b with
    (n := n_pre) (p := p_pre) (k := k_pre) (aud := aud_input)
    (default := __default__List_Z) (skill := skill)
    (sorted_audience := audience_sorted_14)
    (sorted_order := order_sorted_14) (processed := i_2)
    (old_values := dp_values_14) (next_values := ndp_values_14)
    (source := m_2) (role := j) (person := person_2)
    (full := full_2)
    (mask := signed_last_nbits (Z.shiftl 1 j) 32);
    eauto; try lia.
  all: try (rewrite <- PreH40; exact PreH43).
  all: try (apply signed_last_nbits_eq; [lia |];
    rewrite Z.shiftl_1_l;
    split;
    [pose proof (Z.pow_nonneg 2 j ltac:(lia)); lia |
     apply Z.pow_lt_mono_r; lia]).
Qed.

Lemma proof_of_solver_entail_wit_16_12 : solver_entail_wit_16_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_12_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_13_split_goal_1 : solver_entail_wit_16_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsigned :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    apply signed_last_nbits_eq; [lia |].
    rewrite Z.shiftl_1_l.
    assert (Hpow_le : 2 ^ j <= 2 ^ 7) by
      (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in Hpow_le.
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.pow_nonneg 2 j ltac:(lia)). lia.
  }
  rewrite Hsigned in PreH1.
  eapply bounded_team_role_update_skip_or_write__solver_role_update_c.
  - lia.
  - eapply testbit_from_land_shiftl_one__solver_role_update_c; eauto; lia.
  - exact PreH39.
Qed.

Lemma proof_of_solver_entail_wit_16_13 : solver_entail_wit_16_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_13_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_14_split_goal_1 : solver_entail_wit_16_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsigned :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    apply signed_last_nbits_eq; [lia |].
    rewrite Z.shiftl_1_l.
    assert (Hpow_le : 2 ^ j <= 2 ^ 7) by
      (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in Hpow_le.
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.pow_nonneg 2 j ltac:(lia)). lia.
  }
  rewrite Hsigned in PreH1.
  eapply bounded_team_role_update_skip_or_write__solver_role_update_c.
  - lia.
  - eapply testbit_from_land_shiftl_one__solver_role_update_c; eauto; lia.
  - exact PreH39.
Qed.

Lemma proof_of_solver_entail_wit_16_14 : solver_entail_wit_16_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_14_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_15_split_goal_1 : solver_entail_wit_16_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsigned :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    apply signed_last_nbits_eq; [lia |].
    rewrite Z.shiftl_1_l.
    assert (Hpow_le : 2 ^ j <= 2 ^ 7) by
      (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in Hpow_le.
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.pow_nonneg 2 j ltac:(lia)). lia.
  }
  rewrite Hsigned in PreH1.
  eapply bounded_team_role_update_skip_or_write__solver_role_update_c.
  - lia.
  - eapply testbit_from_land_shiftl_one__solver_role_update_c; eauto; lia.
  - exact PreH39.
Qed.

Lemma proof_of_solver_entail_wit_16_15 : solver_entail_wit_16_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_15_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_16_split_goal_1 : solver_entail_wit_16_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsigned :
    signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  {
    apply signed_last_nbits_eq; [lia |].
    rewrite Z.shiftl_1_l.
    assert (Hpow_le : 2 ^ j <= 2 ^ 7) by
      (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in Hpow_le.
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.pow_nonneg 2 j ltac:(lia)). lia.
  }
  rewrite Hsigned in PreH1.
  eapply bounded_team_role_update_skip_or_write__solver_role_update_c.
  - lia.
  - eapply testbit_from_land_shiftl_one__solver_role_update_c; eauto; lia.
  - exact PreH39.
Qed.

Lemma proof_of_solver_entail_wit_16_16 : solver_entail_wit_16_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_16_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_17_split_goal_1 : solver_entail_wit_16_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply bounded_team_role_update_skip_or_write__solver_role_update_c;
    [lia | | assumption].
  assert (Hcast : signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  { apply signed_last_nbits_eq; [lia |].
    rewrite Z.shiftl_1_l.
    split.
    - assert (0 <= 2 ^ j) by (apply Z.pow_nonneg; lia). lia.
    - apply Z.pow_lt_mono_r; lia. }
  rewrite Hcast in PreH1.
  destruct (Z.testbit m_2 j) eqn:Hbit; [reflexivity |].
  exfalso. apply PreH1.
  apply Z.bits_inj. intro bit.
  rewrite Z.land_spec, Z.testbit_0_l.
  destruct (Z_lt_ge_dec bit 0) as [Hnegative | Hnonnegative].
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
  - rewrite Z.shiftl_1_l, testbit_pow2__solver_row_close_dispatch by lia.
    destruct (Z.eqb bit j) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst bit. rewrite Hbit. reflexivity.
    + rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_16_17 : solver_entail_wit_16_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_17_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_18_split_goal_1 : solver_entail_wit_16_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply bounded_team_role_update_skip_or_write__solver_role_update_c;
    [lia | | assumption].
  assert (Hcast : signed_last_nbits (Z.shiftl 1 j) 32 = Z.shiftl 1 j).
  { apply signed_last_nbits_eq; [lia |].
    rewrite Z.shiftl_1_l.
    split.
    - assert (0 <= 2 ^ j) by (apply Z.pow_nonneg; lia). lia.
    - apply Z.pow_lt_mono_r; lia. }
  rewrite Hcast in PreH1.
  destruct (Z.testbit m_2 j) eqn:Hbit; [reflexivity |].
  exfalso. apply PreH1.
  apply Z.bits_inj. intro bit.
  rewrite Z.land_spec, Z.testbit_0_l.
  destruct (Z_lt_ge_dec bit 0) as [Hnegative | Hnonnegative].
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
  - rewrite Z.shiftl_1_l, testbit_pow2__solver_row_close_dispatch by lia.
    destruct (Z.eqb bit j) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst bit. rewrite Hbit. reflexivity.
    + rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_16_18 : solver_entail_wit_16_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_18_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_1 : solver_entail_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply PreH37; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_2 : solver_entail_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply PreH36; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_3 : solver_entail_wit_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_4 : solver_entail_wit_17_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply PreH34; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_5 : solver_entail_wit_17_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply PreH33; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_6 : solver_entail_wit_17_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst aud_input.
  eapply (bounded_team_next_row_closes__solver_row_close_dispatch
    n_pre aud skill order_values audience_sorted_2 order_sorted_2
    p_pre k_pre i dp_values_2 ndp_values_2);
    try eassumption; try lia.
  - assert (Hskill_len : Zlength skill = Zlength aud).
    { unfold Pre in PreH29.
      destruct PreH29 as [Hskill_input Hrest].
      exact Hskill_input. }
    assert (Haud_len : n_pre = Zlength aud) by exact PreH8.
    assert (Hskill_index : 0 <= 0 < Zlength skill) by lia.
    rewrite (Znth_indep skill 0 __default__List_Z (@nil Z) Hskill_index) in PreH9.
    exact PreH9.
  - intros q Hq. specialize (PreH33 q Hq). lia.
  - rewrite Z.shiftl_1_l in PreH14.
    replace m with (2 ^ p_pre) in PreH32 by lia.
    exact PreH32.
Qed.

Lemma proof_of_solver_entail_wit_17 : solver_entail_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_1 : solver_entail_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(eauto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_2 : solver_entail_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(eauto).
  apply PreH31. exact H.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_3 : solver_entail_wit_18_split_goal_3.
Proof.
  LLM_pre_process ltac:(eauto).
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_4 : solver_entail_wit_18_split_goal_4.
Proof.
  LLM_pre_process ltac:(eauto).
  apply PreH29. exact H.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_5 : solver_entail_wit_18_split_goal_5.
Proof.
  LLM_pre_process ltac:(eauto).
  all: try solve [apply PreH28; assumption].
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_6 : solver_entail_wit_18_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || eauto).
  unfold BoundedTeamCopyPrefix.
  intros.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_18 : solver_entail_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_19_split_goal_1 : solver_entail_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || eauto).
  unfold BoundedTeamCopyPrefix in *.
  intros q Hq.
  destruct (Z.eq_dec q m) as [Heq | Hneq].
  - subst q.
    rewrite Znth_replace_Znth_Same by lia.
    apply Znth_indep.
    lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply PreH31.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_19_split_goal_2 : solver_entail_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || eauto).
  rewrite Zlength_replace_Znth.
  exact PreH26.
Qed.

Lemma proof_of_solver_entail_wit_19 : solver_entail_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_20_split_goal_1 : solver_entail_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(eauto).
  dump_pre_spatial.
  intros q_4 Hq_4.
  specialize (PreH36 q_4 ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_20_split_goal_2 : solver_entail_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || eauto).
Qed.

Lemma proof_of_solver_entail_wit_20_split_goal_3 : solver_entail_wit_20_split_goal_3.
Proof.
  LLM_pre_process ltac:(eauto).
Qed.

Lemma proof_of_solver_entail_wit_20_split_goal_4 : solver_entail_wit_20_split_goal_4.
Proof.
  LLM_pre_process ltac:(eauto).
Qed.

Lemma proof_of_solver_entail_wit_20_split_goal_5 : solver_entail_wit_20_split_goal_5.
Proof.
  LLM_pre_process ltac:(eauto).
Qed.

Lemma proof_of_solver_entail_wit_20_split_goal_6 : solver_entail_wit_20_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || eauto).
  dump_pre_spatial.
  rewrite Z.shiftl_1_l in PreH7 by lia.
  unfold BoundedTeamDPTable in *.
  intros mask Hmask.
  rewrite PreH31 by lia.
  apply PreH30. exact Hmask.
Qed.

Lemma proof_of_solver_entail_wit_20_split_goal_spatial : solver_entail_wit_20_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || eauto).
  sep_apply (Int64Array.full_to_full_shape ndp_pre 128 ndp_values).
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_20 : solver_entail_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_20_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_20_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_20_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_20_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_20_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_20_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_20_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_21 : solver_entail_wit_21.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Z.shiftl_1_l in PreH13.
  pose proof PreH19 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as
    [Hskill_len [positions [Hspace [Hskill_len' Hrows]]]].
  destruct skill as [|row rows].
  { rewrite Zlength_nil in Hskill_len. lia. }
  inversion Hrows as [|row' rows' Hrow_length Hrows']; subst row' rows'.
  rewrite Znth0_cons in PreH8.
  assert (Hpositions_eq : positions = p_pre) by lia.
  assert (Hfull_space : p_pre + k_pre <= n_pre) by lia.
  assert (Hskill0 : p_pre = Zlength (Znth 0 (row :: rows) (@nil Z))).
  { rewrite Znth0_cons. exact PreH8. }
  replace i with n_pre in PreH21 by lia.
  assert (Hspec :
    Spec k_pre aud (row :: rows) (Znth (full - 1) dp_values_2 0)).
  {
    rewrite PreH13.
    eapply bounded_full_mask_to_team_choice__solver_result.
    - lia.
    - lia.
    - exact Hfull_space.
    - exact PreH7.
    - exact Hskill0.
    - exact PreH9.
    - exact PreH24.
    - exact PreH20.
    - exact PreH18.
    - lia.
    - exact PreH21.
  }
  assert (Hshape_rec :
    forall (storeA : addr -> Z -> Z -> Assertion) k x lo hi,
      store_undef_array_rec (fun x lo => EX a : Z, storeA x lo a)
        x lo hi k
      |-- EX l : list Z, store_array_rec storeA x lo hi l).
  {
    intros storeA k.
    induction k as [|k IH]; intros x lo hi; simpl.
    - Exists (@nil Z). simpl. split_pure_spatial.
      + Intros_p Hlohi. cancel.
      + Intros_p Hlohi2. split_pures; dump_pre_spatial; auto.
    - Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      Intros l.
      Exists (a :: l).
      simpl. cancel.
  }
  assert (Hshape_full :
    forall x n,
      Int64Array.full_shape x n
      |-- EX l : list Z, Int64Array.full x n l).
  {
    intros x n.
    unfold Int64Array.full_shape, Int64Array.full,
      store_undef_array, store_array.
    apply Hshape_rec.
  }
  sep_apply_l_atomic (Hshape_full ndp_pre 128).
  Intros ndp_values.
  prop_apply_p (Int64Array.full_Zlength ndp_pre 128 ndp_values).
  Intros_p Hndp_length.
  Exists ndp_values.
  Exists dp_values_2 order_sorted_2 audience_sorted_2.
  split_pure_spatial.
  - cancel. cancel. cancel.
  - split_pures; dump_pre_spatial; auto;
      rewrite Z.shiftl_1_l; exact PreH13.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (Int64Array.full_to_full_shape dp_pre 128 dp_values).
  sep_apply_l_atomic
    (Int64Array.full_to_full_shape ndp_pre 128 ndp_values).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
Qed.
