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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P055_567C_geometric_progression_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P055_567C_geometric_progression_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P055_567C_geometric_progression_lib.
Local Open Scope sac.

Lemma proof_of_cmp_ll_return_wit_1_split_goal_1 : cmp_ll_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CompareResult.
  right; left.
  split; lia.
Qed.

Lemma proof_of_cmp_ll_return_wit_1 : cmp_ll_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_ll_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmp_ll_return_wit_2_split_goal_1 : cmp_ll_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CompareResult.
  left.
  split; lia.
Qed.

Lemma proof_of_cmp_ll_return_wit_2 : cmp_ll_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_ll_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmp_ll_return_wit_3_split_goal_1 : cmp_ll_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CompareResult.
  right; right.
  split; lia.
Qed.

Lemma proof_of_cmp_ll_return_wit_3 : cmp_ll_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_ll_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_1_split_goal_1 : lower_bound_ll_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_1_split_goal_2 : lower_bound_ll_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_1 : lower_bound_ll_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lower_bound_ll_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_lower_bound_ll_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_2_split_goal_1 : lower_bound_ll_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (l + r) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (l + r) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_2_split_goal_2 : lower_bound_ll_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (l + r) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (l + r) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_2 : lower_bound_ll_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lower_bound_ll_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_lower_bound_ll_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_3_1_split_goal_1 : lower_bound_ll_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (l + r) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (l + r) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_3_1 : lower_bound_ll_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lower_bound_ll_entail_wit_3_1_split_goal_1.
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_3_2_split_goal_1 : lower_bound_ll_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (l + r) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (l + r) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_lower_bound_ll_entail_wit_3_2 : lower_bound_ll_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lower_bound_ll_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_lower_bound_ll_return_wit_1_split_goal_1 : lower_bound_ll_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold LowerBoundResult.
  repeat split; try lia.
  - intros i Hi.
    apply PreH9.
    lia.
  - intros i Hi.
    apply PreH10.
    lia.
Qed.

Lemma proof_of_lower_bound_ll_return_wit_1 : lower_bound_ll_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lower_bound_ll_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH43 retval ltac:(lia)).
  specialize (PreH44 retval_2 ltac:(lia)).
  destruct (Z.eq_dec retval_2 ix) as [Heq | Hneq].
  - subst retval_2.
    rewrite Znth_replace_Znth_Same by lia.
    dump_pre_spatial.
    nia.
  - rewrite Znth_replace_Znth_Diff by lia.
    dump_pre_spatial.
    nia.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH43 retval ltac:(lia)).
  specialize (PreH44 retval_2 ltac:(lia)).
  destruct (Z.eq_dec retval_2 ix) as [Heq | Hneq].
  - subst retval_2.
    rewrite Znth_replace_Znth_Same by lia.
    dump_pre_spatial.
    nia.
  - rewrite Znth_replace_Znth_Diff by lia.
    dump_pre_spatial.
    nia.
Qed.

Lemma proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH43 retval ltac:(lia)).
  specialize (PreH44 retval_2 ltac:(lia)).
  destruct (Z.eq_dec retval_2 ix) as [Heq | Hneq].
  - subst retval_2.
    rewrite Znth_replace_Znth_Same by lia.
    dump_pre_spatial.
    nia.
  - rewrite Znth_replace_Znth_Diff by lia.
    dump_pre_spatial.
    nia.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH43 retval ltac:(lia)).
  specialize (PreH44 retval_2 ltac:(lia)).
  destruct (Z.eq_dec retval_2 ix) as [Heq | Hneq].
  - subst retval_2.
    rewrite Znth_replace_Znth_Same by lia.
    dump_pre_spatial.
    nia.
  - rewrite Znth_replace_Znth_Diff by lia.
    dump_pre_spatial.
    nia.
Qed.

Lemma proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(apply PreH7; lia).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
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
  rewrite (sublist_split 0 (i + 1) i values) by lia.
  rewrite (@sublist_single Z 0 i values) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (sublist_split 0 (i + 1) i values) by lia.
  rewrite (@sublist_single Z 0 i values) by lia.
  reflexivity.
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
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_spatial : solver_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  subst n_pre.
  rewrite (sublist_self values (Zlength values)) by reflexivity.
  sep_apply_l_atomic
    (Int64Array.seg_to_full a 0 (Zlength values) values).
  sep_apply_l_atomic
    (Int64Array.seg_to_full vals 0 (Zlength values) values).
  simpl.
  replace (vals + 0) with vals by lia.
  replace (a + 0) with a by lia.
  replace (Zlength values - 0) with (Zlength values) by lia.
  cancel (Int64Array.full a (Zlength values) values).
  cancel (Int64Array.full vals (Zlength values) values).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (compression_state_init__compression sorted_2) as Hstate.
  Exists sorted_2 sorted_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hstate.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (compression_state_insert_new__compression
      sorted_2 i un storage_2 PreH14 ltac:(lia)
      ltac:(left; exact PreH1) PreH19) as Hstate.
  Exists (replace_Znth un (Znth i storage_2 0) storage_2) sorted_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hstate;
      try rewrite Zlength_replace_Znth; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (compression_state_insert_new__compression
      sorted_2 i un storage_2 PreH15 ltac:(lia)
      ltac:(right; exact PreH1) PreH20) as Hstate.
  Exists (replace_Znth un (Znth i storage_2 0) storage_2) sorted_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hstate;
      try rewrite Zlength_replace_Znth; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (compression_state_skip_duplicate__compression
      sorted_2 i un storage_2 ltac:(lia) PreH1 PreH20) as Hstate.
  Exists storage_2 sorted_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hstate.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  pose proof
    (compression_state_finish__compression
      sorted_2 un storage ltac:(lia)
      ltac:(rewrite PreH10; exact PreH18))
    as [Hun [Hkeys_length [Htail_length Hkeys]]].
  assert (Hvalue_bounds :
    Forall (fun x => -1000000000 <= x <= 1000000000) values).
  {
    apply Forall_forall.
    intros x Hx.
    destruct (In_Znth_exists__compression values x Hx)
      as [j [Hj <-]].
    apply PreH9. lia.
  }
  pose proof
    (unique_keys_bounds__compression
      values sorted_2 (sublist 0 un storage)
      (-1000000000) 1000000000
      Hvalue_bounds PreH12 Hkeys) as Hkey_bounds.
  sep_apply_l_atomic
    (Int64Array.full_split_to_seg vals un n_pre storage).
  - dump_pre_spatial. lia.
  - Exists (sublist un n_pre storage) (sublist 0 un storage) sorted_2.
    split_pure_spatial.
    + cancel (Int64Array.full input_pre n_pre values).
      cancel (Int64Array.full a n_pre values).
      cancel (Int64Array.seg vals 0 un (sublist 0 un storage)).
      cancel (Int64Array.seg vals un n_pre (sublist un n_pre storage)).
    + split_pures.
      * dump_pre_spatial. exact PreH2.
      * dump_pre_spatial. exact PreH3.
      * dump_pre_spatial. exact PreH4.
      * dump_pre_spatial. exact PreH5.
      * dump_pre_spatial. exact PreH6.
      * dump_pre_spatial. exact PreH7.
      * dump_pre_spatial. exact PreH8.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. exact PreH10.
      * dump_pre_spatial. exact Hkeys_length.
      * dump_pre_spatial. rewrite <- PreH10. exact Htail_length.
      * dump_pre_spatial. exact PreH12.
      * dump_pre_spatial. exact PreH13.
      * dump_pre_spatial. exact Hkeys.
      * dump_pre_spatial. exact PreH9.
      * dump_pre_spatial.
        intros j Hj.
        apply Hkey_bounds.
        rewrite Hkeys_length.
        exact Hj.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (repeat_Z 0 un) (repeat_Z 0 un) tail_2 keys_2 sorted_2.
  assert (Hzero_length : Zlength (repeat_Z 0 un) = un).
  { unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia. }
  assert (Hzero_at : forall j, 0 <= j < un ->
    Znth j (repeat_Z 0 un) 0 = 0).
  { intros j Hj. unfold repeat_Z. rewrite Znth_repeat. reflexivity. }
  assert (Hright :
    RightBuildState values 0 keys_2 (repeat_Z 0 un)).
  {
    unfold RightBuildState, FrequencyProfile.
    split; [lia |].
    split; [lia |].
    split; [lia |].
    intros j Hj.
    rewrite Hzero_at by lia.
    symmetry.
    apply set_card_empty__right_frequency.
    intros x Hx. lia.
  }
  split_pure_spatial.
  - cancel (Int64Array.full input_pre n_pre values).
    cancel (Int64Array.full a n_pre values).
    cancel (Int64Array.seg vals 0 un keys_2).
    cancel (Int64Array.seg vals un n_pre tail_2).
    cancel (Int64Array.full retval un (repeat_Z 0 un)).
    cancel (Int64Array.full retval_2 un (repeat_Z 0 un)).
  - split_pures; try (dump_pre_spatial; assumption); try (dump_pre_spatial; lia).
    all: dump_pre_spatial.
    + reflexivity.
    + intros j Hj. rewrite Hzero_at by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists right_data_2 left_data_2 tail_2 keys_2 sorted_2.
  assert (Hkey : KeyAt keys_2 (Znth i values 0) retval).
  {
    eapply lower_bound_unique_key__right_frequency;
      try eassumption; lia.
  }
  split_pure_spatial.
  - cancel (Int64Array.full input_pre n_pre values).
    cancel (Int64Array.full a n_pre values).
    cancel (Int64Array.seg vals 0 un keys_2).
    cancel (Int64Array.seg vals un n_pre tail_2).
    cancel (Int64Array.full left un left_data_2).
    cancel (Int64Array.full right un right_data_2).
  - split_pures; try (dump_pre_spatial; assumption); try (dump_pre_spatial; lia).
    dump_pre_spatial. unfold KeyAt in Hkey. lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (new_right :=
    replace_Znth index (Znth index right_data_2 0 + 1) right_data_2).
  Exists new_right left_data_2 tail_2 keys_2 sorted_2.
  assert (Hright : RightBuildState values (i + 1) keys_2 new_right).
  {
    unfold RightBuildState in PreH27 |- *.
    unfold new_right.
    eapply frequency_profile_increment__right_frequency;
      try eassumption; lia.
  }
  assert (Hnew_bounds : forall j, 0 <= j < un ->
    0 <= Znth j new_right 0 <= i + 1).
  {
    intros j Hj.
    unfold new_right.
    destruct (Z.eq_dec j index) as [-> | Hneq].
    - rewrite Znth_replace_Znth_Same by lia.
      specialize (PreH29 index ltac:(lia)). lia.
    - rewrite Znth_replace_Znth_Diff by lia.
      specialize (PreH29 j Hj). lia.
  }
  split_pure_spatial.
  - unfold new_right.
    cancel (Int64Array.full input_pre n_pre values).
    cancel (Int64Array.full a n_pre values).
    cancel (Int64Array.seg vals 0 un keys_2).
    cancel (Int64Array.seg vals un n_pre tail_2).
    cancel (Int64Array.full left un left_data_2).
    cancel (Int64Array.full right un
      (replace_Znth index (Znth index right_data_2 0 + 1) right_data_2)).
  - split_pures; try (dump_pre_spatial; assumption); try (dump_pre_spatial; lia).
    dump_pre_spatial. unfold new_right.
    rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hiend : i = n_pre) by lia.
  subst i.
  subst left_data_2.
  assert (Hleft :
    FrequencyProfile values 0 0 keys_2 (repeat_Z 0 un)).
  {
    unfold FrequencyProfile.
    split.
    - unfold repeat_Z.
      rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
      lia.
    - split; [lia |].
      split; [apply Zlength_nonneg |].
      intros j Hj.
      unfold repeat_Z.
      rewrite Znth_repeat.
      symmetry.
      apply set_card_empty__counting_init.
      intros x Hx. lia.
  }
  assert (Hright :
    FrequencyProfile values 0 (Zlength values) keys_2 right_data_2).
  {
    unfold RightBuildState in PreH25.
    rewrite <- PreH6.
    exact PreH25.
  }
  pose proof (counting_state_zero__counting_init
    k_pre values keys_2 (repeat_Z 0 un) right_data_2 Hleft Hright)
    as Hstate.
  Exists right_data_2 (repeat_Z 0 un) tail_2 keys_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + intros j Hj. unfold repeat_Z. rewrite Znth_repeat. lia.
    + intros j Hj. specialize (PreH27 j ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : 0 <= i < Zlength values) by lia.
  pose proof (lower_bound_key_at__counting_init
    values sorted_2 keys_2 i retval Hi PreH21 PreH23 PreH3) as Hkey.
  pose proof PreH30 as Hstate_parts.
  unfold CountingState in Hstate_parts.
  destruct Hstate_parts as [_ [Hright_profile _]].
  pose proof (frequency_profile_current_positive__counting_init
    values i keys_2 right_data_2 retval Hi Hkey Hright_profile)
    as Hpositive.
  assert (Hretval : retval < un).
  {
    pose proof Hkey as Hkey_parts.
    unfold KeyAt in Hkey_parts.
    lia.
  }
  pose proof (PreH32 retval ltac:(lia)) as Hright_bound.
  Exists right_data_2 left_data_2 tail_2 keys_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpred : KeyAt keys_2 (Znth i values 0 ÷ k_pre) retval).
  { unfold KeyAt. replace (retval - 0) with retval in PreH3 by lia.
    split; [rewrite PreH28; lia | exact PreH3]. }
  assert (Hsucc : KeyAt keys_2 (Znth i values 0 * k_pre) retval_2).
  { unfold KeyAt. replace (retval_2 - 0) with retval_2 in PreH1 by lia.
    split; [rewrite PreH28; lia | exact PreH1]. }
  pose proof (counting_state_advance_hit__counting_transitions
    k_pre values i keys_2 left_data_2 right_data_2 ans sorted_2
    ix retval retval_2 ltac:(rewrite <- PreH16; lia) PreH17 PreH34
    PreH39 PreH11 Hpred Hsucc PreH40) as Hnew.
  pose proof (counting_state_bounds__counting_transitions _ _ _ _ _ _ _ Hnew)
    as Hans_bounds.
  assert (Hleft_new : FrequencyProfile values 0 (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2))
    by exact (proj1 Hnew).
  assert (Hright_new : FrequencyProfile values (i + 1) (Zlength values) keys_2
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2))
    by exact (proj1 (proj2 Hnew)).
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hleft_new) as Hleft_bounds.
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hright_new) as Hright_bounds.
  Exists (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2)
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    tail_2 keys_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try nia.
    all: intros j Hj.
    + specialize (Hleft_bounds j ltac:(rewrite PreH28; exact Hj)). lia.
    + specialize (Hright_bounds j ltac:(rewrite PreH28; exact Hj)). nia.
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (lower_bound_absent_from_values__counting_transitions
    values sorted_2 keys_2 (Znth i values 0 * k_pre) retval_2
    PreH31 PreH33 PreH6 ltac:(left; rewrite PreH27; lia)) as Habs.
  assert (Hnew : CountingState k_pre values (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2) ans).
  { eapply counting_state_advance_miss__counting_transitions.
    - rewrite <- PreH15. lia.
    - exact PreH33.
    - exact PreH38.
    - exact PreH39.
    - right. intros z Hz. apply Habs. lia. }
  pose proof (counting_state_bounds__counting_transitions _ _ _ _ _ _ _ Hnew)
    as Hans_bounds.
  assert (Hleft_new : FrequencyProfile values 0 (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2))
    by exact (proj1 Hnew).
  assert (Hright_new : FrequencyProfile values (i + 1) (Zlength values) keys_2
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2))
    by exact (proj1 (proj2 Hnew)).
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hleft_new) as Hleft_bounds.
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hright_new) as Hright_bounds.
  Exists (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2)
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    tail_2 keys_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try nia.
    all: intros j Hj.
    + specialize (Hleft_bounds j ltac:(rewrite PreH27; exact Hj)). lia.
    + specialize (Hright_bounds j ltac:(rewrite PreH27; exact Hj)). nia.
Qed.

Lemma proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (lower_bound_absent_from_values__counting_transitions
    values sorted_2 keys_2 (Znth i values 0 ÷ k_pre) retval
    PreH29 PreH31 PreH7 ltac:(left; rewrite PreH25; lia)) as Habs.
  assert (Hnew : CountingState k_pre values (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2) ans).
  { eapply counting_state_advance_miss__counting_transitions.
    - rewrite <- PreH13. lia.
    - exact PreH31.
    - exact PreH36.
    - exact PreH37.
    - left. intros x Hx Heq.
      apply (Habs x ltac:(lia)).
      pose proof (quotient_times_divisor__counting_transitions
        (Znth i values 0) k_pre PreH8) as Hexact.
      nia. }
  pose proof (counting_state_bounds__counting_transitions _ _ _ _ _ _ _ Hnew)
    as Hans_bounds.
  assert (Hleft_new : FrequencyProfile values 0 (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2))
    by exact (proj1 Hnew).
  assert (Hright_new : FrequencyProfile values (i + 1) (Zlength values) keys_2
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2))
    by exact (proj1 (proj2 Hnew)).
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hleft_new) as Hleft_bounds.
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hright_new) as Hright_bounds.
  Exists (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2)
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    tail_2 keys_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try nia.
    all: intros j Hj.
    + specialize (Hleft_bounds j ltac:(rewrite PreH25; exact Hj)). lia.
    + specialize (Hright_bounds j ltac:(rewrite PreH25; exact Hj)). nia.
Qed.

Lemma proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (retval - 0) with retval in PreH1 by lia.
  pose proof (lower_bound_absent_from_values__counting_transitions
    values sorted_2 keys_2 (Znth i values 0 ÷ k_pre) retval
    PreH30 PreH32 PreH8 ltac:(right; exact PreH1)) as Habs.
  assert (Hnew : CountingState k_pre values (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2) ans).
  { eapply counting_state_advance_miss__counting_transitions.
    - rewrite <- PreH14. lia.
    - exact PreH32.
    - exact PreH37.
    - exact PreH38.
    - left. intros x Hx Heq.
      apply (Habs x ltac:(lia)).
      pose proof (quotient_times_divisor__counting_transitions
        (Znth i values 0) k_pre PreH9) as Hexact.
      nia. }
  pose proof (counting_state_bounds__counting_transitions _ _ _ _ _ _ _ Hnew)
    as Hans_bounds.
  assert (Hleft_new : FrequencyProfile values 0 (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2))
    by exact (proj1 Hnew).
  assert (Hright_new : FrequencyProfile values (i + 1) (Zlength values) keys_2
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2))
    by exact (proj1 (proj2 Hnew)).
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hleft_new) as Hleft_bounds.
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hright_new) as Hright_bounds.
  Exists (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2)
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    tail_2 keys_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try nia.
    all: intros j Hj.
    + specialize (Hleft_bounds j ltac:(rewrite PreH26; exact Hj)). lia.
    + specialize (Hright_bounds j ltac:(rewrite PreH26; exact Hj)). nia.
Qed.

Lemma proof_of_solver_entail_wit_12_5 : solver_entail_wit_12_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (retval_2 - 0) with retval_2 in PreH1 by lia.
  pose proof (lower_bound_absent_from_values__counting_transitions
    values sorted_2 keys_2 (Znth i values 0 * k_pre) retval_2
    PreH32 PreH34 PreH7 ltac:(right; exact PreH1)) as Habs.
  assert (Hnew : CountingState k_pre values (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2) ans).
  { eapply counting_state_advance_miss__counting_transitions.
    - rewrite <- PreH16. lia.
    - exact PreH34.
    - exact PreH39.
    - exact PreH40.
    - right. intros z Hz. apply Habs. lia. }
  pose proof (counting_state_bounds__counting_transitions _ _ _ _ _ _ _ Hnew)
    as Hans_bounds.
  assert (Hleft_new : FrequencyProfile values 0 (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2))
    by exact (proj1 Hnew).
  assert (Hright_new : FrequencyProfile values (i + 1) (Zlength values) keys_2
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2))
    by exact (proj1 (proj2 Hnew)).
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hleft_new) as Hleft_bounds.
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hright_new) as Hright_bounds.
  Exists (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2)
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    tail_2 keys_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try nia.
    all: intros j Hj.
    + specialize (Hleft_bounds j ltac:(rewrite PreH28; exact Hj)). lia.
    + specialize (Hright_bounds j ltac:(rewrite PreH28; exact Hj)). nia.
Qed.

Lemma proof_of_solver_entail_wit_12_6 : solver_entail_wit_12_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hnew : CountingState k_pre values (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2) ans).
  { eapply counting_state_advance_mod_miss__counting_transitions.
    - rewrite <- PreH6. lia.
    - exact PreH7.
    - exact PreH24.
    - exact PreH29.
    - exact PreH1.
    - exact PreH30. }
  pose proof (counting_state_bounds__counting_transitions _ _ _ _ _ _ _ Hnew)
    as Hans_bounds.
  assert (Hleft_new : FrequencyProfile values 0 (i + 1) keys_2
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2))
    by exact (proj1 Hnew).
  assert (Hright_new : FrequencyProfile values (i + 1) (Zlength values) keys_2
    (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2))
    by exact (proj1 (proj2 Hnew)).
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hleft_new) as Hleft_bounds.
  pose proof (frequency_profile_bounds__counting_transitions
    _ _ _ _ _ Hright_new) as Hright_bounds.
  Exists (replace_Znth ix (Znth ix right_data_2 0 - 1) right_data_2)
    (replace_Znth ix (Znth ix left_data_2 0 + 1) left_data_2)
    tail_2 keys_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try nia.
    all: intros j Hj.
    + specialize (Hleft_bounds j ltac:(rewrite PreH18; exact Hj)). lia.
    + specialize (Hright_bounds j ltac:(rewrite PreH18; exact Hj)). nia.
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia. subst i.
  assert (Hspec : Spec k_pre values ans).
  { apply counting_state_at_end__final_result with
      (keys := keys_2) (left := left_data_2) (right := right_data_2).
    rewrite <- PreH6. exact PreH27. }
  Exists right_data_2 left_data_2 tail_2 keys_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.seg_merge_to_full vals 0 un n_pre keys_2 tail_2
        ltac:(lia)).
    replace (vals + 0 * sizeof(INT64)) with vals by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_17_pure_split_goal_1 : solver_partial_solve_wit_17_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold LowerBoundResult, UniqueKeys in *; intuition lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_17_pure : solver_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_17_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_1 : solver_partial_solve_wit_21_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold KeyAt, UniqueKeys in *; intuition lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure : solver_partial_solve_wit_21_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_27_pure_split_goal_1 : solver_partial_solve_wit_27_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold LowerBoundResult, UniqueKeys in *; intuition lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_27_pure : solver_partial_solve_wit_27_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_27_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_28_pure_split_goal_1 : solver_partial_solve_wit_28_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold LowerBoundResult, UniqueKeys in *; intuition lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_28_pure : solver_partial_solve_wit_28_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_28_pure_split_goal_1.
Qed.
