From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.typeinfer_rc Require Import typeinfer_rc_goal.
From SimpleC.EE.Applications_human.typeinfer_rc Require Import typeinfer_rc_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.typeinfer_rc.typeinfer_rc.
Require Import SimpleC.EE.Applications_human.typeinfer_rc.typeinfer_rc_lib.
Local Open Scope sac.

Lemma proof_of_copy_atype_return_wit_1_nonnull : copy_atype_return_wit_1_nonnull.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (proj1 (TypeinferRCFrameCompat.missing_count_view M_nonnull t_pre n PreH1)).
  Exists (RCMap.retain M_nonnull t_pre).
  split_pure_spatial.
  - apply retain_world_count__copy_update; assumption.
  - split_pures; dump_pre_spatial.
    + reflexivity.
    + apply retain_normal__copy_update; split; [right; exact PreH6|reflexivity].
    + eapply retain_valid__copy_update; eauto.
    + apply RCMap.retain_preserves.
Qed.

Lemma proof_of_copy_atype_return_wit_2_null_split_goal_1 : copy_atype_return_wit_2_null_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply RCMap.preserves_refl.
Qed.

Lemma proof_of_copy_atype_return_wit_2_null_split_goal_2 : copy_atype_return_wit_2_null_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply retain_normal__copy_update; split; [left; reflexivity|].
  unfold RCMap.retain; destruct (Z.eq_dec 0 0); congruence.
Qed.

Lemma proof_of_copy_atype_return_wit_2_null : copy_atype_return_wit_2_null.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_copy_atype_return_wit_2_null_split_goal_1.
  - Goal_apply proof_of_copy_atype_return_wit_2_null_split_goal_2.
Qed.

Lemma proof_of_free_atype_safety_wit_5_nonnull_split_goal_1 : free_atype_safety_wit_5_nonnull_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH4 as [[He [Hcl [Ha [Hr [Hl Hd]]]]] Hp].
  specialize (Hl t_pre n PreH1).
  dump_pre_spatial. unfold rc_count in *; type_rcmap_reduce; cbn in *; lia.
Qed.

Lemma proof_of_free_atype_safety_wit_5_nonnull_split_goal_2 : free_atype_safety_wit_5_nonnull_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH4 as [[He [Hcl [Ha [Hr [Hl Hd]]]]] Hp].
  specialize (Hl t_pre n PreH1).
  dump_pre_spatial. unfold rc_count in *; type_rcmap_reduce; cbn in *; lia.
Qed.

Lemma proof_of_free_atype_safety_wit_5_nonnull : free_atype_safety_wit_5_nonnull.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_free_atype_safety_wit_5_nonnull_split_goal_1.
  - Goal_apply proof_of_free_atype_safety_wit_5_nonnull_split_goal_2.
Qed.

Lemma proof_of_free_atype_entail_wit_1_1_nonnull : free_atype_entail_wit_1_1_nonnull.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists n_2 M_post_3.
  split_pure_spatial.
  - unfold store_node_payload. rewrite PreH5, PreH8. cancel.
    cancel (store_world M_post_3).
  - split_pures; dump_pre_spatial; eauto using release_binary__release_children.
Qed.

Lemma proof_of_free_atype_entail_wit_1_2_nonnull : free_atype_entail_wit_1_2_nonnull.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists n_2 M_post_3.
  split_pure_spatial.
  - unfold store_node_payload. rewrite PreH5, PreH9. cancel.
    cancel (store_world M_post_3).
  - split_pures; dump_pre_spatial; eauto using release_binary__release_children.
Qed.

Lemma proof_of_free_atype_entail_wit_1_3_nonnull : free_atype_entail_wit_1_3_nonnull.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists n_2 (rc_delete M_nonnull t_pre n_2).
  split_pure_spatial.
  - rewrite PreH3.
    sep_apply (proj1 (store_world_missing_at M_nonnull
      ((t_pre,Tag)::(t_pre,RefCount)::nil) t_pre n_2 PreH4
      ltac:(simpl; intros; intuition congruence))).
    sep_apply_l_atomic (delete_world__release_delete M_nonnull t_pre n_2).
    reduce_field_masks; try solve [exfalso; congruence];
      unfold store_type_field, store_node_payload;
      destruct (node_tag n_2) as [|[[z|z|]|z|]|z]; cbn; Intros; cancel; try reflexivity.
    all: contradiction.
  - split_pures; dump_pre_spatial.
    + apply release_leaf__release_delete; auto; lia.
    + apply rc_delete_valid__release_delete; auto; lia.
Qed.

Lemma proof_of_free_atype_return_wit_1_null_split_goal_1 : free_atype_return_wit_1_null_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply release_null__release_scalar.
Qed.

Lemma proof_of_free_atype_return_wit_1_null : free_atype_return_wit_1_null.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_free_atype_return_wit_1_null_split_goal_1.
Qed.

Lemma proof_of_free_atype_return_wit_3_nonnull : free_atype_return_wit_3_nonnull.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (rc_decrement M_nonnull t_pre).
  split_pure_spatial.
  - sep_apply (proj1 (TypeinferRCFrameCompat.missing_count_view M_nonnull t_pre n PreH2)).
    unfold TypeinferRCFrameCompat.store_world_without_count. Intros m.
    sep_apply (decrement_world__release_decrement_open M_nonnull t_pre m ltac:(assumption)).
    cancel.
  - split_pures; dump_pre_spatial.
    + eapply release_decrement_rel__release_decrement_open; eauto; lia.
    + eapply rc_decrement_valid__release_decrement_open; eauto.
      * lia.
      * destruct PreH5 as [[He [Hcl [Ha [Hr [Hl Hd]]]]] Hp].
        specialize (Hl t_pre n PreH2); unfold rc_count in *; type_rcmap_reduce; lia.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_3_nonnull_pure_split_goal_1 : free_atype_partial_solve_wit_3_nonnull_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_free_atype_partial_solve_wit_3_nonnull_pure : free_atype_partial_solve_wit_3_nonnull_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_free_atype_partial_solve_wit_3_nonnull_pure_split_goal_1.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_4_nonnull_pure_split_goal_1 : free_atype_partial_solve_wit_4_nonnull_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (delete_child_credit__release_children M_nonnull t_pre n (node_a n)
    ltac:(assumption) ltac:(assumption)
    ltac:(rewrite node_children_binary__release_children by auto; simpl; auto))
    as [Hcredit [nq Hnode]].
  exact (live_nonzero__right_variable (rc_delete M_nonnull t_pre n)
    (node_a n) nq ltac:(assumption) Hnode).
Qed.

Lemma proof_of_free_atype_partial_solve_wit_4_nonnull_pure_split_goal_2 : free_atype_partial_solve_wit_4_nonnull_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (proj1 (delete_child_credit__release_children M_nonnull t_pre n (node_a n)
    ltac:(assumption) ltac:(assumption)
    ltac:(rewrite node_children_binary__release_children by auto; simpl; auto))).
  lia.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_4_nonnull_pure : free_atype_partial_solve_wit_4_nonnull_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_free_atype_partial_solve_wit_4_nonnull_pure_split_goal_1.
  - Goal_apply proof_of_free_atype_partial_solve_wit_4_nonnull_pure_split_goal_2.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_5_nonnull_pure_split_goal_1 : free_atype_partial_solve_wit_5_nonnull_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (release_second_child__release_children M_nonnull t_pre n M_post
    ltac:(assumption) ltac:(assumption) ltac:(auto)
    ltac:(assumption) ltac:(assumption) ltac:(assumption))
    as [Hcredit [nq Hnode]].
  exact (live_nonzero__right_variable M_post (node_b n) nq
    ltac:(assumption) Hnode).
Qed.

Lemma proof_of_free_atype_partial_solve_wit_5_nonnull_pure_split_goal_2 : free_atype_partial_solve_wit_5_nonnull_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (proj1 (release_second_child__release_children M_nonnull t_pre n M_post
    ltac:(assumption) ltac:(assumption) ltac:(auto)
    ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  lia.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_5_nonnull_pure : free_atype_partial_solve_wit_5_nonnull_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_free_atype_partial_solve_wit_5_nonnull_pure_split_goal_1.
  - Goal_apply proof_of_free_atype_partial_solve_wit_5_nonnull_pure_split_goal_2.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_6_nonnull_pure_split_goal_1 : free_atype_partial_solve_wit_6_nonnull_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_free_atype_partial_solve_wit_6_nonnull_pure : free_atype_partial_solve_wit_6_nonnull_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_free_atype_partial_solve_wit_6_nonnull_pure_split_goal_1.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_7_nonnull_pure_split_goal_1 : free_atype_partial_solve_wit_7_nonnull_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (delete_child_credit__release_children M_nonnull t_pre n (node_a n)
    ltac:(assumption) ltac:(assumption)
    ltac:(rewrite node_children_binary__release_children by auto; simpl; auto))
    as [Hcredit [nq Hnode]].
  exact (live_nonzero__right_variable (rc_delete M_nonnull t_pre n)
    (node_a n) nq ltac:(assumption) Hnode).
Qed.

Lemma proof_of_free_atype_partial_solve_wit_7_nonnull_pure_split_goal_2 : free_atype_partial_solve_wit_7_nonnull_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (proj1 (delete_child_credit__release_children M_nonnull t_pre n (node_a n)
    ltac:(assumption) ltac:(assumption)
    ltac:(rewrite node_children_binary__release_children by auto; simpl; auto))).
  lia.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_7_nonnull_pure : free_atype_partial_solve_wit_7_nonnull_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_free_atype_partial_solve_wit_7_nonnull_pure_split_goal_1.
  - Goal_apply proof_of_free_atype_partial_solve_wit_7_nonnull_pure_split_goal_2.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_8_nonnull_pure_split_goal_1 : free_atype_partial_solve_wit_8_nonnull_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (release_second_child__release_children M_nonnull t_pre n M_post
    ltac:(assumption) ltac:(assumption) ltac:(auto)
    ltac:(assumption) ltac:(assumption) ltac:(assumption))
    as [Hcredit [nq Hnode]].
  exact (live_nonzero__right_variable M_post (node_b n) nq
    ltac:(assumption) Hnode).
Qed.

Lemma proof_of_free_atype_partial_solve_wit_8_nonnull_pure_split_goal_2 : free_atype_partial_solve_wit_8_nonnull_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (proj1 (release_second_child__release_children M_nonnull t_pre n M_post
    ltac:(assumption) ltac:(assumption) ltac:(auto)
    ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  lia.
Qed.

Lemma proof_of_free_atype_partial_solve_wit_8_nonnull_pure : free_atype_partial_solve_wit_8_nonnull_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_free_atype_partial_solve_wit_8_nonnull_pure_split_goal_1.
  - Goal_apply proof_of_free_atype_partial_solve_wit_8_nonnull_pure_split_goal_2.
Qed.

Lemma proof_of_free_atype_which_implies_wit_1_split_goal_1 : free_atype_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply rc_delete_valid__release_delete; eauto; lia.
Qed.

Lemma proof_of_free_atype_which_implies_wit_1_split_goal_spatial : free_atype_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (proj1 (store_world_missing_at M_nonnull
    ((t,Payload1)::(t,Payload0)::(t,Tag)::(t,RefCount)::nil) t n PreH2
    ltac:(simpl; intros; intuition congruence))).
  sep_apply_l_atomic (delete_world__release_delete M_nonnull t n).
  reduce_field_masks; try solve [exfalso; congruence];
    cbn; Intros; cancel; try reflexivity.
  all: contradiction.
Qed.

Lemma proof_of_free_atype_which_implies_wit_1 : free_atype_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_free_atype_which_implies_wit_1_split_goal_spatial.
  - Goal_apply proof_of_free_atype_which_implies_wit_1_split_goal_1.
Qed.

Lemma proof_of_free_atype_which_implies_wit_2_split_goal_1 : free_atype_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply rc_delete_valid__release_delete; eauto; lia.
Qed.

Lemma proof_of_free_atype_which_implies_wit_2_split_goal_spatial : free_atype_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (proj1 (store_world_missing_at M_nonnull
    ((t,Payload1)::(t,Payload0)::(t,Tag)::(t,RefCount)::nil) t n PreH2
    ltac:(simpl; intros; intuition congruence))).
  sep_apply_l_atomic (delete_world__release_delete M_nonnull t n).
  reduce_field_masks; try solve [exfalso; congruence];
    cbn; Intros; cancel; try reflexivity.
  all: contradiction.
Qed.

Lemma proof_of_free_atype_which_implies_wit_2 : free_atype_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_free_atype_which_implies_wit_2_split_goal_spatial.
  - Goal_apply proof_of_free_atype_which_implies_wit_2_split_goal_1.
Qed.

Lemma proof_of_atype_unify_entail_wit_1_2_split_goal_1 : atype_unify_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify_entail_wit_1_2 : atype_unify_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify_entail_wit_1_2_split_goal_1.
Qed.

Lemma proof_of_atype_unify_entail_wit_2_1_split_goal_1 : atype_unify_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify_entail_wit_2_1 : atype_unify_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_atype_unify_return_wit_1_split_goal_1 : atype_unify_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst retval.
  eapply direct_stage_result__stage0_direct; eauto.
Qed.

Lemma proof_of_atype_unify_return_wit_1 : atype_unify_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_atype_unify_return_wit_2_split_goal_1 : atype_unify_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply direct_stage_result__stage0_direct; eauto.
Qed.

Lemma proof_of_atype_unify_return_wit_2 : atype_unify_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_atype_unify_return_wit_3_split_goal_1 : atype_unify_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst retval.
  eapply direct_stage_result__stage0_direct with (np := n); eauto.
  right; apply empty_slot__stage0_direct; assumption.
Qed.

Lemma proof_of_atype_unify_return_wit_3 : atype_unify_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_atype_unify_return_wit_4_split_goal_1 : atype_unify_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply direct_stage_result__stage0_direct with (np := n); eauto.
  right; apply empty_slot__stage0_direct; assumption.
Qed.

Lemma proof_of_atype_unify_return_wit_4 : atype_unify_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_atype_unify_return_wit_5 : atype_unify_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia).
  destruct (repr_decode__representative_cleanup _ _ _ _ _ PreH20) as [trtmp Hdtmp].
  destruct (temporary_release__representative_cleanup _ _ _ _ _ _
    PreH38 PreH21 PreH12 Hdtmp PreH25 PreH13 PreH14 PreH1) as [Hdec [Hpres Hsame]].
  destruct (decode_live__representative_cleanup _ _ _ PreH40) as [nq Hq].
  Exists M_post_5 s_post_3.
  split_pure_spatial.
  - rewrite Hdec.
    sep_apply_l_atomic (solution_cleanup__representative_cleanup M_post_4 retval_3 (&("res")) s_post_3).
    cancel.
  - split_pures; dump_pre_spatial; auto.
    + rewrite PreH33. eapply unify_repr_left__representative_cleanup; eauto.
    + eapply infer_repr_left__representative_cleanup; eauto.
Qed.

Lemma proof_of_atype_unify_return_wit_6 : atype_unify_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia).
  destruct (repr_decode__representative_cleanup _ _ _ _ _ PreH19) as [trtmp Hdtmp].
  destruct (temporary_release__representative_cleanup _ _ _ _ _ _
    PreH37 PreH20 PreH11 Hdtmp PreH24 PreH12 PreH13 PreH1) as [Hdec [Hpres Hsame]].
  destruct (decode_live__representative_cleanup _ _ _ PreH39) as [nq Hq].
  Exists M_post_5 s_post_3.
  split_pure_spatial.
  - rewrite Hdec.
    sep_apply_l_atomic (solution_cleanup__representative_cleanup M_post_4 retval_3 (&("res")) s_post_3).
    cancel.
  - split_pures; dump_pre_spatial; auto.
    eapply infer_repr_left__representative_cleanup; eauto.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_4_pure_split_goal_1 : atype_unify_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (repr_entry_left__representative_entry M_verify s_verify t1_pre t2_pre (node_a n) tr2_verify) as He.
  assert (Hs : s_verify (node_a n) <> None) by (unfold solution_at in *; congruence).
  destruct (He ltac:(assumption) ltac:(assumption) Hs ltac:(assumption)) as [Hsafe Hnext].
  intros q out_tr [Hd Hr].
  cbn [node_a] in Hr.
  eapply repr_headroom__representative_entry; eauto.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_4_pure_split_goal_2 : atype_unify_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (repr_entry_left__representative_entry M_verify s_verify t1_pre t2_pre (node_a n) tr2_verify) as He.
  assert (Hs : s_verify (node_a n) <> None) by (unfold solution_at in *; congruence).
  destruct (He ltac:(assumption) ltac:(assumption) Hs ltac:(assumption)) as [Hsafe Hnext].
  intros q out_tr [Hd Hr].
  cbn [node_a] in Hr.
  eapply repr_headroom__representative_entry; eauto.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_4_pure : atype_unify_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_4_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_5_pure_split_goal_1 : atype_unify_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply repr_terminal_self__representative_entry; eauto.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_5_pure_split_goal_2 : atype_unify_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (repr_entry_left__representative_entry M_verify s_verify t1_pre t2_pre (node_a n) tr2_verify) as He.
  assert (Hs : s_verify (node_a n) <> None) by (unfold solution_at in *; congruence).
  destruct (He ltac:(assumption) ltac:(assumption) Hs ltac:(assumption)) as [Hsafe Hnext].
  eapply Hnext; eauto.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_5_pure : atype_unify_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_6_pure_split_goal_1 : atype_unify_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (decode_live__stage1_direct M_post retval tr_out ltac:(assumption)) as [nd Hnd].
  exact (live_nonzero__right_variable M_post retval nd ltac:(assumption) Hnd).
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_6_pure_split_goal_2 : atype_unify_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (decode_live__stage1_direct M_post retval tr_out ltac:(assumption)) as [nd Hnd].
  pose proof (live_nonzero__right_variable M_post retval nd ltac:(assumption) Hnd) as Hp.
  match goal with
  | Hret : retain_rel ?B retval M_post_2 |- _ =>
      exact (proj1 (retained_credit__representative_cleanup
        B M_post_2 M_post retval ltac:(assumption) ltac:(assumption)
        Hret ltac:(assumption) Hp))
  end.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_6_pure : atype_unify_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_6_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_7_pure_split_goal_1 : atype_unify_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (decode_live__stage1_direct M_post retval tr_out ltac:(assumption)) as [nd Hnd].
  exact (live_nonzero__right_variable M_post retval nd ltac:(assumption) Hnd).
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_7_pure_split_goal_2 : atype_unify_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (decode_live__stage1_direct M_post retval tr_out ltac:(assumption)) as [nd Hnd].
  pose proof (live_nonzero__right_variable M_post retval nd ltac:(assumption) Hnd) as Hp.
  match goal with
  | Hret : retain_rel ?B retval M_post_2 |- _ =>
      exact (proj1 (retained_credit__representative_cleanup
        B M_post_2 M_post retval ltac:(assumption) ltac:(assumption)
        Hret ltac:(assumption) Hp))
  end.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_7_pure : atype_unify_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_7_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_8_pure_split_goal_1 : atype_unify_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply repr_empty__stage1_direct; eauto.
  apply empty_slot__stage1_direct; assumption.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_8_pure_split_goal_2 : atype_unify_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply direct_stage_capacity__stage0_direct; eauto.
  right; cbn; apply empty_slot__stage1_direct; assumption.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_8_pure : atype_unify_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_8_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_9_pure_split_goal_1 : atype_unify_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply repr_nonvar__stage1_direct; eauto.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_9_pure_split_goal_2 : atype_unify_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply direct_stage_capacity__stage0_direct; eauto.
Qed.

Lemma proof_of_atype_unify_partial_solve_wit_9_pure : atype_unify_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify_partial_solve_wit_9_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify1_entail_wit_1_2_split_goal_1 : atype_unify1_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify1_entail_wit_1_2 : atype_unify1_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify1_entail_wit_1_2_split_goal_1.
Qed.

Lemma proof_of_atype_unify1_entail_wit_2_1_split_goal_1 : atype_unify1_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify1_entail_wit_2_1 : atype_unify1_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify1_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_atype_unify1_return_wit_1_split_goal_1 : atype_unify1_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval.
  eapply direct_result__stage1_direct; eauto.
Qed.

Lemma proof_of_atype_unify1_return_wit_1 : atype_unify1_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify1_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_atype_unify1_return_wit_2_split_goal_1 : atype_unify1_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply direct_result__stage1_direct; eauto.
Qed.

Lemma proof_of_atype_unify1_return_wit_2 : atype_unify1_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify1_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_atype_unify1_return_wit_3_split_goal_1 : atype_unify1_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval.
  eapply direct_result__stage1_direct with (tr := tr1) (nq := n); eauto.
  right; apply empty_slot__stage1_direct; assumption.
Qed.

Lemma proof_of_atype_unify1_return_wit_3 : atype_unify1_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify1_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_atype_unify1_return_wit_4_split_goal_1 : atype_unify1_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply direct_result__stage1_direct with (tr := tr1) (nq := n); eauto.
  right; apply empty_slot__stage1_direct; assumption.
Qed.

Lemma proof_of_atype_unify1_return_wit_4 : atype_unify1_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify1_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_atype_unify1_return_wit_5 : atype_unify1_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia).
  destruct (repr_decode__representative_cleanup _ _ _ _ _ PreH20) as [trtmp Hdtmp].
  destruct (temporary_release__representative_cleanup _ _ _ _ _ _
    PreH38 PreH21 PreH12 Hdtmp PreH25 PreH13 PreH14 PreH1) as [Hdec [Hpres Hsame]].
  destruct (decode_live__representative_cleanup _ _ _ PreH39) as [np Hp].
  Exists M_post_5 s_post_3.
  split_pure_spatial.
  - rewrite Hdec.
    sep_apply_l_atomic (solution_cleanup__representative_cleanup M_post_4 retval_3 (&("res")) s_post_3).
    cancel.
  - split_pures; dump_pre_spatial; auto.
    + rewrite PreH33. eapply unify_repr_right__representative_cleanup; eauto.
    + eapply infer_repr_right__representative_cleanup; eauto.
Qed.

Lemma proof_of_atype_unify1_return_wit_6 : atype_unify1_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia).
  destruct (repr_decode__representative_cleanup _ _ _ _ _ PreH19) as [trtmp Hdtmp].
  destruct (temporary_release__representative_cleanup _ _ _ _ _ _
    PreH37 PreH20 PreH11 Hdtmp PreH24 PreH12 PreH13 PreH1) as [Hdec [Hpres Hsame]].
  destruct (decode_live__representative_cleanup _ _ _ PreH38) as [np Hp].
  Exists M_post_5 s_post_3.
  split_pure_spatial.
  - rewrite Hdec.
    sep_apply_l_atomic (solution_cleanup__representative_cleanup M_post_4 retval_3 (&("res")) s_post_3).
    cancel.
  - split_pures; dump_pre_spatial; auto.
    eapply infer_repr_right__representative_cleanup; eauto.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_4_pure_split_goal_1 : atype_unify1_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (repr_entry_right__representative_entry M0 s t1_pre t2_pre (node_a n) tr1) as He.
  assert (Hs : s (node_a n) <> None) by (unfold solution_at in *; congruence).
  destruct (He ltac:(assumption) ltac:(assumption) Hs ltac:(assumption)) as [Hsafe Hnext].
  intros q out_tr [Hd Hr].
  cbn [node_a] in Hr.
  eapply repr_headroom__representative_entry; eauto.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_4_pure_split_goal_2 : atype_unify1_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (repr_entry_right__representative_entry M0 s t1_pre t2_pre (node_a n) tr1) as He.
  assert (Hs : s (node_a n) <> None) by (unfold solution_at in *; congruence).
  destruct (He ltac:(assumption) ltac:(assumption) Hs ltac:(assumption)) as [Hsafe Hnext].
  intros q out_tr [Hd Hr].
  cbn [node_a] in Hr.
  eapply repr_headroom__representative_entry; eauto.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_4_pure : atype_unify1_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_4_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_5_pure_split_goal_1 : atype_unify1_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply repr_terminal_self__representative_entry; eauto.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_5_pure_split_goal_2 : atype_unify1_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (repr_entry_right__representative_entry M0 s t1_pre t2_pre (node_a n) tr1) as He.
  assert (Hs : s (node_a n) <> None) by (unfold solution_at in *; congruence).
  destruct (He ltac:(assumption) ltac:(assumption) Hs ltac:(assumption)) as [Hsafe Hnext].
  eapply Hnext; eauto.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_5_pure : atype_unify1_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_6_pure_split_goal_1 : atype_unify1_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (decode_live__stage1_direct M_post retval tr_out ltac:(assumption)) as [nd Hnd].
  exact (live_nonzero__right_variable M_post retval nd ltac:(assumption) Hnd).
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_6_pure_split_goal_2 : atype_unify1_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (decode_live__stage1_direct M_post retval tr_out ltac:(assumption)) as [nd Hnd].
  pose proof (live_nonzero__right_variable M_post retval nd ltac:(assumption) Hnd) as Hp.
  match goal with
  | Hret : retain_rel ?B retval M_post_2 |- _ =>
      exact (proj1 (retained_credit__representative_cleanup
        B M_post_2 M_post retval ltac:(assumption) ltac:(assumption)
        Hret ltac:(assumption) Hp))
  end.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_6_pure : atype_unify1_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_6_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_7_pure_split_goal_1 : atype_unify1_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (decode_live__stage1_direct M_post retval tr_out ltac:(assumption)) as [nd Hnd].
  exact (live_nonzero__right_variable M_post retval nd ltac:(assumption) Hnd).
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_7_pure_split_goal_2 : atype_unify1_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (decode_live__stage1_direct M_post retval tr_out ltac:(assumption)) as [nd Hnd].
  pose proof (live_nonzero__right_variable M_post retval nd ltac:(assumption) Hnd) as Hp.
  match goal with
  | Hret : retain_rel ?B retval M_post_2 |- _ =>
      exact (proj1 (retained_credit__representative_cleanup
        B M_post_2 M_post retval ltac:(assumption) ltac:(assumption)
        Hret ltac:(assumption) Hp))
  end.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_7_pure : atype_unify1_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_7_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_8_pure_split_goal_1 : atype_unify1_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply repr_empty__stage1_direct; eauto.
  apply empty_slot__stage1_direct; assumption.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_8_pure_split_goal_2 : atype_unify1_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply direct_capacity__stage1_direct; eauto.
  right; cbn; apply empty_slot__stage1_direct; assumption.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_8_pure : atype_unify1_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_8_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_9_pure_split_goal_1 : atype_unify1_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply repr_nonvar__stage1_direct; eauto.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_9_pure_split_goal_2 : atype_unify1_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply direct_capacity__stage1_direct; eauto.
Qed.

Lemma proof_of_atype_unify1_partial_solve_wit_9_pure : atype_unify1_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify1_partial_solve_wit_9_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify2_entail_wit_1_1_same_node_split_goal_1 : atype_unify2_entail_wit_1_1_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify2_entail_wit_1_1_same_node : atype_unify2_entail_wit_1_1_same_node.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_entail_wit_1_1_same_node_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_entail_wit_1_3_distinct_nodes_split_goal_1 : atype_unify2_entail_wit_1_3_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify2_entail_wit_1_3_distinct_nodes : atype_unify2_entail_wit_1_3_distinct_nodes.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_entail_wit_1_3_distinct_nodes_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_entail_wit_2_2_same_node_split_goal_1 : atype_unify2_entail_wit_2_2_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify2_entail_wit_2_2_same_node : atype_unify2_entail_wit_2_2_same_node.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_entail_wit_2_2_same_node_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_entail_wit_2_4_distinct_nodes_split_goal_1 : atype_unify2_entail_wit_2_4_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify2_entail_wit_2_4_distinct_nodes : atype_unify2_entail_wit_2_4_distinct_nodes.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_entail_wit_2_4_distinct_nodes_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_entail_wit_3_1_distinct_nodes_split_goal_1 : atype_unify2_entail_wit_3_1_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify2_entail_wit_3_1_distinct_nodes : atype_unify2_entail_wit_3_1_distinct_nodes.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_entail_wit_3_1_distinct_nodes_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_entail_wit_4_2_distinct_nodes_split_goal_1 : atype_unify2_entail_wit_4_2_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_atype_unify2_entail_wit_4_2_distinct_nodes : atype_unify2_entail_wit_4_2_distinct_nodes.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_entail_wit_4_2_distinct_nodes_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_1_distinct_nodes_split_goal_1 : atype_unify2_return_wit_1_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intro; reflexivity.
Qed.

Lemma proof_of_atype_unify2_return_wit_1_distinct_nodes_split_goal_2 : atype_unify2_return_wit_1_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply RCMap.preserves_refl.
Qed.

Lemma proof_of_atype_unify2_return_wit_1_distinct_nodes_split_goal_3 : atype_unify2_return_wit_1_distinct_nodes_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with |- infer_result 2 ?m ?ss ?p ?q _ ?m ?ss =>
    pose proof (atom_normal__atom_and_mismatch m ss p q n n_2 PreH13 PreH9 PreH2 ltac:(lia)) as Hatom end.
  destruct (Z.eq_dec (node_a n) (node_a n_2)); [contradiction|exact Hatom].
Qed.

Lemma proof_of_atype_unify2_return_wit_1_distinct_nodes : atype_unify2_return_wit_1_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_1_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_1_distinct_nodes_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_1_distinct_nodes_split_goal_3.
Qed.

Lemma proof_of_atype_unify2_return_wit_2_same_node_split_goal_1 : atype_unify2_return_wit_2_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intro; reflexivity.
Qed.

Lemma proof_of_atype_unify2_return_wit_2_same_node_split_goal_2 : atype_unify2_return_wit_2_same_node_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply RCMap.preserves_refl.
Qed.

Lemma proof_of_atype_unify2_return_wit_2_same_node_split_goal_3 : atype_unify2_return_wit_2_same_node_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst t1_pre.
  match goal with |- infer_result 2 ?m ?ss ?p ?p 0 ?m ?ss =>
    pose proof (atom_normal__atom_and_mismatch m ss p p n n PreH8 PreH8 PreH1 PreH1) as Hatom end.
  destruct (Z.eq_dec (node_a n) (node_a n)); [exact Hatom|contradiction].
Qed.

Lemma proof_of_atype_unify2_return_wit_2_same_node_split_goal_4 : atype_unify2_return_wit_2_same_node_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst t1_pre.
  assert (E1 : tr1 = TAtom (node_a n)) by (eapply decode_atom__atom_and_mismatch; eauto).
  assert (E2 : tr2 = TAtom (node_a n)) by (eapply decode_atom__atom_and_mismatch; eauto).
  eapply unify_rel_atom with (n := node_a n); rewrite <- E1 in *; congruence.
Qed.

Lemma proof_of_atype_unify2_return_wit_2_same_node : atype_unify2_return_wit_2_same_node.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_2_same_node_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_2_same_node_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_2_same_node_split_goal_3.
  - Goal_apply proof_of_atype_unify2_return_wit_2_same_node_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_return_wit_3_distinct_nodes_split_goal_1 : atype_unify2_return_wit_3_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intro; reflexivity.
Qed.

Lemma proof_of_atype_unify2_return_wit_3_distinct_nodes_split_goal_2 : atype_unify2_return_wit_3_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply RCMap.preserves_refl.
Qed.

Lemma proof_of_atype_unify2_return_wit_3_distinct_nodes_split_goal_3 : atype_unify2_return_wit_3_distinct_nodes_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with |- infer_result 2 ?m ?ss ?p ?q _ ?m ?ss =>
    pose proof (atom_normal__atom_and_mismatch m ss p q n n_2 PreH13 PreH9 PreH2 ltac:(lia)) as Hatom end.
  destruct (Z.eq_dec (node_a n) (node_a n_2)); [exact Hatom|contradiction].
Qed.

Lemma proof_of_atype_unify2_return_wit_3_distinct_nodes_split_goal_4 : atype_unify2_return_wit_3_distinct_nodes_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (E1 : tr1 = TAtom (node_a n)) by (eapply decode_atom__atom_and_mismatch; eauto).
  assert (E2 : tr2 = TAtom (node_a n_2)) by (eapply decode_atom__atom_and_mismatch; eauto; lia).
  eapply unify_rel_atom with (n := node_a n); rewrite <- E1, <- PreH1 in *; congruence.
Qed.

Lemma proof_of_atype_unify2_return_wit_3_distinct_nodes : atype_unify2_return_wit_3_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_3_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_3_distinct_nodes_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_3_distinct_nodes_split_goal_3.
  - Goal_apply proof_of_atype_unify2_return_wit_3_distinct_nodes_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_return_wit_4_same_node_split_goal_1 : atype_unify2_return_wit_4_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rc_reservations_same in *.
  intro p; etransitivity; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_4_same_node_split_goal_2 : atype_unify2_return_wit_4_same_node_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply preserves_trans__app_success; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_4_same_node_split_goal_3 : atype_unify2_return_wit_4_same_node_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply infer_binary_normal__app_success with (Mc := M_post_3) (sc := s_post_3); eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_4_same_node_split_goal_4 : atype_unify2_return_wit_4_same_node_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst t1_pre.
  assert (tr1 = tr2) as E by (eapply decode_type_unique; eauto).
  subst tr2 tr1.
  eapply unify_rel_apply with (s1 := s_post_3); eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_4_same_node : atype_unify2_return_wit_4_same_node.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_4_same_node_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_4_same_node_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_4_same_node_split_goal_3.
  - Goal_apply proof_of_atype_unify2_return_wit_4_same_node_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_return_wit_5_same_node_split_goal_1 : atype_unify2_return_wit_5_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rc_reservations_same in *.
  intro p; etransitivity; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_5_same_node_split_goal_2 : atype_unify2_return_wit_5_same_node_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply preserves_trans__app_success; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_5_same_node_split_goal_3 : atype_unify2_return_wit_5_same_node_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply infer_binary_normal__app_success with (Mc := M_post_3) (sc := s_post_3); eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_5_same_node : atype_unify2_return_wit_5_same_node.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_5_same_node_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_5_same_node_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_5_same_node_split_goal_3.
Qed.

Lemma proof_of_atype_unify2_return_wit_6_distinct_nodes_split_goal_1 : atype_unify2_return_wit_6_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rc_reservations_same in *.
  intro p; etransitivity; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_6_distinct_nodes_split_goal_2 : atype_unify2_return_wit_6_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply preserves_trans__app_success; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_6_distinct_nodes_split_goal_3 : atype_unify2_return_wit_6_distinct_nodes_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply infer_binary_normal__app_success with (Mc := M_post_3) (sc := s_post_3); eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_6_distinct_nodes_split_goal_4 : atype_unify2_return_wit_6_distinct_nodes_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst tr1 tr2.
  eapply unify_rel_apply with (s1 := s_post_3); eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_6_distinct_nodes : atype_unify2_return_wit_6_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_6_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_6_distinct_nodes_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_6_distinct_nodes_split_goal_3.
  - Goal_apply proof_of_atype_unify2_return_wit_6_distinct_nodes_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_return_wit_7_distinct_nodes_split_goal_1 : atype_unify2_return_wit_7_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rc_reservations_same in *.
  intro p; etransitivity; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_7_distinct_nodes_split_goal_2 : atype_unify2_return_wit_7_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply preserves_trans__app_success; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_7_distinct_nodes_split_goal_3 : atype_unify2_return_wit_7_distinct_nodes_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply infer_binary_normal__app_success with (Mc := M_post_3) (sc := s_post_3); eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_7_distinct_nodes : atype_unify2_return_wit_7_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_7_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_7_distinct_nodes_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_7_distinct_nodes_split_goal_3.
Qed.

Lemma proof_of_atype_unify2_return_wit_8_same_node_split_goal_1 : atype_unify2_return_wit_8_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply infer_binary_failure__binary_failure; eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_8_same_node : atype_unify2_return_wit_8_same_node.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_8_same_node_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_9_distinct_nodes_split_goal_1 : atype_unify2_return_wit_9_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply infer_binary_failure__binary_failure; eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_9_distinct_nodes : atype_unify2_return_wit_9_distinct_nodes.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_9_distinct_nodes_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_10_distinct_nodes_split_goal_1 : atype_unify2_return_wit_10_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rc_reservations_same in *; intro p; etransitivity; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_10_distinct_nodes_split_goal_2 : atype_unify2_return_wit_10_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply preserves_trans__app_success; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_10_distinct_nodes_split_goal_3 : atype_unify2_return_wit_10_distinct_nodes_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval_2.
  subst retval.
  eapply infer_binary_normal__arrow_success with
    (Mc := M_post_3) (sc := s_post_3) (n1 := n) (n2 := n_2); eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_10_distinct_nodes_split_goal_4 : atype_unify2_return_wit_10_distinct_nodes_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst tr1 tr2.
  eapply unify_rel_arrow with (s1 := s_post_3); eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_10_distinct_nodes : atype_unify2_return_wit_10_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_10_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_10_distinct_nodes_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_10_distinct_nodes_split_goal_3.
  - Goal_apply proof_of_atype_unify2_return_wit_10_distinct_nodes_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_return_wit_11_distinct_nodes_split_goal_1 : atype_unify2_return_wit_11_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rc_reservations_same in *; intro p; etransitivity; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_11_distinct_nodes_split_goal_2 : atype_unify2_return_wit_11_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply preserves_trans__app_success; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_11_distinct_nodes_split_goal_3 : atype_unify2_return_wit_11_distinct_nodes_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval_2.
  eapply infer_binary_normal__arrow_success with
    (Mc := M_post_3) (sc := s_post_3) (n1 := n) (n2 := n_2); eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_11_distinct_nodes : atype_unify2_return_wit_11_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_11_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_11_distinct_nodes_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_11_distinct_nodes_split_goal_3.
Qed.

Lemma proof_of_atype_unify2_return_wit_12_same_node_split_goal_1 : atype_unify2_return_wit_12_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rc_reservations_same in *; intro p; etransitivity; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_12_same_node_split_goal_2 : atype_unify2_return_wit_12_same_node_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply preserves_trans__app_success; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_12_same_node_split_goal_3 : atype_unify2_return_wit_12_same_node_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval_2.
  subst retval.
  subst t1_pre.
  eapply infer_binary_normal__arrow_success with
    (Mc := M_post_3) (sc := s_post_3) (n1 := n) (n2 := n); eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_12_same_node_split_goal_4 : atype_unify2_return_wit_12_same_node_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst t1_pre.
  assert (tr1 = tr2) as Heq.
  { unfold store_type in *; eapply decode_type_unique; eauto. }
  subst tr2 tr1.
  eapply unify_rel_arrow with (s1 := s_post_3); eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_12_same_node : atype_unify2_return_wit_12_same_node.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_12_same_node_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_12_same_node_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_12_same_node_split_goal_3.
  - Goal_apply proof_of_atype_unify2_return_wit_12_same_node_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_return_wit_13_same_node_split_goal_1 : atype_unify2_return_wit_13_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rc_reservations_same in *; intro p; etransitivity; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_13_same_node_split_goal_2 : atype_unify2_return_wit_13_same_node_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply preserves_trans__app_success; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_13_same_node_split_goal_3 : atype_unify2_return_wit_13_same_node_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval_2.
  subst t1_pre.
  eapply infer_binary_normal__arrow_success with
    (Mc := M_post_3) (sc := s_post_3) (n1 := n) (n2 := n); eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_13_same_node : atype_unify2_return_wit_13_same_node.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_13_same_node_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_13_same_node_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_13_same_node_split_goal_3.
Qed.

Lemma proof_of_atype_unify2_return_wit_14_distinct_nodes_split_goal_1 : atype_unify2_return_wit_14_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply infer_binary_failure__binary_failure; eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_14_distinct_nodes : atype_unify2_return_wit_14_distinct_nodes.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_14_distinct_nodes_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_15_same_node_split_goal_1 : atype_unify2_return_wit_15_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  eapply infer_binary_failure__binary_failure; eauto; lia.
Qed.

Lemma proof_of_atype_unify2_return_wit_15_same_node : atype_unify2_return_wit_15_same_node.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_return_wit_15_same_node_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_return_wit_16_distinct_nodes_split_goal_1 : atype_unify2_return_wit_16_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intro; reflexivity.
Qed.

Lemma proof_of_atype_unify2_return_wit_16_distinct_nodes_split_goal_2 : atype_unify2_return_wit_16_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply RCMap.preserves_refl.
Qed.

Lemma proof_of_atype_unify2_return_wit_16_distinct_nodes_split_goal_3 : atype_unify2_return_wit_16_distinct_nodes_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply mismatch_normal__atom_and_mismatch; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_16_distinct_nodes : atype_unify2_return_wit_16_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_16_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_16_distinct_nodes_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_16_distinct_nodes_split_goal_3.
Qed.

Lemma proof_of_atype_unify2_return_wit_17_distinct_nodes_split_goal_1 : atype_unify2_return_wit_17_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply right_infer_success__right_variable; eauto using decode_not_var__right_variable.
Qed.

Lemma proof_of_atype_unify2_return_wit_17_distinct_nodes_split_goal_2 : atype_unify2_return_wit_17_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst tr2.
  eapply unify_rel_right_var; eauto using decode_not_var__right_variable.
Qed.

Lemma proof_of_atype_unify2_return_wit_17_distinct_nodes : atype_unify2_return_wit_17_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_17_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_17_distinct_nodes_split_goal_2.
Qed.

Lemma proof_of_atype_unify2_return_wit_18_distinct_nodes_split_goal_1 : atype_unify2_return_wit_18_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intro; reflexivity.
Qed.

Lemma proof_of_atype_unify2_return_wit_18_distinct_nodes_split_goal_2 : atype_unify2_return_wit_18_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply RCMap.preserves_refl.
Qed.

Lemma proof_of_atype_unify2_return_wit_18_distinct_nodes_split_goal_3 : atype_unify2_return_wit_18_distinct_nodes_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply variable_failure_right__variable_failure; eauto using decoded_nonvariable__stage0_direct.
Qed.

Lemma proof_of_atype_unify2_return_wit_18_distinct_nodes : atype_unify2_return_wit_18_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_18_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_18_distinct_nodes_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_18_distinct_nodes_split_goal_3.
Qed.

Lemma proof_of_atype_unify2_return_wit_19_same_node_split_goal_1 : atype_unify2_return_wit_19_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst t1_pre.
  eapply left_variable_normal__left_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_19_same_node_split_goal_2 : atype_unify2_return_wit_19_same_node_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst tr1.
  eapply unify_rel_left_var; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_19_same_node : atype_unify2_return_wit_19_same_node.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_19_same_node_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_19_same_node_split_goal_2.
Qed.

Lemma proof_of_atype_unify2_return_wit_20_distinct_nodes_split_goal_1 : atype_unify2_return_wit_20_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply left_variable_normal__left_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_20_distinct_nodes_split_goal_2 : atype_unify2_return_wit_20_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst tr1.
  eapply unify_rel_left_var; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_20_distinct_nodes : atype_unify2_return_wit_20_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_20_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_20_distinct_nodes_split_goal_2.
Qed.

Lemma proof_of_atype_unify2_return_wit_21_same_node_split_goal_1 : atype_unify2_return_wit_21_same_node_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intro; reflexivity.
Qed.

Lemma proof_of_atype_unify2_return_wit_21_same_node_split_goal_2 : atype_unify2_return_wit_21_same_node_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply RCMap.preserves_refl.
Qed.

Lemma proof_of_atype_unify2_return_wit_21_same_node_split_goal_3 : atype_unify2_return_wit_21_same_node_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst t1_pre.
  eapply variable_failure_left__variable_failure; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_21_same_node : atype_unify2_return_wit_21_same_node.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_21_same_node_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_21_same_node_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_21_same_node_split_goal_3.
Qed.

Lemma proof_of_atype_unify2_return_wit_22_distinct_nodes_split_goal_1 : atype_unify2_return_wit_22_distinct_nodes_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intro; reflexivity.
Qed.

Lemma proof_of_atype_unify2_return_wit_22_distinct_nodes_split_goal_2 : atype_unify2_return_wit_22_distinct_nodes_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply RCMap.preserves_refl.
Qed.

Lemma proof_of_atype_unify2_return_wit_22_distinct_nodes_split_goal_3 : atype_unify2_return_wit_22_distinct_nodes_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply variable_failure_left__variable_failure; eauto.
Qed.

Lemma proof_of_atype_unify2_return_wit_22_distinct_nodes : atype_unify2_return_wit_22_distinct_nodes.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_return_wit_22_distinct_nodes_split_goal_1.
  - Goal_apply proof_of_atype_unify2_return_wit_22_distinct_nodes_split_goal_2.
  - Goal_apply proof_of_atype_unify2_return_wit_22_distinct_nodes_split_goal_3.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_1 : atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (live_preserved_node__binary_checkpoints _ _ _ PreH16 PreH15).
  lia.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_2 : atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH22.
  unfold rc_count.
  eapply left_retain_capacity__left_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_3 : atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH22.
  unfold rc_count.
  eapply left_retain_capacity__left_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_4 : atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (live_preserved_node__binary_checkpoints _ _ _ PreH16 PreH15).
  lia.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_7_same_node_pure : atype_unify2_partial_solve_wit_7_same_node_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_2.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_3.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_8_distinct_nodes_pure_split_goal_1 : atype_unify2_partial_solve_wit_8_distinct_nodes_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (decode_node__right_variable _ _ _ PreH18) as [nd Hnd].
  pose proof (live_preserved_node__binary_checkpoints _ _ _ PreH16 Hnd).
  lia.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_8_distinct_nodes_pure_split_goal_2 : atype_unify2_partial_solve_wit_8_distinct_nodes_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold rc_count.
  eapply left_retain_capacity__left_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_8_distinct_nodes_pure : atype_unify2_partial_solve_wit_8_distinct_nodes_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_8_distinct_nodes_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_8_distinct_nodes_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_1 : atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH19 in PreH27.
  pose proof (repr_self_empty__right_variable _ _ PreH27) as Hempty.
  cbn [node_a]. unfold solution_at; intros old Hbad; rewrite Hempty in Hbad; discriminate.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_2 : atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH30.
  rewrite (retain_eq__right_variable _ _ _ PreH10).
  apply Z.lt_gt.
  apply retained_reserved__right_variable; [exact PreH24|].
  destruct (decode_node__right_variable _ _ _ PreH26) as [nd Hnd].
  eapply live_nonzero__right_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_3 : atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH30.
  rewrite (retain_eq__right_variable _ _ _ PreH10).
  apply Z.lt_gt.
  apply retained_reserved__right_variable; [exact PreH24|].
  destruct (decode_node__right_variable _ _ _ PreH26) as [nd Hnd].
  eapply live_nonzero__right_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_4 : atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH19 in PreH27.
  pose proof (repr_self_empty__right_variable _ _ PreH27) as Hempty.
  unfold solution_at; intros old Hbad; rewrite Hempty in Hbad; discriminate.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_9_same_node_pure : atype_unify2_partial_solve_wit_9_same_node_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_2.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_3.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_1 : atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH19 in PreH27.
  pose proof (repr_self_empty__right_variable _ _ PreH27) as Hempty.
  cbn [node_a]. unfold solution_at; intros old Hbad; rewrite Hempty in Hbad; discriminate.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_2 : atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (retain_eq__right_variable _ _ _ PreH10).
  apply Z.lt_gt.
  apply retained_reserved__right_variable; [exact PreH24|].
  destruct (decode_node__right_variable _ _ _ PreH26) as [nd Hnd].
  eapply live_nonzero__right_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_3 : atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (retain_eq__right_variable _ _ _ PreH10).
  apply Z.lt_gt.
  apply retained_reserved__right_variable; [exact PreH24|].
  destruct (decode_node__right_variable _ _ _ PreH26) as [nd Hnd].
  eapply live_nonzero__right_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_4 : atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH19 in PreH27.
  pose proof (repr_self_empty__right_variable _ _ PreH27) as Hempty.
  unfold solution_at; intros old Hbad; rewrite Hempty in Hbad; discriminate.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure : atype_unify2_partial_solve_wit_10_distinct_nodes_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_2.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_3.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_15_distinct_nodes_pure_split_goal_1 : atype_unify2_partial_solve_wit_15_distinct_nodes_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (live_preserved_node__binary_checkpoints _ _ _ PreH20 PreH19).
  lia.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_15_distinct_nodes_pure_split_goal_2 : atype_unify2_partial_solve_wit_15_distinct_nodes_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hnv : not_var tr1) by (eapply decode_not_var__right_variable; eauto).
  unfold rc_count.
  eapply right_retain_capacity__right_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_15_distinct_nodes_pure : atype_unify2_partial_solve_wit_15_distinct_nodes_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_15_distinct_nodes_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_15_distinct_nodes_pure_split_goal_2.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_1 : atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH20 in PreH33.
  pose proof (repr_self_empty__right_variable _ _ PreH33) as Hempty.
  cbn [node_a]. unfold solution_at; intros old Hbad; rewrite Hempty in Hbad; discriminate.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_2 : atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (retain_eq__right_variable _ _ _ PreH11).
  apply Z.lt_gt.
  apply retained_reserved__right_variable; [exact PreH29|].
  eapply live_nonzero__right_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_3 : atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (retain_eq__right_variable _ _ _ PreH11).
  apply Z.lt_gt.
  apply retained_reserved__right_variable; [exact PreH29|].
  eapply live_nonzero__right_variable; eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_4 : atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH20 in PreH33.
  pose proof (repr_self_empty__right_variable _ _ PreH33) as Hempty.
  unfold solution_at; intros old Hbad; rewrite Hempty in Hbad; discriminate.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure : atype_unify2_partial_solve_wit_16_distinct_nodes_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_1.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_2.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_3.
  - Goal_apply proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_4.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_24_distinct_nodes_pure_split_goal_1 : atype_unify2_partial_solve_wit_24_distinct_nodes_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply binary_first_capacity__binary_first_call with (p := t1_pre) (q := t2_pre); eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_24_distinct_nodes_pure : atype_unify2_partial_solve_wit_24_distinct_nodes_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_partial_solve_wit_24_distinct_nodes_pure_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_25_same_node_pure_split_goal_1 : atype_unify2_partial_solve_wit_25_same_node_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst t1_pre.
  eapply binary_first_capacity__binary_first_call with (p := t2_pre) (q := t2_pre); eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_25_same_node_pure : atype_unify2_partial_solve_wit_25_same_node_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_partial_solve_wit_25_same_node_pure_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_30_distinct_nodes_pure_split_goal_1 : atype_unify2_partial_solve_wit_30_distinct_nodes_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst retval.
  eapply binary_second_capacity__binary_second_call with (M := M0) (s := s) (p := t1_pre) (q := t2_pre); eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_30_distinct_nodes_pure : atype_unify2_partial_solve_wit_30_distinct_nodes_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_partial_solve_wit_30_distinct_nodes_pure_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_31_same_node_pure_split_goal_1 : atype_unify2_partial_solve_wit_31_same_node_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst retval t1_pre.
  eapply binary_second_capacity__binary_second_call with (M := M0) (s := s) (p := t2_pre) (q := t2_pre); eauto.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_31_same_node_pure : atype_unify2_partial_solve_wit_31_same_node_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_partial_solve_wit_31_same_node_pure_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_36_same_node_pure_split_goal_1 : atype_unify2_partial_solve_wit_36_same_node_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst t2_pre.
  eapply binary_first_capacity__binary_first_call with (M := M0) (s := s) (p := t1_pre) (q := t1_pre);
    [eassumption | eassumption | reflexivity | auto | eassumption].
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_36_same_node_pure : atype_unify2_partial_solve_wit_36_same_node_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_partial_solve_wit_36_same_node_pure_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_37_distinct_nodes_pure_split_goal_1 : atype_unify2_partial_solve_wit_37_distinct_nodes_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply binary_first_capacity__binary_first_call with (M := M0) (s := s) (p := t1_pre) (q := t2_pre);
    [eassumption | eassumption | eassumption | auto | eassumption].
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_37_distinct_nodes_pure : atype_unify2_partial_solve_wit_37_distinct_nodes_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_partial_solve_wit_37_distinct_nodes_pure_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_42_same_node_pure_split_goal_1 : atype_unify2_partial_solve_wit_42_same_node_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst t2_pre.
  subst retval.
  eapply binary_second_capacity__binary_second_call with (M := M0) (s := s) (p := t1_pre) (q := t1_pre);
    [eassumption | eassumption | reflexivity | auto | eassumption | eassumption].
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_42_same_node_pure : atype_unify2_partial_solve_wit_42_same_node_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_partial_solve_wit_42_same_node_pure_split_goal_1.
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_43_distinct_nodes_pure_split_goal_1 : atype_unify2_partial_solve_wit_43_distinct_nodes_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst retval.
  eapply binary_second_capacity__binary_second_call with (M := M0) (s := s) (p := t1_pre) (q := t2_pre);
    [eassumption | eassumption | eassumption | auto | eassumption | eassumption].
Qed.

Lemma proof_of_atype_unify2_partial_solve_wit_43_distinct_nodes_pure : atype_unify2_partial_solve_wit_43_distinct_nodes_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_atype_unify2_partial_solve_wit_43_distinct_nodes_pure_split_goal_1.
Qed.

Lemma proof_of_atype_unify_verify_entail_final : atype_unify_verify_entail_final.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists M_final raw_final tr1_final tr2_final.
  split_pure_spatial.
  - cancel (store_world M_final).
    cancel (store_solution M_final ( &( "res" ) ) raw_final).
    Intros_r r.
    apply_sepcon_adjoint.
    Split.
    + Intros Mpost rawpost.
      assert (Hmath : r = 0 -> forall t1 t2,
        store_type M_final t1_pre t1 /\ store_type M_final t2_pre t2 ->
        unify_rel t1 t2 raw_final rawpost).
      { intros _ a b [Ha Hb].
        assert (Ha' : a = tr1_final) by (eapply decode_type_unique; eauto).
        assert (Hb' : b = tr2_final) by (eapply decode_type_unique; eauto).
        subst a b; assumption. }
      sep_apply (same_return_final_bridge__final_compression
        M_final Mpost t1_pre t2_pre tr1_final tr2_final raw_final
        s_pre_final rawpost ( &( "res" ) ) r
        ltac:(assumption) ltac:(assumption) ltac:(assumption)
        ltac:(assumption) ltac:(assumption) ltac:(assumption)
        ltac:(assumption) Hmath).
      Split.
      * Intros sc. Left. Exists Mpost sc.
        split_pure_spatial.
        -- cancel.
        -- repeat split_pures; dump_pre_spatial; tauto.
      * Intros. Right. Exists rawpost Mpost.
        split_pure_spatial.
        -- cancel.
        -- repeat split_pures; dump_pre_spatial; tauto.
    + Intros Mpost rawpost.
      assert (Hmath : r = 0 -> forall t1 t2,
        store_type M_final t1_pre t1 /\ store_type M_final t2_pre t2 ->
        unify_rel t1 t2 raw_final rawpost).
      { intros Hr; exfalso; lia. }
      sep_apply (same_return_final_bridge__final_compression
        M_final Mpost t1_pre t2_pre tr1_final tr2_final raw_final
        s_pre_final rawpost ( &( "res" ) ) r
        ltac:(assumption) ltac:(assumption) ltac:(assumption)
        ltac:(assumption) ltac:(assumption) ltac:(assumption)
        ltac:(assumption) Hmath).
      Split.
      * Intros sc. Left. Exists Mpost sc.
        split_pure_spatial.
        -- cancel.
        -- repeat split_pures; dump_pre_spatial; tauto.
      * Intros. Right. Exists rawpost Mpost.
        split_pure_spatial.
        -- cancel.
        -- repeat split_pures; dump_pre_spatial; tauto.
  - repeat split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_copy_atype_nonnull_entail_open_var : copy_atype_nonnull_entail_open_var.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (positive_old_node__world_reopen M_open_var t_pre H ltac:(lia))
    as [n Hn].
  assert (Ht : t_pre <> 0)
    by (eapply live_nonzero__right_variable; eauto).
  sep_apply (proj1 (TypeinferRCFrameCompat.missing_payload_view
    M_open_var p_open_var (Node 3 v_open_var 0) H2)).
  sep_apply (var_world_close__copy_update M_open_var p_open_var v_open_var H2).
  Exists M_open_var.
  match goal with |- _ |-- ?Pre ** _ =>
    assert (Hpre : store_world M_open_var |-- Pre)
  end.
  { split_pure_spatial; [cancel|split_pures; dump_pre_spatial; assumption]. }
  rewrite <- Hpre.
  cancel (store_world M_open_var).
  Intros_r retval.
  apply derivable1_wand_sepcon_adjoint.
  Intros M_post.
  Exists M_post.
  assert (Hpostnode : node_at M_post p_open_var (Node 3 v_open_var 0)).
  { destruct H6 as [Hnodes Hroots]. apply Hnodes. exact H2. }
  rewrite (TypeinferRCFrameCompat.missing_payload_view
    M_post p_open_var (Node 3 v_open_var 0) Hpostnode).
  split_pure_spatial.
  - apply var_world_open__copy_update. exact Hpostnode.
  - split_pures; dump_pre_spatial; assumption.
Qed.

