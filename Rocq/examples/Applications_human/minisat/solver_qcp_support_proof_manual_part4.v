From SimpleC.Verification Require Import VCPrelude.
Require Import Coq.Reals.Reals.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.

Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_proof_common.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_support_goal.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_proof_automation.
Lemma proof_of_solver_read_wlist_which_implies_wit_1 : solver_read_wlist_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_9_pure : solver_reducedb_partial_solve_wit_9_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_open_state.
  bind_fact ( i < retval ÷ 2 ) as H_i.
  bind_fact (retval = Zlength words) as H_length.
  rewrite H_length.
  assert (Hlt : i < retval) by
    (apply (Z.lt_le_trans _ (Z.quot retval 2) _);
     [ exact H_i | apply Z.quot_le_upper_bound; lia ]).
  split_pures; dump_pre_spatial; solve [auto | lia].
Qed.


Lemma proof_of_solver_reducedb_which_implies_wit_4 : solver_reducedb_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_focus_learnt n F A_arr A_inst Mcur i words lits_now lits_now activity_now Hdbi Hact Hpos Hev Hne.
Qed.


Lemma proof_of_sortrnd_entail_wit_3 : sortrnd_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( sortrnd_partition_inv srt_db srt_activities srt_origin current_2 size_pre pivot i j ) as
    H_sortrnd_partition_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  unfold sortrnd_left_scan_inv.
  pose proof
    (sortrnd_left_scan_entry__sortrnd
       _ _ _ _ _ _ _ _ H_sortrnd_partition_inv H_Zlength) as [Hb Hinv].
  replace (i + 1 - 1) with i by lia.
  assert (Hrefl : fp64_eq (Z_to_fp64 seed_shadow_now_2)
                          (Z_to_fp64 seed_shadow_now_2)).
  { apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  Exists seed_shadow_now_2 seed_value_now_2 current_2.
  cancel.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_partial_solve_wit_5_pure : sortrnd_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( sortrnd_left_scan_inv srt_db srt_activities srt_origin current size_pre pivot (i - 1) j ) as
    H_sortrnd_left_scan_inv.
  rewrite ?Z.sub_0_r in *.
  unfold sortrnd_left_scan_inv, sortrnd_partition_inv in H_sortrnd_left_scan_inv.
  destruct H_sortrnd_left_scan_inv as [Hdom [Hctx [Hpiv [Hperm Hrest]]]].
  pose proof
    (learnt_sort_segment_domain_Znth__sortrnd _ _ i
       (learnt_sort_segment_domain_perm__sortrnd
          _ _ _ Hperm Hdom) ltac:(lia)) as Hin.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_act_clause_bump_partial_solve_wit_3_pure : act_clause_bump_partial_solve_wit_3_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_entailer_with ltac:(apply Zlength_nonneg).
Qed.


Lemma proof_of_act_var_bump_return_wit_1_split_goal_1 : act_var_bump_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_update_post (Zlength activity1_2) v heap0 orderpos0 heap1_2 orderpos1_2 ) as H_order_update_post.
  bind_fact ( Zlength activity1_2 = n ) as H_Zlength.
  rewrite H_Zlength in H_order_update_post.
  unfold order_update_post in H_order_update_post.
  destruct H_order_update_post as (_ & Hwf & Hperm & Hiff).
  pose proof (Hiff u_2 ltac:(rewrite <- H_Zlength; exact H)) as Huiff.
  apply (proj2 Huiff). exact H0.
Qed.


Lemma proof_of_act_var_bump_return_wit_1_split_goal_2 : act_var_bump_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_update_post (Zlength activity1_2) v heap0 orderpos0 heap1_2 orderpos1_2 ) as H_order_update_post.
  bind_fact ( Zlength activity1_2 = n ) as H_Zlength.
  rewrite H_Zlength in H_order_update_post.
  unfold order_update_post in H_order_update_post.
  destruct H_order_update_post as (_ & Hwf & Hperm & Hiff).
  pose proof (Hiff u ltac:(rewrite <- H_Zlength; exact H)) as Huiff.
  apply (proj1 Huiff). exact H0.
Qed.


Lemma proof_of_act_var_bump_return_wit_1_split_goal_3 : act_var_bump_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_update_post (Zlength activity1_2) v heap0 orderpos0 heap1_2 orderpos1_2 ) as H_order_update_post.
  bind_fact ( Zlength activity1_2 = n ) as H_Zlength.
  rewrite H_Zlength in H_order_update_post.
  unfold order_update_post in H_order_update_post.
  destruct H_order_update_post as (_ & Hwf & Hperm & Hiff).
  exact Hperm.
Qed.


Lemma proof_of_act_var_bump_return_wit_1_split_goal_4 : act_var_bump_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_update_post (Zlength activity1_2) v heap0 orderpos0 heap1_2 orderpos1_2 ) as H_order_update_post.
  bind_fact ( Zlength activity1_2 = n ) as H_Zlength.
  rewrite H_Zlength in H_order_update_post.
  unfold order_update_post in H_order_update_post.
  destruct H_order_update_post as (_ & Hwf & Hperm & Hiff).
  exact Hwf.
Qed.


Lemma proof_of_act_var_bump_return_wit_1 : act_var_bump_return_wit_1.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_act_var_bump_return_wit_1_split_goal_1 orderpos0 heap0 n activity1_2 v heap1_2 orderpos1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
- Goal_apply (proof_of_act_var_bump_return_wit_1_split_goal_2 orderpos0 heap0 n activity1_2 v heap1_2 orderpos1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
- Goal_apply (proof_of_act_var_bump_return_wit_1_split_goal_3 orderpos0 heap0 n activity1_2 v heap1_2 orderpos1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
- Goal_apply (proof_of_act_var_bump_return_wit_1_split_goal_4 orderpos0 heap0 n activity1_2 v heap1_2 orderpos1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
Qed.


Lemma proof_of_act_var_rescale_entail_wit_1 : act_var_rescale_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec n 0) as [-> | Hnpos].
  - Left. Exists activity0. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - Right. Exists activity0 0.
    sep_apply_l_atomic
      (DoubleArray.seg_split_to_missing_i
         activity_ptr 0 0 n activity0 msat_fp64_zero).
    + dump_pre_spatial. lia.
    + unfold StoreDoubleAsElement.storeA, double_Znth.
      msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_cmp_partial_solve_wit_2_pure : clause_cmp_partial_solve_wit_2_pure.
Proof.
  msat_clause_cmp_hdr_word_nonneg.
Qed.


Lemma proof_of_clause_cmp_partial_solve_wit_5_pure : clause_cmp_partial_solve_wit_5_pure.
Proof.
  msat_clause_cmp_hdr_word_nonneg.
Qed.


Lemma proof_of_clause_learnt_return_wit_1 : clause_learnt_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hland : Z.land header 1 = Z.rem header 2).
  { rewrite land_1_mod2. rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  unfold clause_hdr_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_new_entail_wit_3_1 : clause_new_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite ?Z.sub_0_r in *.
  cn_pin_learnt cn_sel_clause_new_spec.
  bind_fact ( c % 2 = 0 ) as H_c.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec cn_M_clause_new_spec cn_words_clause_new_spec 1 cn_root_clause_new_spec ) as H_clause_new_stage_ready.
  pose proof H_clause_new_stage_ready as Hready.
  unfold clause_new_stage_ready_root in Hready.
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof Hphysical as Hshape.
  destruct Hcert as (_ & Hall & _).
  destruct (msat_first_two_lits_wf _ _ Hall ltac:(lia))
    as (Hlit0 & Hlit1 & Hneg0 & Hneg1).
  unfold solver_shape in Hshape.
  unfold lit_wf_c in Hlit0, Hlit1, Hneg0, Hneg1.
  msat_split_after_llm.
  2-23: dump_pre_spatial; solve [auto | lia].
  cancel.
  assert (Hi : i = size) by lia.
  subst i.
  subst size.
  rewrite (sublist_self cn_words_clause_new_spec
    (Zlength cn_words_clause_new_spec)) by reflexivity.
  unfold MiniSatClause.rep, clause_hdr_word, activity_state.
  cbn -[Z.mul].
  Exists (fp32_of_real 0.0%R).
  unfold clause_hdr_addr, clause_act_addr, clause_lits_addr.
  change (sizeof (INT)) with 4.
  Intros_p Hfloat.
  split_pure_spatial.
  - cancel.
    rewrite (Z.mul_comm (Zlength cn_words_clause_new_spec) 2).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      split; [apply Zlength_nonneg |].
      split; [lia |].
      rewrite <- (Z.rem_mod_nonneg c 2) by lia.
      exact H_c.
    + dump_pre_spatial.
      replace (fp32_of_real
        (Rdefinitions.Q2R
          {| QArith_base.Qnum := 0; QArith_base.Qden := 10 |})) with
        (fp32_of_real (Rdefinitions.IZR 0)).
      * exact MSatFloatFacts.fp32_of_real_zero_nonnegative.
      * f_equal. lra.
    + dump_pre_spatial.
      exact Hfloat.
Qed.


Lemma proof_of_lit_neg_return_wit_1_bounded : lit_neg_return_wit_1_bounded.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lit_neg_c_wf lit_bound_n_bounded l_pre
    ltac:(unfold lit_wf_c; lia)) as Hneg.
  unfold lit_wf_c in Hneg.
  unfold lit_neg_c in *.
  msat_manual_entailer_with lia.
Qed.


Lemma proof_of_lit_var_return_wit_1_bounded_index : lit_var_return_wit_1_bounded_index.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold lit_var_c in *.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  assert (Hlo : 0 <= l_pre / 2) by (apply Z.div_pos; lia).
  assert (Hhi : l_pre / 2 < lv_bound_n_bounded_index)
    by (apply Z.div_lt_upper_bound; lia).
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_order_select_safety_wit_34 : order_select_safety_wit_34.
Proof.
  msat_order_select_sift_child_bound size.
Qed.


Lemma proof_of_solver_read_wlist_return_wit_1 : solver_read_wlist_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_18_pure : solver_reducedb_partial_solve_wit_18_pure.
Proof.
 msat_reducedb_state_pure.
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_39_pure : solver_reducedb_partial_solve_wit_39_pure.
Proof.
 msat_reducedb_state_pure.
Qed.


Lemma proof_of_sortrnd_entail_wit_7 : sortrnd_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  copy_fact ( sortrnd_right_scan_inv srt_db srt_activities srt_origin current size_pre pivot i (j + 1) ) as
    H_sortrnd_right_scan_inv.
  unfold sortrnd_right_scan_inv in H_sortrnd_right_scan_inv.
  destruct H_sortrnd_right_scan_inv as [Hdom [Hctx [Hpiv [Hperm Hrest]]]].
  pose proof
    (learnt_sort_segment_domain_perm__sortrnd
       _ _ _ Hperm Hdom) as Hdom'.
  assert (Hfp : fp64_eq (Z_to_fp64 seed_shadow_now) (Z_to_fp64 seed_shadow_now)).
  { apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  Exists seed_shadow_now seed_value_now current.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_act_clause_bump_partial_solve_wit_2_pure : act_clause_bump_partial_solve_wit_2_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_entailer_with ltac:(apply Zlength_nonneg).
Qed.


Lemma proof_of_clause_activity_return_wit_1 : clause_activity_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hshift : Z.shiftr (clause_hdr_word msat_true size) 1 = size).
  { unfold clause_hdr_word, msat_true.
    rewrite Z.shiftr_div_pow2 by lia.
    change ((2 * size + 1) / 2 = size).
    replace (2 * size + 1) with (1 + size * 2) by lia.
    rewrite Z.div_add by lia. simpl. lia. }
  rewrite Hshift.
  unfold clause_act_addr, clause_lits_addr, clause_hdr_addr, msat_fp32_same.
  unfold clause_hdr_word, msat_true in *.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_cmp_partial_solve_wit_9_pure : clause_cmp_partial_solve_wit_9_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_entailer_with ltac:(apply Zlength_nonneg).
Qed.


Lemma proof_of_clause_new_entail_wit_1_split_goal_1 : clause_new_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst learnt_pre endvar_pre.
  rewrite sizeof_int in *.
  replace ((begin_pre + Zlength cn_words_clause_new_spec * 4 - begin_pre) ÷ 4)
    with (Zlength cn_words_clause_new_spec) in * by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1) with 2.
  rewrite signed_last_nbits_eq by (try lia; cbn; lia).
  assert (Hland : Z.land (Zlength cn_words_clause_new_spec * 2) cn_sel_clause_new_spec = 0).
  { assert (cn_sel_clause_new_spec = 0 \/ cn_sel_clause_new_spec = 1) as [-> | ->] by lia.
    - apply Z.land_0_r.
    - rewrite land_1_mod2. apply Z_mod_mult. }
  rewrite <- Z.lxor_lor by exact Hland.
  rewrite <- Z.add_nocarry_lxor by exact Hland.
  lia.
Qed.


Lemma proof_of_clause_new_entail_wit_1_split_goal_2 : clause_new_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_clause_new_entail_wit_1 : clause_new_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_clause_new_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_clause_new_entail_wit_1_split_goal_2.
Qed.


Lemma proof_of_clause_new_which_implies_wit_6 : clause_new_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlearnt : cn_sel_clause_new_spec = 1) by lia.
  subst cn_sel_clause_new_spec.
  unfold activity_undef, solver_selected_is_learnt, clause_act_addr, clause_lits_addr.
  cbn [Z.eqb negb].
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_14_pure : clause_remove_partial_solve_wit_14_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_remove_watch_in_pure false.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_11_pure : clause_remove_partial_solve_wit_11_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_13_pure : clause_remove_partial_solve_wit_13_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_remove_watch_in_pure true.
Qed.





Lemma proof_of_clause_simplify_return_wit_1_split_goal_1 : clause_simplify_return_wit_1_split_goal_1.
Proof.
Abort.


Lemma proof_of_clause_simplify_return_wit_1 : clause_simplify_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - subst lits; cancel.
  - split_pures; dump_pre_spatial.
    bind_fact (retval = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2) as H_retval.
    bind_fact (clause_simplify_scan_inv n clause_words assigns0 i) as Hinv.
    unfold clause_simplify_scan_inv in Hinv.
    destruct Hinv as (Hi & Halen & Hlits & Hcells & Hprefix).
    assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
      by (apply clause_hdr_word_nonneg; apply Zlength_nonneg).
    rewrite zdiv_equiv in H_retval by lia.
    rewrite clause_hdr_word_div2 in H_retval by apply Zlength_nonneg.
    unfold clause_simplify_result.
    right; split; [reflexivity |].
    intros j Hj; apply Hprefix; lia.
    + exact PreH5.
    + exact PreH6.
Qed.


Lemma proof_of_clause_size_return_wit_1 : clause_size_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hshift : Z.shiftr header 1 = header ÷ 2).
  { rewrite Z.quot_div_nonneg by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    reflexivity. }
  unfold clause_hdr_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_order_select_entail_wit_2_3 : order_select_entail_wit_2_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval.
  Exists z2 v2 heap0 orderpos0.
  sep_apply store_float_undef_store_float.
  unfold order_select_loop_inv.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. split; [exact PreH9 | unfold incl; auto].
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.



Lemma proof_of_order_select_entail_wit_8 : order_select_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; rewrite ?Z.sub_0_r in *; solve [lia | assumption].
Qed.


Lemma proof_of_order_select_entail_wit_12_1 : order_select_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left. Left. Left. cbn [poly_store poly_undef_store].
  msat_order_select_sift_capacity s_pre heap cap.
Qed.



Lemma proof_of_order_select_return_wit_1 : order_select_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hempty : heap_now = @nil Z).
  { apply Zlength_nil_inv. pose proof (Zlength_nonneg heap_now). lia. }
  subst heap_now.
  pose proof (order_select_loop_empty_post__order_select
    n heap0 orderpos_now assigns0 trail0 qhead PreH3) as Hpost.
  Exists seed_shadow_now seed_value_now (@nil Z) orderpos_now.
  sep_apply Veci.rep_ptr_rep.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_order_update_entail_wit_2_split_goal_1 : order_update_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  (bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre);
    (bind_fact ( 0 <= Znth (Znth v_pre orderpos0 (-1)) heap0 0 ) as H_Znth);
    (bind_fact ( Znth (Znth v_pre orderpos0 (-1)) heap0 0 < n ) as H_Znth_2);
    (unfold order_update_pre, order_heap_wf, heap_wf in H_order_update_pre);
    (cbn in H_order_update_pre);
    (destruct H_order_update_pre as ((Hlen & _) & _));
    (replace (v_pre - 0) with v_pre by lia);
    (rewrite (Znth_indep orderpos0 v_pre 0 (-1)) by lia);
    (replace (Znth v_pre orderpos0 (-1) - 0)
         with (Znth v_pre orderpos0 (-1)) by lia).
  exact H_Znth_2.
Qed.


Lemma proof_of_order_update_entail_wit_2_split_goal_2 : order_update_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  (bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre);
    (bind_fact ( 0 <= Znth (Znth v_pre orderpos0 (-1)) heap0 0 ) as H_Znth);
    (bind_fact ( Znth (Znth v_pre orderpos0 (-1)) heap0 0 < n ) as H_Znth_2);
    (unfold order_update_pre, order_heap_wf, heap_wf in H_order_update_pre);
    (cbn in H_order_update_pre);
    (destruct H_order_update_pre as ((Hlen & _) & _));
    (replace (v_pre - 0) with v_pre by lia);
    (rewrite (Znth_indep orderpos0 v_pre 0 (-1)) by lia);
    (replace (Znth v_pre orderpos0 (-1) - 0)
         with (Znth v_pre orderpos0 (-1)) by lia).
  exact H_Znth.
Qed.


Lemma proof_of_order_update_entail_wit_2 : order_update_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_order_update_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_order_update_entail_wit_2_split_goal_2.
Qed.



Lemma proof_of_solver_reducedb_entail_wit_2_1 : solver_reducedb_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_open_state.
  LLM_pre_process ltac:(lia || nia || int_auto).
  msat_reducedb_remove_current n F A_arr A_inst Mcur words i j s_pre levels_ptr.
Qed.



Lemma proof_of_solver_reducedb_entail_wit_5_2 : solver_reducedb_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (PtrArray.full_to_seg learnts (Zlength words)
    (replace_Znth j (Znth (i - 0) words 0) words)).
  rewrite <- (Zlength_replace_Znth words j (Znth (i - 0) words 0)).
  sep_apply (Vecp.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "learnts") learnts (replace_Znth j (Znth (i - 0) words 0) words) cap _ _ _ eq_refl eq_refl eq_refl);
    [ | rewrite ?Zlength_replace_Znth; first [lia | vec_buf_solve] .. ].
  msat_reducedb_open_state.
  Exists (replace_Znth j (Znth (i - 0) words 0) words) Mcur.
  split_pure_spatial;
  [ cancel (clause_db_rep (ms_learnt Mcur)); cancel
  | split_pures; dump_pre_spatial;
    [ unfold db_compaction_step; repeat split; auto
    | repeat match goal with |- _ /\ _ => split end; solve [auto | lia | tauto] ] ].
Qed.



Lemma proof_of_solver_reducedb_which_implies_wit_1 : solver_reducedb_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_reducedb_pre_at, solver_rep_levels_wl_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_db_mutation_frame_at,
    solver_ptrs_rep,
    solver_var_arrays_rep, solver_levels_slice_at,
    clause_new_scalars_frame, solver_vecs_without_learnts_rep,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep.
  Intros act asg opos rsn trl tgs.
  Exists rsn.
  destruct H as [Hinv [Hq [Hcap Hseed]]].
  assert (Hsort : learnt_sort_domain (ms_learnt M0) (db_words (ms_learnt M0))).
  { unfold learnt_sort_domain, db_words. split.
    - exact (msw_learnt_db (msi_weak Hinv)).
    - apply Permutation_refl. }
  assert (Hnodup : NoDup (db_words (ms_learnt M0))).
  { unfold db_words.
    pose proof (proj1 (msw_db_wf (msi_weak Hinv))) as Hdb.
    unfold msolver_db in Hdb.
    rewrite map_app in Hdb.
    revert Hdb.
    generalize (map fst (ms_prob M0)) as p.
    induction p as [|a p IHp]; intros Hdb.
    - exact Hdb.
    - inversion Hdb as [|x xs Hx Hrest]. subst.
      apply IHp. exact Hrest. }
  Exists act asg opos trl tgs.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_reducedb_which_implies_wit_7 : solver_reducedb_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_focus_learnt n F A_arr A_inst Mcur i words lits_now lits_now activity_now Hdbi Hact Hpos Hev Hne.
Qed.


Lemma proof_of_sortrnd_partial_solve_wit_7_pure : sortrnd_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( sortrnd_right_scan_inv srt_db srt_activities srt_origin current size_pre pivot i (j + 1) ) as
    H_sortrnd_right_scan_inv.
  rewrite ?Z.sub_0_r in *.
  unfold sortrnd_right_scan_inv in H_sortrnd_right_scan_inv.
  destruct H_sortrnd_right_scan_inv as [Hdom [Hctx [Hpiv [Hperm Hrest]]]].
  pose proof
    (learnt_sort_segment_domain_Znth__sortrnd _ _ j
       (learnt_sort_segment_domain_perm__sortrnd
          _ _ _ Hperm Hdom) ltac:(lia)) as Hin.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_return_wit_1 : sortrnd_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hrefl : fp64_eq (Z_to_fp64 seed_shadow) (Z_to_fp64 seed_shadow)).
  { apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  Exists seed_shadow seed_value current_2.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_which_implies_wit_2 : sortrnd_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
    sep_apply (proj1 (PtrArray.seg_0_shift array i size right)).
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_which_implies_wit_3 : sortrnd_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (proj2 (PtrArray.seg_0_shift array i size right_after)).
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_clause_remove_which_implies_wit_2 : clause_remove_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst lits.
  prop_apply_p (IntArray.seg_valid (clause_lits_addr c) 2
    (Zlength clause_words)
    (sublist 2 (Zlength clause_words) clause_words)).
  Intros.
  rewrite Z.mul_0_l, Z.add_0_r, Z.mul_1_l.
  sep_apply (intarray_refold_first_two__clause_remove
    (clause_lits_addr c) clause_words ltac:(lia)).
  sep_apply IntArray.seg_to_undef_seg.
  sep_apply store_int_undef_store_int.
  sep_apply activity_state_undef.
  sep_apply (store_ptr_undef_store_ptr (&("lits"))).
  unfold MiniSatClause.owned.
  cancel (&("lits") # Ptr |->_).
  split_pure_spatial; [cancel; cancel | dump_pre_spatial].
  rewrite Z.rem_mod_nonneg in PreH3 by lia.
  lia.
Qed.




Lemma proof_of_act_clause_decay_return_wit_1_split_goal_1 : act_clause_decay_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply MSatFloatFacts.fp32_nonnegative_mul_positive_finite; assumption.
Qed.


Lemma proof_of_act_clause_decay_return_wit_1 : act_clause_decay_return_wit_1.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_act_clause_decay_return_wit_1_split_goal_1 cla_decay0 cla_inc0 PreH1 PreH2).
Qed.


Lemma proof_of_act_var_bump_partial_solve_wit_4_pure : act_var_bump_partial_solve_wit_4_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  repeat lazymatch goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end.
  3: {
    prop_apply_p (store_int_range (&( s_pre # "solver_t" ->ₛ "size")) n).
    Intros_p Hn.
    dump_pre_spatial.
    change Int.max_signed with 2147483647 in Hn.
    lia. }
  all: dump_pre_spatial.
  all: rewrite ?Zlength_replace_Znth by lia.
  all: lia.
Qed.


Lemma proof_of_clause_cmp_partial_solve_wit_6_pure : clause_cmp_partial_solve_wit_6_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_entailer_with ltac:(apply Zlength_nonneg).
Qed.


Lemma proof_of_clause_from_lit_return_wit_1 : clause_from_lit_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold tag_of_lit in *.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_new_entail_wit_2_split_goal_1 : clause_new_entail_wit_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  rewrite (sublist_split 0 (i + 1) i cn_words_clause_new_spec) by lia.
  rewrite (sublist_single 0 i cn_words_clause_new_spec) by lia.
  replace (i - 0) with i by lia.
  reflexivity.
Qed.


Lemma proof_of_clause_new_entail_wit_2 : clause_new_entail_wit_2.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_clause_new_entail_wit_2_split_goal_1 cn_root_clause_new_spec cn_sel_clause_new_spec cn_words_clause_new_spec cn_M_clause_new_spec cn_A_inst_clause_new_spec cn_A_arr_clause_new_spec cn_F_clause_new_spec cn_n_clause_new_spec watch_words0 watch_words1 c size i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15).
Qed.


Lemma proof_of_clause_new_which_implies_wit_2 : clause_new_which_implies_wit_2.
Proof.
LLM_pre_process ltac:(lia).
  copy_fact ( endvar = begin + Zlength cn_words_clause_new_spec * sizeof ( INT ) ) as H_endvar.
  rewrite sizeof_int in *.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    rewrite H_endvar.
    replace (begin + Zlength cn_words_clause_new_spec * 4 - begin)
      with (Zlength cn_words_clause_new_spec * 4) by lia.
    rewrite Z.quot_mul by lia. reflexivity.
Qed.


Lemma proof_of_clause_remove_return_wit_1 : clause_remove_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_remove_close s_pre is_learnt retval_8 retval_10 k_2 true true.
Qed.



Lemma proof_of_clause_simplify_return_wit_3 : clause_simplify_return_wit_3.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH23 as Hinv.
  unfold clause_simplify_scan_inv in Hinv.
  destruct Hinv as (Hi & Halen & Hlits & Hcells & Hprefix).
  assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; apply Zlength_nonneg).
  rewrite zdiv_equiv in PreH18 by lia.
  rewrite clause_hdr_word_div2 in PreH18 by apply Zlength_nonneg.
  apply derivable1s_coq_prop_andp_r.
  2: { unfold clause_simplify_result, packed_lit_satisfying_value.
       left; split; [reflexivity|].
       exists i; split; [lia|].
       subst retval_3 current_value current_lit.
       rewrite replace_Znth_Znth in PreH1.
       unfold lit_sign_c in PreH12, PreH13 |- *.
       destruct (Z.odd (Znth i clause_words 0)); simpl in *; lia. }
  apply derivable1s_coq_prop_andp_r; [ | exact PreH21 ].
  apply derivable1s_coq_prop_andp_r; [ | exact PreH22 ].
  subst lits retval_3 current_value current_lit.
  rewrite replace_Znth_Znth.
  change (CharArray.full assigns_ptr n assigns0) with (CharArray.seg assigns_ptr 0 n assigns0).
  cancel.
  pose proof (IntArray.missing_i_merge_to_seg (clause_lits_addr c_pre) 0 i (Zlength clause_words)
    (Znth i clause_words 0) clause_words ltac:(lia)) as Hm.
  rewrite Z.sub_0_r, replace_Znth_Znth in Hm.
  exact Hm.
Qed.


Lemma proof_of_clause_simplify_safety_wit_10 : clause_simplify_safety_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_simplify_hdr_word_safety.
Qed.


Lemma proof_of_lit_var_return_wit_2_zero_index : lit_var_return_wit_2_zero_index.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.sub_0_r.
  unfold lit_var_c in *.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  assert (Hlo : 0 <= l_pre / 2) by (apply Z.div_pos; lia).
  assert (Hhi : l_pre / 2 < Zlength lv_assigns_zero_index)
    by (apply Z.div_lt_upper_bound; lia).
  msat_manual_entailer_with ltac:(assumption).
Qed.


Lemma proof_of_order_select_entail_wit_10_1 : order_select_entail_wit_10_1.
Proof.
  msat_order_select_cursor_open. msat_order_select_orp_left.
  msat_order_select_cursor_ranges s_pre cap sift_heap_now n size next x
    Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
Qed.



Lemma proof_of_order_select_entail_wit_13_3 : order_select_entail_wit_13_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (next - 0) assigns0 0 <> 0 ) as H_Znth.
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before sift_heap_now
    sift_orderpos_now assigns0 trail0 qhead ) as H_sift.
  replace (next - 0) with next in * by lia.
  replace (child + 1 - 0) with (child + 1) in * by lia.
  replace (child - 0) with child in * by lia.
  set (hp := replace_Znth i x sift_heap_now).
  set (op := replace_Znth (Znth i hp 0) i sift_orderpos_now).
  assert (Hmoved : Znth i hp 0 = x).
  { subst hp. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hloop : order_select_loop_inv n heap0 hp op assigns0 trail0 qhead).
  { subst op. rewrite Hmoved.
    eapply order_select_sift_close_assigned__order_select
      with (popped := next) (before := sift_heap_before);
      [ exact H_sift | exact H_Znth ]. }
  assert (Hheaplen : Zlength hp = Zlength sift_heap_now).
  { subst hp. rewrite Zlength_replace_Znth. reflexivity. }
  replace (Znth child sift_heap_now 0 - 0) with (Znth child sift_heap_now 0) by lia.
  replace (Znth (child + 1) sift_heap_now 0 - 0) with (Znth (child + 1) sift_heap_now 0) by lia.
  sep_apply_l_atomic (double_array_missing2_refold
    activity_ptr (Znth child sift_heap_now 0)
    (Znth (child + 1) sift_heap_now 0) n activity0
    ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n op).
  sep_apply_l_atomic (IntArray.full_to_seg heap (Zlength sift_heap_now) hp).
  rewrite <- Hheaplen.
  sep_apply (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "order") heap hp cap _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  Exists sift_seed_shadow_now sift_seed_value_now hp op.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.



Lemma proof_of_order_select_entail_wit_13_4 : order_select_entail_wit_13_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (next - 0) assigns0 0 <> 0 ) as H_Znth.
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before sift_heap_now
    sift_orderpos_now assigns0 trail0 qhead ) as H_sift.
  replace (next - 0) with next in * by lia.
  replace (child - 0) with child in * by lia.
  set (hp := replace_Znth i x sift_heap_now).
  set (op := replace_Znth (Znth i hp 0) i sift_orderpos_now).
  assert (Hmoved : Znth i hp 0 = x).
  { subst hp. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hloop : order_select_loop_inv n heap0 hp op assigns0 trail0 qhead).
  { subst op. rewrite Hmoved.
    eapply order_select_sift_close_assigned__order_select
      with (popped := next) (before := sift_heap_before);
      [ exact H_sift | exact H_Znth ]. }
  assert (Hheaplen : Zlength hp = Zlength sift_heap_now) by apply Zlength_replace_Znth.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n op).
  sep_apply_l_atomic (IntArray.full_to_seg heap (Zlength sift_heap_now) hp).
  rewrite <- Hheaplen.
  sep_apply (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "order") heap hp cap _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  Exists sift_seed_shadow_now sift_seed_value_now hp op.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.



Lemma proof_of_order_select_safety_wit_29 : order_select_safety_wit_29.
Proof.
  msat_order_select_sift_child_bound size.
Qed.


Lemma proof_of_order_select_safety_wit_30 : order_select_safety_wit_30.
Proof.
  msat_order_select_sift_child_bound size.
Qed.


Lemma proof_of_order_unassigned_which_implies_wit_3 : order_unassigned_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_unassigned_pre n v heap0 orderpos0 ) as H_order_unassigned_pre.
  bind_fact ( Znth v orderpos0 0 = -1 ) as H_Znth.
  pose proof H_order_unassigned_pre as Hun.
  destruct Hun as (Hwf & Hv & Htwon).
  pose proof (heap_wf_orderpos_length n
    {| mh_heap := heap0; mh_orderpos := orderpos0 |} Hwf) as Hoplen.
  cbn [mh_orderpos] in Hoplen.
  assert (Hmissing : Znth v orderpos0 (-1) = -1).
  { rewrite (Znth_indep orderpos0 v (-1) 0) by lia. exact H_Znth. }
  assert (Hinsert : order_heap_wf n (heap0 ++ v :: nil)
      (replace_Znth v (Zlength heap0) orderpos0)).
  { unfold order_heap_wf.
    change (heap_wf n
      {| mh_heap := heap0 ++ v :: nil;
         mh_orderpos := replace_Znth v (Zlength heap0) orderpos0 |}).
    apply (heap_wf_insert n
      {| mh_heap := heap0; mh_orderpos := orderpos0 |} v);
      cbn [mh_heap mh_orderpos]; assumption. }
  assert (Hpresent :
      Znth v (replace_Znth v (Zlength heap0) orderpos0) (-1) <> -1).
  { rewrite Znth_replace_Znth_Same by lia.
    pose proof (Zlength_nonneg heap0). lia. }
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold order_update_pre.
    split; [exact Hinsert |].
    split; [exact Hv | exact Hpresent].
Qed.


Lemma proof_of_order_update_entail_wit_3 : order_update_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (DoubleArray.seg_Zlength activity_ptr 0 n activity0).
  Intros_p Hactlen.
  sep_apply (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "order") p heap0 cap _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre.
  bind_fact ( 0 <= Znth (Znth v_pre orderpos0 (-1)) heap0 0 ) as H_Znth.
  bind_fact ( Znth (Znth v_pre orderpos0 (-1)) heap0 0 < n ) as H_Znth_2.
  pose proof H_order_update_pre as Hpre.
  unfold order_update_pre, order_heap_wf, heap_wf in Hpre.
  cbn in Hpre.
  destruct Hpre as ((Hoplen & _) & _).
  replace (v_pre - 0) with v_pre in * by lia.
  assert (Hiind : Znth v_pre orderpos0 0 = Znth v_pre orderpos0 (-1)).
  { apply Znth_indep. lia. }
  rewrite Hiind in *.
  replace (Znth v_pre orderpos0 (-1) - 0)
    with (Znth v_pre orderpos0 (-1)) in * by lia.
  assert (Hxind :
    Znth (Znth v_pre orderpos0 (-1)) heap0 0 =
    Znth (Znth v_pre orderpos0 (-1)) heap0 (-1)).
  { apply Znth_indep. lia. }
  rewrite Hxind in *.
  pose proof (order_update_loop_inv_init n v_pre
    (Znth v_pre orderpos0 (-1))
    (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1))
    heap0 orderpos0 H_order_update_pre eq_refl eq_refl) as Hinit.
  destruct Hinit as (Hirange & Hxv & Hinv).
  destruct (Z.eq_dec (Znth v_pre orderpos0 (-1)) 0) as [Hi0|Hi0].
  - assert (Hparent0 :
      (Znth v_pre orderpos0 (-1) - 1) ÷ 2 = 0).
    { rewrite Hi0. reflexivity. }
    assert (Hzeroind : Znth 0 heap0 0 = Znth 0 heap0 (-1)).
    { apply Znth_indep. rewrite Hi0 in Hirange. lia. }
    assert (Hzero_lo : 0 <= Znth 0 heap0 (-1)).
    { replace (Znth 0 heap0 (-1))
        with (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1)).
      - exact H_Znth.
      - rewrite Hi0. reflexivity. }
    assert (Hzero_hi : Znth 0 heap0 (-1) < n).
    { replace (Znth 0 heap0 (-1))
        with (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1)).
      - exact H_Znth_2.
      - rewrite Hi0. reflexivity. }
    Left. subst retval.
    Exists heap0 orderpos0.
    rewrite Hparent0.
    replace (0 - 0) with 0 by lia.
    rewrite Hzeroind.
    split_pure_spatial.
    + cancel (DoubleArray.seg activity_ptr 0 n activity0).
      cancel.
    + split_pures; dump_pre_spatial; solve [auto | lia].
  - assert (Hparent_lo :
      0 <= (Znth v_pre orderpos0 (-1) - 1) ÷ 2).
    { rewrite zdiv_equiv by lia. apply Z.div_pos; lia. }
    assert (Hparent_lt_i :
      (Znth v_pre orderpos0 (-1) - 1) ÷ 2 <
      Znth v_pre orderpos0 (-1)).
    { rewrite zdiv_equiv by lia. apply Z.div_lt_upper_bound; lia. }
    pose proof Hinv as Hinv_copy.
    unfold order_update_loop_inv in Hinv_copy.
    destruct Hinv_copy as (_ & _ & Hhole).
    assert (Hparent_range :
      0 <= Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1) < n).
    { apply (order_heap_one_hole_cell_range n heap0
        (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1))
        (Znth v_pre orderpos0 (-1)) heap0 orderpos0
        ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) Hhole); lia. }
    assert (Hparent_ind :
      Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 0 =
      Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1)).
    { apply Znth_indep. lia. }
    assert (Hx_ne_parent :
      Znth (Znth v_pre orderpos0 (-1)) heap0 (-1) <>
      Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1)).
    { apply (order_heap_one_hole_x_neq_cell__order_update n heap0
        (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1))
        (Znth v_pre orderpos0 (-1)) heap0 orderpos0
        ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) Hhole); lia. }
    Right. subst retval.
    Exists heap0 orderpos0.
    cancel;
      try replace
        ((Znth v_pre orderpos0 (-1) - 1) ÷ 2 - 0)
        with ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) by lia;
      try rewrite Hparent_ind;
      try lia;
      try exact Hparent_range;
      try exact Hx_ne_parent.
    sep_apply (double_array_seg_split_to_missing2__order_select
      activity_ptr
      (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1))
      (Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1))
      n activity0 (conj H_Znth H_Znth_2) Hparent_range Hx_ne_parent).
    replace (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1) - 0)
      with (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1)) by lia.
    replace (Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1) - 0)
      with (Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1)) by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_reducedb_entail_wit_2_2 : solver_reducedb_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (PtrArray.full_to_seg learnts (Zlength words)
    (replace_Znth j (Znth (i - 0) words 0) words)).
  rewrite <- (Zlength_replace_Znth words j (Znth (i - 0) words 0)).
  sep_apply (Vecp.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "learnts") learnts (replace_Znth j (Znth (i - 0) words 0) words) cap _ _ _ eq_refl eq_refl eq_refl);
    [ | rewrite ?Zlength_replace_Znth; first [lia | vec_buf_solve] .. ].
  msat_reducedb_open_state.
  Exists (replace_Znth j (Znth (i - 0) words 0) words) Mcur.
  split_pure_spatial;
  [ cancel (clause_db_rep (ms_learnt Mcur)); cancel
  | split_pures; dump_pre_spatial;
    [ unfold db_compaction_step; repeat split; auto
    | repeat match goal with |- _ /\ _ => split end; solve [auto | lia | tauto] ] ].
Qed.



Lemma proof_of_solver_reducedb_partial_solve_wit_11_pure : solver_reducedb_partial_solve_wit_11_pure.
Proof.
  msat_reducedb_hdr_word_range_pure.
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_26_pure : solver_reducedb_partial_solve_wit_26_pure.
Proof.
 msat_reducedb_state_pure.
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_34_pure : solver_reducedb_partial_solve_wit_34_pure.
Proof.
  msat_reducedb_first_lit_bounds_pure.
Qed.


Lemma proof_of_solver_reducedb_which_implies_wit_6 : solver_reducedb_which_implies_wit_6.
Proof.
  msat_reducedb_focus_head_clause.
Qed.


Lemma proof_of_sortrnd_entail_wit_4 : sortrnd_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval < 0 ) as H_retval.
  bind_fact ( learnt_cmp_result srt_db srt_activities pivot (Znth (j - 0) current_2 0) retval ) as H_learnt_cmp_result.
  bind_fact ( sortrnd_right_scan_inv srt_db srt_activities srt_origin current_2 size_pre pivot i (j + 1) ) as
    H_sortrnd_right_scan_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < size_pre ) as H_j_2.
  rewrite ?Z.sub_0_r in *.
  pose proof
    (sortrnd_right_scan_step__sortrnd
       _ _ _ _ _ _ _ _ _ H_sortrnd_right_scan_inv H_learnt_cmp_result H_retval H_Zlength
       H_j H_j_2) as [Hb Hinv].
  rewrite H_Zlength in Hinv.
  replace (j - 1 + 1) with j by lia.
  Exists seed_shadow_now_2 seed_value_now_2 current_2.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_entail_wit_6 : sortrnd_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( i < j ) as H_i.
  bind_fact ( retval >= 0 ) as H_retval.
  bind_fact ( learnt_cmp_result srt_db srt_activities pivot (Znth (j - 0) current_2 0) retval ) as H_learnt_cmp_result.
  bind_fact ( sortrnd_right_scan_inv srt_db srt_activities srt_origin current_2 size_pre pivot i (j + 1) ) as
    H_sortrnd_right_scan_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  bind_fact ( 0 <= i ) as H_i_2.
  bind_fact ( i < size_pre ) as H_i_3.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < size_pre ) as H_j_2.
  rewrite ?Z.sub_0_r in *.
  pose proof
    (sortrnd_swap_preserves_partition_inv__sortrnd
       _ _ _ _ _ _ _ _ _ H_sortrnd_right_scan_inv H_learnt_cmp_result H_retval H_i H_Zlength
       H_i_2 H_i_3 H_j H_j_2) as Hinv.
  sep_apply_l_atomic
    (PtrArray.full_to_seg array_pre size_pre
       (replace_Znth j (Znth i current_2 0)
          (replace_Znth i (Znth j current_2 0) current_2))).
  sep_apply (store_ptr_undef_store_ptr (&( "tmp"))).
  Exists seed_shadow_now_2 seed_value_now_2
    (replace_Znth j (Znth i current_2 0)
       (replace_Znth i (Znth j current_2 0) current_2)).
  rewrite !Zlength_replace_Znth.
  split_pure_spatial.
  - msat_cancel_sound; lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel.
  - split_pures; dump_pre_spatial; solve [auto | lia].
Qed.
