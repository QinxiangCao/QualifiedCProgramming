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
Lemma proof_of_sortrnd_return_wit_2 : sortrnd_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hrefl : fp64_eq (Z_to_fp64 shadow_after_right) (Z_to_fp64 shadow_after_right)).
  { apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  Exists shadow_after_right seed_after_right joined.
  msat_manual_entailer_with ltac:(lia).
Qed.





Lemma proof_of_act_clause_rescale_partial_solve_wit_8_pure : act_clause_rescale_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (msat_fp32_same retval activity_now) as Hsame.
  assert (Hretval : msat_fp32_nonnegative retval).
  { unfold msat_fp32_same in Hsame. rewrite Hsame. assumption. }
  assert (Hscale : msat_fp32_positive_finite (fp32_of_real (0.000000000000000000009999999682655225388967887463487205224055287544615566730499267578125)%R)).
  { apply (MSatFloatFacts.fp32_of_real_positive_from_bpow _ (-100) 0); try lia.
    - unfold Flocq.Core.Raux.bpow. simpl. field_simplify; nra.
    - rewrite Rabs_right by lra.
      change (Flocq.Core.Raux.bpow Flocq.Core.Zaux.radix2 0) with 1%R. lra. }
  pose proof
    (MSatFloatFacts.fp32_nonnegative_mul_positive_finite
       _ _ Hretval Hscale) as Hscaled.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_act_clause_rescale_which_implies_wit_2_split_goal_spatial : act_clause_rescale_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (i - 0) (db_words db) 0 % 2 = 0 ) as H_Znth.
  set (c := Znth (i - 0) (db_words db) 0) in *.
  unfold clause_db_pair_remainder at 1.
  Split.
  - Intros co pre post.
    destruct H as (Hdb & Hlits & Htag).
    unfold db_nil in Hdb. destruct pre; discriminate Hdb.
  - Intros co pre post.
    destruct H as (Hdb & Hlits & Htag).
    rewrite Hdb. unfold msat_true in *; simpl in Htag.
    assert (Hmod : c mod 2 = 0) by
      (rewrite <- (Z.rem_mod_nonneg c 2) by lia; exact H_Znth).
    sep_apply_r_atomic (clause_db_rep_app_intro pre ((c, co) :: post)).
    rewrite clause_db_rep_cons.
    unfold MiniSatClause.rep, activity_state.
    cbn [fst snd]. rewrite Htag, Hlits.
    Exists activity_after.
    unfold db_nil. rewrite clause_db_rep_nil.
    split_pure_spatial.
    + cancel.
      cancel.
    + split_pures; dump_pre_spatial.
      * pose proof (Zlength_nonneg clause_words). lia.
      * exact PreH4.
Qed.


Lemma proof_of_act_clause_rescale_which_implies_wit_2 : act_clause_rescale_which_implies_wit_2.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_act_clause_rescale_which_implies_wit_2_split_goal_spatial db clause_words a_v activity_after i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
Qed.


Lemma proof_of_act_var_rescale_entail_wit_2 : act_var_rescale_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- context [fp64_mul ?value ?scale] =>
      remember (fp64_mul value scale) as scaled
  end.
  destruct (Z.eq_dec (i_2 + 1) n) as [Hdone | Hnext].
  - Left.
    Exists (replace_Znth i_2 scaled activity_now_2).
    sep_apply_l_atomic
      (DoubleArray.missing_i_merge_to_seg
         activity_ptr 0 i_2 n scaled activity_now_2).
    + dump_pre_spatial. lia.
    + replace (i_2 - 0) with i_2 by lia.
      subst n.
      rewrite Zlength_replace_Znth by lia.
      rewrite <- Hdone.
      (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - Right.
    Exists (replace_Znth i_2 scaled activity_now_2) (i_2 + 1).
    sep_apply_l_atomic
      (DoubleArray.missing_i_merge_to_seg
         activity_ptr 0 i_2 n scaled activity_now_2).
    + dump_pre_spatial. lia.
    + replace (i_2 - 0) with i_2 by lia.
      sep_apply_l_atomic
        (DoubleArray.seg_split_to_missing_i
           activity_ptr 0 (i_2 + 1) n
           (replace_Znth i_2 scaled activity_now_2)
           msat_fp64_zero).
      * dump_pre_spatial. lia.
      * unfold StoreDoubleAsElement.storeA, double_Znth.
        rewrite Zlength_replace_Znth by lia.
        msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_activity_which_implies_wit_1 : clause_activity_which_implies_wit_1.
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


Lemma proof_of_clause_begin_return_wit_1 : clause_begin_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold clause_lits_addr in *.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_cmp_partial_solve_wit_3_pure : clause_cmp_partial_solve_wit_3_pure.
Proof.
  msat_clause_cmp_hdr_word_nonneg.
Qed.


Lemma proof_of_clause_cmp_partial_solve_wit_7_pure : clause_cmp_partial_solve_wit_7_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_entailer_with ltac:(apply Zlength_nonneg).
Qed.


Lemma proof_of_clause_cmp_return_wit_4 : clause_cmp_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( fp32_ge retval_3 retval_4 ) as H_fp32_ge.
  bind_fact ( msat_fp32_same retval_4 y_activity ) as H_msat_fp32_same.
  bind_fact ( msat_fp32_same retval_3 x_activity ) as H_msat_fp32_same_2.
  bind_fact ( retval_2 <> 2 ) as H_retval_2.
  bind_fact ( retval_2 = clause_hdr_word msat_true (Zlength y_words) ÷ 2 ) as H_retval_2_2.
  bind_fact ( retval = clause_hdr_word msat_true (Zlength x_words) ÷ 2 ) as H_retval.
  bind_fact ( 0 < x_pre ) as H_x_pre.
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2.
  bind_fact ( 0 < y_pre ) as H_y_pre.
  bind_fact ( y_pre % 2 = 0 ) as H_y_pre_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  bind_fact ( msat_fp32_nonnegative y_activity ) as H_msat_fp32_nonnegative_2.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength y_words)
    (Zlength_nonneg y_words)) as Hylen0.
  unfold msat_true in H_retval_2_2, H_retval.
  assert (Hynotbinary : Zlength y_words <> 2).
  { intros Hylen.
    apply H_retval_2.
    transitivity (clause_hdr_word true (Zlength y_words) ÷ 2).
    - exact H_retval_2_2.
    - transitivity (Zlength y_words); assumption. }
  assert (Hxmod : x_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_x_pre_2. }
  assert (Hymod : y_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_y_pre_2. }
  unfold msat_fp32_same in H_msat_fp32_same, H_msat_fp32_same_2.
  subst retval_4 retval_3.
  unfold msat_true.
  sep_apply_r_atomic (learnt_cmp_result_stop_two_activity_first__clause_cmp
    db activities x_pre x_words x_activity
    y_pre y_words y_activity
    H_x_pre Hxmod H_msat_fp32_nonnegative H_y_pre Hymod H_msat_fp32_nonnegative_2
    (or_intror (conj Hynotbinary H_fp32_ge))).
  (Intros; cancel).
Qed.


Lemma proof_of_clause_new_entail_wit_3_2 : clause_new_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite ?Z.sub_0_r in *.
  cn_pin_prob cn_sel_clause_new_spec.
  bind_fact ( c % 2 = 0 ) as H_c.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec cn_M_clause_new_spec cn_words_clause_new_spec 0 cn_root_clause_new_spec ) as H_clause_new_stage_ready.
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
  2-23: dump_pre_spatial; solve [assumption | lia].
  assert (Hi : i = size) by lia.
  subst i.
  subst size.
  rewrite (sublist_self cn_words_clause_new_spec
    (Zlength cn_words_clause_new_spec)) by reflexivity.
  lazymatch goal with
  | |- context [IntArray.undef_seg ?x ?lo ?lo] =>
      sep_apply_l_atomic (IntArray.undef_seg_empty x lo)
  end.
  unfold MiniSatClause.rep, clause_hdr_word, activity_state, activity_undef.
  unfold clause_hdr_addr, clause_lits_addr.
  cbv beta iota.
  rewrite (Z.mul_comm 2 (Zlength cn_words_clause_new_spec)).
  split_pure_spatial.
  - cancel.
    cancel.
  - split_pures; dump_pre_spatial.
    rewrite <- (Z.rem_mod_nonneg c 2) by lia.
    pose proof (Zlength_nonneg cn_words_clause_new_spec).
    lia.
Qed.


Lemma proof_of_clause_new_which_implies_wit_1 : clause_new_which_implies_wit_1.
Proof.
LLM_pre_process ltac:(lia).
  copy_fact ( Forall (lit_wf_c cn_n_clause_new_spec) cn_words_clause_new_spec ) as H_Forall.
  copy_fact ( solver_support_inv cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_root_clause_new_spec cn_M_clause_new_spec ) as H_msolver_inv.
  pose proof (msi_shape H_msolver_inv) as Hshape.
  pose proof (msi_size H_msolver_inv) as Hsize.
  change (cn_n_clause_new_spec = ms_size cn_M_clause_new_spec) in Hsize.
  pose proof (solver_shape_wm_len _ Hshape) as Hwm_len.
  change (Zlength (ms_wm cn_M_clause_new_spec) =
    2 * ms_size cn_M_clause_new_spec) in Hwm_len.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 0 H_Forall ltac:(lia)) as Hlit0.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 1 H_Forall ltac:(lia)) as Hlit1.
  pose proof (lit_neg_c_wf _ _ Hlit0) as Hneg0.
  pose proof (lit_neg_c_wf _ _ Hlit1) as Hneg1.
  assert (Hidx0 :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by
    (unfold lit_wf_c in Hneg0; lia).
  assert (Hidx1 :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by
    (unfold lit_wf_c in Hneg1; lia).
  assert (Hne :
    lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <>
    lit_neg_c (Znth 1 cn_words_clause_new_spec 0)).
  { apply first_two_neg_distinct_ge2__clause_new; assumption. }
  unfold solver_rep_levels_wl_at, solver_nonlevel_rep,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  unfold wlists_rep at 1. Intros_p Hwlshape.
  assert (Hidx0' :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) < 2 * ms_size cn_M_clause_new_spec)
    by lia.
  assert (Hidx1' :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) < 2 * ms_size cn_M_clause_new_spec)
    by lia.
  sep_apply (VecpArray.full_split_to_missing2
    cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
    (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
    (2 * ms_size cn_M_clause_new_spec) (ms_wm cn_M_clause_new_spec) nil Hidx0' Hidx1' Hne).
  unfold VecpArray.vec_store.
  prop_apply_p (Vecp.rep_distinct
    (Vecp.slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wm cn_M_clause_new_spec) nil)
    (Vecp.slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))
    (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wm cn_M_clause_new_spec) nil)).
  Intros.
  assert (Hrefold :
    Vecp.rep (Vecp.slot cn_wl_clause_new_spec
        (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))
      (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
        (ms_wm cn_M_clause_new_spec) nil) **
    Vecp.rep (Vecp.slot cn_wl_clause_new_spec
        (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))
      (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
        (ms_wm cn_M_clause_new_spec) nil) **
    VecpArray.missing2 cn_wl_clause_new_spec
      (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (2 * ms_size cn_M_clause_new_spec) (ms_wm cn_M_clause_new_spec)
    |-- VecpArray.full cn_wl_clause_new_spec
          (2 * ms_size cn_M_clause_new_spec) (ms_wm cn_M_clause_new_spec)).
  { pose proof (VecpArray.missing2_merge_to_full
      cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (2 * ms_size cn_M_clause_new_spec) (ms_wm cn_M_clause_new_spec)
      (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
        (ms_wm cn_M_clause_new_spec) nil)
      (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
        (ms_wm cn_M_clause_new_spec) nil) Hidx0' Hidx1' Hne) as Hm.
    rewrite !replace_Znth_Znth in Hm.
    exact Hm. }
  sep_apply Hrefold.
  unfold clause_new_transaction_rest_at_gen, clause_new_frame_at_gen,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep,
    solver_ptrs_rep, solver_var_arrays_rep, solver_trail_array_rep,
    clause_new_scalars_frame, clause_new_vecs_frame_gen,
    clause_new_ptrs_frame.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  unfold solver_wlists_handle, db_words.
  unfold wlists_rep. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  rewrite Hsize. cancel.
  assert (cn_sel_clause_new_spec = 0 \/ cn_sel_clause_new_spec = 1)
    as [-> | ->] by lia.
  (* At a CONCRETE index the
     selectors simply reduce, so unfold is exactly right here -- it is only at
     a symbolic index that unfolding is the wrong move. *)
  - cn_at_prob. cancel.
    replace (1 - 0) with 1 by lia.
    unfold solver_selected_db, solver_selected_vec; cbn.
    cancel.
  - cn_at_learnt. cancel.
    replace (1 - 1) with 0 by lia.
    unfold solver_selected_db, solver_selected_vec; cbn.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_remove_return_wit_2 : clause_remove_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_remove_close s_pre is_learnt retval_9 retval_12 k_2 false true.
Qed.



Lemma proof_of_clause_setactivity_return_wit_1 : clause_setactivity_return_wit_1.
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


Lemma proof_of_clause_setactivity_which_implies_wit_1 : clause_setactivity_which_implies_wit_1.
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


Lemma proof_of_lit_neg_return_wit_3_sentinel_split_goal_1 : lit_neg_return_wit_3_sentinel_split_goal_1.
Abort.


Lemma proof_of_lit_neg_return_wit_3_sentinel : lit_neg_return_wit_3_sentinel.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_order_select_safety_wit_37 : order_select_safety_wit_37.
Proof.
  msat_order_select_sift_child_bound size.
Qed.


Lemma proof_of_order_update_entail_wit_1_split_goal_1 : order_update_entail_wit_1_split_goal_1.
Abort.


Lemma proof_of_order_update_entail_wit_1_split_goal_2 : order_update_entail_wit_1_split_goal_2.
Abort.


Lemma proof_of_order_update_entail_wit_1 : order_update_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (store_int_range (&("v")) v_pre).
  prop_apply_p (store_int_range (&("i")) (Znth (v_pre - 0) orderpos0 0)).
  bind_fact (order_update_pre n v_pre heap0 orderpos0) as H_order_update_pre.
  unfold order_update_pre, order_heap_wf, heap_wf in H_order_update_pre.
  cbn in H_order_update_pre.
  destruct H_order_update_pre as ((Hlen & _) & _).
  replace (v_pre - 0) with v_pre in * by lia.
  rewrite (Znth_indep orderpos0 v_pre 0 (-1)) by lia.
  entailer!.
Qed.



Lemma proof_of_order_update_return_wit_1 : order_update_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre.
  bind_fact ( order_update_loop_inv n v_pre heap0 x i heap_now orderpos_now ) as H_order_update_loop_inv.
  pose proof (order_update_close_post__order_update
    n v_pre heap0 orderpos0 x i heap_now orderpos_now H_order_update_pre H_order_update_loop_inv) as Hpost.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth x i orderpos_now)).
  sep_apply_l_atomic (IntArray.full_to_seg heap
    (Zlength heap_now) (replace_Znth i x heap_now)).
  Exists (replace_Znth i x heap_now) (replace_Znth x i orderpos_now).
  replace (Zlength heap_now) with (Zlength (replace_Znth i x heap_now)) by (rewrite Zlength_replace_Znth; reflexivity).
  sep_apply (Veci.rep_intro &(s_pre # "solver_t" ->ₛ "order") heap (replace_Znth i x heap_now) cap _ _ _ eq_refl eq_refl eq_refl ltac:(rewrite Zlength_replace_Znth; lia) ltac:(lia) ltac:(vec_buf_solve)).
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_selectionsort_entail_wit_3_1_split_goal_1 : selectionsort_entail_wit_3_1_split_goal_1.
Abort.


Lemma proof_of_selectionsort_entail_wit_3_1 : selectionsort_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold selectionsort_inner_inv, learnt_cmp_result in *.
  Exists current_2.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_reducedb_entail_wit_3_split_goal_1 : solver_reducedb_entail_wit_3_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state;
  bind_fact ( msolver_inv n F A_arr A_inst Mnext ) as H_msolver_inv;
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv;
    unfold db_compaction_inv in H_db_compaction_inv; lia.
Qed.


Lemma proof_of_solver_reducedb_entail_wit_3_split_goal_2 : solver_reducedb_entail_wit_3_split_goal_2.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state;
  bind_fact ( msolver_inv n F A_arr A_inst Mnext ) as H_msolver_inv;
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv;
    unfold db_compaction_inv in H_db_compaction_inv; lia.
Qed.


Lemma proof_of_solver_reducedb_entail_wit_3_split_goal_3 : solver_reducedb_entail_wit_3_split_goal_3.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state;
  bind_fact ( msolver_inv n F A_arr A_inst Mnext ) as H_msolver_inv;
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv;
    unfold db_compaction_inv in H_db_compaction_inv; lia.
Qed.


Lemma proof_of_solver_reducedb_entail_wit_3_split_goal_4 : solver_reducedb_entail_wit_3_split_goal_4.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state;
  bind_fact ( msolver_inv n F A_arr A_inst Mnext ) as H_msolver_inv.
  apply MSatFloatFacts.fp32_nonnegative_eq_refl.
  exact (msi_cla_inc_nonnegative H_msolver_inv).
Qed.


Lemma proof_of_solver_reducedb_entail_wit_3 : solver_reducedb_entail_wit_3.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_solver_reducedb_entail_wit_3_split_goal_1 M0 A_inst A_arr F n Mcur_2 words_2 Mnext words_next i extra_lim j PreH1 PreH2).
- Goal_apply (proof_of_solver_reducedb_entail_wit_3_split_goal_2 M0 A_inst A_arr F n Mcur_2 words_2 Mnext words_next i extra_lim j PreH1 PreH2).
- Goal_apply (proof_of_solver_reducedb_entail_wit_3_split_goal_3 M0 A_inst A_arr F n Mcur_2 words_2 Mnext words_next i extra_lim j PreH1 PreH2).
- Goal_apply (proof_of_solver_reducedb_entail_wit_3_split_goal_4 M0 A_inst A_arr F n Mcur_2 words_2 Mnext words_next i extra_lim j PreH1 PreH2).
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_15_pure : solver_reducedb_partial_solve_wit_15_pure.
Proof.
  msat_reducedb_first_lit_bounds_pure.
Qed.


Lemma proof_of_sortrnd_which_implies_wit_1 : sortrnd_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Permutation srt_origin current ) as H_Permutation.
  bind_fact ( Zlength current = size ) as H_Zlength.
  bind_fact ( learnt_sort_segment_domain srt_db current ) as H_learnt_sort_segment_domain.
  assert (Hsplit :
    current = sublist 0 i current ++ sublist i size current).
  { rewrite <- (sublist_split 0 size i current) by lia.
    rewrite sublist_self by lia. reflexivity. }
  assert (Hll : Zlength (sublist 0 i current) = i)
    by (apply Zlength_sublist0; lia).
  assert (Hlr : Zlength (sublist i size current) = size - i)
    by (apply Zlength_sublist; lia).
  assert (Hdoms :
    learnt_sort_segment_domain srt_db (sublist 0 i current) /\
    learnt_sort_segment_domain srt_db (sublist i size current)).
  { unfold learnt_sort_segment_domain in *.
    rewrite Hsplit in H_learnt_sort_segment_domain.
    apply Forall_app in H_learnt_sort_segment_domain. exact H_learnt_sort_segment_domain. }
  destruct Hdoms as [Hdl Hdr].
  assert (Hsp : sortrnd_split srt_db srt_origin current
    (sublist 0 i current) (sublist i size current) size i).
  { unfold sortrnd_split.
    split; [exact H_Permutation |].
    split; [exact H_Zlength |].
    split; [lia |].
    split; [exact Hsplit |].
    split; [exact Hll |].
    split; [exact Hlr |].
    split; assumption. }
  sep_apply_l_atomic
    (PtrArray.seg_split_to_seg array 0 i size current ltac:(lia)).
  replace (i - 0) with i by lia.
  replace (size - 0) with size by lia.
  Exists (sublist 0 i current) (sublist i size current).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_cmp_return_wit_1 : clause_cmp_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval_2 = 2 ) as H_retval_2.
  bind_fact ( retval_2 = clause_hdr_word msat_true (Zlength y_words) ÷ 2 ) as H_retval_2_2.
  bind_fact ( retval > 2 ) as H_retval.
  bind_fact ( retval = clause_hdr_word msat_true (Zlength x_words) ÷ 2 ) as H_retval_3.
  bind_fact ( 0 < x_pre ) as H_x_pre.
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2.
  bind_fact ( 0 < y_pre ) as H_y_pre.
  bind_fact ( y_pre % 2 = 0 ) as H_y_pre_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  bind_fact ( msat_fp32_nonnegative y_activity ) as H_msat_fp32_nonnegative_2.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength y_words)
    (Zlength_nonneg y_words)) as Hylen0.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength x_words)
    (Zlength_nonneg x_words)) as Hxlen0.
  unfold msat_true in H_retval_2_2, H_retval_3.
  apply Z.gt_lt in H_retval.
  assert (Hylen : Zlength y_words = 2).
  { rewrite <- Hylen0.
    transitivity retval_2.
    - symmetry. exact H_retval_2_2.
    - exact H_retval_2. }
  assert (Hxlen : 2 < Zlength x_words).
  { rewrite <- Hxlen0, <- H_retval_3. exact H_retval. }
  assert (Hxmod : x_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_x_pre_2. }
  assert (Hymod : y_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_y_pre_2. }
  unfold msat_true.
  pose proof (learnt_cmp_result_lt_two_yx_headers__clause_cmp
    db activities x_pre x_words x_activity
    y_pre y_words y_activity
    H_x_pre Hxmod H_msat_fp32_nonnegative H_y_pre Hymod H_msat_fp32_nonnegative_2
    Hxlen (or_introl Hylen))
    as Hresult.
  sep_apply Hresult.
  cancel.
Qed.


Lemma proof_of_clause_cmp_return_wit_3 : clause_cmp_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( fp32_lt retval_3 retval_4 ) as H_fp32_lt.
  bind_fact ( msat_fp32_same retval_4 x_activity ) as H_msat_fp32_same.
  bind_fact ( msat_fp32_same retval_3 x_activity ) as H_msat_fp32_same_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  unfold msat_fp32_same in H_msat_fp32_same, H_msat_fp32_same_2.
  subst retval_4 retval_3.
  pose proof (MSatFloatFacts.fp32_nonnegative_eq_refl
    x_activity H_msat_fp32_nonnegative) as Heq.
  unfold fp32_lt, fp32_eq in H_fp32_lt, Heq.
  congruence.
Qed.


Lemma proof_of_clause_cmp_return_wit_6 : clause_cmp_return_wit_6.
Proof.
  msat_clause_cmp_alias_stop y_pre x_pre x_activity db activities x_words
    learnt_cmp_result_stop_alias_header_first__clause_cmp.
Qed.


Lemma proof_of_clause_cmp_which_implies_wit_1 : clause_cmp_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( In x (db_words db) ) as Hx.
  bind_fact ( In y (db_words db) ) as Hy.
  destruct (Z.eq_dec x y) as [Heq | Hneq].
  - subst y.
    sep_apply (learnt_sort_rep_focus_one__clause_cmp db activities x Hx).
    Intros xlits xa.
    unfold learnt_clause_snapshot_raw, msat_true.
    Left. Exists xlits xa.
    Intros_p Hxf.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial.
      * reflexivity.
      * tauto.
      * rewrite Z.rem_mod_nonneg by lia. tauto.
      * tauto.
  - sep_apply (learnt_sort_rep_focus_two__clause_cmp
      db activities x y Hx Hy Hneq).
    Intros xlits ylits xa ya.
    unfold learnt_clause_snapshot_raw, msat_true.
    Right. Exists ylits xlits ya xa.
    Intros_p Hxf.
    Intros_p Hyf.
    split_pure_spatial.
    + cancel (learnt_sort_two_remainder db activities x xlits xa y ylits ya).
      cancel.
    + split_pures; dump_pre_spatial.
      * exact Hneq.
      * tauto.
      * rewrite Z.rem_mod_nonneg by lia. tauto.
      * tauto.
      * rewrite Z.rem_mod_nonneg by lia. tauto.
      * tauto.
      * tauto.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_25_pure : clause_remove_partial_solve_wit_25_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_clause_remove_partial_solve_wit_28_pure : clause_remove_partial_solve_wit_28_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_23_pure : clause_remove_partial_solve_wit_23_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_remove_watch_in_pure false.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_24_pure : clause_remove_partial_solve_wit_24_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_clause_remove_return_wit_3 : clause_remove_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_remove_close s_pre is_learnt retval_8 retval_10 k_2 true false.
Qed.



Lemma proof_of_lit_var_return_wit_3_original : lit_var_return_wit_3_original.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
    unfold lit_var_c;
    rewrite Z.shiftr_div_pow2 by lia;
    change (2 ^ 1) with 2;
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_order_select_entail_wit_2_2 : order_select_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hfp : fp64_eq (Z_to_fp64 seed_shadow) (Z_to_fp64 seed_shadow)).
  { apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  subst retval.
  sep_apply store_float_undef_store_float.
  Exists seed_shadow seed_value heap0 orderpos0.
  split_pure_spatial;
    [ cancel (CharArray.seg assigns_ptr 0 n assigns0); cancel
    | split_pures; dump_pre_spatial;
      first [ reflexivity | assumption | lia
            | (unfold order_select_loop_inv; split; [assumption | apply incl_refl]) ] .. ].
Qed.



Lemma proof_of_order_select_return_wit_2 : order_select_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (next - 0) assigns0 0 = 0 ) as H_Znth.
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before sift_heap_now sift_orderpos_now assigns0 trail0
      qhead ) as H_order_select_sift_inv.
  replace (next - 0) with next in * by lia.
  set (heap' := replace_Znth i x sift_heap_now).
  set (orderpos' := replace_Znth (Znth i heap' 0) i sift_orderpos_now).
  assert (Hmoved : Znth i heap' 0 = x).
  { subst heap'. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hpost : order_select_post n next heap0 heap' orderpos'
    assigns0 trail0 qhead).
  { subst orderpos'. rewrite Hmoved.
    eapply order_select_sift_close_unassigned_post__order_select
      with (before := sift_heap_before).
    - exact H_order_select_sift_inv.
    - exact H_Znth. }
  assert (Hheaplen : Zlength heap' = Zlength sift_heap_now).
  { subst heap'. rewrite Zlength_replace_Znth. reflexivity. }
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n orderpos').
  sep_apply_l_atomic (IntArray.full_to_seg heap
    (Zlength sift_heap_now) heap').
  Exists sift_seed_shadow_now sift_seed_value_now heap' orderpos'.
  rewrite <- Hheaplen.
  sep_apply (Veci.rep_intro &(s_pre # "solver_t" ->ₛ "order") heap heap' cap _ _ _ eq_refl eq_refl eq_refl);
    [ | pose proof (Zlength_nonneg heap'); first [lia | vec_buf_solve] .. ].
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.



Lemma proof_of_order_select_return_wit_5 : order_select_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (next - 0) assigns0 0 = 0 ) as H_Znth.
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before sift_heap_now sift_orderpos_now assigns0 trail0
      qhead ) as H_order_select_sift_inv.
  replace (next - 0) with next in * by lia.
  assert (Hati : Znth i (replace_Znth i x sift_heap_now) 0 = x)
    by (rewrite Znth_replace_Znth_Same; lia).
  rewrite Hati in *.
  pose proof (order_select_sift_close_post__order_select
    n next x i heap0 sift_heap_before sift_heap_now sift_orderpos_now
    assigns0 trail0 qhead H_order_select_sift_inv H_Znth) as Hpost.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth x i sift_orderpos_now)).
  sep_apply_l_atomic (IntArray.full_to_seg heap
    (Zlength sift_heap_now) (replace_Znth i x sift_heap_now)).
  Exists sift_seed_shadow_now sift_seed_value_now
    (replace_Znth i x sift_heap_now) (replace_Znth x i sift_orderpos_now).
  assert (Hheaplen : Zlength (replace_Znth i x sift_heap_now) = Zlength sift_heap_now)
    by (rewrite Zlength_replace_Znth; reflexivity).
  rewrite <- Hheaplen.
  sep_apply (Veci.rep_intro &(s_pre # "solver_t" ->ₛ "order") heap (replace_Znth i x sift_heap_now) cap _ _ _ eq_refl eq_refl eq_refl);
    [ | pose proof (Zlength_nonneg (replace_Znth i x sift_heap_now)); first [lia | vec_buf_solve] .. ].
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.



Lemma proof_of_order_select_safety_wit_38 : order_select_safety_wit_38.
Proof.
  msat_order_select_sift_child_bound size.
Qed.


Lemma proof_of_order_update_entail_wit_5 : order_update_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hparent_def : parent = (i - 1) ÷ 2) by assumption.
  assert (Hactivity_len : Zlength activity0 = n) by assumption.
  replace (x - 0) with x in * by lia.
  replace (parent - 0) with parent in * by lia.
  replace (Znth parent heap_now_2 0 - 0)
    with (Znth parent heap_now_2 0) in * by lia.
  set (y := Znth parent heap_now_2 0).
  set (heap' := replace_Znth i y heap_now_2).
  set (pos' := replace_Znth y i orderpos_now_2).
  assert (Hparent_lt : parent < i).
  { rewrite Hparent_def. apply Z.quot_lt_upper_bound; lia. }
  assert (Hparent_ne : parent <> i) by lia.
  assert (Hstep : order_update_loop_inv n v_pre heap0 x parent heap' pos').
  { subst heap' pos' y.
    apply order_update_loop_inv_step__order_update; try assumption; lia. }
  assert (Hlen' : Zlength heap' = Zlength heap_now_2) by apply Zlength_replace_Znth.
  assert (Hy : 0 <= y < n) by (unfold y; lia).
  assert (Hxy : x <> y) by (unfold y; lia).
  assert (Hxrange : 0 <= x < n) by lia.
  assert (Hati : Znth i heap' 0 = y).
  { unfold heap'. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hposarr :
    replace_Znth
      (Znth i (replace_Znth i (Znth parent heap_now_2 0) heap_now_2) 0)
      i orderpos_now_2 = pos').
  { unfold pos', y. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hheaparr :
    replace_Znth i (Znth parent heap_now_2 0) heap_now_2 = heap')
    by reflexivity.
  fold heap'.
  rewrite Hati.
  fold pos'.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n pos').
  sep_apply_l_atomic
    (IntArray.full_to_seg heap (Zlength heap_now_2) heap').
  sep_apply_l_atomic (double_array_missing2_refold
    activity_ptr x y n activity0 Hxrange Hy Hxy).
  rewrite <- Hlen'.
  sep_apply (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "order") heap heap' cap _ _ _ eq_refl eq_refl eq_refl);
    [ | pose proof (Zlength_nonneg heap'); first [lia | vec_buf_solve] .. ].
  set (gp := (parent - 1) ÷ 2).
  replace (gp - 0) with gp in * by lia.
  destruct (Z.eq_dec parent 0) as [Hparent_zero|Hparent_nonzero].
  - assert (Hgp0 : gp = 0)
      by (unfold gp; rewrite Hparent_zero; reflexivity).
    assert (Hlookup0 : Znth 0 heap' 0 = y).
    { unfold heap'.
      rewrite (Znth_replace_Znth_Diff 0 heap_now_2 i 0 y) by lia.
      unfold y. now rewrite Hparent_zero. }
    Left. Exists heap' pos'.
    rewrite Hlen'.
    split_pure_spatial.
    + cancel (DoubleArray.seg activity_ptr 0 n activity0).
      cancel.
    + rewrite Hgp0, Hlookup0.
      split_pures; dump_pre_spatial; solve [auto | lia].
  - assert (Hgp_lo : 0 <= gp).
    { unfold gp. rewrite zdiv_equiv by lia. apply Z.div_pos; lia. }
    assert (Hgp_lt : gp < parent).
    { unfold gp. rewrite zdiv_equiv by lia.
      apply Z.div_lt_upper_bound; lia. }
    assert (Hgp_idx : 0 <= gp < Zlength heap').
    { rewrite Hlen'. lia. }
    pose proof Hstep as Hstep'.
    unfold order_update_loop_inv in Hstep'.
    destruct Hstep' as (_ & _ & Hhole).
    assert (Hgpvalm1 : 0 <= Znth gp heap' (-1) < n).
    { apply (order_heap_one_hole_cell_range
        n heap0 x parent heap' pos' gp Hhole); lia. }
    assert (Hgpind : Znth gp heap' 0 = Znth gp heap' (-1)).
    { apply Znth_indep. exact Hgp_idx. }
    assert (Hgpval0 : 0 <= Znth gp heap' 0 < n).
    { rewrite Hgpind. exact Hgpvalm1. }
    assert (Hxgp0 : x <> Znth gp heap' 0).
    { rewrite Hgpind.
      apply (order_heap_one_hole_saved_neq_cell__order_update
        n heap0 x parent heap' pos' gp Hhole); lia. }
    sep_apply_l_atomic (double_array_seg_split_to_missing2__order_select
      activity_ptr x (Znth gp heap' 0) n activity0
      Hxrange Hgpval0 Hxgp0).
    Right. Exists heap' pos'.
    rewrite Hlen'.
    replace (Znth gp heap' 0 - 0) with (Znth gp heap' 0) by lia.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]); try lia.
Qed.



Lemma proof_of_order_update_which_implies_wit_1 : order_update_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_update_pre n v heap0 orderpos0 ) as H_order_update_pre.
  pose proof H_order_update_pre as Hpre.
  unfold order_update_pre, order_heap_wf in Hpre.
  destruct Hpre as (Hwf & Hv & Hpresent).
  destruct (heap_wf_lookup n
    {| mh_heap := heap0; mh_orderpos := orderpos0 |}
    v Hwf Hv Hpresent) as [Hidx Hback].
  assert (Hback0 : Znth (Znth v orderpos0 (-1)) heap0 0 = v).
  { rewrite (Znth_indep heap0 (Znth v orderpos0 (-1)) 0 (-1))
      by exact Hidx.
    exact Hback. }
  assert (Hval0 : 0 <= Znth (Znth v orderpos0 (-1)) heap0 0 < n).
  { rewrite Hback0. exact Hv. }
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_selectionsort_entail_wit_3_2_split_goal_1 : selectionsort_entail_wit_3_2_split_goal_1.
Abort.


Lemma proof_of_selectionsort_entail_wit_3_2 : selectionsort_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold selectionsort_inner_inv, learnt_cmp_result in *.
  Exists current_2.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_reducedb_entail_wit_2_3 : solver_reducedb_entail_wit_2_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlenr : Zlength (replace_Znth j (Znth (i - 0) words 0) words) = Zlength words)
    by apply Zlength_replace_Znth.
  sep_apply_l_atomic (PtrArray.full_to_seg learnts (Zlength words)
    (replace_Znth j (Znth (i - 0) words 0) words)).
  rewrite <- Hlenr.
  sep_apply (Vecp.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "learnts") learnts (replace_Znth j (Znth (i - 0) words 0) words) cap _ _ _ eq_refl eq_refl eq_refl);
    [ | pose proof (Zlength_nonneg words); first [lia | vec_buf_solve] .. ].
  msat_reducedb_open_state.
  Exists (replace_Znth j (Znth (i - 0) words 0) words) Mcur.
  split_pure_spatial;
  [ cancel (clause_db_rep (ms_learnt Mcur)); cancel
  | split_pures; dump_pre_spatial;
    [ unfold db_compaction_step; repeat split; auto
    | tauto ] ].
Qed.



Lemma proof_of_solver_reducedb_entail_wit_5_4 : solver_reducedb_entail_wit_5_4.
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



Lemma proof_of_solver_reducedb_partial_solve_wit_28_pure : solver_reducedb_partial_solve_wit_28_pure.
Proof.
 msat_reducedb_state_pure.
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_49_pure : solver_reducedb_partial_solve_wit_49_pure.
Proof.
 msat_reducedb_state_pure.
Qed.


Lemma proof_of_sortrnd_entail_wit_1 : sortrnd_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst size_pre.
  assert (Hinv : sortrnd_partition_inv srt_db srt_activities srt_origin srt_origin
                   (Zlength srt_origin) (Znth (retval - 0) srt_origin 0)
                   (-1) (Zlength srt_origin)).
  { replace (retval - 0) with retval by lia.
    eapply sortrnd_initial_partition__solve; eauto. }
  Exists z2 v2 srt_origin.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_entail_wit_9 : sortrnd_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists seed_shadow1_2 seed_value1_2 current_4.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_which_implies_wit_4 : sortrnd_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( sortrnd_split srt_db srt_origin current left right size i ) as H_sortrnd_split.
  bind_fact ( Permutation left left_after ) as H_Permutation.
  bind_fact ( Permutation right right_after ) as H_Permutation_2.
  unfold sortrnd_split in H_sortrnd_split.
  destruct H_sortrnd_split as
    [Horigin [Hcurrent [Hcut [Happ [Hleft [Hright [Hleftdom Hrightdom]]]]]]].
  pose proof (Zlength_perm_eq _ _ _ H_Permutation) as Hleft_after.
  pose proof (Zlength_perm_eq _ _ _ H_Permutation_2) as Hright_after.
  assert (Hlen : Zlength (left_after ++ right_after) = size).
  { rewrite Zlength_app. lia. }
  assert (Hperm : Permutation srt_origin (left_after ++ right_after)).
  { eapply Permutation_trans; [exact Horigin|].
    rewrite Happ. apply Permutation_app; assumption. }
  sep_apply_l_atomic
    (PtrArray.seg_merge_to_seg array 0 i size left_after right_after).
  - dump_pre_spatial. lia.
  - Exists (left_after ++ right_after). msat_manual_entailer_with ltac:(lia).
Qed.









Lemma proof_of_act_clause_bump_partial_solve_wit_5_pure : act_clause_bump_partial_solve_wit_5_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
  try solve [msat_manual_entailer_with ltac:(lia)].
Qed.


Lemma proof_of_act_var_bump_entail_wit_1_2_split_goal_1 : act_var_bump_entail_wit_1_2_split_goal_1.
Abort.


Lemma proof_of_act_var_bump_entail_wit_1_2 : act_var_bump_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists var_inc0
    (replace_Znth (v_pre - 0)
       (fp64_add (double_Znth (v_pre - 0) activity0) var_inc0) activity0).
  rewrite Zlength_replace_Znth.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_new_safety_wit_7 : clause_new_safety_wit_7.
Proof.
LLM_pre_process ltac:(lia || int_auto).
msat_clause_new_safety.
Qed.


Lemma proof_of_clause_read_lit_return_wit_1 : clause_read_lit_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( 0 <= c_pre ) as H_c_pre.
  bind_fact ( tagged_word c_pre ) as H_tagged_word.
  bind_fact ( 0 <= tag_lit c_pre ) as H_tag_lit.
  bind_fact ( tag_lit c_pre <= 2147483647 ) as H_tag_lit_2.
  pose proof
    (clause_read_lit_value__clause_is_lit
       c_pre H_c_pre H_tagged_word H_tag_lit H_tag_lit_2) as Hread.
  msat_manual_entailer_with ltac:(lia).
Qed.




Lemma proof_of_clause_size_which_implies_wit_1 : clause_size_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_order_select_entail_wit_4 : order_select_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_select_loop_inv n heap0 heap_now orderpos_now assigns0 trail0 qhead ) as H_order_select_loop_inv.
  pose proof
    (order_select_loop_inv_cell_range__order_select
       n heap0 heap_now orderpos_now assigns0 trail0 qhead 0 H_order_select_loop_inv
       ltac:(lia)) as Hroot_range.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_order_select_entail_wit_10_3 : order_select_entail_wit_10_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_order_select_orp_right.
  prop_rewrite (store_int_range (&(s_pre # "solver_t" ->ₛ "size")) n).
  Intros.
  prop_rewrite (store_int_range (&("size")) size_2).
  Intros.
  prop_rewrite (store_int_range (&("next")) next_2).
  Intros.
  prop_rewrite (store_int_range (&("x")) x_2).
  Intros.
  change (INT_MIN <= n <= INT_MAX) in H.
  change (INT_MIN <= size_2 <= INT_MAX) in H0.
  change (INT_MIN <= next_2 <= INT_MAX) in H1.
  change (INT_MIN <= x_2 <= INT_MAX) in H2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: solve [assumption | lia | rewrite Znth_replace_Znth_Same by lia; lia].
Qed.
