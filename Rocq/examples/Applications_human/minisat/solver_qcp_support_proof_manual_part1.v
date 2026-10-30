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
Lemma proof_of_act_clause_bump_partial_solve_wit_4_pure : act_clause_bump_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (msat_fp32_same retval activity_now) as Hsame.
  assert (Hretval : msat_fp32_nonnegative retval).
  { unfold msat_fp32_same in Hsame. rewrite Hsame. assumption. }
  assert (Hadded : msat_fp32_nonnegative (fp32_add retval cla_inc0)).
  { apply MSatFloatFacts.fp32_nonnegative_add; assumption. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_act_clause_rescale_which_implies_wit_1 : act_clause_rescale_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( learnt_db db ) as H_learnt_db.
  assert (Hin : In (Znth (i - 0) (db_words db) 0) (db_words db)).
  { apply Znth_In. lia. }
  sep_apply
    (learnt_clause_focus_by_word__act_var_bump db
       (Znth (i - 0) (db_words db) 0) H_learnt_db Hin).
  Intros clause_words activity_now.
  Exists clause_words activity_now.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; (int_auto) ..]).
  rewrite Z.rem_mod_nonneg by lia.
  tauto.
Qed.


Lemma proof_of_clause_cmp_partial_solve_wit_8_pure : clause_cmp_partial_solve_wit_8_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_entailer_with ltac:(apply Zlength_nonneg).
Qed.


Lemma proof_of_clause_new_which_implies_wit_7 : clause_new_which_implies_wit_7.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 unfold clause_new_transaction_rest_at_gen.
 cancel.
 cancel.
Qed.


Lemma proof_of_clause_remove_entail_wit_1 : clause_remove_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH8 as Hready.
  unfold clause_remove_ready in Hready.
  destruct Hready as (Hlen & Hforall & Hvars & Hwm & Hstats & Hin0 & Hin1).
  destruct (msat_first_two_lits_wf _ _ Hforall Hlen)
    as (Hlit0 & Hlit1 & Hneg0 & Hneg1).
  unfold lit_wf_c in Hlit0, Hlit1, Hneg0, Hneg1.
  subst retval.
  replace (clause_lits_addr c_pre + 0 * sizeof(INT))
    with (clause_lits_addr c_pre) by lia.
  replace (1 * sizeof(INT)) with (sizeof(INT)) by lia.
  repeat lazymatch goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end.
  all: try (dump_pre_spatial; first [ assumption | lia ]).
  sep_apply_l_atomic
    (intarray_expose_first_two__clause_new
      (clause_lits_addr c_pre) clause_words Hlen).
  msat_cancel_sound.
  cancel.
Qed.


Lemma proof_of_clause_remove_return_wit_4 : clause_remove_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_remove_close s_pre is_learnt retval_9 retval_12 k_2 false false.
Qed.



Lemma proof_of_clause_remove_which_implies_wit_1 : clause_remove_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold clause_remove_open_at in *.
  unfold clause_remove_pre. Intros_p Hpre.
  unfold MiniSatClause.rep. Intros_p Hclause.
  destruct Hpre as (Hn & Hcap & Hbound & Hlen & Hready & Hunlocked).
  destruct Hclause as [_ [Hpos Hmod]].
  split_pure_spatial.
  - cancel (wlists_rep wl n wm).
    cancel.
  - split_pures; dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite Z.rem_mod_nonneg by lia. exact Hmod.
    + exact Hlen.
    + exact Hready.
    + exact Hunlocked.
Qed.


Lemma proof_of_order_select_entail_wit_11_2 : order_select_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before_2 sift_heap_now_2 sift_orderpos_now_2 assigns0
      trail0 qhead ) as H_order_select_sift_inv.
  bind_fact ( Zlength sift_heap_now_2 = size ) as H_Zlength.
  bind_fact ( 0 <= Znth (child - 0) sift_heap_now_2 0 ) as H_Znth.
  bind_fact ( Znth (child - 0) sift_heap_now_2 0 < n ) as H_Znth_2.
  bind_fact ( 0 <= Znth (child + 1 - 0) sift_heap_now_2 0 ) as H_Znth_3.
  bind_fact ( Znth (child + 1 - 0) sift_heap_now_2 0 < n ) as H_Znth_4.
  bind_fact ( Znth (child - 0) sift_heap_now_2 0 <> Znth (child + 1 - 0) sift_heap_now_2 0 ) as H_Znth_5.
  msat_order_select_offsets_all child (child + 1) sift_heap_now_2.
  set (heap' :=
    replace_Znth i (Znth (child + 1) sift_heap_now_2 0) sift_heap_now_2).
  set (orderpos' := replace_Znth (Znth i heap' 0) i sift_orderpos_now_2).
  assert (Hmoved : Znth i heap' 0 = Znth (child + 1) sift_heap_now_2 0).
  { subst heap'. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hsift :
    order_select_sift_inv n next x (child + 1) heap0 sift_heap_before_2
      heap' orderpos' assigns0 trail0 qhead).
  { subst orderpos'. rewrite Hmoved.
    apply order_select_sift_inv_step__order_select.
    - exact H_order_select_sift_inv.
    - lia.
    - lia. }
  assert (Hheaplen : Zlength heap' = Zlength sift_heap_now_2).
  { subst heap'. rewrite Zlength_replace_Znth. reflexivity. }
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n orderpos').
  sep_apply_l_atomic (IntArray.full_to_seg heap
    (Zlength sift_heap_now_2) heap').
  rewrite <- Hheaplen.
  sep_apply (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "order") heap heap' cap _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  assert (Hsz2 : size = Zlength sift_heap_now_2) by lia.
  assert (Hsz : Zlength heap' = size) by lia.
  sep_apply
    (double_array_missing2_refold activity_ptr
      (Znth child sift_heap_now_2 0)
      (Znth (child + 1) sift_heap_now_2 0)
      n activity0 (conj H_Znth H_Znth_2) (conj H_Znth_3 H_Znth_4) H_Znth_5).
  msat_sift_next_reads (child + 1) n size heap' orderpos'
    Hsz Hsz2 Hsift sift_seed_shadow_now_2 sift_seed_value_now_2
    sift_heap_before_2 activity_ptr activity0.
Qed.



Lemma proof_of_order_select_entail_wit_11_3 : order_select_entail_wit_11_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before_2 sift_heap_now_2 sift_orderpos_now_2 assigns0
      trail0 qhead ) as H_order_select_sift_inv.
  set (heap' := replace_Znth i (Znth (child - 0) sift_heap_now_2 0)
    sift_heap_now_2).
  set (orderpos' := replace_Znth (Znth i heap' 0) i
    sift_orderpos_now_2).
  assert (Hmoved : Znth i heap' 0 = Znth child sift_heap_now_2 0).
  { subst heap'. rewrite Znth_replace_Znth_Same by lia.
    replace (child - 0) with child by lia. reflexivity. }
  assert (Hsift : order_select_sift_inv n next x child heap0
    sift_heap_before_2 heap' orderpos' assigns0 trail0 qhead).
  { subst orderpos'. rewrite Hmoved. subst heap'.
    replace (child - 0) with child by lia.
    apply order_select_sift_inv_step__order_select.
    - exact H_order_select_sift_inv.
    - lia.
    - lia. }
  assert (Hheaplen : Zlength heap' = Zlength sift_heap_now_2) by apply Zlength_replace_Znth.
  assert (Hleft_past : Znth (2 * child + 1) heap' 0 = 0)
    by (apply Znth_zero_past_end__order_select; lia).
  assert (Hright_past : Znth (2 * child + 1 + 1) heap' 0 = 0)
    by (apply Znth_zero_past_end__order_select; lia).
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n orderpos').
  sep_apply_l_atomic (IntArray.full_to_seg heap
    (Zlength sift_heap_now_2) heap').
  rewrite <- Hheaplen.
  sep_apply (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "order") heap heap' cap _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  Exists sift_seed_shadow_now_2 sift_seed_value_now_2 sift_heap_before_2
    heap' orderpos'.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_order_select_entail_wit_13_5 : order_select_entail_wit_13_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (Znth (0 - 0) heap_now_2 0 - 0) assigns0 0 <> 0 ) as H_Znth.
  bind_fact ( order_select_loop_inv n heap0 heap_now_2 orderpos_now_2 assigns0 trail0 qhead ) as
      H_order_select_loop_inv.
  replace (0 - 0) with 0 in * by lia.
  replace (Znth 0 heap_now_2 0 - 0)
    with (Znth 0 heap_now_2 0) in * by lia.
  assert (Hone : Zlength heap_now_2 = 1) by lia.
  assert (Hloop : order_select_loop_inv n heap0 (@nil Z)
    (replace_Znth (Znth 0 heap_now_2 (-1)) (-1) orderpos_now_2)
    assigns0 trail0 qhead).
  { apply order_select_loop_pop_assigned_empty__order_select.
    - exact H_order_select_loop_inv.
    - exact Hone.
    - rewrite (Znth_indep heap_now_2 0 (-1) 0) by lia.
      exact H_Znth. }
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth (Znth 0 heap_now_2 0) (-1) orderpos_now_2)).
  rewrite (Znth_indep heap_now_2 0 0 (-1)) by lia.
  rewrite (Zsublist_nil heap_now_2 0 (retval_2 - 1)) by lia.
  Exists seed_shadow_now_2 seed_value_now_2 (@nil Z)
    (replace_Znth (Znth 0 heap_now_2 (-1)) (-1) orderpos_now_2).
  split_pure_spatial.
  - cancel (Veci.rep_ptr &( s_pre # "solver_t" ->ₛ "order") heap nil).
    cancel.
  - split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_order_unassigned_return_wit_3 : order_unassigned_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_order_unassigned_noop_return.
Qed.


Lemma proof_of_order_unassigned_which_implies_wit_1 : order_unassigned_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_unassigned_pre n v heap0 orderpos0 ) as H_order_unassigned_pre.
  pose proof H_order_unassigned_pre as Hun.
  destruct Hun as (Hwf & Hv & Htwon).
  pose proof (heap_wf_orderpos_length n
    {| mh_heap := heap0; mh_orderpos := orderpos0 |} Hwf) as Hoplen.
  cbn [mh_orderpos] in Hoplen.
  destruct (Z.eq_dec (Znth v orderpos0 (-1)) (-1))
    as [Hmissing | Hpresent].
  - assert (Hshort : Zlength heap0 < n).
    { apply (heap_wf_missing_length n
        {| mh_heap := heap0; mh_orderpos := orderpos0 |} v).
      + lia.
      + exact Hwf.
      + exact Hv.
      + exact Hmissing. }
    Left. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - assert (Hpresent0 : Znth (v - 0) orderpos0 0 <> -1).
    { replace (v - 0) with v by lia.
      rewrite <- (Znth_indep orderpos0 v (-1) 0) by lia.
      exact Hpresent. }
    Right. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_order_unassigned_which_implies_wit_2 : order_unassigned_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_order_unassigned_partial_solve_wit_8_pure : order_unassigned_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (v_pre - 0) orderpos0 0 = -1 ) as H_Znth.
  assert (Hmissing0 : Znth v_pre orderpos0 0 = -1).
  { replace (v_pre - 0) with v_pre in H_Znth by lia. exact H_Znth. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_selectionsort_partial_solve_wit_3_pure : selectionsort_partial_solve_wit_3_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH2 as (_ & Hdomain & Hperm & _).
  apply _derivable1_andp_intros.
  all: eapply sort_Znth_in_sep__solve; [exact Hdomain | exact Hperm | lia].
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_25_pure : solver_reducedb_partial_solve_wit_25_pure.
Proof.
 msat_reducedb_state_pure.
Qed.


Lemma proof_of_solver_reducedb_return_wit_1 : solver_reducedb_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_open_state.
  bind_fact ( Zlength (sublist 0 j words) = j ) as H_Zlength.
  bind_fact ( msolver_inv n F A_arr A_inst Mcur ) as H_msolver_inv.
  bind_fact ( db_compaction_inv Mcur words i j ) as H_db_compaction_inv.
  unfold solver_reducedb_post_at.
  Exists Mcur.
  cancel.
  unfold solver_rep_levels_wl_at.
  unfold solver_db_mutation_frame_at.
  Intros act asg opos trl tgs.
  Exists act asg opos reasons_ptr trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  split_pure_spatial.
  - cancel (clause_db_rep (ms_learnt Mcur)).
    cancel.
    unfold db_compaction_inv in H_db_compaction_inv.
    destruct H_db_compaction_inv as [_ [_ [_ Hwords]]].
    assert (Hi : i = Zlength words) by lia.
    rewrite Hi in Hwords.
    rewrite (Zsublist_nil words (Zlength words) (Zlength words) ltac:(lia)) in Hwords.
    simpl in Hwords.
    unfold solver_scalars_rep, solver_fp_rep, solver_vecs_rep.
    rewrite Hwords.
    rewrite app_nil_r.
    unfold clause_new_scalars_frame, solver_vecs_without_learnts_rep.
    sep_apply (Vecp.rep_ptr_rep &( s_pre # "solver_t" ->ₛ "learnts") learnts
      (sublist 0 j words)).
    cancel (Vecp.rep &( s_pre # "solver_t" ->ₛ "clauses") (map fst (ms_prob Mcur))).
    cancel.
  - split_pures; dump_pre_spatial.
    + tauto.
    + exact (msi_shape H_msolver_inv).
Qed.



Lemma proof_of_solver_reducedb_safety_wit_13 : solver_reducedb_safety_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_open_state.
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv.
  sep_apply (Vecp.rep_ptr_bounds &( s_pre # "solver_t" ->ₛ "learnts") learnts words_next).
  Intros.
  split_pures; dump_pre_spatial; unfold db_compaction_inv in H_db_compaction_inv; lia.
Qed.



Lemma proof_of_sortrnd_entail_wit_5 : sortrnd_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval >= 0 ) as H_retval.
  bind_fact ( learnt_cmp_result srt_db srt_activities (Znth (i - 0) current_2 0) pivot retval ) as H_learnt_cmp_result.
  bind_fact ( sortrnd_left_scan_inv srt_db srt_activities srt_origin current_2 size_pre pivot (i - 1) j ) as
    H_sortrnd_left_scan_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  bind_fact ( 0 <= i ) as H_i.
  bind_fact ( i < size_pre ) as H_i_2.
  bind_fact ( 0 < j ) as H_j.
  bind_fact ( j <= size_pre ) as H_j_2.
  rewrite ?Z.sub_0_r in *.
  unfold sortrnd_left_scan_inv in H_sortrnd_left_scan_inv.
  pose proof
    (sortrnd_right_scan_entry__sortrnd
       _ _ _ _ _ _ _ _ _ H_sortrnd_left_scan_inv H_learnt_cmp_result H_retval H_Zlength
       H_i H_i_2 H_j H_j_2) as Hinv.
  rewrite H_Zlength in Hinv.
  replace (j - 1 + 1) with j by lia.
  assert (Hrefl :
      fp64_eq (Z_to_fp64 seed_shadow_now_2) (Z_to_fp64 seed_shadow_now_2)).
  { apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  Exists seed_shadow_now_2 seed_value_now_2 current_2.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_partial_solve_wit_15_pure : sortrnd_partial_solve_wit_15_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold sortrnd_split in PreH11.
  destruct PreH11 as [_ [Hlc [_ [_ [_ [Hlr [_ Hdr]]]]]]].
  assert (Hrefl :
      fp64_eq (Z_to_fp64 shadow_after_left) (Z_to_fp64 shadow_after_left)).
  { apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  split_pures; dump_pre_spatial; first [ assumption | lia ].
Qed.



Lemma proof_of_clause_remove_partial_solve_wit_22_pure : clause_remove_partial_solve_wit_22_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_remove_watch_in_pure true.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_17_pure : clause_remove_partial_solve_wit_17_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_20_pure : clause_remove_partial_solve_wit_20_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.









Lemma proof_of_act_clause_rescale_return_wit_1_split_goal_1 : act_clause_rescale_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hscale : msat_fp32_positive_finite (fp32_of_real (0.000000000000000000009999999682655225388967887463487205224055287544615566730499267578125)%R)).
  { apply (MSatFloatFacts.fp32_of_real_positive_from_bpow _ (-100) 0); try lia.
    - unfold Flocq.Core.Raux.bpow. simpl. field_simplify; nra.
    - rewrite Rabs_right by lra.
      change (Flocq.Core.Raux.bpow Flocq.Core.Zaux.radix2 0) with 1%R. lra. }

  apply MSatFloatFacts.fp32_nonnegative_mul_positive_finite.
  - assumption.
  - exact Hscale.
Qed.


Lemma proof_of_act_clause_rescale_return_wit_1 : act_clause_rescale_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_act_clause_rescale_return_wit_1_split_goal_1 cla_inc0 db i retval).
Qed.



Lemma proof_of_clause_new_partial_solve_wit_7_pure : clause_new_partial_solve_wit_7_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst.

 try (assert (Hi : i = Zlength cn_words_clause_new_spec) by lia; subst i).
 msat_clause_new_side_conditions.
Qed.


Lemma proof_of_clause_new_which_implies_wit_4 : clause_new_which_implies_wit_4.
Proof.
LLM_pre_process ltac:(lia).
  copy_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec cn_M_clause_new_spec cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as
      H_clause_new_stage_ready.
  split_pure_spatial.
  { cancel. }
  split_pures.
  { dump_pre_spatial. exact H_clause_new_stage_ready. }
  sep_apply (MiniSatClause_undef_db_distinct
    c (solver_selected_is_learnt cn_sel_clause_new_spec) size ((solver_selected_db cn_sel_clause_new_spec cn_M_clause_new_spec))).
  Intros_p Hlearnt.
  unfold clause_new_transaction_rest_at_gen, clause_new_frame_at_gen.
  Intros act asg opos rsn trl tgs.
  sep_apply (MiniSatClause_undef_db_distinct
    c (solver_selected_is_learnt cn_sel_clause_new_spec) size (solver_selected_db (1 - cn_sel_clause_new_spec) cn_M_clause_new_spec)).
  Intros_p Hprob.
  Intros.
  sep_apply_l_atomic (MiniSatClause_undef_binary_distinct
    c (solver_selected_is_learnt cn_sel_clause_new_spec) size
    (ms_binary cn_M_clause_new_spec) (ms_binary_lits cn_M_clause_new_spec)).
  Intros_p Hbinary.
  unfold MiniSatClause.undef at 1. Intros_p Hptr.
  dump_pre_spatial.
  unfold clause_allocator_fresh, msolver_db.
  repeat split; try tauto.
  { apply clause_ptr_even. tauto. }
  { (* membership in the whole database: at a symbolic index the selected and
       complementary halves are unrelated atoms, so tauto has nothing to chain.
       The index decides which is which and nothing else does. *)
    rewrite map_app, in_app_iff.
    assert (cn_sel_clause_new_spec = 0 \/ cn_sel_clause_new_spec = 1)
      as [-> | ->] by lia; [ cn_at_prob | cn_at_learnt ]; tauto. }
Qed.



Lemma proof_of_clause_simplify_partial_solve_wit_9_pure : clause_simplify_partial_solve_wit_9_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_simplify_lit_range_pure.
Qed.


Lemma proof_of_clause_simplify_return_wit_2 : clause_simplify_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - subst lits retval_3 current_value current_lit.
    rewrite replace_Znth_Znth by lia.
    msat_cancel_sound.
    sep_apply_l_atomic (CharArray.full_to_seg assigns_ptr n assigns0).
    unfold clause_simplify_scan_inv in PreH23.
    destruct PreH23 as (Hi & Halen & Hlits & Hcells & Hprefix).
    assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
      by (apply clause_hdr_word_nonneg; apply Zlength_nonneg).
    rewrite zdiv_equiv in PreH18 by lia.
    rewrite clause_hdr_word_div2 in PreH18 by apply Zlength_nonneg.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        (clause_lits_addr c_pre) i (Zlength clause_words) (Znth i clause_words 0) clause_words).
    + dump_pre_spatial; lia.
    + rewrite replace_Znth_Znth by lia.
      sep_apply_l_atomic (IntArray.full_to_seg (clause_lits_addr c_pre) (Zlength clause_words) clause_words).
      cancel.
  - split_pures.
    all: first
      [ dump_pre_spatial; assumption
      | msat_clause_simplify_scan_exit n i clause_words assigns0 is_learnt retval retval_2
          retval_3 current_lit current_value lits c_pre assigns_ptr ( 0 + (0 - 1) ) ( retval_2 <> 0 ) ].
Qed.


Lemma proof_of_clause_simplify_safety_wit_11 : clause_simplify_safety_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_simplify_hdr_word_safety.
Qed.


Lemma proof_of_clause_simplify_which_implies_wit_1_split_goal_1 : clause_simplify_which_implies_wit_1_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
    bind_fact ( clause_simplify_scan_inv n clause_words assigns0 i ) as H_clause_simplify_scan_inv;
    unfold clause_simplify_scan_inv in H_clause_simplify_scan_inv;
    destruct H_clause_simplify_scan_inv as (Hi & Halen & Hlits & Hcells & Hprefix);
    assert (Hwf : lit_wf_c n (Znth i clause_words 0)) by
      (apply (Forall_Znth_elim Z (lit_wf_c n)
         clause_words 0 i Hlits); lia);
    pose proof (lit_var_c_in_range n (Znth i clause_words 0) Hwf) as Hvar;
    try lia.
Qed.


Lemma proof_of_clause_simplify_which_implies_wit_1_split_goal_2 : clause_simplify_which_implies_wit_1_split_goal_2.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
    bind_fact ( clause_simplify_scan_inv n clause_words assigns0 i ) as H_clause_simplify_scan_inv;
    unfold clause_simplify_scan_inv in H_clause_simplify_scan_inv;
    destruct H_clause_simplify_scan_inv as (Hi & Halen & Hlits & Hcells & Hprefix);
    assert (Hwf : lit_wf_c n (Znth i clause_words 0)) by
      (apply (Forall_Znth_elim Z (lit_wf_c n)
         clause_words 0 i Hlits); lia);
    pose proof (lit_var_c_in_range n (Znth i clause_words 0) Hwf) as Hvar;
    try lia.
Qed.


Lemma proof_of_clause_simplify_which_implies_wit_1_split_goal_3 : clause_simplify_which_implies_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia. reflexivity.
Qed.


Lemma proof_of_clause_simplify_which_implies_wit_1 : clause_simplify_which_implies_wit_1.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_clause_simplify_which_implies_wit_1_split_goal_1 assigns0 clause_words n i PreH1 PreH2 PreH3).
- Goal_apply (proof_of_clause_simplify_which_implies_wit_1_split_goal_2 assigns0 clause_words n i PreH1 PreH2 PreH3).
- Goal_apply (proof_of_clause_simplify_which_implies_wit_1_split_goal_3 assigns0 clause_words n i PreH1 PreH2 PreH3).
Qed.


Lemma proof_of_clause_simplify_which_implies_wit_2_split_goal_1 : clause_simplify_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (lit_var_c current_lit - 0) with (lit_var_c current_lit) by lia.
  reflexivity.
Qed.


Lemma proof_of_clause_simplify_which_implies_wit_2 : clause_simplify_which_implies_wit_2.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_clause_simplify_which_implies_wit_2_split_goal_1 assigns0 n current_lit PreH1 PreH2).
Qed.


Lemma proof_of_lit_sign_return_wit_1 : lit_sign_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsign : Z.land l_pre 1 = lit_sign_c l_pre).
  { rewrite land_1_mod2. unfold lit_sign_c.
    destruct (Z.odd l_pre) eqn:Hodd.
    - apply Z.odd_spec in Hodd. destruct Hodd as [k ->].
      apply Zmod2_pack. lia.
    - assert (Heven : Z.even l_pre = true).
      { rewrite <- Z.negb_odd, Hodd. reflexivity. }
      apply Z.even_spec in Heven. destruct Heven as [k ->].
      replace (2 * k) with (2 * k + 0) by lia.
      apply Zmod2_pack. lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_order_select_entail_wit_2_1 : order_select_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hfp : fp64_eq (Z_to_fp64 z2) (Z_to_fp64 z2)).
  { apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  subst retval.
  sep_apply store_float_undef_store_float.
  Exists z2 v2_2 heap0 orderpos0.
  split_pure_spatial;
    [ cancel (CharArray.seg assigns_ptr 0 n assigns0); cancel
    | split_pures; dump_pre_spatial;
      first [ reflexivity | assumption | lia
            | (unfold order_select_loop_inv; split; [assumption | apply incl_refl]) ] .. ].
Qed.



Lemma proof_of_order_select_entail_wit_10_2 : order_select_entail_wit_10_2.
Proof.
  msat_order_select_cursor_open. msat_order_select_orp_right.
  msat_order_select_cursor_ranges s_pre cap sift_heap_now n size next x
    Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
Qed.



Lemma proof_of_order_select_entail_wit_13_1 : order_select_entail_wit_13_1.
Proof.
  msat_order_select_sift_promote H_Znth H_sift hp op false false
    H_Znth_2 H_Znth_3 H_Znth_4 H_Znth_5 H_Znth_6.
  sep_apply_r_atomic (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "order") heap hp cap
    (Zlength hp) (Zlength hp) (Zlength hp));
    [split_pures; dump_pre_spatial; first [vec_buf_solve | lia] .. | csimpl; cancel].
  repeat match goal with |- derivable1 ?L _ =>
    match L with
    | context [store_int ?a ?v] => cancel (store_int a v)
    | context [store_ptr ?a ?v] => cancel (store_ptr a v)
    | context [IntArray.seg ?a ?b ?c ?d] => cancel (IntArray.seg a b c d)
    end end.
Qed.



Lemma proof_of_order_select_entail_wit_13_2 : order_select_entail_wit_13_2.
Proof.
  msat_order_select_sift_promote H_Znth H_sift hp op true true
    H_Znth_2 H_Znth_3 H_Znth_4 H_Znth_5 H_Znth_6.
  sep_apply_r_atomic (Veci.rep_ptr_intro &( s_pre # "solver_t" ->ₛ "order") heap hp cap
    _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  csimpl. cancel.
  repeat match goal with |- derivable1 ?L _ =>
    match L with
    | context [store_int ?a ?v] => cancel (store_int a v)
    | context [store_ptr ?a ?v] => cancel (store_ptr a v)
    | context [IntArray.seg ?a ?b ?c ?d] => cancel (IntArray.seg a b c d)
    end end.
Qed.



Lemma proof_of_order_unassigned_return_wit_1 : order_unassigned_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_update_post (Zlength activity0) v_pre (heap0 +:: v_pre) (replace_Znth v_pre (Zlength heap0)
      orderpos0) heap1_2 orderpos1_2 ) as H_order_update_post.
  bind_fact ( Zlength activity0 = n ) as H_Zlength_act.
  rewrite H_Zlength_act in H_order_update_post.
  rewrite H_Zlength_act.
  bind_fact ( Znth (v_pre - 0) orderpos0 0 = -1 ) as H_Znth.
  bind_fact ( order_unassigned_pre n v_pre heap0 orderpos0 ) as H_order_unassigned_pre.
  assert (Hvpos : 0 <= v_pre < Zlength orderpos0).
  { pose proof (heap_wf_orderpos_length n
      {| mh_heap := heap0; mh_orderpos := orderpos0 |}
      (proj1 H_order_unassigned_pre)) as E.
    cbn [mh_orderpos] in E. lia. }
  assert (Hmissing : Znth v_pre orderpos0 (-1) = -1).
  { replace (v_pre - 0) with v_pre in H_Znth by lia.
    rewrite (Znth_indep orderpos0 v_pre (-1) 0) by exact Hvpos.
    exact H_Znth. }
  assert (Hpost : order_unassigned_post n v_pre heap0 orderpos0 heap1_2 orderpos1_2).
  { eapply order_unassigned_post_after_update__order_unassigned.
    - exact H_order_unassigned_pre.
    - exact Hmissing.
    - exact H_order_update_post. }
  Exists heap1_2 orderpos1_2.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_reducedb_entail_wit_4_split_goal_1 : solver_reducedb_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_open_state.
  bind_fact ( msolver_inv n F A_arr A_inst Mcur_2 ) as H_msolver_inv.
  apply MSatFloatFacts.fp32_nonnegative_eq_refl.
  exact (msi_cla_inc_nonnegative H_msolver_inv).
Qed.


Lemma proof_of_solver_reducedb_entail_wit_4 : solver_reducedb_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_reducedb_entail_wit_4_split_goal_1.
Qed.



Lemma proof_of_sort_which_implies_wit_1 : sort_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( learnt_sort_domain db_sort_spec origin_sort_spec ) as H_learnt_sort_domain.
  unfold learnt_sort_domain in H_learnt_sort_domain.
  destruct H_learnt_sort_domain as [Hlearnt Hperm].
  sep_apply
    (clause_db_rep_learnt_to_sort__sortrnd db_sort_spec Hlearnt).
  Intros activities.
  assert (Hsegment :
      learnt_sort_segment_domain db_sort_spec origin_sort_spec).
  { unfold learnt_sort_segment_domain.
    rewrite Forall_forall. intros p Hp.
    eapply Permutation_in; [exact Hperm|exact Hp]. }
  Exists activities.
  unfold learnt_sort_context.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_entail_wit_2 : sortrnd_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval < 0 ) as H_retval.
  bind_fact ( learnt_cmp_result srt_db srt_activities (Znth (i - 0) current_2 0) pivot retval ) as H_learnt_cmp_result.
  bind_fact ( sortrnd_left_scan_inv srt_db srt_activities srt_origin current_2 size_pre pivot (i - 1) j ) as
    H_sortrnd_left_scan_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  bind_fact ( 0 <= i ) as H_i.
  bind_fact ( i < size_pre ) as H_i_2.
  bind_fact ( 0 < j ) as H_j.
  bind_fact ( j <= size_pre ) as H_j_2.
  bind_fact ( fp64_eq seed_value_now_2 (Z_to_fp64 seed_shadow_now_2) ) as H_fp64_eq.
  rewrite ?Z.sub_0_r in *.
  unfold sortrnd_left_scan_inv in *.
  pose proof
    (sortrnd_left_scan_step__sortrnd
       _ _ _ _ _ _ _ _ _ H_sortrnd_left_scan_inv H_learnt_cmp_result H_retval H_Zlength
       H_i H_i_2 H_j H_j_2) as [Hb Hinv].
  rewrite H_Zlength in Hinv.
  replace (i + 1 - 1) with i by lia.
  assert (Hseedok : seed_ok seed_shadow_now_2) by (unfold seed_ok; lia).
  assert (Hrefl : fp64_eq (Z_to_fp64 seed_shadow_now_2)
                          (Z_to_fp64 seed_shadow_now_2)).
  { rewrite <- (fp64_eq_seed_exact__search _ _ Hseedok H_fp64_eq) at 1.
    exact H_fp64_eq. }
  cancel.
  Exists seed_shadow_now_2 seed_value_now_2 current_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_act_clause_rescale_partial_solve_wit_7_pure : act_clause_rescale_partial_solve_wit_7_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_entailer_with ltac:(apply Zlength_nonneg).
Qed.


Lemma proof_of_clause_cmp_return_wit_5 : clause_cmp_return_wit_5.
Proof.
  msat_clause_cmp_alias_stop y_pre x_pre x_activity db activities x_words
    learnt_cmp_result_stop_alias_header_first__clause_cmp.
Qed.


Lemma proof_of_clause_cmp_return_wit_7 : clause_cmp_return_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval <= 2 ) as H_retval.
  bind_fact ( retval = clause_hdr_word msat_true (Zlength x_words) ÷ 2 ) as H_retval_2.
  bind_fact ( 0 < x_pre ) as H_x_pre.
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2.
  bind_fact ( 0 < y_pre ) as H_y_pre.
  bind_fact ( y_pre % 2 = 0 ) as H_y_pre_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  bind_fact ( msat_fp32_nonnegative y_activity ) as H_msat_fp32_nonnegative_2.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength x_words)
    (Zlength_nonneg x_words)) as Hxlen0.
  unfold msat_true in H_retval_2.
  assert (Hxshort : Zlength x_words <= 2).
  { rewrite <- Hxlen0, <- H_retval_2. exact H_retval. }
  assert (Hxmod : x_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_x_pre_2. }
  assert (Hymod : y_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_y_pre_2. }
  unfold msat_true.
  pose proof (learnt_cmp_result_stop_two_xy_headers__clause_cmp
    db activities x_pre x_words x_activity
    y_pre y_words y_activity
    H_x_pre Hxmod H_msat_fp32_nonnegative H_y_pre Hymod H_msat_fp32_nonnegative_2
    (or_introl Hxshort))
    as Hresult.
  sep_apply Hresult.
  cancel.
Qed.


Lemma proof_of_clause_new_which_implies_wit_8 : clause_new_which_implies_wit_8.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 unfold clause_new_transaction_rest_at_gen.
 cancel.
 cancel.
Qed.


Lemma proof_of_order_select_entail_wit_9 : order_select_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Intros.
  bind_fact ( Zlength (sublist 0 (retval - 1) heap_now) = retval - 1 ) as H_Zlength.
  bind_fact ( order_select_loop_inv n heap0 heap_now orderpos_now assigns0 trail0 qhead ) as H_order_select_loop_inv.
  prop_apply_p (DoubleArray.seg_Zlength activity_ptr 0 n activity0).
  Intros_p Hactivity_len.
  assert (Hn : 0 < n) by lia.
  assert (Hsift :
    order_select_sift_inv n (Znth 0 heap_now 0)
      (Znth (retval - 1) heap_now 0) 0 heap0 heap_now
      (sublist 0 (retval - 1) heap_now)
      (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now)
      assigns0 trail0 qhead).
  { eapply order_select_sift_inv_init__order_select.
    - exact H_order_select_loop_inv.
    - lia.
    - lia.
    - rewrite (Znth_indep heap_now 0 0 (-1)) by lia. reflexivity.
    - rewrite (Znth_indep heap_now (retval - 1) 0 (-1)) by lia.
      reflexivity. }
  destruct (Z_le_gt_dec (retval - 1) 1) as [Hsmall | Hmore].
  - assert (Hsize : retval - 1 = 1) by lia.
    assert (Hone : Znth 1 (sublist 0 (retval - 1) heap_now) 0 = 0).
    { apply Znth_zero_past_end__order_select. rewrite H_Zlength. lia. }
    assert (Htwo : Znth 2 (sublist 0 (retval - 1) heap_now) 0 = 0).
    { apply Znth_zero_past_end__order_select. rewrite H_Zlength. lia. }
    msat_order_select_orp_left.
    msat_order_select_orp_left.
    Exists seed_shadow_now seed_value_now heap_now
      (sublist 0 (retval - 1) heap_now)
      (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now).
    replace (0 - 0) with 0 by lia.
    replace (retval - 1 - 0) with (retval - 1) by lia.
    sep_apply (IntArray.full_to_seg orderpos_ptr n
      (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now)).
    split_pure_spatial.
    + msat_cancel_sound; cancel.
    + split_pures; dump_pre_spatial; solve [auto | lia].
  - destruct (Z_le_gt_dec (retval - 1) 2) as [Htwo_children | Hlarge].
    + assert (Hsize : retval - 1 = 2) by lia.
      assert (Hchild_range :
        0 <= Znth 1 (sublist 0 (retval - 1) heap_now) 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - rewrite H_Zlength. lia.
        - lia. }
      assert (Hpast : Znth 2 (sublist 0 (retval - 1) heap_now) 0 = 0).
      { apply Znth_zero_past_end__order_select. rewrite H_Zlength. lia. }
      msat_order_select_orp_left.
      msat_order_select_orp_right.
      Exists seed_shadow_now seed_value_now heap_now
        (sublist 0 (retval - 1) heap_now)
        (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now).
      replace (0 - 0) with 0 by lia.
      replace (1 - 0) with 1 by lia.
      replace (retval - 1 - 0) with (retval - 1) by lia.
      sep_apply (IntArray.full_to_seg orderpos_ptr n
        (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now)).
      sep_apply_l_atomic
        (DoubleArray.seg_split_to_missing_i activity_ptr 0
          (Znth 1 (sublist 0 (retval - 1) heap_now) 0) n activity0
          msat_fp64_zero).
      * dump_pre_spatial. exact Hchild_range.
      * unfold StoreDoubleAsElement.storeA, double_Znth.
        split_pure_spatial.
        -- msat_cancel_sound; cancel.
        -- split_pures; dump_pre_spatial; solve [auto | lia].
    + assert (Hchild1_range :
        0 <= Znth 1 (sublist 0 (retval - 1) heap_now) 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - rewrite H_Zlength. lia.
        - lia. }
      assert (Hchild2_range :
        0 <= Znth 2 (sublist 0 (retval - 1) heap_now) 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - rewrite H_Zlength. lia.
        - lia. }
      assert (Hchildren_neq :
        Znth 1 (sublist 0 (retval - 1) heap_now) 0 <>
        Znth 2 (sublist 0 (retval - 1) heap_now) 0).
      { eapply order_select_sift_inv_cells_neq__order_select.
        - exact Hsift.
        - rewrite H_Zlength. lia.
        - rewrite H_Zlength. lia.
        - lia.
        - lia.
        - lia. }
      msat_order_select_orp_right.
      Exists seed_shadow_now seed_value_now heap_now
        (sublist 0 (retval - 1) heap_now)
        (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now).
      replace (0 - 0) with 0 by lia.
      replace (1 - 0) with 1 by lia.
      replace (1 + 1 - 0) with 2 by lia.
      replace (retval - 1 - 0) with (retval - 1) by lia.
      replace
        (Znth 1 (sublist 0 (retval - 1) heap_now) 0 - 0)
        with (Znth 1 (sublist 0 (retval - 1) heap_now) 0) by lia.
      replace
        (Znth 2 (sublist 0 (retval - 1) heap_now) 0 - 0)
        with (Znth 2 (sublist 0 (retval - 1) heap_now) 0) by lia.
      sep_apply (IntArray.full_to_seg orderpos_ptr n
        (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now)).
      sep_apply
        (double_array_seg_split_to_missing2__order_select activity_ptr
          (Znth 1 (sublist 0 (retval - 1) heap_now) 0)
          (Znth 2 (sublist 0 (retval - 1) heap_now) 0)
          n activity0 Hchild1_range Hchild2_range Hchildren_neq).
      split_pure_spatial.
      * msat_cancel_sound; cancel.
      * split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_order_select_entail_wit_12_3 : order_select_entail_wit_12_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left. Right.
  msat_order_select_sift_capacity s_pre heap_2 cap_2.
Qed.



Lemma proof_of_order_select_return_wit_6 : order_select_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (Znth (0 - 0) heap_now 0 - 0) assigns0 0 = 0 ) as H_Znth.
  bind_fact ( order_select_loop_inv n heap0 heap_now orderpos_now assigns0 trail0 qhead ) as H_order_select_loop_inv.
  replace (0 - 0) with 0 in * by lia.
  replace (Znth 0 heap_now 0 - 0)
    with (Znth 0 heap_now 0) in * by lia.
  assert (Hzero : retval_2 - 1 = 0) by lia.
  rewrite Hzero in *.
  change (sublist 0 0 heap_now) with (@nil Z) in *.
  pose proof (order_select_singleton_post__order_select
    n heap0 heap_now orderpos_now assigns0 trail0 qhead
    H_order_select_loop_inv ltac:(lia) H_Znth) as Hpost.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now)).
  sep_apply (Veci.rep_ptr_rep &( s_pre # "solver_t" ->ₛ "order") heap (@nil Z)).
  Exists seed_shadow_now seed_value_now (@nil Z)
    (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now).
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_order_update_entail_wit_4_split_goal_1 : order_update_entail_wit_4_split_goal_1.
Abort.


Lemma proof_of_order_update_entail_wit_4_split_goal_2 : order_update_entail_wit_4_split_goal_2.
Abort.


Lemma proof_of_order_update_entail_wit_4 : order_update_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (store_int_range (&("v")) v_pre).
  Intros.
  prop_apply_p (store_int_range (&("x")) x).
  Intros.
  rewrite Znth_replace_Znth_Same by lia; entailer!.
  change Int.min_signed with (-2147483648) in H.
  change Int.max_signed with 2147483647 in H.
  lia.
Qed.



Lemma proof_of_solver_reducedb_partial_solve_wit_7_pure : solver_reducedb_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval = Zlength (db_words (ms_learnt M0)) ) as H_retval.
  bind_fact ( msolver_inv n F A_arr A_inst M0 ) as H_msolver_inv.
  split_pures; dump_pre_spatial; try solve [auto | lia].
  - rewrite H_retval.
    apply MSatFloatFacts.fp64_count_limit_of_div.
    + split; lia.
    + exact (msi_cla_inc_nonnegative H_msolver_inv).
  - apply MSatFloatFacts.fp64_count_limit_of_div.
    + split; lia.
    + exact (msi_cla_inc_nonnegative H_msolver_inv).
Qed.


Lemma proof_of_solver_reducedb_safety_wit_2 : solver_reducedb_safety_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_reducedb_which_implies_wit_2 : solver_reducedb_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Permutation (db_words (ms_learnt M0)) words_sorted ) as H_Permutation.
  bind_fact ( msat_fp64_count_limit (Zlength (db_words (ms_learnt M0))) extra_lim ) as H_msat_fp64_count_limit.
  set (db := ms_learnt M0).
  assert (Hsym : Permutation words_sorted (map fst db)).
  { unfold db, db_words. apply Permutation_sym. exact H_Permutation. }
  destruct (@Permutation_map_inv (Z * clause_obj) Z fst words_sorted db Hsym)
    as [db_sorted [Hwords Hdb]].
  pose proof msat_clause_db_rep_perm as Hdbrep_gen.
  specialize (Hdbrep_gen _ _ Hdb).
  assert (Hlen : Zlength (db_words db) = Zlength words_sorted).
  { unfold db, db_words. rewrite !Zlength_correct.
    exact (f_equal Z.of_nat (Permutation_length H_Permutation)). }
  assert (Hwordsperm : Permutation (db_words db) (db_words db_sorted)).
  { unfold db_words. apply Permutation_map. exact Hdb. }
  assert (Hcomp : db_compaction_inv
      (msolver_reorder_learnts M0 db_sorted) words_sorted 0 0).
  { unfold db_compaction_inv, msolver_reorder_learnts,
      msolver_propagation_overlay, msolver_propagation_update. cbn.
    assert (Hnonneg : 0 <= Zlength words_sorted) by apply Zlength_nonneg.
    repeat split; try lia; try exact Hnonneg.
    unfold db_words.
    replace (sublist 0 0 words_sorted) with (@nil Z) by reflexivity.
    cbn. rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length words_sorted))) with
      (length words_sorted) by lia.
    rewrite firstn_all. symmetry. exact Hwords.
  }
  assert (Hlimit : msat_fp64_count_limit (Zlength words_sorted) extra_lim).
  { unfold msat_fp64_count_limit in *. intro Hpositive.
    apply H_msat_fp64_count_limit. change (0 < Zlength (db_words db)).
    rewrite Hlen. exact Hpositive. }
  assert (Hbase_sorted : minisat_base_watch_completed M0 ->
      minisat_base_watch_completed (msolver_reorder_learnts M0 db_sorted)).
  { apply minisat_base_watch_completed_reorder_learnts__api_reentry.
    exact Hdb. }
  Exists (msolver_reorder_learnts M0 db_sorted) db_sorted.
  split_pure_spatial.
  - sep_apply Hdbrep_gen.
    cbn. cancel.
  - split_pures; dump_pre_spatial;
      solve [auto | int_auto | apply msolver_inv_reorder_learnts__reducedb; assumption].
Qed.



Lemma proof_of_solver_reducedb_which_implies_wit_5 : solver_reducedb_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst Mcur ) as H_msolver_inv.
  bind_fact ( msat_fp32_nonnegative activity_now ) as H_msat_fp32_nonnegative.
  bind_fact ( db_compaction_inv Mcur words i j ) as H_db_compaction_inv.
  unfold clause_db_pair_remainder.
  Split.
  - Intros co pre post.
    match goal with
    | Hdb : db_nil = _ ++ _ :: _ /\ _ |- _ => destruct Hdb as [Hbad _]
    end.
    unfold db_nil in Hbad.
    destruct pre; discriminate.
  - Intros co pre post.
    match goal with
    | Hdb : ms_learnt Mcur = _ ++ _ :: _ /\ _ |- _ =>
        destruct Hdb as [Hlearn [Hlits Hlearnt]]
    end.
    assert (Hcin : In (Znth (i - 0) words 0, co) (msolver_db Mcur)).
    { unfold msolver_db. rewrite Hlearn. apply in_or_app. right.
      apply in_or_app. right. left. reflexivity. }
    unfold db_nil. rewrite clause_db_rep_nil.
    sep_apply (msat_clause_fields_to_rep n (msolver_db Mcur)
      (Znth (i - 0) words 0) co lits_now activity_now
      (msi_db_wf H_msolver_inv) Hcin Hlits Hlearnt H_msat_fp32_nonnegative).
    rewrite Hlearn.
    split_pure_spatial.
    + sep_apply_r_atomic (clause_db_rep_app_intro pre ((Znth (i - 0) words 0, co) :: post)).
      rewrite clause_db_rep_cons. cbn [fst snd].
      cancel (MiniSatClause.rep (Znth (i - 0) words 0) (co_learnt co) (co_lits co)).
      cancel.
    + split_pures.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial.
        unfold db_compaction_inv in H_db_compaction_inv |- *.
        destruct H_db_compaction_inv as [Hj0 [Hji [Hil Hmap]]].
        rewrite Zlength_replace_Znth.
        replace (i - 0) with i by lia.
        split; [lia |]. split; [lia |]. split; [lia |].
        rewrite Hmap. apply msat_db_compaction_shift; lia.
      * dump_pre_spatial. rewrite Zlength_replace_Znth. assumption.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
Qed.
