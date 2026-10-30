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
Lemma proof_of_solver_reducedb_entail_wit_1 : solver_reducedb_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_open_state.
  try subst retval_3. try subst retval_2. try subst retval_4.
  assert (Hlen : Zlength (db_words (ms_learnt M0)) = Zlength words_sorted) by lia.
  rewrite ?Hlen.
  sep_apply (Vecp.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "learnts") p words_sorted cap _ _ _ eq_refl eq_refl eq_refl);
    [ | first [lia | vec_buf_solve] .. ].
  subst Msorted.
  Exists (msolver_reorder_learnts M0 db_sorted) words_sorted.
  unfold msolver_reorder_learnts in *; simpl in *.
  split_pure_spatial.
  - change (solver_db_mutation_frame_at s_pre _ levels_ptr)
      with (solver_db_mutation_frame_at s_pre M0 levels_ptr).
    cancel (solver_db_mutation_frame_at s_pre M0 levels_ptr).
    cancel.
  - split_pures.
    + dump_pre_spatial. tauto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.



Lemma proof_of_solver_reducedb_entail_wit_5_3 : solver_reducedb_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (nw := replace_Znth j (Znth (i - 0) words 0) words).
  assert (Hnl : Zlength nw = Zlength words) by (subst nw; rewrite Zlength_replace_Znth; lia).
  sep_apply_l_atomic (PtrArray.full_to_seg learnts (Zlength words) nw).
  rewrite <- Hnl.
  sep_apply (Vecp.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "learnts") learnts nw cap _ _ _ eq_refl eq_refl eq_refl ltac:(pose proof (Zlength_nonneg nw); lia) ltac:(lia) ltac:(vec_buf_solve)).
  subst nw.
  msat_reducedb_open_state;
  Exists (replace_Znth j (Znth (i - 0) words 0) words) Mcur;
  split_pure_spatial;
  [ cancel (clause_db_rep (ms_learnt Mcur)); cancel
  | split_pures; dump_pre_spatial;
    [ unfold db_compaction_step; repeat split; auto
    | repeat match goal with |- _ /\ _ => split end; solve [auto | lia] ] ].
Qed.



Lemma proof_of_solver_reducedb_safety_wit_1 : solver_reducedb_safety_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_reducedb_safety_wit_8 : solver_reducedb_safety_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_open_state.
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv.
  sep_apply Vecp.rep_ptr_bounds. Intros_p Hvec.
  unfold db_compaction_inv in H_db_compaction_inv.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.



Lemma proof_of_solver_reducedb_which_implies_wit_8 : solver_reducedb_which_implies_wit_8.
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



Lemma proof_of_sortrnd_entail_wit_8 : sortrnd_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists seed_shadow1 seed_value1 current_3.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_act_clause_rescale_partial_solve_wit_5_pure : act_clause_rescale_partial_solve_wit_5_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_entailer_with ltac:(apply Zlength_nonneg).
Qed.


Lemma proof_of_act_var_bump_partial_solve_wit_6_pure : act_var_bump_partial_solve_wit_6_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (v - 0) orderpos0 0 <> -1 ) as H_Znth.
  bind_fact ( order_heap_wf n heap0 orderpos0 ) as H_order_heap_wf.
  bind_fact ( Zlength activity1 = n ) as H_Zlength.
  unfold order_heap_wf in H_order_heap_wf.
  pose proof
    (heap_wf_orderpos_length n
       {| mh_heap := heap0; mh_orderpos := orderpos0 |} H_order_heap_wf) as Hoplen.
  cbn [mh_orderpos] in Hoplen.
  replace (v - 0) with v in H_Znth by lia.
  assert (Hne : Znth v orderpos0 (-1) <> -1).
  { assert (Hvpos : 0 <= v < Zlength orderpos0) by lia.
    rewrite (Znth_indep orderpos0 v (-1) 0 Hvpos).
    exact H_Znth. }
  assert (Hpre : order_update_pre n v heap0 orderpos0).
  { unfold order_update_pre, order_heap_wf.
    split; [exact H_order_heap_wf |].
    split; [lia | exact Hne]. }
  assert (Hpre_len : order_update_pre (Zlength activity1) v heap0 orderpos0).
  { rewrite H_Zlength. exact Hpre. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_learnt_which_implies_wit_1 : clause_learnt_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_clause_new_which_implies_wit_3 : clause_new_which_implies_wit_3.
Proof.
LLM_pre_process ltac:(lia).
  rewrite ?Z.sub_0_r in *.

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
  unfold wlists_rep at 1. Intros_p Hwlshape.
  assert (Hidx0' :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) < 2 * cn_n_clause_new_spec)
    by lia.
  assert (Hidx1' :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) < 2 * cn_n_clause_new_spec)
    by lia.
  sep_apply (VecpArray.full_split_to_missing2
    cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
    (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
    (2 * cn_n_clause_new_spec) (ms_wm cn_M_clause_new_spec) nil Hidx0' Hidx1' Hne).
  unfold VecpArray.vec_store.
  Exists (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wm cn_M_clause_new_spec) nil)
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wm cn_M_clause_new_spec) nil).
  unfold clause_new_transaction_rest_at_gen, clause_new_frame_at_gen.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  replace (2 * ms_size cn_M_clause_new_spec) with (2 * cn_n_clause_new_spec) by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_new_which_implies_wit_5 : clause_new_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MiniSatClause.undef, activity_undef, clause_hdr_addr, clause_act_addr, clause_lits_addr.
  Intros_p Hpre.
  destruct Hpre as [Hsize [Hpos Hmod]].
  split_pure_spatial.
  - cancel (IntArray.undef_seg &( c # "clause_t" ->ₛ "lits") 0 size).
    cancel.
  - split_pures; dump_pre_spatial.
    + lia.
    + rewrite Z.rem_mod_nonneg by lia. exact Hmod.
Qed.



Lemma proof_of_clause_simplify_entail_wit_1_split_goal_1 : clause_simplify_entail_wit_1_split_goal_1.
Abort.


Lemma proof_of_clause_simplify_entail_wit_1_split_goal_2 : clause_simplify_entail_wit_1_split_goal_2.
Abort.


Lemma proof_of_clause_simplify_entail_wit_1 : clause_simplify_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Zlength_nonneg clause_words) as Hlen.
  unfold clause_simplify_scan_inv.
  rewrite PreH8.
  entailer!.
  rewrite PreH4.
  cancel.
Qed.


Lemma proof_of_clause_simplify_entail_wit_3_2 : clause_simplify_entail_wit_3_2.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  repeat match goal with
  | |- _ |-- “ _ ” && _ =>
      apply _derivable1_andp_intros; [ try (dump_pre_spatial; assumption) | ]
  end.
  2: msat_cancel_sound.
  all: msat_clause_simplify_scan_step n i clause_words assigns0 is_learnt retval retval_2
    retval_3 current_lit current_value lits assigns_ptr ( 1 + (1 - 1) ) ( retval_2 = 0 ).
Qed.


Lemma proof_of_clause_simplify_partial_solve_wit_4_pure : clause_simplify_partial_solve_wit_4_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
    dump_pre_spatial;
    apply clause_hdr_word_nonneg;
    apply Zlength_nonneg.
Qed.


Lemma proof_of_order_select_entail_wit_12_2 : order_select_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left. Left. Right. cbn [poly_store poly_undef_store].
  msat_order_select_sift_capacity s_pre heap_2 cap_2.
Qed.



Lemma proof_of_order_select_return_wit_3 : order_select_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_order_select_sift_close s_pre heap cap orderpos_ptr activity_ptr.
Qed.



Lemma proof_of_order_select_safety_wit_33 : order_select_safety_wit_33.
Proof.
  msat_order_select_sift_child_bound size.
Qed.


Lemma proof_of_order_select_which_implies_wit_1 : order_select_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_select_pre n heap0 orderpos0 assigns0 trail0 qhead ) as H_order_select_pre.
  unfold order_select_pre in H_order_select_pre.
  assert (Hn : 0 <= n).
  { destruct H_order_select_pre as (_ & _ & _ & _ & Hlen & _).
    rewrite <- Hlen. apply Zlength_nonneg. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_order_unassigned_return_wit_2 : order_unassigned_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_order_unassigned_noop_return.
Qed.


Lemma proof_of_solver_dlevel_return_wit_1_split_goal_1 : solver_dlevel_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval = Zlength lim ) as H_retval.
  subst lim. unfold z_nil in H_retval.
  rewrite Zlength_nil in H_retval. lia.
Qed.


Lemma proof_of_solver_dlevel_return_wit_1 : solver_dlevel_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_dlevel_return_wit_1_split_goal_1.
Qed.



Lemma proof_of_solver_reducedb_partial_solve_wit_30_pure : solver_reducedb_partial_solve_wit_30_pure.
Proof.
  msat_reducedb_hdr_word_range_pure.
Qed.


Lemma proof_of_solver_reducedb_which_implies_wit_3 : solver_reducedb_which_implies_wit_3.
Proof.
  msat_reducedb_focus_head_clause.
Qed.


Lemma proof_of_sort_which_implies_wit_2 : sort_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (learnt_sort_rep_to_clause_db__sortrnd db_sort_spec activities).
  sep_apply store_double_undef_store_double.
  Exists current_2. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_sortrnd_partial_solve_wit_13_pure : sortrnd_partial_solve_wit_13_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold sortrnd_split in PreH1.
  destruct PreH1 as [_ [_ [_ [_ [Hll [_ [Hdl _]]]]]]].
  split_pures; dump_pre_spatial.
  all: first
    [ assumption
    | lia
    | apply msat_fp64_eq_finite_refl;
      apply MSatFloatFacts.Z_to_fp64_i32_finite; lia ].
Qed.




Lemma proof_of_clause_cmp_partial_solve_wit_4_pure : clause_cmp_partial_solve_wit_4_pure.
Proof.
  msat_clause_cmp_hdr_word_nonneg.
Qed.


Lemma proof_of_clause_is_lit_return_wit_1 : clause_is_lit_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.odd c_pre) eqn:Hodd.
  - Left.
    assert (Hland : Z.land c_pre 1 = 1).
    { rewrite land_1_mod2.
      apply Z.odd_spec in Hodd. destruct Hodd as [k ->].
      apply Zmod2_pack. lia. }
    unfold clause_is_lit_result, is_tag, msat_true, msat_false.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - Right.
    assert (Heven : Z.even c_pre = true).
    { rewrite <- Z.negb_odd, Hodd. reflexivity. }
    assert (Hland : Z.land c_pre 1 = 0).
    { rewrite land_1_mod2.
      apply Z.even_spec in Heven. destruct Heven as [k ->].
      replace (2 * k) with (2 * k + 0) by lia.
      apply Zmod2_pack. lia. }
    unfold clause_is_lit_result, is_tag, msat_true, msat_false.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_clause_new_return_wit_2 : clause_new_return_wit_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (Hnd : NoDup (map lit_var_c cn_words_clause_new_spec)).
 { match goal with H : clause_new_stage_ready_root _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hstage
    end.
    unfold clause_new_stage_ready_root in Hstage.
    assert (Hcert : clause_install_pending_cert cn_n_clause_new_spec cn_F_clause_new_spec
      (msolver_set_root cn_M_clause_new_spec cn_root_clause_new_spec)
      cn_words_clause_new_spec (solver_selected_is_learnt cn_sel_clause_new_spec)) by tauto.
    pose proof (clause_install_pending_cert_wf _ _ _ _ _ Hcert) as Hwf.
    tauto. }
 pose proof (first_two_neg_distinct_ge2__clause_new cn_words_clause_new_spec ltac:(lia) Hnd) as Hdistinct.
 repeat match goal with
 | H : ?v = Vecp.slot _ _ |- _ => is_var v; subst v
 | H : ?v = lit_neg_c _ |- _ => is_var v; subst v
 | H : ?v = tag_of_lit _ |- _ => is_var v; subst v
 end.
 rewrite ?Z.sub_0_r in *.
 unfold clause_new_pending_at_root; cbn zeta.
 unfold clause_watch_word.
 assert (Hchoice : (Z.ltb 2 (Zlength cn_words_clause_new_spec)) = false)
   by (apply Z.ltb_ge; lia).
 rewrite Hchoice.

 split_pure_spatial.
 - cancel (clause_new_transaction_rest_at_gen s_pre cn_wl_clause_new_spec
     (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
     cn_M_clause_new_spec lvl_clause_new_spec cn_sel_clause_new_spec).
   cancel (IntArray.seg begin_pre 0 (Zlength cn_words_clause_new_spec) cn_words_clause_new_spec).
   cancel (MiniSatClause.rep c (solver_selected_is_learnt cn_sel_clause_new_spec) cn_words_clause_new_spec).
   cancel (Vecp.rep (solver_selected_vec s_pre cn_sel_clause_new_spec)
     (db_words (solver_selected_db cn_sel_clause_new_spec cn_M_clause_new_spec))).
   cancel (clause_db_rep (solver_selected_db cn_sel_clause_new_spec cn_M_clause_new_spec)).
   cancel (&( s_pre # "solver_t" ->ₛ "size") # Int |-> cn_n_clause_new_spec).
   msat_entailer_with ltac:(lia || tauto).
 - dump_pre_spatial. tauto.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_27_pure : clause_remove_partial_solve_wit_27_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_26_pure : clause_remove_partial_solve_wit_26_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_clause_remove_partial_solve_wit_29_pure : clause_remove_partial_solve_wit_29_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_clause_simplify_entail_wit_3_1 : clause_simplify_entail_wit_3_1.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH23 as Hinv.
  unfold clause_simplify_scan_inv in Hinv.
  destruct Hinv as (Hi & Halen & Hlits & Hcells & Hprefix).
  assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; apply Zlength_nonneg).
  rewrite zdiv_equiv in PreH18 by lia.
  rewrite clause_hdr_word_div2 in PreH18 by apply Zlength_nonneg.
  subst retval_3 current_value current_lit.
  rewrite replace_Znth_Znth in PreH1 by lia.
  repeat lazymatch goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end.
  6: {
    rewrite replace_Znth_Znth by lia.
    change (CharArray.full assigns_ptr n assigns0) with (CharArray.seg assigns_ptr 0 n assigns0).
    cancel.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_seg lits 0 i (Zlength clause_words)
         (Znth i clause_words 0) clause_words).
    - dump_pre_spatial; lia.
    - rewrite Z.sub_0_r, replace_Znth_Znth by lia.
      cancel. }
  all: dump_pre_spatial.
  all: try assumption.
  unfold clause_simplify_scan_inv.
  repeat split; auto; try lia;
  intros j Hj;
  destruct (Z.lt_ge_cases j i) as [Hji | Hji];
  [ apply Hprefix; lia
  | assert (j = i) by lia; subst j;
    unfold packed_lit_satisfying_value, lit_sign_c in PreH12, PreH13 |- *;
    destruct (Z.odd (Znth i clause_words 0)); simpl in *; lia ].
Qed.


Lemma proof_of_clause_simplify_partial_solve_wit_5_pure : clause_simplify_partial_solve_wit_5_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH7 as Hinv.
  unfold clause_simplify_scan_inv in Hinv.
  destruct Hinv as (Hi & Halen & Hlits & Hcells & Hprefix).
  assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; apply Zlength_nonneg).
  rewrite zdiv_equiv in PreH2 by lia.
  rewrite clause_hdr_word_div2 in PreH2 by apply Zlength_nonneg.
  repeat lazymatch goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end.
  all: dump_pre_spatial.
  all: first [assumption | lia].
Qed.


Lemma proof_of_clause_simplify_partial_solve_wit_6_pure_split_goal_1 : clause_simplify_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_simplify_lit_range_pure.
Qed.


Lemma proof_of_clause_simplify_partial_solve_wit_6_pure : clause_simplify_partial_solve_wit_6_pure.
Proof.
aggressive_pre_process.
Goal_apply proof_of_clause_simplify_partial_solve_wit_6_pure_split_goal_1.
Qed.


Lemma proof_of_clause_simplify_partial_solve_wit_10_pure : clause_simplify_partial_solve_wit_10_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_clause_simplify_lit_range_pure.
Qed.


Lemma proof_of_lit_neg_return_wit_2_original_split_goal_1 : lit_neg_return_wit_2_original_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_lit_neg_return_wit_2_original : lit_neg_return_wit_2_original.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_lit_neg_return_wit_2_original_split_goal_1 l_pre PreH1 PreH2).
Qed.


Lemma proof_of_order_select_entail_wit_12_4 : order_select_entail_wit_12_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right. cbn [poly_store poly_undef_store].
  msat_order_select_sift_capacity s_pre heap_3 cap_3.
Qed.



Lemma proof_of_selectionsort_entail_wit_2_split_goal_1 : selectionsort_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold selectionsort_outer_inv, selectionsort_inner_inv in *.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_selectionsort_entail_wit_2 : selectionsort_entail_wit_2.
Proof.
aggressive_pre_process.
Goal_apply proof_of_selectionsort_entail_wit_2_split_goal_1.
Qed.


Lemma proof_of_selectionsort_return_wit_1_split_goal_1 : selectionsort_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold selectionsort_outer_inv in *.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_selectionsort_return_wit_1 : selectionsort_return_wit_1.
Proof.
aggressive_pre_process.
Goal_apply proof_of_selectionsort_return_wit_1_split_goal_1.
Qed.


Lemma proof_of_solver_reducedb_entail_wit_5_1 : solver_reducedb_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_reducedb_open_state.
  LLM_pre_process ltac:(lia || nia || int_auto).
  msat_reducedb_remove_current n F A_arr A_inst Mcur words i j s_pre levels_ptr.
Qed.



Lemma proof_of_solver_reducedb_entail_wit_6_split_goal_1 : solver_reducedb_entail_wit_6_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state;
  bind_fact ( msolver_inv n F A_arr A_inst Mnext ) as H_msolver_inv;
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv;
    try (unfold db_compaction_inv in H_db_compaction_inv; lia).
Qed.


Lemma proof_of_solver_reducedb_entail_wit_6_split_goal_2 : solver_reducedb_entail_wit_6_split_goal_2.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state;
  bind_fact ( msolver_inv n F A_arr A_inst Mnext ) as H_msolver_inv;
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv;
    try (unfold db_compaction_inv in H_db_compaction_inv; lia).
Qed.


Lemma proof_of_solver_reducedb_entail_wit_6_split_goal_3 : solver_reducedb_entail_wit_6_split_goal_3.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state;
  bind_fact ( msolver_inv n F A_arr A_inst Mnext ) as H_msolver_inv;
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv;
    try (unfold db_compaction_inv in H_db_compaction_inv; lia).
Qed.


Lemma proof_of_solver_reducedb_entail_wit_6_split_goal_4 : solver_reducedb_entail_wit_6_split_goal_4.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state;
  bind_fact ( msolver_inv n F A_arr A_inst Mnext ) as H_msolver_inv.
  apply MSatFloatFacts.fp32_nonnegative_eq_refl.
  exact (msi_cla_inc_nonnegative H_msolver_inv).
Qed.


Lemma proof_of_solver_reducedb_entail_wit_6 : solver_reducedb_entail_wit_6.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_solver_reducedb_entail_wit_6_split_goal_1 M0 A_inst A_arr F n Mcur_2 words_2 Mnext words_next i extra_lim j PreH1 PreH2).
- Goal_apply (proof_of_solver_reducedb_entail_wit_6_split_goal_2 M0 A_inst A_arr F n Mcur_2 words_2 Mnext words_next i extra_lim j PreH1 PreH2).
- Goal_apply (proof_of_solver_reducedb_entail_wit_6_split_goal_3 M0 A_inst A_arr F n Mcur_2 words_2 Mnext words_next i extra_lim j PreH1 PreH2).
- Goal_apply (proof_of_solver_reducedb_entail_wit_6_split_goal_4 M0 A_inst A_arr F n Mcur_2 words_2 Mnext words_next i extra_lim j PreH1 PreH2).
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_48_pure : solver_reducedb_partial_solve_wit_48_pure.
Proof.
 msat_reducedb_state_pure.
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_50_pure : solver_reducedb_partial_solve_wit_50_pure.
Proof.
 msat_reducedb_state_pure.
Qed.


Lemma proof_of_solver_reducedb_partial_solve_wit_6_pure : solver_reducedb_partial_solve_wit_6_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.rep_ptr_bounds &((s_pre) # "solver_t" ->ₛ "learnts") p (db_words (ms_learnt M0))).
  Intros.
  LLM_pre_process ltac:(lia || int_auto).
Qed.




Lemma proof_of_act_clause_bump_which_implies_wit_1 : act_clause_bump_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( learnt_db db ) as H_learnt_db.
  bind_fact ( In c (db_words db) ) as H_In.
  sep_apply
    (learnt_clause_focus_by_word__act_var_bump db c H_learnt_db H_In).
  Intros clause_words activity_now.
  Exists clause_words activity_now.
  destruct H as (_ & _ & Hnonneg & Hpos & Hmod).
  split_pure_spatial.
  - cancel (clause_db_pair_remainder db_nil db c msat_true clause_words).
    cancel.
  - split_pures.
    + dump_pre_spatial. exact H_learnt_db.
    + dump_pre_spatial. exact H_In.
    + dump_pre_spatial. exact Hnonneg.
    + dump_pre_spatial. exact Hpos.
    + dump_pre_spatial. rewrite Z.rem_mod_nonneg by lia. exact Hmod.
Qed.


Lemma proof_of_act_clause_bump_which_implies_wit_2_split_goal_spatial : act_clause_bump_which_implies_wit_2_split_goal_spatial.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
  bind_fact ( c % 2 = 0 ) as H_c.
  unfold clause_db_pair_remainder at 1.
  Split.
  + Intros co pre post.
    destruct H as (Hdb & Hlits & Htag).
    unfold db_nil in Hdb. destruct pre; discriminate Hdb.
  + Intros co pre post.
    destruct H as (Hdb & Hlits & Htag).
    subst db. unfold msat_true in *; simpl in Htag.
    assert (Hmod : c mod 2 = 0) by
      (rewrite <- (Z.rem_mod_nonneg c 2) by lia; exact H_c).
    sep_apply_r_atomic (clause_db_rep_app_intro pre ((c, co) :: post)).
    rewrite clause_db_rep_cons.
    unfold MiniSatClause.rep, activity_state.
    cbn [fst snd]. rewrite Htag, Hlits.
    Exists a_v. unfold db_nil. simpl.
    split_pure_spatial.
    * cancel.
      cancel (clause_hdr_addr c # Int |-> clause_hdr_word true (Zlength clause_words)).
      cancel (clause_act_addr c (Zlength clause_words) # Float |-> a_v).
    * split_pures; dump_pre_spatial.
      -- repeat split; [apply Zlength_nonneg | exact PreH4 | exact Hmod].
      -- exact PreH6.
Qed.


Lemma proof_of_act_clause_bump_which_implies_wit_2_split_goal_1 : act_clause_bump_which_implies_wit_2_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
  bind_fact ( c % 2 = 0 ) as H_c.
  unfold clause_db_pair_remainder at 1.
  Split.
  + Intros co pre post.
    destruct H as (Hdb & Hlits & Htag).
    unfold db_nil in Hdb. destruct pre; discriminate Hdb.
  + Intros co pre post.
    destruct H as (Hdb & Hlits & Htag).
    subst db. dump_pre_spatial.
    unfold db_words. rewrite map_app. simpl.
    apply in_or_app. right. left. reflexivity.
Qed.


Lemma proof_of_act_clause_bump_which_implies_wit_2 : act_clause_bump_which_implies_wit_2.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_act_clause_bump_which_implies_wit_2_split_goal_spatial db clause_words a_v c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
- Goal_apply (proof_of_act_clause_bump_which_implies_wit_2_split_goal_1 db clause_words a_v c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
Qed.


Lemma proof_of_act_var_bump_return_wit_2_split_goal_1 : act_var_bump_return_wit_2_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
  auto using Permutation_refl.
Qed.


Lemma proof_of_act_var_bump_return_wit_2_split_goal_2 : act_var_bump_return_wit_2_split_goal_2.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
  auto using Permutation_refl.
Qed.


Lemma proof_of_act_var_bump_return_wit_2_split_goal_3 : act_var_bump_return_wit_2_split_goal_3.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
  auto using Permutation_refl.
Qed.


Lemma proof_of_act_var_bump_return_wit_2 : act_var_bump_return_wit_2.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_act_var_bump_return_wit_2_split_goal_1 orderpos0 heap0 n activity1_2 v PreH1 PreH2 PreH3 PreH4 PreH5).
- Goal_apply (proof_of_act_var_bump_return_wit_2_split_goal_2 orderpos0 heap0 n activity1_2 v PreH1 PreH2 PreH3 PreH4 PreH5).
- Goal_apply (proof_of_act_var_bump_return_wit_2_split_goal_3 orderpos0 heap0 n activity1_2 v PreH1 PreH2 PreH3 PreH4 PreH5).
Qed.


Lemma proof_of_clause_cmp_return_wit_2 : clause_cmp_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( fp32_lt retval_3 retval_4 ) as H_fp32_lt.
  bind_fact ( msat_fp32_same retval_4 y_activity ) as H_msat_fp32_same.
  bind_fact ( msat_fp32_same retval_3 x_activity ) as H_msat_fp32_same_2.
  bind_fact ( retval_2 = clause_hdr_word msat_true (Zlength y_words) ÷ 2 ) as H_retval_2.
  bind_fact ( retval > 2 ) as H_retval.
  bind_fact ( retval = clause_hdr_word msat_true (Zlength x_words) ÷ 2 ) as H_retval_3.
  bind_fact ( 0 < x_pre ) as H_x_pre.
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2.
  bind_fact ( 0 < y_pre ) as H_y_pre.
  bind_fact ( y_pre % 2 = 0 ) as H_y_pre_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  bind_fact ( msat_fp32_nonnegative y_activity ) as H_msat_fp32_nonnegative_2.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength x_words)
    (Zlength_nonneg x_words)) as Hxlen0.
  unfold msat_true in H_retval_2, H_retval_3.
  apply Z.gt_lt in H_retval.
  assert (Hxlen : 2 < Zlength x_words).
  { rewrite <- Hxlen0, <- H_retval_3. exact H_retval. }
  assert (Hxmod : x_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_x_pre_2. }
  assert (Hymod : y_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_y_pre_2. }
  unfold msat_fp32_same in H_msat_fp32_same, H_msat_fp32_same_2.
  subst retval_4 retval_3.
  unfold msat_true.
  sep_apply_r_atomic (learnt_cmp_result_lt_two_activity_first__clause_cmp
    db activities x_pre x_words x_activity
    y_pre y_words y_activity
    H_x_pre Hxmod H_msat_fp32_nonnegative H_y_pre Hymod H_msat_fp32_nonnegative_2
    Hxlen (or_intror H_fp32_lt)).
  (Intros; cancel).
Qed.


Lemma proof_of_clause_new_return_wit_1 : clause_new_return_wit_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (Hnd : NoDup (map lit_var_c cn_words_clause_new_spec)).
 { match goal with H : clause_new_stage_ready_root _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hstage
    end.
    unfold clause_new_stage_ready_root in Hstage.
    assert (Hcert : clause_install_pending_cert cn_n_clause_new_spec cn_F_clause_new_spec
      (msolver_set_root cn_M_clause_new_spec cn_root_clause_new_spec)
      cn_words_clause_new_spec (solver_selected_is_learnt cn_sel_clause_new_spec)) by tauto.
    pose proof (clause_install_pending_cert_wf _ _ _ _ _ Hcert) as Hwf.
    tauto. }
 pose proof (first_two_neg_distinct_ge2__clause_new cn_words_clause_new_spec ltac:(lia) Hnd) as Hdistinct.
 repeat match goal with
 | H : ?v = Vecp.slot _ _ |- _ => is_var v; subst v
 | H : ?v = lit_neg_c _ |- _ => is_var v; subst v
 | H : ?v = tag_of_lit _ |- _ => is_var v; subst v
 end.
 rewrite ?Z.sub_0_r in *.
 unfold clause_new_pending_at_root; cbn zeta.
 unfold clause_watch_word.
 assert (Hchoice : (Z.ltb 2 (Zlength cn_words_clause_new_spec)) = true)
   by (apply Z.ltb_lt; lia).
 rewrite Hchoice.
 split_pure_spatial.
 - cancel (clause_new_transaction_rest_at_gen s_pre cn_wl_clause_new_spec
     (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
     cn_M_clause_new_spec lvl_clause_new_spec cn_sel_clause_new_spec).
   cancel (IntArray.seg begin_pre 0 (Zlength cn_words_clause_new_spec) cn_words_clause_new_spec).
   cancel (MiniSatClause.rep c (solver_selected_is_learnt cn_sel_clause_new_spec) cn_words_clause_new_spec).
   cancel (Vecp.rep (solver_selected_vec s_pre cn_sel_clause_new_spec)
     (db_words (solver_selected_db cn_sel_clause_new_spec cn_M_clause_new_spec))).
   cancel (clause_db_rep (solver_selected_db cn_sel_clause_new_spec cn_M_clause_new_spec)).
   cancel (&( s_pre # "solver_t" ->ₛ "size") # Int |-> cn_n_clause_new_spec).
   cancel.
 - dump_pre_spatial. tauto.
Qed.



Lemma proof_of_order_select_entail_wit_7 : order_select_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_select_loop_inv n heap0 heap_now orderpos_now assigns0 trail0 qhead ) as H_order_select_loop_inv.
  pose proof
    (order_select_loop_inv_cell_range__order_select
       n heap0 heap_now orderpos_now assigns0 trail0 qhead
       (retval_2 - 1) H_order_select_loop_inv ltac:(lia)) as Hlast_range.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_order_select_entail_wit_11_1 : order_select_entail_wit_11_1.
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
    replace_Znth i (Znth child sift_heap_now_2 0) sift_heap_now_2).
  set (orderpos' := replace_Znth (Znth i heap' 0) i sift_orderpos_now_2).
  assert (Hmoved : Znth i heap' 0 = Znth child sift_heap_now_2 0).
  { subst heap'. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hsift :
    order_select_sift_inv n next x child heap0 sift_heap_before_2
      heap' orderpos' assigns0 trail0 qhead).
  { subst orderpos'. rewrite Hmoved.
    apply order_select_sift_inv_step__order_select.
    - exact H_order_select_sift_inv.
    - lia.
    - lia. }
  assert (Hheaplen : Zlength heap' = Zlength sift_heap_now_2) by apply Zlength_replace_Znth.
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
  msat_sift_next_reads child n size heap' orderpos'
    Hsz Hsz2 Hsift sift_seed_shadow_now_2 sift_seed_value_now_2
    sift_heap_before_2 activity_ptr activity0.
Qed.



Lemma proof_of_order_select_return_wit_4 : order_select_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_order_select_sift_close s_pre heap cap orderpos_ptr activity_ptr.
Qed.



Lemma proof_of_order_select_return_wit_7 : order_select_return_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (retval - 0) assigns0 0 = 0 ) as H_Znth.
  bind_fact ( 0 <= retval ) as H_retval.
  bind_fact ( retval < n ) as H_retval_2.
  bind_fact ( order_select_pre n heap0 orderpos0 assigns0 trail0 qhead ) as H_order_select_pre.
  replace (retval - 0) with retval in * by lia.
  pose proof (order_select_noop_post__order_select
    n retval heap0 orderpos0 assigns0 trail0 qhead
    H_order_select_pre (conj H_retval H_retval_2) H_Znth) as Hpost.
  Exists z2 v2_2 heap0 orderpos0.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.



Lemma proof_of_order_update_return_wit_2 : order_update_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre.
  bind_fact ( order_update_loop_inv n v_pre heap0 x i heap_now orderpos_now ) as H_order_update_loop_inv.
  bind_fact ( 0 <= x ) as H_x.
  bind_fact ( x < n ) as H_x_2.
  bind_fact ( 0 <= Znth (parent - 0) heap_now 0 ) as H_Znth.
  bind_fact ( Znth (parent - 0) heap_now 0 < n ) as H_Znth_2.
  bind_fact ( x <> Znth (parent - 0) heap_now 0 ) as H_x_3.
  replace (x - 0) with x in * by lia.
  replace (parent - 0) with parent in * by lia.
  replace (Znth parent heap_now 0 - 0)
    with (Znth parent heap_now 0) in * by lia.
  pose proof (order_update_close_post__order_update
    n v_pre heap0 orderpos0 x i heap_now orderpos_now H_order_update_pre H_order_update_loop_inv) as Hpost.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth x i orderpos_now)).
  sep_apply_l_atomic (IntArray.full_to_seg heap
    (Zlength heap_now) (replace_Znth i x heap_now)).
  sep_apply_l_atomic (double_array_missing2_refold
    activity_ptr x (Znth parent heap_now 0) n activity0
    (conj H_x H_x_2) (conj H_Znth H_Znth_2) H_x_3).
  Exists (replace_Znth i x heap_now) (replace_Znth x i orderpos_now).
  replace (Zlength heap_now) with (Zlength (replace_Znth i x heap_now))
    by apply Zlength_replace_Znth.
  sep_apply (Veci.rep_intro &(s_pre # "solver_t" ->ₛ "order") heap (replace_Znth i x heap_now) cap _ _ _ eq_refl eq_refl eq_refl); [| rewrite ?Zlength_replace_Znth; first [lia | vec_buf_solve] ..].
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_selectionsort_entail_wit_1_split_goal_1 : selectionsort_entail_wit_1_split_goal_1.
Proof.
Abort.


Lemma proof_of_selectionsort_entail_wit_1 : selectionsort_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold selectionsort_outer_inv in *.
  Exists origin.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_selectionsort_entail_wit_4 : selectionsort_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (store_int_undef_store_int &( "best_i")).
  sep_apply (store_int_undef_store_int &( "j")).
  sep_apply (store_ptr_undef_store_ptr &( "tmp")).
  bind_fact ( selectionsort_inner_inv db activities origin current_2 size_pre i j best_i ) as H_selectionsort_inner_inv.
  unfold selectionsort_inner_inv in H_selectionsort_inner_inv.
  destruct H_selectionsort_inner_inv as
    (Hcontext & Hdomain & Hperm & Hlen & Hi & Hbest & Hj).
  replace (i - 0) with i by lia.
  replace (best_i - 0) with best_i by lia.
  set (swapped :=
    replace_Znth best_i (Znth i current_2 0)
      (replace_Znth i (Znth best_i current_2 0) current_2)).
  assert (Hswap : Permutation current_2 swapped).
  { subst swapped.
    apply selectionsort_swap_perm__solve; lia. }
  assert (Horigin : Permutation origin swapped).
  { eapply Permutation_trans; eauto. }
  assert (Hswapped_len : Zlength swapped = size_pre).
  { subst swapped. rewrite !Zlength_replace_Znth. exact Hlen. }
  Exists swapped.
  unfold selectionsort_outer_inv.
  unfold PtrArray.full, PtrArray.seg, store_array.
  msat_manual_entailer_with ltac:(lia).
Qed.
