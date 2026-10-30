From SimpleC.Verification Require Import VCPrelude.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.


Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_proof_common.

Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_state_search_goal.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_proof_automation.
Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_state_search_proof_manual_part4.

Lemma proof_of_solver_search_which_implies_wit_39_split_goal_spatial : solver_search_which_implies_wit_39_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( model_copy_finish n F A_arr A_inst Mselected model_words Mdone ) as H_model_copy_finish.
  unfold model_copy_finish in H_model_copy_finish.
  destruct H_model_copy_finish as (_ & Hinv & Hqtail & _ & _ & _).
  assert (Hshape : solver_shape Mdone).
  { exact (msi_shape Hinv). }
  pose proof (msi_size Hinv) as Hsize.
  assert (Htrail : mtrail_wf (ms_size Mdone) (ms_core Mdone)).
  { rewrite <- Hsize. exact (msi_trail_wf Hinv). }
  assert (Hheap : heap_wf (ms_size Mdone) (msolver_heap Mdone)).
  { rewrite <- Hsize. exact (msi_heap_wf Hinv). }
  assert (Hrange :
      0 <= ms_root_level Mdone <= Zlength (mt_lim (ms_core Mdone))).
  { exact (msi_root_range Hinv). }
  assert (Htrail_len :
      Zlength (mt_trail (ms_core Mdone)) = ms_qtail Mdone).
  { unfold solver_shape in Hshape. tauto. }
  assert (Hcancel : cancel_bound_ready Mdone (ms_root_level Mdone)).
  { unfold cancel_bound_ready.
    destruct (Z_lt_le_dec (ms_root_level Mdone)
      (Zlength (mt_lim (ms_core Mdone)))) as [Hlt | Hge].
    - right.
      pose proof (lim_lt_trail (ms_size Mdone) (ms_core Mdone)
        (ms_root_level Mdone) Htrail (conj (proj1 Hrange) Hlt)) as Hlim.
      rewrite Htrail_len in Hlim. rewrite <- Hqtail in Hlim. lia.
    - left. exact Hge. }
  unfold solver_search_root_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_cancel_pre, solver_cancel_owned,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep,
    solver_scalars_without_root_rep,
    solver_vecs_rep, solver_vecs_without_lim_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_manual_entailer_with ltac:(first [assumption | lia]).
Qed.


Lemma proof_of_solver_search_which_implies_wit_39 : solver_search_which_implies_wit_39.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_search_which_implies_wit_39_split_goal_spatial A_inst A_arr F n search_wl Mselected Mdone model_words s levels PreH1 PreH2 PreH3).
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_4_pure : solver_setnvars_partial_solve_wit_4_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_simplify_return_wit_2_split_goal_spatial : solver_simplify_return_wit_2_split_goal_spatial.
Abort.


Lemma proof_of_solver_simplify_return_wit_2 : solver_simplify_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  entailer!.
  msat_simplify_propagation_frame M_solver_simplify_spec Mprop s_pre
    assigns_prop levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec.
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_4 : solver_simplify_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec M_solver_simplify_spec ) as H_msolver_inv.
  bind_fact ( ms_capacity_root_propagation_pending M_solver_simplify_spec = 0 ) as H_ms_capacity_root_propagation_pending.
  assert (Hprop : solver_propagation_inv smp_n_solver_simplify_spec
    smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    (PropagationAssuming smp_A_arr_solver_simplify_spec)
    M_solver_simplify_spec).
  { unfold solver_propagation_inv. simpl.
    split.
    - exact H_ms_capacity_root_propagation_pending.
    - constructor.
      + exact (msas_weak H_msolver_inv).
      + exact (msas_prop_level H_msolver_inv).
      + exact (msas_watch_frontier H_msolver_inv).
      + left. exact (msas_heap_covers H_msolver_inv).
      + exact (msas_reasonless_current H_msolver_inv). }

  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_solve_entail_wit_8_2_split_goal_spatial : solver_solve_entail_wit_8_2_split_goal_spatial.
Abort.


Lemma proof_of_solver_solve_entail_wit_8_2 : solver_solve_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact (assumption_root_install n F A_arr Mcur Mroot A_inst)
    as H_assumption_root_install.
  bind_fact (endvar_pre = begin_pre + Zlength raw * sizeof (INT))
    as H_endvar_pre.
  bind_fact (A_arr = assumption_prefix raw (Zlength raw)) as H_A_arr.
  bind_fact (Forall (lit_wf_c n) raw) as H_Forall.
  bind_fact (raw <> nil) as H_raw.
  assert (HA : A_arr = lits_denote raw).
  { rewrite H_A_arr.
    unfold assumption_prefix.
    rewrite sublist_self by reflexivity.
    reflexivity. }
  unfold assumption_root_install in H_assumption_root_install.
  destruct H_assumption_root_install as
    [HAinst [HMroot [Hinv [Hatroot [Hpending Hshadow]]]]].
  assert (Hrestart_frame :
      ms_cap Mroot = ms_cap M_solver_solve_spec /\
      (solver_query_reuse_guard M_solver_solve_spec ->
       minisat_base_watch_completed Mroot)).
  { split; assumption. }
  assert (Harray_facts :
      endvar_pre = begin_pre + Zlength raw * sizeof ( INT ) /\
      A_arr = lits_denote raw /\ Forall (lit_wf_c n) raw /\
      (raw = nil -> valid_int_position begin_pre)).
  { split; [exact H_endvar_pre|].
    split; [exact HA|].
    split; [exact H_Forall|].
    intros Hnil; exfalso; apply H_raw; exact Hnil. }
  unfold solver_restart_loop, assumptions_array.
  Exists raw.
  cancel.
  Exists Mroot A_inst.
  Right.
  unfold solver_search_pre.
  rewrite H_endvar_pre.
  entailer!.
Qed.


Lemma proof_of_solver_solve_partial_solve_wit_10_pure : solver_solve_partial_solve_wit_10_pure.
Proof.
  msat_solve_close_assumption_lit_bounds k.
Qed.


Lemma proof_of_solver_solve_partial_solve_wit_27_pure : solver_solve_partial_solve_wit_27_pure.
Proof.
  msat_solve_assume_fresh_pure.
Qed.


Lemma proof_of_enqueue_return_wit_3 : enqueue_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_enqueue_assign_keep_close (-1) retval_2 l_pre l0 assigns qtail levels0 reasons0 trail rsn trl asg n.
Qed.


Lemma proof_of_enqueue_return_wit_4 : enqueue_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_enqueue_assign_keep_close (-1) retval_2 l_pre l0 assigns qtail levels0 reasons0 trail rsn trl asg n.
Qed.


Lemma proof_of_enqueue_return_wit_2 : enqueue_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_enqueue_assign_bump_close 1 retval_2 l_pre retval_3 l0 assigns
    qtail levels0 reasons0 trail rsn trl asg lvl n lim reason_pre.
Qed.


Lemma proof_of_solver_addclause_entail_wit_1 : solver_addclause_entail_wit_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign.
Exists (sublist 1 (Zlength ac_input_addclause_spec) ac_input_addclause_spec)
       (Znth 0 ac_input_addclause_spec 0 :: nil)
       (Zlength (Znth 0 ac_input_addclause_spec 0 :: nil)).
assert (Hlen1 : 1 <= Zlength ac_input_addclause_spec) by ac_arith.
assert (Hinit := addclause_sort_outer_init ac_n_addclause_spec
                   ac_input_addclause_spec Hlen1 ltac:(assumption)).
rewrite Z.sub_0_r.
(* the read of *begin emits its cell at the BARE address, which
   missing_i_merge_to_seg cannot unify with its own [storeA x 0 _];
   [int_head_merge] bridges the two. *)
sep_apply (int_head_merge begin_pre (Zlength ac_input_addclause_spec)
             ac_input_addclause_spec ltac:(lia) ltac:(lia)).
simpl app.
rewrite hd_sublist_app by exact Hlen1.
subst endvar_pre.
msat_manual_entailer_with ltac:(ac_close).
Qed.


Lemma proof_of_solver_addclause_entail_wit_4_1 : solver_addclause_entail_wit_4_1.
Proof.
  (* The pointer guard forces p = 0, so insertion is at the front. Preserve
   folded sort invariants as pairs with I: ac_shape would destruct a plain
   copy before the insertion lemma could consume it. *)
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  match goal with H : addclause_sort_inner_inv _ _ _ _ |- _ =>
    pose proof (conj I H) as Hin end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout]; destruct Hin as [_ Hin].
  assert (Hp0 : p = 0) by (rewrite ?sizeof_int in *; lia).
  subst p.
  assert (Hpre : pre = nil) by (apply Zlength_nil_inv; lia).
  subst pre. subst arr.
  Exists rest2 (l :: suf) (Zlength (l :: suf)).
  try (rewrite replace_Znth_twice).
  (* must fire BEFORE any [simpl app], which would normalise the `nil ++' away *)
  rewrite (replace_Znth_hole (@nil Z) junk (suf ++ rest2) l).
  simpl app.
  sep_apply IntArray.full_to_seg.
  sep_apply (store_ptr_undef_store_ptr &( "j")).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try solve [auto | ac_close].
    + (* [Zlength (nil ++ suf)] never reduces on its own; normalise the appends
         away first, or lia sees an opaque atom. *)
      simpl app in *; rewrite ?Zlength_cons, ?Zlength_app in *; ac_zlen; lia.
    + exact (addclause_sort_insert_outer _ _ _ nil suf rest2 l Hout Hin
               (Forall_nil _) ltac:(assumption)).
Qed.


Lemma proof_of_solver_addclause_entail_wit_7_1 : solver_addclause_entail_wit_7_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_keep sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 last Mnew endvar_pre.
Qed.


Lemma proof_of_solver_record_entail_wit_2 : solver_record_entail_wit_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
copy_fact ( record_allocated rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage ) as H_record_allocated.
  replace (0 - 0) with 0 by lia.
  unfold record_allocated in H_record_allocated.
  destruct H_record_allocated as [_ [Hcert _]].
  unfold record_clause_cert, record_ready_cert in Hcert.
  destruct Hcert as (_ & _ & _ & _ & Hfresh & _).
  unfold enqueue_post_at at 1.
  Intros qtail' assigns' levels' reasons' trail'.
  rename H into Htrans.
  assert (Hret : retval = 1).
  { unfold enqueue_transition in Htrans.
    destruct Htrans as
      [(Hassigned & Hret & _)|[(Hnonzero & _)|(Hzero & Hret & _)]];
      try exact Hret; congruence. }
  subst retval.
  unfold enqueue_post_at.
  Exists qtail' assigns' levels' reasons' trail'.
  split_pure_spatial.
  + msat_manual_entailer_with ltac:(lia).
  + split_pures; dump_pre_spatial; first [assumption | exact Htrans | lia].
Qed.



Lemma proof_of_solver_record_which_implies_wit_2 : solver_record_which_implies_wit_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
pose proof (record_allocated_enqueue_input__record _ _ _ _ _ _ _ _ PreH1) as Hinput.
 sep_apply record_rep_enqueue_focus. Intros assigns_ptr. Exists assigns_ptr.
 msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_search_entail_wit_3_2_split_goal_1 : solver_search_entail_wit_3_2_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_search_close_conflict_count_nonneg.
Qed.


Lemma proof_of_solver_search_entail_wit_3_2 : solver_search_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_solver_search_entail_wit_3_2_split_goal_1 M0 A_inst A_arr F n conflict_count_value Mcur learnt_words retval propagation_result result_focus result_clause Mconf p focus Cconf retval_2 Manalyze Manalyzed words backjump p_2 retval_3 retval_4 cap retval_5 Mback Mrecord cla_inc1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77 PreH78 PreH79 PreH80 PreH81 PreH82 PreH83 PreH84 PreH85 PreH86 PreH87 PreH88 PreH89 PreH90 PreH91 PreH92 PreH93 PreH94).
Qed.



Lemma proof_of_solver_search_entail_wit_4_4 : solver_search_entail_wit_4_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold solver_simplify_post_at, solver_simplify_post_sat_at,
    solver_simplify_post_unsat_at. Split.
- Intros Mclean. Exists Mclean.
  match goal with
  | H : ms_cap Mclean = ms_cap Mstable /\ _ |- _ =>
    destruct H as [Hcap [Hroot [Hstrong [Hreuse [Hdepth [Hdrain [Hpending [Hseed [Hmodel Hdecay]]]]]]]]]
  end.
  assert (Hinv : msolver_inv n F A_arr nil Mclean).
  { apply solver_assuming_zero_stable__api_reentry; [exact Hstrong|exact Hdepth|lia]. }
  assert (Hreuse_new : solver_search_reuse M0 Mclean).
  { intro Hbase. eapply minisat_full_completion_implies_base__api_reentry.
    - exact (msi_trail_wf Hinv).
    - exact (msi_db_wf Hinv).
    - apply Hreuse. left. eapply minisat_base_completion_at_depth_zero__api_reentry.
      + exact (msi_trail_wf PreH11).
      + exact (msi_db_wf PreH11).
      + lia.
      + apply PreH10. exact Hbase. }
  subst A_inst. sep_apply (store_ptr_undef_store_ptr &( "confl")).
  msat_manual_entailer_with ltac:(lia || tauto).
- Intros Mclean. exfalso. lia.
Qed.


Lemma proof_of_solver_search_entail_wit_4_5 : solver_search_entail_wit_4_5.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Exists Mstable.
unfold solver_search_root_frame_at, solver_search_bundle_at, solver_search_payload, solver_rep_levels_wl_at.
unfold solver_payload_cells, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
  solver_scalars_rep, solver_scalars_without_root_rep, clause_new_scalars_frame,
  solver_vecs_rep, solver_vecs_without_lim_rep.
Intros act asg opos rsn trl tgs.
Exists act asg opos rsn trl tgs.
sep_apply (store_ptr_undef_store_ptr &( "confl")).
msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_partial_solve_wit_26_pure : solver_search_partial_solve_wit_26_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact (Forall (lit_wf_c n) words) as Hwords.
bind_fact (solver_propagation_inv n F A_arr (PropagationStable A_inst) Mcur) as Hprop.
pose proof (msp_weak n F A_arr A_inst Mcur (proj2 Hprop)) as Hweak.
pose proof (msw_size Hweak) as Hsize. pose proof (msw_shape Hweak) as Hshape.
unfold solver_shape in Hshape. destruct Hshape as [Hsize0 [Hcap [Hbound Hrest]]].
assert (Hidx : 0 <= 1 < Zlength words) by lia.
pose proof (Forall_Znth_elim Z (lit_wf_c n) words 0 1 Hwords Hidx) as Hlit.
unfold lit_wf_c in Hlit. replace (1-0) with 1 in * by lia.
msat_manual_entailer_with ltac:(assumption || lia).
Qed.


Lemma proof_of_solver_search_partial_solve_wit_51_pure : solver_search_partial_solve_wit_51_pure.
Proof.
  msat_search_cla_inc_nonneg H_msolver_inv n F A_arr A_inst Mrecord.
Qed.


Lemma proof_of_solver_search_partial_solve_wit_102_pure : solver_search_partial_solve_wit_102_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact (solver_search_selection_state n F A_arr A_inst retval Mselected) as Hselected.
unfold solver_search_selection_state in Hselected.
destruct Hselected as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbound & Hrange & _).
msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_40 : solver_search_which_implies_wit_40.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( model_copy_finish n F A_arr A_inst Mselected model_words Mdone ) as H_model_copy_finish.
  unfold model_copy_finish in H_model_copy_finish.
  destruct H_model_copy_finish as (_ & Hinv & Hqtail & Horder & Hpending & Hseed & Hsaved).
  unfold solver_cancel_post.
  Split.
  - Intros.
    Exists Mdone.
    split_pure_spatial.
    + sep_apply (solver_cancel_join_rep_levels_at s Mdone levels search_wl).
      cancel.
    + pose proof (msw_root_range (msi_weak Hinv)) as Hr.
      assert (Hroot : solver_at_root Mdone).
      { unfold solver_at_root. lia. }
      (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
  - Intros orderpos order.
    destruct H as (Hlevel & Hheap & Hincl & Hre).
    set (Mrestart := msolver_cancel_project Mdone
      (ms_root_level Mdone) orderpos order
      (ms_root_level Mdone)).
    assert (Hweak : msolver_inv_weak n F A_arr A_inst Mrestart).
    { unfold Mrestart. apply msolver_inv_weak_cancel__search
        with (M := Mdone) (level := ms_root_level Mdone)
             (orderpos := orderpos) (order := order).
      - exact (msi_weak Hinv).
      - exact Hlevel.
      - reflexivity.
      - exact Hheap.
      - exact Hincl.
      - exact Hre. }
    assert (Hseed_restart : msolver_seed_shadow Mrestart) by exact Hseed.
    Exists Mrestart.
    split_pure_spatial.
    + unfold Mrestart.
      sep_apply (solver_cancel_project_join_rep_levels_at s Mdone levels
        (ms_root_level Mdone) orderpos order (ms_root_level Mdone) search_wl).
      cancel.
    + pose proof (msi_trail_wf Hinv) as Htrail.
      assert (Hbound : Znth (ms_root_level Mdone)
          (mt_lim (ms_core Mdone)) 0 <= mt_qhead (ms_core Mdone)).
      { apply Forall_Znth_elim; [exact (msi_prop_level Hinv)|lia]. }
      lazymatch goal with
      | Hreuse : solver_search_reuse ?entry Mdone |- _ =>
          assert (Hreuse_restart : solver_search_reuse entry Mrestart)
            by (intro Hbase; unfold Mrestart;
                exact (minisat_base_completion_cancel__api_reentry
                  n Mdone (ms_root_level Mdone) orderpos order
                  (ms_root_level Mdone) Htrail (msw_db_wf (msi_weak Hinv))
                  Hlevel Hbound (Hreuse Hbase)))
      end.
      assert (Hprop : prop_level (ms_core Mrestart)).
      { unfold Mrestart. apply (prop_level_cancel n (ms_core Mdone)
          (ms_root_level Mdone)).
        - exact Htrail.
        - exact Hlevel. }
      assert (Hwatch : minisat_watch_frontier n (msolver_db Mrestart)
          (mt_assigns (ms_core Mrestart)) (mt_trail (ms_core Mrestart))
          (mt_qhead (ms_core Mrestart))).
      { unfold Mrestart. apply minisat_watch_frontier_cancel__search
          with (M := Mdone) (level := ms_root_level Mdone)
               (orderpos := orderpos) (order := order)
               (root := ms_root_level Mdone).
        - exact Htrail.
        - exact Hlevel.
        - exact Hbound.
        - exact (msi_watch_frontier Hinv). }
      assert (Hheap_n : heap_wf n (heap_of_lists order orderpos)).
      { rewrite (msi_size Hinv). exact Hheap. }
      assert (Hheapcov : heap_covers n (msolver_heap Mrestart)
          (mt_assigns (ms_core Mrestart)) (mt_trail (ms_core Mrestart))
          (mt_qhead (ms_core Mrestart))).
      { unfold Mrestart. apply heap_covers_cancel_project__canceluntil_cap
          with (M := Mdone) (level := ms_root_level Mdone)
               (orderpos := orderpos) (order := order).
        - exact Htrail.
        - exact Hlevel.
        - exact Hbound.
        - exact (msi_heap_wf Hinv).
        - exact Hheap_n.
        - exact Hincl.
        - exact (msi_heap_covers Hinv).
        - exact Hre. }
      assert (Hreasonless : current_reasonless_earliest n Mrestart).
      { unfold current_reasonless_earliest.
        intros d Hd v Hlev Hword.
        unfold Mrestart, msolver_cancel_project, msolver_core_heap_update in Hd.
        simpl in Hd. rewrite Zlength_ztake in Hd by lia. lia. }
      assert (Hinv_restart : msolver_inv n F A_arr A_inst Mrestart).
      { refine {| msi_weak := Hweak; msi_prop_level := Hprop;
                 msi_watch_frontier := Hwatch; msi_heap_covers := Hheapcov;
                 msi_reasonless_current := Hreasonless |}. }
      assert (HrootM : solver_at_root Mrestart).
      { unfold solver_at_root, Mrestart, msolver_cancel_project,
          msolver_core_heap_update. simpl. rewrite Zlength_ztake by lia.
        lia. }
      assert (Hqtail_restart : mt_qhead (ms_core Mrestart) = ms_qtail Mrestart).
      { unfold Mrestart, msolver_cancel_project, msolver_core_heap_update.
        reflexivity. }
      assert (Hsaved_restart : model_saved n F A_arr Mrestart).
      { unfold model_saved in *.
        unfold Mrestart, msolver_cancel_project, msolver_core_heap_update.
        simpl. exact Hsaved. }
      msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_setnvars_entail_wit_1 : solver_setnvars_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (proj1 PreH3) as Hsize.
  change (n_pre <= Z.max (ms_cap sn_M_setnvars_spec) 536870911) in PreH5.
  destruct (Z_le_gt_dec (ms_cap sn_M_setnvars_spec) 536870911) as [Hcap | Hcap].
  - rewrite Z.max_r in PreH5 by lia.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; solve [auto | lia].
  - rewrite Z.max_l in PreH5 by lia.
    cancel; lia.
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_16_pure : solver_setnvars_partial_solve_wit_16_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_simplify_partial_solve_wit_25_pure : solver_simplify_partial_solve_wit_25_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( db_lookup (solver_selected_db type Mcur) (Znth (i - 0) words 0) co ) as H_db_lookup.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  unfold db_lookup in H_db_lookup.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [Htype _].
  assert (Hin : In (Znth (i - 0) words 0, co) (msolver_db Mcur)).
  { eapply solver_selected_db_in; [exact Htype | exact H_db_lookup]. }
  pose proof (db_wf_even _ _ _ _ (msa_db_wf (msas_weak H_msolver_inv)) Hin) as Heven.
  pose proof (db_wf_ptr_pos _ _ _ _ (msa_db_wf (msas_weak H_msolver_inv)) Hin) as Hpos.
  apply clause_ptr_mod2 in Heven.
  split_pures; dump_pre_spatial; try solve [assumption | lia].
  rewrite Z.rem_mod_nonneg by lia. exact Heven.
Qed.


Lemma proof_of_solver_solve_which_implies_wit_1 : solver_solve_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Mdrained into Md.
  unfold solver_rep_wl, solver_rep_levels_wl_at, solver_cancel_owned.
  Intros lvl act asg opos rsn trl tgs.
  Exists lvl asg.
  unfold solver_solve_entry_rest_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at, solver_nonlevel_rep_at,
    solver_nonlevel_rep_nostats_at, solver_vecs_rep,
    solver_vecs_without_clauses_rep, db_words.
  Exists act opos rsn trl tgs.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_2 : solver_solve_which_implies_wit_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_solve_entry_rest_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at, solver_nonlevel_rep_at,
    solver_nonlevel_rep_nostats_at, solver_vecs_rep,
    solver_vecs_without_clauses_rep, db_words.
  Intros act opos rsn trl tgs.
  Exists act opos rsn trl tgs.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_15 : solver_solve_which_implies_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  prop_apply_p (CharArray.seg_Zlength values 0 n (mt_assigns (ms_core Mcur))).
  Intros_p Hassigns_len.
  unfold solver_assigns_focus_frame_wl_at, solver_root_install_frame_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  assert (Hn : n = ms_size Mcur).
  { match goal with
    | Hshape : solver_shape Mcur |- _ => unfold solver_shape in Hshape; lia
    end. }
  subst n.
  unfold solver_scalars_rep, solver_scalars_without_root_rep,
    solver_vecs_rep, solver_vecs_without_lim_rep.
  Exists act opos rsn trl tgs.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_addclause_addclause_spec_entail_solver_addclause_incremental_spec :
  solver_addclause_addclause_spec_entail_solver_addclause_incremental_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename begin_pre into begin, s_pre into s,
    input_solver_addclause_incremental_spec into input,
    M_solver_addclause_incremental_spec into physical,
    F_solver_addclause_incremental_spec into F,
    input_bound_solver_addclause_incremental_spec into input_bound,
    n_solver_addclause_incremental_spec into n.
  unfold solver_incremental_ownership_at. Intros.
  assert (Hupdate : solver_update_ready n F nil physical) by tauto.
  assert (Hwatch : solver_query_watch_ready physical) by tauto.
  assert (Hseed : msolver_seed_shadow physical) by tauto.
  assert (Hbound : 2 * ms_cap physical <= INT_MAX) by tauto.
  assert (Hpending_physical : ms_capacity_root_propagation_pending physical = 0) by tauto.
  set (entry := physical).
  assert (Hbase : solver_base_state n F entry).
  { unfold solver_update_ready in Hupdate.
    rewrite (msolver_resume_pending_ordinary__api_reentry physical Hpending_physical) in Hupdate.
    exact Hupdate. }
  assert (Hcomplete : minisat_watch_completed entry) by (apply (proj1 Hwatch); exact Hpending_physical).
  assert (Hseed_entry : msolver_seed_shadow entry) by exact Hseed.
  assert (Hentry_size : ms_size entry = n).
  { symmetry. exact (msa_size (msas_weak (proj1 Hbase))). }
  assert (Hshape : solver_shape entry).
  { exact (msa_shape (msas_weak (proj1 Hbase))). }
  assert (Hsupport : solver_support_inv (ms_size entry) F nil nil 0 entry).
  { rewrite Hentry_size. apply solver_assuming_zero_support__update_surface.
    - exact (proj1 Hbase).
    - exact (proj1 (proj2 Hbase)). }
  Exists F (@nil literal) (@nil literal) entry input_bound input.
  split_pure_spatial.
  - cancel (solver_rep_growable s physical).
    cancel (IntArray.seg begin 0 (Zlength input) input).
    cancel (( &( "l_Undef" )) # Char |-> 0).
    cancel (( &( "lit_Undef" )) # Int |-> (-2)).
    cancel (( &( "true" )) # Int |-> 1).
    cancel (( &( "false" )) # Int |-> 0).
    pre_process_default.
    Split.
    {  Intros.
    assert (Hret_domain : retval = 0 \/ retval = 1) by tauto.
    sep_apply (solver_addclause_result_same_ret__incremental_public
      s begin n input_bound F entry input retval Hbase Hcomplete Hseed_entry).
    Intros Mout current. unfold solver_incremental_ownership_at. Intros.
    match goal with
    | Hfacts : Zlength current = Zlength input /\ n <= ms_size Mout /\
        solver_query_watch_ready Mout /\ _ |- _ =>
        destruct Hfacts as [Hlen [Hsize_out [Hwatch_out
          [Hpending_out Hcases]]]]
    end.
    destruct Hcases as [[Hret [Fnew [Hupdate_out Hequiv]]] |
      [Hret [Hunsat Hupdate_out]]].
    + Left.
      Exists Fnew Mout current. msat_entailer_with ltac:(tauto).
    + Right.
      Exists Mout current. msat_entailer_with ltac:(tauto). }
    {  Intros.
    assert (Hret_domain : retval = 0 \/ retval = 1) by tauto.
    sep_apply (solver_addclause_result_same_ret__incremental_public
      s begin n input_bound F entry input retval Hbase Hcomplete Hseed_entry).
    Intros Mout current. unfold solver_incremental_ownership_at. Intros.
    match goal with
    | Hfacts : Zlength current = Zlength input /\ n <= ms_size Mout /\
        solver_query_watch_ready Mout /\ _ |- _ =>
        destruct Hfacts as [Hlen [Hsize_out [Hwatch_out
          [Hpending_out Hcases]]]]
    end.
    destruct Hcases as [[Hret [Fnew [Hupdate_out Hequiv]]] |
      [Hret [Hunsat Hupdate_out]]].
    + Left.
      Exists Fnew Mout current. msat_entailer_with ltac:(tauto).
    + Right.
      Exists Mout current. msat_entailer_with ltac:(tauto). }
  - assert (Hpending : ms_capacity_root_propagation_pending entry = 0)
      by exact (proj2 (proj2 Hbase)).
    assert (Hdepth : Zlength (mt_lim (ms_core entry)) = 0)
      by exact (proj1 (proj2 Hbase)).
    unfold entry. msat_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_addclause_partial_solve_wit_26_pure : solver_addclause_partial_solve_wit_26_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( addclause_dedup_inv (ms_size Mnew) (mt_assigns (ms_core Mnew)) ac_input_addclause_spec kept last ) as Hded.
  unfold addclause_dedup_inv in Hded.
  destruct Hded as (_ & _ & _ & _ & Hwf & _ & _ & Hlast & Hge).
  bind_fact ( solver_shape Mnew ) as Hshape.
  destruct Hshape as (Hsz & _).
  apply _derivable1_andp_intros; apply dump_spatial_left; [ | lia ].
  destruct (Z_lt_le_dec last 0) as [Hneg | Hnn]; [ lia | ].
  pose proof (addclause_last_member kept last Hlast Hnn) as Hin.
  rewrite Forall_forall in Hwf.
  specialize (Hwf last Hin).
  unfold lit_wf_c in Hwf.
  lia.
Qed.


Lemma proof_of_solver_canceluntil_partial_solve_wit_13_pure : solver_canceluntil_partial_solve_wit_13_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pures; dump_pre_spatial; replace (c - 0) with c by lia; assumption.
Qed.


Lemma proof_of_solver_new_which_implies_wit_2 : solver_new_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MiniSatClause.undef, activity_undef, solver_selected_is_learnt, clause_hdr_addr, clause_act_addr, clause_lits_addr.
  cbn [Z.eqb negb].
  Intros_p Hb. destruct Hb as [Hsize [Hpos Hmod]].
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. rewrite Z.rem_mod_nonneg by lia. exact Hmod.
Qed.


Lemma proof_of_solver_search_partial_solve_wit_2_pure : solver_search_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst M0 ) as H_msolver_inv.
  dump_pre_spatial.
  exact (msi_shape H_msolver_inv).
Qed.


Lemma proof_of_solver_search_which_implies_wit_28 : solver_search_which_implies_wit_28.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (msolver_inv n F A_arr A_inst Mstable) as Hentry.
  bind_fact (Zlength (mt_lim (ms_core Mstable)) = 0) as Hdepth.
  pose proof (solver_level_zero_assuming__api_reentry
    n F A_arr A_inst Mstable Hentry Hdepth) as Hassuming.
  pose proof (solver_installed_assumptions_at_zero__api_reentry
    n F A_arr A_inst Mstable Hentry Hdepth) as Hinst.
  assert (Hroot : ms_root_level Mstable = 0).
  { pose proof (msi_root_range Hentry). lia. }
  unfold solver_simplify_pre_at, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_search_root_frame_at,
    solver_search_bundle_at, solver_search_payload, solver_payload_cells, solver_scalars_rep,
    solver_scalars_without_root_rep,
    solver_fp_rep, solver_vecs_without_lim_rep,
    solver_var_arrays_rep, solver_trail_array_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  unfold solver_vecs_rep, solver_levels_slice_at.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_42 : solver_search_which_implies_wit_42.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_search_selection_state n F A_arr A_inst next Mselected ) as H_solver_search_selection_state.
  pose proof (solver_search_selection_pure__search
    n F A_arr A_inst next Mselected H_solver_search_selection_state) as [Hlim Henqueue].
  pose proof H_solver_search_selection_state as Hsel.
  unfold solver_search_selection_state in Hsel.
  destruct Hsel as (Hweak & _ & _ & _ & _ & Hdrain & _).
  pose proof (msw_size Hweak) as Hsize.
  sep_apply (solver_rep_levels_at_assume_focus__search
    s Mselected levels search_wl).
  Intros decision_asg. Exists decision_asg.
  rewrite <- Hsize, Hdrain.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_setnvars_setnvars_spec_entail_solver_setnvars_incremental_spec :
  solver_setnvars_setnvars_spec_entail_solver_setnvars_incremental_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_incremental_ownership_at. Intros.
  assert (Hupdate : solver_update_ready nv_solver_setnvars_incremental_spec F_solver_setnvars_incremental_spec nil M_solver_setnvars_incremental_spec) by tauto.
  assert (Hwatch : solver_query_watch_ready M_solver_setnvars_incremental_spec) by tauto.
  assert (Hpending : ms_capacity_root_propagation_pending M_solver_setnvars_incremental_spec = 0) by tauto.
  assert (Hseed : msolver_seed_shadow M_solver_setnvars_incremental_spec) by tauto.
  assert (Hbound : 2 * ms_cap M_solver_setnvars_incremental_spec <= INT_MAX) by tauto.
  unfold solver_update_ready, msolver_resume_pending in Hupdate.
  rewrite Hpending in Hupdate. simpl in Hupdate.
  destruct Hupdate as [Hstrong [Hdepth _]].
  assert (Hsize : ms_size M_solver_setnvars_incremental_spec = nv_solver_setnvars_incremental_spec)
    by (symmetry; exact (msa_size (msas_weak Hstrong))).
  assert (Hcompleted : minisat_watch_completed M_solver_setnvars_incremental_spec)
    by (destruct Hwatch as [Hordinary _]; exact (Hordinary Hpending)).
  assert (Hsupport : solver_support_inv (ms_size M_solver_setnvars_incremental_spec) F_solver_setnvars_incremental_spec nil nil 0 M_solver_setnvars_incremental_spec).
  { rewrite Hsize. apply solver_assuming_zero_support__update_surface;
      [exact Hstrong | exact Hdepth]. }
  Exists F_solver_setnvars_incremental_spec (@nil literal) (@nil literal) M_solver_setnvars_incremental_spec 0.
  split_pure_spatial.
  - cancel (solver_rep_growable s_pre M_solver_setnvars_incremental_spec).
    cancel.
    pre_process_default.
Intros Mnew;
  assert (Hgrow : ms_size M_solver_setnvars_incremental_spec <= ms_size Mnew) by tauto;
  assert (Hsupport_new : solver_support_inv (ms_size Mnew) F_solver_setnvars_incremental_spec nil nil 0 Mnew)
    by tauto;
  assert (Hcond :
    (Zlength (mt_lim (ms_core M_solver_setnvars_incremental_spec)) = 0 /\
     ms_capacity_root_propagation_pending M_solver_setnvars_incremental_spec = 0 /\ msolver_seed_shadow M_solver_setnvars_incremental_spec) ->
    (Zlength (mt_lim (ms_core Mnew)) = 0 /\
     ms_capacity_root_propagation_pending Mnew = 0 /\
     msolver_seed_shadow Mnew)) by tauto;
  assert (Hwc : minisat_watch_completed M_solver_setnvars_incremental_spec -> minisat_watch_completed Mnew)
    by tauto;
  destruct (Hcond (conj Hdepth (conj Hpending Hseed)))
    as [Hdepth_new [Hpending_new Hseed_new]];
  specialize (Hwc Hcompleted);
  sep_apply solver_rep_growable_shape__public; Intros;
  assert (Hshape_new : solver_shape Mnew) by tauto;
  destruct (solver_support_zero_assuming__update_surface
    (ms_size Mnew) F_solver_setnvars_incremental_spec nil nil Mnew Hsupport_new Hshape_new Hdepth_new)
    as [Hstrong_new _];
  assert (Hbase_new : solver_base_state (ms_size Mnew) F_solver_setnvars_incremental_spec Mnew)
    by (split; [exact Hstrong_new | split; assumption]);
  pose proof (solver_base_update_ready__incremental_public
    (ms_size Mnew) F_solver_setnvars_incremental_spec Mnew Hbase_new) as Hupdate_new;
  pose proof (solver_completed_query_watch__incremental_public
    Mnew Hpending_new Hwc) as Hwatch_new;
  rewrite <- Hsize;
  Exists Mnew; unfold solver_incremental_ownership_at;
  msat_entailer_with ltac:(tauto || lia).
  - msat_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_simplify_solver_simplify_spec_entail_solver_simplify_incremental_spec :
  solver_simplify_solver_simplify_spec_entail_solver_simplify_incremental_spec.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold solver_incremental_ownership_at. Intros.
assert (Hupdate : solver_update_ready n_solver_simplify_incremental_spec F_solver_simplify_incremental_spec nil M_solver_simplify_incremental_spec) by tauto.
assert (Hpending : ms_capacity_root_propagation_pending M_solver_simplify_incremental_spec = 0) by tauto.
assert (Hwatch : solver_query_watch_ready M_solver_simplify_incremental_spec) by tauto.
assert (Hseed : msolver_seed_shadow M_solver_simplify_incremental_spec) by tauto.
assert (Hbound : 2 * ms_cap M_solver_simplify_incremental_spec <= INT_MAX) by tauto.
assert (Hbase : solver_base_state n_solver_simplify_incremental_spec F_solver_simplify_incremental_spec M_solver_simplify_incremental_spec).
{ unfold solver_update_ready in Hupdate.
  rewrite (msolver_resume_pending_ordinary__api_reentry M_solver_simplify_incremental_spec Hpending) in Hupdate.
  exact Hupdate. }
assert (Hcomplete : minisat_watch_completed M_solver_simplify_incremental_spec) by (apply (proj1 Hwatch); exact Hpending).
assert (Hsize : ms_size M_solver_simplify_incremental_spec = n_solver_simplify_incremental_spec) by (symmetry; exact (msa_size (msas_weak (proj1 Hbase)))).
sep_apply solver_rep_growable_to_wl. Intros wl lvl.
Exists n_solver_simplify_incremental_spec F_solver_simplify_incremental_spec (@nil literal) M_solver_simplify_incremental_spec lvl wl.
unfold solver_simplify_pre_at.
split_pure_spatial.
- cancel (solver_rep_levels_wl_at s_pre M_solver_simplify_incremental_spec wl lvl).
  cancel (( &( "l_Undef" )) # Char |-> 0).
  cancel (( &( "l_True" )) # Char |-> 1).
  cancel (( &( "l_False" )) # Char |-> (-1)).
  cancel (( &( "true" )) # Int |-> 1).
  cancel (( &( "false" )) # Int |-> 0).
  pre_process_default.
  rewrite Hsize. Split.
  + Intros. subst retval.
    sep_apply (solver_simplify_result_same_ret__incremental_public s_pre n_solver_simplify_incremental_spec F_solver_simplify_incremental_spec M_solver_simplify_incremental_spec lvl wl 0 Hcomplete Hbound).
    Intros Mout.
    match goal with Hfacts : solver_update_ready n_solver_simplify_incremental_spec F_solver_simplify_incremental_spec nil Mout /\ _ |- _ =>
      destruct Hfacts as [Hupdate_out Hcases]
    end.
    destruct Hcases as [[Hret _] | [Hret Hrest]]; try discriminate.
    Left. Exists Mout. msat_manual_entailer_with ltac:(tauto).
  + Intros. subst retval.
    sep_apply (solver_simplify_result_same_ret__incremental_public s_pre n_solver_simplify_incremental_spec F_solver_simplify_incremental_spec M_solver_simplify_incremental_spec lvl wl 1 Hcomplete Hbound).
    Intros Mout.
    match goal with Hfacts : solver_update_ready n_solver_simplify_incremental_spec F_solver_simplify_incremental_spec nil Mout /\ _ |- _ =>
      destruct Hfacts as [Hupdate_out Hcases]
    end.
    destruct Hcases as [[Hret Hrest] | [Hret _]]; try discriminate.
    Right. Exists Mout. msat_manual_entailer_with ltac:(tauto).
- unfold solver_base_state in Hbase. msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_simplify_entail_wit_3_1_split_goal_1 : solver_simplify_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_simplify_db_compaction_inv, db_words.
  pose proof (Zlength_nonneg (map fst (solver_selected_db 1 Mtype))) as Hlen.
  split; [right; reflexivity |].
  split; [lia |]. split; [lia |]. split; [lia |].
  rewrite Zsublist_nil by lia.
  simpl.
  unfold sublist.
  simpl.
  rewrite Zlength_correct, Nat2Z.id.
  symmetry.
  apply List.firstn_all.
Qed.



Lemma proof_of_solver_simplify_entail_wit_3_1 : solver_simplify_entail_wit_3_1.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_simplify_entail_wit_3_1_split_goal_1 M_solver_simplify_spec smp_A_arr_solver_simplify_spec smp_F_solver_simplify_spec smp_n_solver_simplify_spec type words_type Mtype p retval).
Qed.



Lemma proof_of_solver_solve_entail_wit_6_1 : solver_solve_entail_wit_6_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
pose proof PreH4 as Hready. unfold propagation_cancel_ready in Hready.
destruct Hready as (Hweak & Hprop & Hlit & Hprocessed & Hlevel & Hfront & Hheap & Hcovers & Hreasonless).
destruct Hweak as [Hpending Hassuming]. cbn in Hassuming.
pose proof (msa_size Hassuming) as Hsize.
pose proof PreH9 as (Hentails & Hfalse & Hwf & Hnodup & Hlevelmax).
assert (Hunsat : cnf_unsat n_solver_solve_spec (cnf_with_units F_solver_solve_spec A_arr_solver_solve_spec)) by (eapply assuming_conflict_unsat; eauto).
assert (Hcap : ms_cap propagation_result = ms_cap M_solver_solve_spec) by (unfold propagation_caller_frame in PreH5; intuition congruence).
assert (Hreuse : solver_query_reuse_guard M_solver_solve_spec -> minisat_watch_conflict_ready n_solver_solve_spec propagation_result) by (intro Hg; exact (PreH6 (PreH14 Hg))).
Exists result_focus 1 propagation_result. unfold assumptions_array. Exists raw.
assert (HA : A_arr_solver_solve_spec = lits_denote raw) by (rewrite PreH25; unfold assumption_prefix; rewrite sublist_self by reflexivity; reflexivity).
sep_apply (store_ptr_undef_store_ptr (&( "i"))).
sep_apply (store_char_undef_store_char (&( "assumption_status"))).
msat_manual_entailer_with ltac:(lia || tauto).
Qed.


Lemma proof_of_solver_solve_partial_solve_wit_18_pure : solver_solve_partial_solve_wit_18_pure.
Proof.
  msat_solve_close_assumption_lit_bounds k.
Qed.


Lemma proof_of_solver_solve_which_implies_wit_7 : solver_solve_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  bind_fact (assumption_fresh_ready n raw k Mcur) as Hready.
  pose proof Hready as Hparts.
  unfold assumption_fresh_ready in Hparts.
  destruct Hparts as (Hsize & Hdrain & Hfresh & Hlim & Henqueue).
  subst n.
  unfold solver_assigns_focus_frame_wl_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  unfold enqueue_state_at, solver_assume_frame_wl,
    solver_enqueue_frame_with_scalars_wl, solver_enqueue_cells_at,
    solver_assume_scalars_frame, solver_vecs_without_lim_rep,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep,
    solver_trail_array_rep, solver_levels_slice_at.
  Exists rsn trl act opos tgs.
  rewrite Hdrain.
  split_pure_spatial.
  - msat_cancel_sound; cancel.
  - split_pures.
    + dump_pre_spatial. exact Hready.
    + dump_pre_spatial. unfold solver_shape in H. lia.
Qed.


Lemma proof_of_solver_solve_which_implies_wit_10_split_goal_1 : solver_solve_which_implies_wit_10_split_goal_1.
Proof.
(LLM_pre_process ltac:(lia || int_auto));
assert (Hcap : ms_cap propagation_result = ms_cap M_solver_solve_spec)
by (unfold propagation_caller_frame in PreH4; intuition congruence);
assert (Hreuse : solver_query_reuse M_solver_solve_spec propagation_result)
by (intro Hentry; exact ((proj1 PreH5) (PreH2 Hentry)));
pose proof PreH3 as (Hpending & Hprop);
assert (Hstrong : msolver_inv_assuming_strong n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec (assumption_prefix raw (k+1)) propagation_result)
by (eapply solver_propagation_drained_assuming_strong; eauto).
all: unfold assumption_propagation_success; msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_10_split_goal_2 : solver_solve_which_implies_wit_10_split_goal_2.
Proof.
(LLM_pre_process ltac:(lia || int_auto));
assert (Hcap : ms_cap propagation_result = ms_cap M_solver_solve_spec)
by (unfold propagation_caller_frame in PreH4; intuition congruence);
assert (Hreuse : solver_query_reuse M_solver_solve_spec propagation_result)
by (intro Hentry; exact ((proj1 PreH5) (PreH2 Hentry)));
pose proof PreH3 as (Hpending & Hprop);
assert (Hstrong : msolver_inv_assuming_strong n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec (assumption_prefix raw (k+1)) propagation_result)
by (eapply solver_propagation_drained_assuming_strong; eauto).
all: unfold assumption_propagation_success; msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_10_split_goal_3 : solver_solve_which_implies_wit_10_split_goal_3.
Proof.
(LLM_pre_process ltac:(lia || int_auto));
assert (Hcap : ms_cap propagation_result = ms_cap M_solver_solve_spec)
by (unfold propagation_caller_frame in PreH4; intuition congruence);
assert (Hreuse : solver_query_reuse M_solver_solve_spec propagation_result)
by (intro Hentry; exact ((proj1 PreH5) (PreH2 Hentry)));
pose proof PreH3 as (Hpending & Hprop);
assert (Hstrong : msolver_inv_assuming_strong n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec (assumption_prefix raw (k+1)) propagation_result)
by (eapply solver_propagation_drained_assuming_strong; eauto).
all: unfold assumption_propagation_success; msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_10 : solver_solve_which_implies_wit_10.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_solver_solve_which_implies_wit_10_split_goal_1 M_solver_solve_spec A_arr_solver_solve_spec F_solver_solve_spec n_solver_solve_spec raw k Mdecide propagation_result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
- Goal_apply (proof_of_solver_solve_which_implies_wit_10_split_goal_2 M_solver_solve_spec A_arr_solver_solve_spec F_solver_solve_spec n_solver_solve_spec raw k Mdecide propagation_result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
- Goal_apply (proof_of_solver_solve_which_implies_wit_10_split_goal_3 M_solver_solve_spec A_arr_solver_solve_spec F_solver_solve_spec n_solver_solve_spec raw k Mdecide propagation_result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
Qed.




Lemma proof_of_assume_partial_solve_wit_4_pure : assume_partial_solve_wit_4_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst. match goal with H : enqueue_input _ _ _ _ _ _ _ |- _ => pose proof H as Hin; unfold enqueue_input, lit_wf_c in Hin end. msat_manual_entailer_with ltac:(intuition lia).
Qed.
