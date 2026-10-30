From SimpleC.Verification Require Import VCPrelude.
Require Import Coq.Reals.Reals.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.


Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_proof_common.

Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_analysis_goal.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_proof_automation.
Lemma proof_of_solver_analyze_entail_wit_2 : solver_analyze_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K M0 anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( propagation_conflict_cert anz_n anz_F M0 C ) as H_propagation_conflict_cert.
  bind_fact ( conflict_ptr_denotes M0 c_pre C ) as H_conflict_ptr_denotes.
  bind_fact ( ms_root_level M0 < Zlength (mt_lim (ms_core M0)) ) as H_ms_root_level.
  bind_fact ( ms_tags M0 = repeat_Z 0 anz_n ) as H_ms_tags.
  bind_fact ( ms_tagged M0 = nil ) as H_ms_tagged.
  bind_fact ( msolver_seed_shadow M0 ) as H_msolver_seed_shadow.
  bind_fact ( 2 * anz_n <= INT_MAX ) as H_two_n_le_int_max.
  destruct (msat_analyze_cancel_ready_core anz_n anz_F anz_A_arr K M0 anz_focus
    H_analysis_cancel_ready)
    as (Htrail & Hlim & Hroot_nonnegative & Htrail_length & Hbinary_nonzero & Hdb
        & Hshape_from_lengths).
  assert (Hlim_positive : 0 < Zlength (mt_lim (ms_core M0))) by lia.
  assert (Hlim_index : 0 <= 0 < Zlength (mt_lim (ms_core M0))) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 0
    (mtw_lim_range Htrail) Hlim_index) as Hfirst_boundary.
  destruct Hfirst_boundary as [Hboundary_nonnegative Htrail_positive].
  rewrite Htrail_length in Htrail_positive.
  assert (Hqtail_positive : 0 < ms_qtail M0) by lia.
  assert (Hn_positive : 0 < anz_n) by lia.
  assert (Htags : analysis_tags_exact anz_n (ms_tags M0) (ms_tagged M0)).
  {
    unfold analysis_tags_exact.
    rewrite H_ms_tags, H_ms_tagged.
    unfold repeat_Z.
    repeat split.
    - rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. reflexivity.
    - constructor.
    - constructor.
    - induction (Z.to_nat anz_n) as [| k IH]; simpl.
      + constructor.
      + constructor; [tauto | exact IH].
    - intro Hz. rewrite Znth_repeat in Hz. lia.
    - intro Hin. contradiction.
  }
  assert (Hloop :
    analyze_resolution_loop_inv anz_n anz_F anz_A_arr K M0 anz_focus AnalyzeInitial
      c_pre C ((-2) :: nil) 0 (ms_qtail M0 - 1) (-2)).
  {
    unfold analyze_resolution_loop_inv.
    split; [exact H_analysis_cancel_ready |].
    split; [lia |].
    split; [cbn; lia |].
    split; [exact H_ms_root_level |].
    split; [exact Htags |].
    cbn.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [lia |].
    split; [exact H_propagation_conflict_cert |].
    split; [exact H_conflict_ptr_denotes |].
    split; [exact H_ms_tagged |].
    cbn [lits_denote]. reflexivity.
  }
  assert (Hconflict_nonzero : c_pre <> 0).
  {
    unfold conflict_ptr_denotes in H_conflict_ptr_denotes.
    destruct H_conflict_ptr_denotes as [[Hptr [_ _]] | [co [_ [Hin _]]]].
    - rewrite Hptr. exact Hbinary_nonzero.
    - pose proof (db_wf_ptr_pos anz_n (msolver_db M0) c_pre co Hdb Hin).
      lia.
  }
  assert (Hcore_refl : analysis_core_equiv M0 M0).
  { unfold analysis_core_equiv. repeat split; reflexivity. }
  pose proof (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K M0 anz_focus H_analysis_cancel_ready) as Hreason_core.
  destruct Hreason_core as [Hn_size _].
  Exists AnalyzeInitial C ((-2) :: nil) M0.
  (* The loop enters with the literal one-element learnt vector; spell it
     the way the postcondition does, so the terminal cancel is syntactic. *)
  assert (Hwords_lit : z_nil +:: (-2) = (-2) :: nil) by reflexivity.
  rewrite Hwords_lit.
  (* Discharge the six pure conjuncts against hypotheses already in scope,
     so that the [ms_size] rewrite below cannot disturb them and what is left
     is the bare spatial closure. *)
  split_pure_spatial;
    [ idtac
    | split_pures; dump_pre_spatial;
      first [ exact Hcore_refl | exact H_msolver_seed_shadow | exact Hconflict_nonzero
            | exact Hloop | exact H_ms_root_level | exact H_two_n_le_int_max ] .. ].
  rewrite Hn_size.
  prop_apply_p (solver_analyze_frame_stats_len s_pre M0 anz_wl).
  Intros_p Hstats_shape.
  prop_apply_p (DoubleArray.seg_Zlength activity_ptr 0
    (ms_size M0) (ms_activity M0)).
  Intros_p Hactivity_len.
  prop_apply_p (IntArray.seg_Zlength orderpos_ptr 0
    (ms_size M0) (ms_orderpos M0)).
  Intros_p Horder_len.
  prop_apply_p (CharArray.seg_Zlength tags_ptr 0
    (ms_size M0) (ms_tags M0)).
  Intros_p Htags_len.
  assert (Hactivity_shape :
    Zlength (ms_activity M0) = ms_size M0) by lia.
  assert (Horder_shape :
    Zlength (ms_orderpos M0) = ms_size M0) by lia.
  assert (Htags_shape :
    Zlength (ms_tags M0) = ms_size M0) by lia.
  assert (Hshape : solver_shape M0)
    by (apply Hshape_from_lengths; assumption).
  unfold solver_analyze_inert_at.
  Intros.
  sep_apply (analyze_frame_join s_pre M0 anz_wl).
  Intros asg.
  unfold solver_rep_analyze_at, solver_rep_at.
  Exists activity_ptr asg orderpos_ptr.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_trail_array_rep.
  unfold msat_false.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_analyze_entail_wit_7_3 : solver_analyze_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  bind_fact ( Znth (retval_6 - 0) (mt_levels (ms_core Mcur)) 0 <= 0 ) as H_Znth.
  bind_fact ( retval_6 = lit_var_c (tag_lit c) ) as H_retval_6.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mcur anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( level_of (msolver_view anz_n Mcur) (lit_var_c (tag_lit c)) = Some (current_level (msolver_view anz_n
      Mcur)) ) as H_level_of.
  bind_fact ( solver_shape Mcur ) as H_solver_shape.
  pose proof H_analysis_cancel_ready as Hready_copy.
  unfold analysis_cancel_ready in Hready_copy.
  destruct Hready_copy as
    (Mentry & Hcancel & Hequiv & Hheapwf & Hcovers & Hearliest &
     Hfocuslev & Hclainc).
  unfold propagation_cancel_ready in Hcancel.
  destruct Hcancel as
    (Hweak & Hprop & Hfocuswf & Hprocessed & Hentryfocus & Hfrontier &
     Hentryheap & Hentrycovers & Hentryearliest).
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as (Hcaproot & Hweak).
  assert (Htrailwf_entry : mtrail_wf anz_n (ms_core Mentry)).
  {
    destruct K as [A_inst | A_proc]; cbn in Hweak.
    - exact (msw_trail_wf Hweak).
    - exact (msa_trail_wf Hweak).
  }
  pose proof Hequiv as Hequiv_fields.
  unfold analysis_core_equiv in Hequiv_fields.
  destruct Hequiv_fields as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason & Eprob &
     Elearnt & Erest).
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mcur)).
  { rewrite Ecore. exact Htrailwf_entry. }
  assert (Hcell :
    Znth (lit_var_c (tag_lit c)) (mt_levels (ms_core Mcur)) 0 =
    Zlength (mt_lim (ms_core Mcur))).
  {
    change
      (option_map
         (fun k => level_of_index (ms_core Mcur) (Z.of_nat k))
         (trail_pos (ms_core Mcur) (lit_var_c (tag_lit c))) =
       Some (Zlength (mt_lim (ms_core Mcur)))) in H_level_of.
    destruct (trail_pos (ms_core Mcur) (lit_var_c (tag_lit c)))
      as [k|] eqn:Hpos; cbn in H_level_of; try discriminate.
    assert (Hlevel :
      level_of_index (ms_core Mcur) (Z.of_nat k) =
      Zlength (mt_lim (ms_core Mcur))) by congruence.
    pose proof (trail_pos_bound
      (ms_core Mcur) (lit_var_c (tag_lit c)) k Hpos) as Hbound.
    pose proof (mtw_levels_agree Htrailwf (Z.of_nat k)) as Hagree.
    rewrite (trail_pos_var
      (ms_core Mcur) (lit_var_c (tag_lit c)) k Hpos) in Hagree.
    rewrite Hlevel in Hagree.
    apply Hagree. lia.
  }
  assert (Hroot_nonneg : 0 <= ms_root_level Mcur).
  { unfold solver_shape in H_solver_shape. tauto. }
  rewrite H_retval_6 in H_Znth.
  replace (lit_var_c (tag_lit c) - 0) with (lit_var_c (tag_lit c))
    in H_Znth by lia.
  lia.
Qed.


Lemma proof_of_solver_analyze_entail_wit_33_split_goal_1 : solver_analyze_entail_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval.
  replace (1 - 0) with 1 in * by lia.
  replace (lit_var_c (Znth 1 words_compact 0) - 0)
    with (lit_var_c (Znth 1 words_compact 0)) by lia.
  unfold analyze_max_loop_inv.
  split; [lia | ].
  split; [lia | ].
  split; [exact PreH6 | ].
  split; [reflexivity | ].
  intros k Hk.
  assert (k = 1) by lia. subst k. lia.
Qed.



Lemma proof_of_solver_analyze_entail_wit_33 : solver_analyze_entail_wit_33.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_analyze_entail_wit_33_split_goal_1 anz_focus M0 K anz_A_arr anz_F anz_n Mstats words_compact lits i retval_2 tags_now tags_final tagged_list Mclear retval_3 cap retval).
Qed.



Lemma proof_of_solver_analyze_partial_solve_wit_10_pure : solver_analyze_partial_solve_wit_10_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase_2 c Ccur words_2 cnt ind p ) as
    H_analyze_resolution_loop_inv.
  split_pures.
  - dump_pre_spatial. assumption.
  - dump_pre_spatial. assumption.
  - dump_pre_spatial. assumption.
  - dump_pre_spatial. reflexivity.
  - dump_pre_spatial. exact (proj1 H_analyze_resolution_loop_inv).
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_20_pure : solver_analyze_partial_solve_wit_20_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pures;
    dump_pre_spatial; congruence.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_111_learnt_pure : solver_analyze_partial_solve_wit_111_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan anz_focus phase Ccur j ind S0 R2 learnt0 x
    Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
  destruct H_analyze_clause_scan_inv as [Hready _].
  unfold analysis_cancel_ready in Hready.
  destruct Hready as [Mready [_ [_ [Hheap _]]]].
  prop_apply_p (DoubleArray.seg_Zlength activity_ptr_scan 0 anz_n
    (ms_activity Mscan)).
  Intros.
  repeat lazymatch goal with
  | |- _ |-- _ && _ => apply _derivable1_andp_intros
  end;
  apply dump_spatial_left.
  all: first [ exact Hheap | lia ].
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_114_learnt_pure : solver_analyze_partial_solve_wit_114_learnt_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | HF : Forall (lit_wf_c anz_n) clause_words2 |- _ =>
      pose proof (Forall_Znth_elim _ _ _ 0 j HF ltac:(lia)) as Hlit
  end.
  unfold lit_wf_c in Hlit.
  subst j.
  repeat apply _derivable1_andp_intros; dump_pre_spatial; rewrite ?Z.sub_0_r; lia.
Qed.


Lemma proof_of_solver_analyze_return_wit_1 : solver_analyze_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (analysis_core_equiv_base_completion__api_reentry
    M0 Mfinal PreH1) as Hbase_reuse.
  unfold solver_analyze_post.
  unfold analysis_core_equiv in PreH1.
  Exists Mfinal words_final blevel.
  split_pure_spatial;
    [ cancel; cancel (Veci.rep learnt_pre words_final);
      cancel (solver_rep_levels_wl_at s_pre Mfinal anz_wl levels_ptr)
    | split_pures; dump_pre_spatial; solve [auto | int_auto | tauto] .. ].
Qed.



Lemma proof_of_solver_analyze_safety_wit_41_learnt : solver_analyze_safety_wit_41_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pures.
 - dump_pre_spatial. msat_analyze_bound_scan_index_by_nodup anz_n Ccur j Hinv clause_words2.
 - dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_13 : solver_analyze_which_implies_wit_13.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_focus_clause_db c Mcur ( Intros_p Hb; destruct Hb as [Hc [Htag [Hlits Hinitialized]]];
    subst c is_learnt_now clause_words;
    rewrite (binary_scratch_initialized _ _ Hinitialized); unfold MiniSatClause.rep;
    split_pure_spatial;
    [ cancel (clause_db_rep (ms_prob Mcur)); cancel
    | split; [ apply Zlength_nonneg | split; [ lia | msat_analyze_clause_ptr_even ] ] ] ).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_23 : solver_analyze_which_implies_wit_23.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Forall_Znth_elim
    _ _ words_uip 0 i PreH1 ltac:(lia)) as Hwf.
  replace (i - 0) with i by lia.
  pose proof (lit_var_c_in_range anz_n _ Hwf) as Hrange.
  entailer!.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_4_pure : solver_lit_removable_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_lit_var_parity_bounds l_pre.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_7_pure : solver_lit_removable_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_lit_var_parity_bounds l_pre.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_69_pure : solver_lit_removable_partial_solve_wit_69_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  msat_lit_removable_lits_pointer_even lrm_n M0 c is_learnt_now clause_words.
Qed.


Lemma proof_of_solver_lit_removable_return_wit_3 : solver_lit_removable_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Veci.rep_ptr_open
    &(s_pre # "solver_t" ->ₛ "tagged") tagged (sublist 0 top tagged_now)).
  Intros tagged_cap_rb.
  pose proof (Zlength_nonneg tagged_now) as H_Zlength.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  sep_apply
    (solver_removable_frame_lengths_keep__lit_removable
      s_pre M0 trail_ptr lrm_wl);
    Intros_p Hframe_lengths;
    destruct Hframe_lengths as
      (Hactivity_len & Horder_len & Hstats_len).
  prop_apply_p (CharArray.seg_Zlength tags_ptr 0 lrm_n tags_rollback);
    Intros_p Htags_len.
  try match goal with
       | Hinv : removable_rollback_inv _ _ _ _ _ _ _ _ ,
         Hj : _ = Zlength _ |- _ =>
           pose proof Hinv as Hinv_bounds;
           unfold removable_rollback_inv in Hinv_bounds;
           destruct Hinv_bounds as
             (Htop_nonneg & Htop_j & Hj_tagged & Htop_base & _);
           pose proof (removable_rollback_restore__lit_removable
             _ _ _ _ _ _ _ _ Hinv Hj) as [Htags Hbase]
       end.
  subst tags_rollback.
  rewrite Hbase in *.
  pose proof (analysis_cancel_ready_size__lit_removable
    _ _ _ _ _ _ H_analysis_cancel_ready) as Hnsize.
  assert (Horder_shape :
    Zlength (ms_orderpos M0) = ms_size M0) by lia.
  assert (Hactivity_shape :
    Zlength (ms_activity M0) = ms_size M0) by lia.
  assert (Htags_shape : Zlength (ms_tags M0) = ms_size M0) by lia.
  assert (Hstats_shape : Zlength (ms_stats M0) = 11) by lia.
  pose proof (analysis_cancel_ready_shape__lit_removable
    _ _ _ _ _ _ H_analysis_cancel_ready Horder_shape Hactivity_shape
    Htags_shape Hstats_shape) as Hshape.
  subst lrm_n.
  sep_apply (solver_removable_scratch_refold_return3__lit_removable
    s_pre M0 reasons_ptr levels_ptr trail_ptr tags_ptr tagged
    tagged_cap_rb stack_after lrm_wl Hshape).
  bind_fact (msolver_seed_shadow M0) as Hseed.
  msat_removable_scratch_carry
    (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0) stack_after)
    H_analysis_cancel_ready Hseed as Hreadyout Hseedout Hequivout.
  pose proof
    (removable_failure_post_pure__lit_removable
      (ms_size M0) lrm_F lrm_A_arr lrm_K M0 lrm_focus (ms_tags M0) (ms_tagged M0)
      stack_after Hreadyout Hseedout Hequivout
      eq_refl eq_refl) as Hpostpure.
  unfold solver_lit_removable_post.
  Exists (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0) stack_after).
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_lit_removable_safety_wit_35 : solver_lit_removable_safety_wit_35.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold clause_hdr_word in PreH11.
  split_pures; dump_pre_spatial; destruct is_learnt_now; lia.
Qed.


Lemma proof_of_solver_analyze_entail_wit_8_learnt : solver_analyze_entail_wit_8_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  bind_fact ( msat_fp32_nonnegative cla_inc1 ) as H_msat_fp32_nonnegative.
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p ) as
      H_analyze_resolution_loop_inv.
  bind_fact ( msolver_seed_shadow Mcur ) as H_msolver_seed_shadow.
  set (Mact := msolver_with_cla_inc_stats Mcur cla_inc1 (ms_stats Mcur)).
  assert (Hcore : analysis_core_equiv Mcur Mact).
  { subst Mact. unfold analysis_core_equiv, msolver_with_cla_inc_stats.
    cbn. repeat split; reflexivity. }
  assert (Hcore0 : analysis_core_equiv M0 Mact).
  { subst Mact. unfold analysis_core_equiv, msolver_with_cla_inc_stats in *.
    cbn in *. tauto. }
  assert (Hseed : msolver_seed_shadow Mact).
  { subst Mact. unfold msolver_with_cla_inc_stats. cbn. exact H_msolver_seed_shadow. }
  assert (Hframe_act :
    solver_analyze_frame s_pre Mact anz_wl = solver_analyze_frame s_pre Mcur anz_wl).
  { subst Mact.
    unfold solver_analyze_frame, solver_analyze_frame_cells, msolver_with_cla_inc_stats.
    cbn. reflexivity. }
  assert (Hinert_act :
    solver_analyze_inert_at s_pre Mact anz_n activity_ptr_loop orderpos_ptr_loop
      reasons_loop levels_ptr trail_loop tags_loop
    = solver_analyze_inert_at s_pre Mcur anz_n activity_ptr_loop orderpos_ptr_loop
      reasons_loop levels_ptr trail_loop tags_loop).
  { subst Mact. apply solver_analyze_inert_at_cla_inc. }
  assert (Hloop :
    analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mact anz_focus phase c Ccur
      words cnt ind p).
  { pose proof H_analyze_resolution_loop_inv as Hloop0.
    unfold analyze_resolution_loop_inv in Hloop0.
    destruct Hloop0 as
      (Hready & Hind & Hwords & Hroot & Htags & Hphase).
    assert (Hready_act : analysis_cancel_ready anz_n anz_F anz_A_arr K Mact anz_focus).
    { destruct Hready as
        (Mentry & Hcancel & Hequiv & Hheap & Hcovers & Hreason & Hfocus & Hcla).
      exists Mentry.
      split. { exact Hcancel. }
      split.
      - subst Mact.
        cbn [msolver_with_cla_inc_stats]. exact Hequiv.
      - split.
        + subst Mact. cbn. exact Hheap.
        + split.
          * subst Mact. cbn. exact Hcovers.
          * split.
            -- subst Mact. cbn. exact Hreason.
            -- split.
               ++ subst Mact. cbn. exact Hfocus.
               ++ subst Mact. cbn. exact H_msat_fp32_nonnegative. }
    unfold analyze_resolution_loop_inv.
    split. { exact Hready_act. }
    split. { subst Mact. cbn. exact Hind. }
    split. { subst Mact. cbn. exact Hwords. }
    split. { subst Mact. cbn. exact Hroot. }
    split. { subst Mact. cbn. exact Htags. }
    subst Mact. cbn. exact Hphase. }
  Exists Mact.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  rewrite Hframe_act, Hinert_act.
  subst Mact.
  unfold msolver_with_cla_inc_stats.
  cbn [ms_qtail ms_cap ms_activity ms_orderpos ms_reason_words ms_core ms_tags ms_order ms_stack ms_tagged ms_var_inc ms_cla_inc ms_learnt ms_prob ms_binary ms_binary_lits ms_stats].
  cancel.
Qed.


Lemma proof_of_solver_analyze_entail_wit_9 : solver_analyze_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  Exists Mcur.
  split_pure_spatial.
  - cancel (clause_db_rep (ms_prob Mcur)).
    cancel.
  - split_pures; dump_pre_spatial; solve [auto | lia | unfold analysis_core_equiv; repeat split; reflexivity].
Qed.


Lemma proof_of_solver_analyze_entail_wit_10_2_learnt : solver_analyze_entail_wit_10_2_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  msat_analyze_resolve Mact phase Ccur clause_words2 is_learnt2 orderpos_ptr_clause activity_ptr_clause.
Qed.


Lemma proof_of_solver_analyze_entail_wit_11_1 : solver_analyze_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  msat_analyze_scan_entry Mact phase Ccur clause_words2 is_learnt2 orderpos_ptr_clause activity_ptr_clause.
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_2_learnt : solver_analyze_entail_wit_12_2_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_9 - 0) (mt_levels (ms_core Mscan_2)) 0 = retval_10 ) as H_Znth.
  bind_fact ( retval_10 = Zlength (mt_lim (ms_core Mscan_2)) ) as H_retval_11.
  bind_fact ( retval_9 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  set (v := lit_var_c (Znth (j - 0) clause_words2 0)).
  set (Mnext := analyze_tag_step_msolver Mscan_2
    (replace_Znth v 1 (ms_tags Mscan_2))
    (ms_tagged Mscan_2 ++ (v :: nil)) activity1 orderpos1 heap1 var_inc1).
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & _).
  assert (HSold : Sscan_2 = analyze_start_S (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HLold : learnt_scan_2 = analyze_start_learnt (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hreadynew : analysis_cancel_ready anz_n anz_F anz_A_arr K Mnext anz_focus)
    by (unfold Mnext; apply ms_analyze_tag_step_cancel_ready;
        [exact Hreadyold | exact H_order_heap_wf | exact H_u_2]).
  assert (Htagsnew : analysis_tags_exact anz_n (replace_Znth v 1 (ms_tags Mscan_2))
      (ms_tagged Mscan_2 ++ (v :: nil)))
    by (apply ms_analysis_tags_exact_snoc;
        [exact Htagsold | unfold v; lia | unfold v in *; lia]).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2))
    by (apply ms_analyze_tags_perm_snoc_s; exact Hpermold).
  assert (Hcert : propagation_conflict_cert anz_n anz_F Mact Ccur)
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (EscanCore : ms_core Mscan_2 = ms_core Mact).
  { unfold analysis_core_equiv in H_analysis_core_equiv.
    destruct H_analysis_core_equiv as [_ [_ [_ [EcoreEq _]]]]. exact EcoreEq. }
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  destruct Hcert as [_ [Hfalse [_ [_ _]]]].
  destruct (eval_partial_false_shape _ _
    (Hfalse (lit_denote q) HqC)) as [b [Hass _]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hmt : mt_pv (ms_core Mscan_2) v = Some b).
  { rewrite mt_pv_nonneg by (unfold v; lia).
    rewrite EscanCore. rewrite Eqv in Hass. exact Hass. }
  destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
  2: { pose proof (proj2 (view_unassigned_iff anz_n (ms_core Mscan_2) v Htrailwf)
         Hrank) as Hnone.
       rewrite Hmt in Hnone. discriminate. }
  assert (Hrqb : Z.of_nat rq < Zlength (mt_trail (ms_core Mscan_2))).
  { apply (trail_pos_bound (ms_core Mscan_2) v rq Hrank). }
  pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree.
  rewrite (trail_pos_var (ms_core Mscan_2) v rq Hrank) in Hagree.
  assert (Hdqcur : level_of_index (ms_core Mscan_2) (Z.of_nat rq) =
      Zlength (mt_lim (ms_core Mscan_2))).
  { fold v in H_retval_10. rewrite H_retval_10, H_retval_11 in H_Znth.
    replace (v - 0) with v in H_Znth by lia. lia. }
  assert (Hat : at_current_level_b (msolver_view anz_n Mact) (lit_denote q) = true).
  { apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite Eqv.
    unfold msolver_view, view_of. cbn [level_of current_level].
    rewrite <- EscanCore.
    rewrite Hrank. cbn. f_equal. exact Hdqcur. }
  assert (Hbelow : below_current_b (msolver_view anz_n Mact) (lit_denote q) = false).
  { unfold below_current_b.
    rewrite Eqv.
    unfold msolver_view, view_of. cbn [level_of current_level].
    rewrite <- EscanCore.
    rewrite Hrank. cbn. rewrite Hdqcur, Z.ltb_irrefl, Bool.andb_false_r.
    reflexivity. }
  msat_analyze_start_step_tag q v anz_n Mact Ccur j clause_words2
    Sscan_2 learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow Eqv.
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext anz_focus phase Ccur
      (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2 words_scan_2 (cnt + 1))
    by (msat_analyze_scan_inv_tag Mnext phase H_Ccur HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 (Sscan_2 ++ (v :: nil)) Rscan_2
    learnt_scan_2 words_scan_2 Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame Mnext Mscan_2 v activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    fold v in H_retval_7, H_retval_6.
    rewrite H_retval_7, H_retval_6.
    sep_apply CharArray.full_to_seg.
    cancel.
  - msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_5_learnt : solver_analyze_entail_wit_12_5_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_9 - 0) (mt_levels (ms_core Mscan_2)) 0 <> retval_10 ) as H_Znth.
  bind_fact ( retval_10 = Zlength (mt_lim (ms_core Mact)) ) as H_retval_11.
  bind_fact ( retval_9 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Znth (retval_5 - 0) (mt_levels (ms_core Mscan_2)) 0 > 0 ) as H_Znth_2.
  bind_fact ( retval_5 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_5.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Mscan_2 = Mact ) as H_Mscan_2.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  rewrite <- H_Mscan_2 in H_retval_11.
  Left.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_initial_pack H_phase H_analyze_clause_scan_inv)
    as (Hcert & HSold & HLold).
  msat_analyze_tag_step_open v Mnext j clause_words2 activity1
    orderpos1 heap1 var_inc1 Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  destruct Hcert as [_ [Hfalse [HwfC [HndC [lcur [Hlcur Hlevcur]]]]]].
  destruct (eval_partial_false_shape _ _
    (Hfalse (lit_denote q) HqC)) as [b [Hass _]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags Sscan_2 Rscan_2
        (learnt_scan_2 ++ (lit_denote q :: nil))))
    by (rewrite <- Eqv; apply ms_analyze_tags_perm_snoc_l; exact Hpermold).
  assert (Hmt : mt_pv (ms_core Mscan_2) v = Some b).
  { rewrite mt_pv_nonneg by (unfold v; lia).
    rewrite H_Mscan_2. rewrite Eqv in Hass. exact Hass. }
  destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
  2: { pose proof (proj2 (view_unassigned_iff anz_n (ms_core Mscan_2) v Htrailwf)
         Hrank) as Hnone.
       rewrite Hmt in Hnone. discriminate. }
  msat_analyze_initial_level_readback v anz_n Mact Mscan_2 rq
    Hrank Htrailwf Eview H_retval_5 H_Znth_2 H_retval_10 H_retval_11 H_Znth.
  msat_analyze_offlevel_flags anz_n Mact q dq Hlevq Hdqne Eqv Eview.
  assert (Hneqcur : literal_var lcur <> v).
  { intro Heq. rewrite Heq, Hlevq in Hlevcur.
    injection Hlevcur as Ecur. rewrite <- H_Mscan_2 in Ecur. lia. }
  assert (Hn2 : 2 <= anz_n).
  { rewrite Forall_forall in HwfC.
    pose proof (HwfC (lit_denote q) HqC) as Hqwf.
    pose proof (HwfC lcur Hlcur) as Hcurwf.
    unfold literal_wf, var_in_range in Hqwf, Hcurwf.
    rewrite Eqv in Hqwf. lia. }
  assert (HLempty : learnt_scan_2 = nil).
  { rewrite HLold. subst j. unfold sublist, analyze_start_learnt.
    cbn. reflexivity. }
  assert (Htailnil : tl words_scan_2 = nil).
  { unfold lits_denote in Hwordsold. rewrite HLempty in Hwordsold.
    apply map_eq_nil in Hwordsold. exact Hwordsold. }
  assert (Hwordlenold : Zlength words_scan_2 = 1).
  { destruct words_scan_2 as [|w ws].
    - rewrite Zlength_nil in Hwordlower. lia.
    - cbn in Htailnil. subst ws. reflexivity. }
  assert (Hwordlennew : 1 <= Zlength (words_scan_2 ++ (q :: nil)) <= anz_n).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hwordsnext : lits_denote (tl (words_scan_2 ++ (q :: nil))) =
      learnt_scan_2 ++ (lit_denote q :: nil)).
  { destruct words_scan_2 as [|w ws].
    - rewrite Zlength_nil in Hwordlower. lia.
    - cbn in Htailnil. subst ws.
      cbn [lits_denote]. rewrite HLempty. reflexivity. }
  msat_analyze_start_step_word q anz_n Mact Ccur j clause_words2 Sscan_2
    learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow.
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext
      anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      Sscan_2 Rscan_2 (learnt_scan_2 ++ (lit_denote q :: nil))
      (words_scan_2 ++ (q :: nil)) cnt)
    by (msat_analyze_scan_inv_word Mnext phase H_Ccur Hwordlennew
          Hwordsnext HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
    (learnt_scan_2 ++ (lit_denote q :: nil))
    (words_scan_2 ++ (q :: nil)) Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame Mnext Mscan_2 v activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    rewrite <- H_Mscan_2.
    fold v in H_retval_7, H_retval_6.
    rewrite H_retval_7, H_retval_6.
    replace (j - 0) with j by lia.
    fold q.
    sep_apply CharArray.full_to_seg.
    cancel.
  - msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_26_pure : solver_analyze_partial_solve_wit_26_pure.
Proof.
  LLM_pre_process ltac:(lia). split_pures; msat_analyze_cancel_heap_tail.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_55_learnt_pure : solver_analyze_partial_solve_wit_55_learnt_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_analyze_clause_word_range anz_n j clause_words2 0.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_57_learnt_pure : solver_analyze_partial_solve_wit_57_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  msat_analyze_word_range_context anz_n j clause_words2.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_63_learnt_pure : solver_analyze_partial_solve_wit_63_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia). bind_fact ( Forall (lit_wf_c anz_n) clause_words2 ) as H_Forall.
  split_pures; msat_analyze_learnt_lit_range_tail H_Forall anz_n clause_words2 j.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_64_learnt_pure : solver_analyze_partial_solve_wit_64_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia). bind_fact ( Forall (lit_wf_c anz_n) clause_words2 ) as H_Forall.
  split_pures; msat_analyze_learnt_lit_range_tail H_Forall anz_n clause_words2 j.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_92_learnt_pure : solver_analyze_partial_solve_wit_92_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_clause_word_int_range_via_wf j clause_words2 Hlit.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_109_learnt_pure : solver_analyze_partial_solve_wit_109_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_113_learnt_pure : solver_analyze_partial_solve_wit_113_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan anz_focus phase Ccur j ind S0 R2 learnt0 x
      Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  pose proof H_analyze_clause_scan_inv as Hscan.
  unfold analyze_clause_scan_inv in Hscan.
  destruct Hscan as [Hready Hscan_rest].
  unfold analysis_cancel_ready in Hready.
  destruct Hready as [Mbase [Hcancel [Hequiv [Hheap Hready_rest]]]].
  unfold order_heap_wf, msolver_heap in Hheap.
  prop_apply_p (DoubleArray.seg_Zlength
    activity_ptr_scan 0 anz_n (ms_activity Mscan)).
  Intros_p Hactivity.
  replace (anz_n - 0) with anz_n in Hactivity by lia.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. exact Hactivity.
  - dump_pre_spatial. exact Hheap.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_144_pure : solver_analyze_partial_solve_wit_144_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( analyze_resolution_exit anz_n anz_F anz_A_arr K Mresolution anz_focus p words_before ) as
      H_analyze_resolution_exit.
  bind_fact ( 2 * anz_n <= INT_MAX ) as Htwo.
  destruct H_analyze_resolution_exit as
    [Hready [_ [_ [x [R [learnt [r Hexist]]]]]]].
  destruct Hexist as [Hx [Hr [Htrail _]]].
  unfold msolver_view, view_of in Hr.
  pose proof (trail_pos_bound _ _ _ Hr) as Hrng.
  assert (Hi : 0 <= Z.of_nat r < Zlength (mt_trail (ms_core Mresolution))) by lia.
  msat_analyze_trail_lit Hready (Z.of_nat r) Hi as Hlit.
  rewrite Htrail in Hlit.
  unfold lit_wf_c in Hlit.
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_161_pure : solver_analyze_partial_solve_wit_161_pure.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( Znth (retval - 0) (ms_reason_words Mmin) 0 <> 0 ) as H_Znth.
  bind_fact ( retval = lit_var_c (Znth (i - 0) words_min 0) ) as H_retval.
  bind_fact ( analyze_clause_cert anz_n anz_F Mmin words_uip ) as H_cert.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin words_uip kept removed words_min T i j ) as H_inv.
  bind_fact ( incl (map lit_var_c words_min) (map lit_var_c (mt_trail (ms_core Mmin))) ) as H_incl.
  bind_fact ( incl (map lit_var_c words_min) (ms_tagged Mmin) ) as H_incl_2.
  bind_fact ( 0 <= i ) as H_i_low.
  bind_fact ( i < Zlength words_min ) as H_i_high.
  pose proof (msat_analyze_minimize_scan_assigned anz_n anz_F Mmin words_uip
    kept removed words_min T i j H_cert H_inv H_incl H_i_low H_i_high) as Hbelow.
  assert (Htrail : In (lit_var_c (Znth (i - 0) words_min 0))
    (map lit_var_c (mt_trail (ms_core Mmin)))).
  { apply H_incl. apply in_map. apply Znth_In. lia. }
  assert (Htagged : In (lit_var_c (Znth (i - 0) words_min 0)) (ms_tagged Mmin)).
  { apply H_incl_2. apply in_map. apply Znth_In. lia. }
  assert (Hreason : Znth (lit_var_c (Znth (i - 0) words_min 0))
    (ms_reason_words Mmin) 0 <> 0).
  { replace (retval - 0) with retval in H_Znth by lia.
    rewrite H_retval in H_Znth. exact H_Znth. }
  subst retval.
  split_pures; msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_safety_wit_48_learnt : solver_analyze_safety_wit_48_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pures.
 - dump_pre_spatial. msat_analyze_bound_scan_index_by_nodup anz_n Ccur j Hinv clause_words2.
 - dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_4 : solver_analyze_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia).
    bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p ) as
      H_analyze_resolution_loop_inv.
  bind_fact ( is_tag c = msat_true ) as H_is_tag.
  pose proof H_analyze_resolution_loop_inv as H_analyze_resolution_loop_inv_folded.
  unfold msat_true in H_is_tag.
  destruct H_analyze_resolution_loop_inv as
    [Hready [Hind [Hwords [Hroot [Htags Hphase]]]]].
  destruct phase.
  - cbn in Hphase.
    destruct Hphase as
      [Hp [Hcnt [Hqtail [Hcert [Hconflict [Htagged Hlearnt]]]]]].
    pose proof Hready as Hreadycopy.
    destruct Hreadycopy as [M0 [Hcancel [Hequiv Hrest]]].
    destruct Hcancel as [[Hpending Hweak] Hcancelrest].
    assert (Hshape_db :
      solver_shape M0 /\ db_wf anz_n (msolver_db M0)).
    { destruct K as [A_inst | A_proc]; cbn in Hweak.
      - split; [exact (msw_shape Hweak) | exact (msw_db_wf Hweak)].
      - split; [exact (msa_shape Hweak) | exact (msa_db_wf Hweak)]. }
    destruct Hshape_db as [Hshape0 Hdb0].
    destruct Hequiv as
      [Esize [_ [_ [Ecore [_ [Ewords [Ereason
        [Eprob [Elearnt [Ebinary Erest]]]]]]]]]].
    assert (Hbinary_not_tag : is_tag (ms_binary Mcur) = false).
    { rewrite Ebinary. apply solver_shape_binary_not_tag. exact Hshape0. }
    assert (Hdb : db_wf anz_n (msolver_db Mcur)).
    { unfold msolver_db in *. rewrite Eprob, Elearnt. exact Hdb0. }
    destruct Hconflict as
      [[Hc [HC Hout]] | [co [Hnotbin [Hin HC]]]].
    + subst c. rewrite Hbinary_not_tag in H_is_tag. discriminate.
    + pose proof (db_wf_even anz_n (msolver_db Mcur) c co Hdb Hin) as Heven.
      pose proof (even_not_tag c Heven) as Hnottag.
      rewrite H_is_tag in Hnottag. discriminate.
  - cbn in Hphase.
    destruct Hphase as [S [R [learnt [x Hphase]]]].
    destruct Hphase as (Hpnot & Hx & HxS & Htrail & Hrank & Hmax & Hlit & Hcnt &
        Hcntpos & Hc & Hreason & Htarget & Hfocus & Hvalid & Hent & HCwf & HCnodup &
        Hainv & Hlearnt & Hperm).
    pose proof Hainv as Hainv'.
    destruct Hainv' as [_ [_ [HS Hainvrest]]].
    rewrite Forall_forall in HS.
    pose proof (HS x HxS) as Hxlevel.
    Exists R learnt x S.
    msat_manual_entailer_with ltac:(lia).
Qed.


