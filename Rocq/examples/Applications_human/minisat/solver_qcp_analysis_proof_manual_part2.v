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
Lemma proof_of_solver_analyze_which_implies_wit_3 : solver_analyze_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hsize : ms_size ?Msol = ?n |-
      solver_rep_analyze_at ?s ?Msol ?reasons ?levels ?trail ?tags ?wl |-- _ =>
      sep_apply (solver_rep_analyze_at_open
        s Msol n reasons levels trail tags wl Hsize)
  end.
  Intros activity orderpos.
  Exists activity orderpos.
  unfold msat_false.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_17 : solver_analyze_which_implies_wit_17.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mdone anz_focus words_done cnt ind Sdone Rdone
      learnt_done ) as H_analyze_backward_scan_inv.
  pose proof H_analyze_backward_scan_inv as Hscan.
  unfold analyze_backward_scan_inv in Hscan.
  destruct Hscan as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Hlits_done
    [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  repeat match goal with
  | |- _ |-- “ _ ” && _ =>
      apply _derivable1_andp_intros; [dump_pre_spatial; first [assumption | lia] | ]
  end.
  sep_apply (store_int_undef_store_int (&( "j")) j_addr_v).
  unfold solver_analyze_open_at.
  bind_fact ( clause_lits_pointer c lits ) as H_clause_lits_pointer.
  assert (Hstats_keep :
    solver_analyze_frame s Mdone anz_wl |--
      “ Zlength (ms_stats Mdone) = 11 ” &&
      solver_analyze_frame s Mdone anz_wl).
  {
    unfold solver_analyze_frame, solver_analyze_frame_cells, stats_analyze_frame.
    Intros asg. Exists asg. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  }
  sep_apply Hstats_keep.
  Intros_p Hstats.
  prop_apply_p (DoubleArray.seg_Zlength activity_ptr_done 0 anz_n
    (ms_activity Mdone)).
  Intros_p Hactivity_raw.
  assert (Hactivity : Zlength (ms_activity Mdone) = anz_n) by lia.
  destruct (analyze_backward_scan_shape_db _ _ _ _ _ _ _ _ _ _ _ _
    H_analyze_backward_scan_inv Hstats Hactivity) as [Hshape Hdb].
  pose proof (proj1 (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mdone anz_focus Hready)) as Hsize.
  unfold solver_analyze_frame at 1.
  cbv [solver_analyze_frame_cells].
  Intros asg.
  assert (Hbinary_nonneg_keep :
    (&(s # "solver_t" ->ₛ "binary")) # Ptr |-> ms_binary Mdone |--
      “ 0 <= ms_binary Mdone ” &&
      (&(s # "solver_t" ->ₛ "binary")) # Ptr |-> ms_binary Mdone).
  { unfold store_ptr, valid_ptr_value. unfold_arch. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]). }
  sep_apply Hbinary_nonneg_keep.
  Intros_p Hbinary_nonneg.
  pose proof (analysis_focus_clause_db_close anz_n Mdone c is_learnt2
    clause_words2 lits Hdb Hshape Hbinary_nonneg H_clause_lits_pointer)
    as Hfocus_close.
  pose proof (analyze_stats_frame_close s Mdone) as Hstats_close.
  unfold solver_analyze_inert_at.
  set (AH := clause_hdr_addr c # Int |->
    clause_hdr_word is_learnt2 (Zlength clause_words2)).
  set (AA := activity_state c is_learnt2 (Zlength clause_words2)).
  set (AS := IntArray.seg lits 0 (Zlength clause_words2) clause_words2).
  set (AR := analysis_clause_remainder Mdone c is_learnt2 clause_words2).
  set (ST := stats_analyze_frame &(s # "solver_t" ->ₛ "stats") (ms_stats Mdone)).
  set (SM := &(s # "solver_t" ->ₛ "stats" .ₛ "max_literals")
    # UInt64 |-> stats_max_literals (ms_stats Mdone)).
  set (SO := &(s # "solver_t" ->ₛ "stats" .ₛ "tot_literals")
    # UInt64 |-> stats_tot_literals (ms_stats Mdone)).
  assert (Hfocus_atoms : AH ** AA ** AS ** AR |--
    clause_db_rep (ms_prob Mdone) **
    clause_db_rep (ms_learnt Mdone) **
    binary_scratch_rep (ms_binary Mdone) (ms_binary_lits Mdone))
    by exact Hfocus_close.
  assert (Hstats_atoms : ST ** SM ** SO |--
    stats_rep &(s # "solver_t" ->ₛ "stats") (ms_stats Mdone))
    by exact Hstats_close.
  lazymatch goal with
  | |- ?P |-- _ =>
      let R3 := msat_sep_replace_atom_with_emp AH P in
      let R2 := msat_sep_replace_atom_with_emp AA R3 in
      let R3 := msat_sep_replace_atom_with_emp AS R2 in
      let R4 := msat_sep_replace_atom_with_emp AR R3 in
      let R5 := msat_sep_replace_atom_with_emp ST R4 in
      let R6 := msat_sep_replace_atom_with_emp SM R5 in
      let R7 := msat_sep_replace_atom_with_emp SO R6 in
      pose (analyze_close_rest := R7)
  end.
  lazymatch goal with
  | |- _ |-- ?T =>
      assert (Hcut : AH ** AA ** AS ** AR ** (ST ** SM ** SO) ** analyze_close_rest |-- T)
  end.
  { sep_apply Hfocus_atoms.
    sep_apply Hstats_atoms.
    unfold solver_rep_analyze_at, solver_rep_at.
    Exists activity_ptr_done asg orderpos_ptr_done.
    split_pure_spatial.
    - unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
        solver_scalars_rep, solver_fp_rep, solver_vecs_rep,
        solver_trail_array_rep.
      unfold analyze_close_rest.
      rewrite Hsize.
      unfold db_words.
      msat_cancel_sound.
      solve [ cancel | change (emp |-- emp); cancel | Intros; cancel ].
    - dump_pre_spatial. exact Hshape. }
  sep_apply_r_atomic Hcut.
  unfold analyze_close_rest.
  msat_cancel_sound.
  solve [ cancel | change (emp |-- emp); cancel | Intros; cancel ].
Qed.




Lemma proof_of_solver_lit_removable_entail_wit_9_split_goal_1 : solver_lit_removable_entail_wit_9_split_goal_1.
Abort.


Lemma proof_of_solver_lit_removable_entail_wit_9_split_goal_2 : solver_lit_removable_entail_wit_9_split_goal_2.
Abort.


Lemma proof_of_solver_lit_removable_entail_wit_9 : solver_lit_removable_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_rewrite (store_int_range (&("v")) retval_2).
  prop_rewrite (store_int_range (&("i")) i).
  prop_rewrite (store_int_range (&("v")) v).
  prop_rewrite (store_int_range (clause_hdr_addr c)
    (clause_hdr_word is_learnt_now (Zlength clause_words))).
  prop_rewrite (store_int_range (&("l")) l_pre).
  prop_rewrite (store_uint_range (&("minl")) minl_pre).
  prop_rewrite (store_int_range (&("top")) top).
  prop_rewrite (store_int_range (&(s_pre # "solver_t" ->ₛ "size")) lrm_n).
  replace (i - 0) with i in * by lia.
  entailer!.
  all: try lia.
  - replace Int.min_signed with (-2147483648) in H1 by reflexivity.
    apply Z.le_ge; exact (proj1 H1).
  - replace Int.min_signed with (-2147483648) in H2 by reflexivity.
    apply Z.le_ge; exact (proj1 H2).
  - replace Int.min_signed with (-2147483648) in H3 by reflexivity.
    apply Z.le_ge; exact (proj1 H3).
  - replace Int.min_signed with (-2147483648) in H5 by reflexivity.
    apply Z.le_ge; exact (proj1 H5).
Qed.


Lemma proof_of_solver_lit_removable_entail_wit_10_2 : solver_lit_removable_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  bind_fact ( top = Zlength (ms_tagged M0) ) as Htop.
  bind_fact ( lits = clause_lits_addr c ) as Hlits.
  bind_fact ( analysis_tags_exact lrm_n tags_scan tagged_scan ) as Htags.
  bind_fact ( removable_reason_scan_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan
    stack_scan tags_scan tagged_scan Cnext v c i ) as Hscan.
  replace (i - 0) with i in * by lia.
  replace (retval_3 - 0) with retval_3 in * by lia.
  assert (Hdfs : removable_dfs_loop_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) tags_scan tagged_scan (v :: stack_scan) done_scan)
    by (unfold removable_reason_scan_inv in Hscan; tauto).
  assert (Hrollback : removable_rollback_inv lrm_n top top (ms_tagged M0)
    (ms_tags M0) tags_scan tagged_scan tags_scan)
    by (eapply removable_rollback_start__lit_removable; eauto).
  assert (Htop0 : 0 <= top) by (rewrite Htop; apply Zlength_nonneg).
  assert (Hundef :
    ((&( "v")) # Int |-> retval_3) ** ((&( "i")) # Int |-> i) **
    ((&( "v")) # Int |-> v) ** ((&( "reasons")) # Ptr |-> reasons_ptr) **
    ((&( "levels")) # Ptr |-> levels_ptr) |--
    ((&( "v")) # Int |->_) ** ((&( "i")) # Int |->_) **
    ((&( "v")) # Int |->_) ** ((&( "reasons")) # Ptr |->_) **
    ((&( "levels")) # Ptr |->_))
    by (sep_apply (store_int_undef_store_int (&( "v")) retval_3);
        sep_apply (store_int_undef_store_int (&( "i")) i);
        sep_apply (store_int_undef_store_int (&( "v")) v);
        sep_apply (store_ptr_undef_store_ptr (&( "reasons")) reasons_ptr);
        sep_apply (store_ptr_undef_store_ptr (&( "levels")) levels_ptr);
        cancel).
  sep_apply Hundef.
  rewrite Hlits.
  destruct (Z_lt_ge_dec top (Zlength tagged_scan)) as [Hlt | Hge].
  - assert (Htagvar : 0 <= Znth top tagged_scan 0 < lrm_n)
      by (unfold analysis_tags_exact in Htags;
          destruct Htags as [_ [_ [Hbounds _]]];
          eapply Forall_Znth_elim; [exact Hbounds | lia]).
    Left. Exists tags_scan.
    msat_manual_entailer_with ltac:(lia).
  - assert (Htople : top <= Zlength tagged_scan)
      by (unfold removable_rollback_inv in Hrollback; tauto).
    assert (Htopeq : top = Zlength tagged_scan) by lia.
    Right. Exists tags_scan.
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_lit_removable_entail_wit_12_1 : solver_lit_removable_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( retval_3 = lit_var_c (Znth (i - 0) clause_words 0) ) as H_retval_3.
  bind_fact ( Znth retval_2 tags_scan_2 0 = 0 ) as H_Znth.
  bind_fact ( reason_target_wf lrm_n M0 retval_2 (Znth retval_2 (ms_reason_words M0) 0) Cpush ) as H_reason_target_wf.
  bind_fact ( retval_2 = lit_var_c (Znth (i - 0) clause_words 0) ) as H_retval_2.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( incl (v :: stack_scan_2) (map lit_var_c (mt_trail (ms_core M0))) ) as H_incl.
  bind_fact ( In (lit_var_c l_pre) (ms_tagged M0) ) as H_In.
  bind_fact ( removable_reason_scan_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan_2 stack_scan_2 tags_scan_2
      tagged_scan_2 Cnext v c i ) as H_removable_reason_scan_inv.
  bind_fact ( Cnext = lits_denote clause_words ) as H_Cnext.
  replace (i - 0) with i in * by lia.
  assert (Hsame : retval_3 = retval_2) by congruence.
  assert (Hxdef : retval_2 = literal_var (Znth i Cnext (Pos 0))).
  { rewrite H_Cnext. unfold lits_denote.
    rewrite (Znth_map Z literal lit_denote clause_words i 0 (Pos 0)) by lia.
    rewrite lit_var_c_denote. exact H_retval_2. }
  assert (Hneq : literal_var (Znth i Cnext (Pos 0)) <> v).
  { eapply removable_reason_scan_side_neq_untagged__lit_removable;
      [exact H_removable_reason_scan_inv | exact H_In | |].
    - rewrite <- Hxdef. lia.
    - rewrite <- Hxdef. exact H_Znth. }
  assert (Hbelow : assigned_below_current (msolver_view lrm_n M0) retval_2).
  { rewrite Hxdef.
    eapply removable_reason_scan_side_assigned_below__lit_removable;
      [exact H_analysis_cancel_ready | exact H_removable_reason_scan_inv | | exact Hneq].
    rewrite H_Cnext, lits_denote_length. lia. }
  assert (Hscan : removable_reason_scan_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) done_scan_2 (stack_scan_2 ++ retval_2 :: nil)
    (replace_Znth retval_2 1 tags_scan_2)
    (tagged_scan_2 ++ retval_2 :: nil) Cnext v c (i + 1)).
  { eapply removable_reason_scan_push_pending__lit_removable
      with (q := Znth retval_2 (ms_reason_words M0) 0) (Cx := Cpush).
    - exact H_removable_reason_scan_inv.
    - exact H_In.
    - rewrite H_Cnext, lits_denote_length. lia.
    - exact Hxdef.
    - lia.
    - exact H_Znth.
    - exact Hbelow.
    - exact H_reason_target_wf. }
  assert (Hincl : incl (v :: stack_scan_2 ++ retval_2 :: nil)
    (map lit_var_c (mt_trail (ms_core M0)))).
  { intros x [<- | Hx].
    - apply H_incl. left. reflexivity.
    - apply in_app_or in Hx. destruct Hx as [Hx | [<- | []]].
      + apply H_incl. right. exact Hx.
      + eapply assigned_below_in_trail__lit_removable.
        exact Hbelow. }
  assert (Htags : analysis_tags_exact lrm_n
    (replace_Znth retval_2 1 tags_scan_2)
    (tagged_scan_2 ++ retval_2 :: nil)).
  { unfold removable_reason_scan_inv in Hscan.
    destruct Hscan as [Hdfs _].
    unfold removable_dfs_loop_inv in Hdfs.
    destruct Hdfs as [fresh [_ [Hexact _]]].
    exact Hexact. }
  subst retval_3.
  rewrite Hsame.
  Exists done_scan_2
    (stack_scan_2 ++ retval_2 :: nil)
    (replace_Znth retval_2 1 tags_scan_2)
    (tagged_scan_2 ++ retval_2 :: nil).
  sep_apply_l_atomic
    (CharArray.full_to_seg tags_ptr lrm_n
      (replace_Znth retval_2 1 tags_scan_2)).
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_12_split_goal_1 : solver_lit_removable_which_implies_wit_12_split_goal_1.
Abort.


Lemma proof_of_solver_lit_removable_which_implies_wit_12_split_goal_2 : solver_lit_removable_which_implies_wit_12_split_goal_2.
Abort.


Lemma proof_of_solver_lit_removable_which_implies_wit_12 : solver_lit_removable_which_implies_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus) as Hready.
  bind_fact (removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0)
    tags_now tagged_now stack_now done) as Hinv.
  pose proof Hinv as Hinv_copy.
  destruct (analysis_cancel_ready_reason_core
    lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus Hready) as [Hsize _].
  destruct Hinv_copy as [fresh [_ [_ [_ [Hnodup [_ [_ [Htargets _]]]]]]]].
  assert (Hnodup_stack : NoDup stack_now)
    by (eapply NoDup_app_remove_l; exact Hnodup).
  pose proof (msat_reason_target_stack_var_range
    lrm_n M0 stack_now Hsize Htargets) as Hbounded.
  assert (Hn : 0 <= lrm_n)
    by (assert (Hin : In (Znth (Zlength stack_now - 1) stack_now 0) stack_now)
          by (apply Znth_In; lia);
        pose proof (Hbounded _ Hin); lia).
  pose proof (NoDup_Z_bounded_length
    stack_now lrm_n Hn Hnodup_stack Hbounded) as Hlen.
  rewrite <- Zlength_correct in Hlen.
  assert (Hafterlen : Zlength stack_after = Zlength stack_now - 1)
    by (rewrite PreH4; rewrite Zlength_sublist by lia; lia).
  entailer!.
  assert (Hcat :
    Zlength (stack_after ++ (Znth (Zlength stack_now - 1) stack_now 0 :: nil)) =
      Zlength stack_now)
    by (rewrite Zlength_app, Hafterlen;
        rewrite Zlength_cons, Zlength_nil; lia).
  rewrite Zlength_sublist by lia; lia.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_15 : solver_lit_removable_which_implies_wit_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
    bind_fact ( removable_reason_scan_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan stack_scan tags_scan
      tagged_scan Cnext v c i ) as H_removable_reason_scan_inv.
  destruct (analysis_cancel_ready_reason_core
    lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready) as [Hsize _].
  pose proof
    (removable_scan_stack_strict__lit_removable
      lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan stack_scan
      tags_scan tagged_scan Cnext v c i H_removable_reason_scan_inv Hsize) as Hstrict.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_16_split_goal_1 : solver_lit_removable_which_implies_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: bind_fact ( Forall (lit_wf_c lrm_n) clause_words ) as H_Forall.
  all: bind_fact ( 0 <= i ) as H_i.
  all: bind_fact ( i < Zlength clause_words ) as H_i_2.
  all: pose proof (Forall_Znth_elim Z (lit_wf_c lrm_n) clause_words 0 i
    H_Forall (conj H_i H_i_2)) as Hlit.
  all: pose proof (lit_var_c_in_range lrm_n (Znth i clause_words 0) Hlit) as Hrange.
  all: lia.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_16_split_goal_2 : solver_lit_removable_which_implies_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: bind_fact ( Forall (lit_wf_c lrm_n) clause_words ) as H_Forall.
  all: bind_fact ( 0 <= i ) as H_i.
  all: bind_fact ( i < Zlength clause_words ) as H_i_2.
  all: pose proof (Forall_Znth_elim Z (lit_wf_c lrm_n) clause_words 0 i
    H_Forall (conj H_i H_i_2)) as Hlit.
  all: pose proof (lit_var_c_in_range lrm_n (Znth i clause_words 0) Hlit) as Hrange.
  all: lia.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_16 : solver_lit_removable_which_implies_wit_16.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_solver_lit_removable_which_implies_wit_16_split_goal_1 lrm_n clause_words i PreH1 PreH2 PreH3).
- Goal_apply (proof_of_solver_lit_removable_which_implies_wit_16_split_goal_2 lrm_n clause_words i PreH1 PreH2 PreH3).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_20_split_goal_spatial : solver_lit_removable_which_implies_wit_20_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst lits.
  bind_fact ( c % 2 = 0 ) as H_c.
  unfold MiniSatClause.rep.
  pose proof (Zlength_nonneg clause_words).
  assert (Hmod : c mod 2 = 0).
  { apply Z.mod_divide; [lia |].
    apply Z.rem_divide; [lia | exact H_c]. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_20 : solver_lit_removable_which_implies_wit_20.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_lit_removable_which_implies_wit_20_split_goal_spatial M0 is_learnt_now clause_words c lits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_35 : solver_analyze_which_implies_wit_35.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply solver_rep_analyze_join_levels_at.
  sep_apply (store_ptr_undef_store_ptr (&("tags"))).
  sep_apply (store_ptr_undef_store_ptr (&("trail"))).
  sep_apply (store_ptr_undef_store_ptr (&("reasons"))).
  cancel.
Qed.



Lemma proof_of_solver_lit_removable_safety_wit_8 : solver_lit_removable_safety_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Veci.rep_ptr_bounds (&((s_pre) # "solver_t" ->ₛ "stack")) p stack_now).
  Intros.
  split_pures; dump_pre_spatial; lia.
Qed.




Lemma proof_of_solver_analyze_entail_wit_12_11_learnt : solver_analyze_entail_wit_12_11_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_4 - 0) (ms_tags Mscan_2) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_4 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_4.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( 0 <= lit_var_c (Znth (j - 0) clause_words2 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth (j - 0) clause_words2 0) < anz_n ) as H_lit_var_c_2.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  set (q := Znth j clause_words2 0).
  set (v := lit_var_c q).
  assert (Eqv : literal_var (lit_denote q) = v).
  { rewrite lit_var_c_denote. reflexivity. }
  assert (Htags : analysis_tags_exact anz_n (ms_tags Mscan_2)
      (ms_tagged Mscan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hperm : Permutation (ms_tagged Mscan_2)
      (analyze_tags Sscan_2 Rscan_2 learnt_scan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (HS : Sscan_2 = analyze_start_S (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HR : Rscan_2 = nil) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HL : learnt_scan_2 = analyze_start_learnt (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HndC : NoDup (map literal_var Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hv : 0 <= v < anz_n).
  { unfold v, q. replace (j - 0) with j in H_lit_var_c, H_lit_var_c_2 by lia. lia. }
  assert (Hseen : In v (ms_tagged Mscan_2)).
  { eapply analysis_tags_exact_nonzero_in__lit_removable;
      [exact Htags | exact Hv |].
    intro Hzero. apply H_Znth.
    rewrite H_retval_4, !Z.sub_0_r. exact Hzero. }
  pose proof (Permutation_in v Hperm Hseen) as HinAnalyze.
  assert (HinPrefix : In v (map literal_var (sublist 0 j Ccur))).
  { rewrite HS, HR, HL in HinAnalyze.
    unfold analyze_tags, analyze_start_S, analyze_start_learnt in HinAnalyze.
    cbn in HinAnalyze. rewrite !in_app_iff in HinAnalyze.
    destruct HinAnalyze as [HinS|HinL].
    - apply in_map_iff in HinS. destruct HinS as [l [<- Hl]].
      apply filter_In in Hl. destruct Hl as [Hl _].
      apply in_map. exact Hl.
    - apply in_map_iff in HinL. destruct HinL as [l [<- Hl]].
      apply filter_In in Hl. destruct Hl as [Hl _].
      apply in_map. exact Hl. }
  assert (Hprefix : sublist 0 (j + 1) Ccur =
      sublist 0 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 0 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
  assert (HndSub : NoDup (map literal_var (sublist 0 (j + 1) Ccur))).
  { unfold sublist. cbn. pose proof HndC as Hndpre.
    rewrite <- (firstn_skipn (Z.to_nat (j + 1)) Ccur) in Hndpre.
    rewrite map_app in Hndpre.
    eapply NoDup_app_remove_r. exact Hndpre. }
  rewrite Hprefix, map_app in HndSub. cbn in HndSub. rewrite Eqv in HndSub.
  pose proof (NoDup_app_disjoint _ _ v HndSub HinPrefix) as Hdis.
  exfalso. apply Hdis. simpl. tauto.
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_15_learnt : solver_analyze_entail_wit_12_15_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  unfold solver_analyze_open_at in *.
  Right.
  Exists activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2
    words_scan_2 Mscan_2.
  split_pure_spatial.
  - msat_cancel_sound; cancel.
  - split_pures; dump_pre_spatial; try solve [auto | lia].
    unfold analyze_clause_scan_inv in *.
    subst phase j Mact.
    cbn in *.
    match goal with
    | Hbundle0 : analysis_cancel_ready anz_n anz_F anz_A_arr K Mscan_2 anz_focus /\ _ |- _ =>
        rename Hbundle0 into Hbundle_scan
    end.
    pose proof Hbundle_scan as Hscan_facts.
    decompose [and] Hscan_facts.
    assert (Hrootnonneg : 0 <= ms_root_level Mscan_2).
    { match goal with
      | Hready0 : analysis_cancel_ready anz_n anz_F anz_A_arr K Mscan_2 anz_focus |- _ =>
          pose proof Hready0 as Hready
      end.
      destruct Hready as [Mready [Hcancel [Hequiv _]]].
      destruct Hcancel as [Hweak _].
      destruct Hweak as [_ Hinv].
      assert (Hrootready : 0 <= ms_root_level Mready).
      { destruct K.
        - pose proof (msw_shape Hinv) as Hshape.
          unfold solver_shape in Hshape. tauto.
        - pose proof (msa_shape Hinv) as Hshape.
          unfold solver_shape in Hshape. tauto. }
      unfold analysis_core_equiv in Hequiv.
      destruct Hequiv as [_ [_ [_ [_ [Eroot _]]]]].
      rewrite Eroot. exact Hrootready. }
    assert (Hwf : mtrail_wf anz_n (ms_core Mscan_2)) by
      (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
    pose proof (msat_msolver_view_level_cell anz_n Mscan_2 Hwf) as Hlevelcell.
    assert (HClen : Zlength Ccur = Zlength clause_words2).
    { match goal with
      | HCwords : Ccur = lits_denote clause_words2 |- _ =>
          rewrite HCwords, lits_denote_length
      end. reflexivity. }
    assert (HCsingle :
      sublist 1 2 Ccur = Znth 1 Ccur (Pos 0) :: nil).
    { replace 2 with (1 + 1) by lia. apply sublist_single. lia. }
    assert (Hqnth :
      Znth 1 Ccur (Pos 0) = lit_denote (Znth 1 clause_words2 0)).
    { match goal with
      | HCwords : Ccur = lits_denote clause_words2 |- _ => rewrite HCwords
      end. unfold lits_denote.
      apply Znth_map. lia. }
    assert (Hlevxcur :
      level_of (msolver_view anz_n Mscan_2) x_2 =
        Some (current_level (msolver_view anz_n Mscan_2))).
    { match goal with
      | Hinv0 : analyze_inv anz_F (msolver_view anz_n Mscan_2)
          S0_2 R0_2 learnt0_2 |- _ =>
          destruct Hinv0 as [_ [_ [HlevS _]]]
      end.
      rewrite Forall_forall in HlevS. apply HlevS. assumption. }
    match goal with
    | Hrv : reason_valid (msolver_view anz_n Mscan_2) x_2 Ccur |- _ =>
        destruct Hrv as
          [b [d [r [Hass [Hlevx [Hrank [Hsat Hside]]]]]]]
    end.
    assert (HqIn : In (Znth 1 Ccur (Pos 0)) Ccur).
    { apply Znth_In. lia. }
    assert (Hqraw :
      Znth (literal_var (Znth 1 Ccur (Pos 0)))
        (mt_levels (ms_core Mscan_2)) 0 <= 0).
    { rewrite Hqnth, lit_var_c_denote.
      match goal with
      | Hraw0 : Znth (?rv - 0) (mt_levels (ms_core Mscan_2)) 0 <= 0,
        Heq0 : ?rv = lit_var_c (Znth 1 clause_words2 0) |- _ =>
          rewrite <- Heq0;
          replace rv with (rv - 0) by lia;
          exact Hraw0
      end. }
    assert (Hqneq : literal_var (Znth 1 Ccur (Pos 0)) <> x_2).
    { intro Heq. rewrite Heq in Hqraw.
      pose proof (Hlevelcell x_2
        (current_level (msolver_view anz_n Mscan_2)) Hlevxcur) as Hxcell.
      rewrite Hxcell, msolver_view_current_level in Hqraw. lia. }
    destruct (Hside _ HqIn Hqneq) as
      [_ [dy [ry [Hqlevel [Hqrank [Hdyle Hry]]]]]].
    pose proof (Hlevelcell
      (literal_var (Znth 1 Ccur (Pos 0))) dy Hqlevel) as Hqcell.
    rewrite Hqcell in Hqraw.
    assert (Hat : at_current_level_b (msolver_view anz_n Mscan_2)
      (Znth 1 Ccur (Pos 0)) = false).
    { unfold at_current_level_b. rewrite Hqlevel.
      apply Z.eqb_neq. rewrite msolver_view_current_level. lia. }
    assert (Hbelow : below_current_b (msolver_view anz_n Mscan_2)
      (Znth 1 Ccur (Pos 0)) = false).
    { unfold below_current_b. rewrite Hqlevel.
      destruct (Z.ltb 0 dy) eqn:Hdypos.
      - apply Z.ltb_lt in Hdypos. lia.
      - reflexivity. }
    intuition (try lia).
    + match goal with
      | Hbase0 : Sscan_2 = resolve_S (msolver_view anz_n Mscan_2) x_2
          (skipn (Pos.to_nat 1) (firstn (Pos.to_nat 1) Ccur))
          S0_2 R0_2 learnt0_2 |- _ => pose proof Hbase0 as Hbase
      end.
      change (Sscan_2 = resolve_S (msolver_view anz_n Mscan_2) x_2
        (sublist 1 1 Ccur) S0_2 R0_2 learnt0_2) in Hbase.
      rewrite (Zsublist_nil Ccur 1 1) in Hbase by lia.
      change (Sscan_2 = resolve_S (msolver_view anz_n Mscan_2) x_2
        (sublist 1 2 Ccur) S0_2 R0_2 learnt0_2).
      rewrite HCsingle.
      unfold resolve_S, resolve_new_S. cbn [filter map].
      rewrite Hat. cbn.
      exact Hbase.
    + match goal with
      | Hbase0 : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mscan_2)
          (skipn (Pos.to_nat 1) (firstn (Pos.to_nat 1) Ccur))
          S0_2 R0_2 learnt0_2 |- _ => pose proof Hbase0 as Hbase
      end.
      change (learnt_scan_2 = resolve_learnt (msolver_view anz_n Mscan_2)
        (sublist 1 1 Ccur) S0_2 R0_2 learnt0_2) in Hbase.
      rewrite (Zsublist_nil Ccur 1 1) in Hbase by lia.
      change (learnt_scan_2 = resolve_learnt (msolver_view anz_n Mscan_2)
        (sublist 1 2 Ccur) S0_2 R0_2 learnt0_2).
      rewrite HCsingle.
      unfold resolve_learnt, resolve_new_lits. cbn [filter].
      rewrite Hbelow. cbn.
      exact Hbase.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_12_pure : solver_analyze_partial_solve_wit_12_pure.
Proof.
  msat_analyze_reason_target_lit_bound.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_58_learnt_pure : solver_analyze_partial_solve_wit_58_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  msat_analyze_word_range_context anz_n j clause_words2.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_73_learnt_pure : solver_analyze_partial_solve_wit_73_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_word_range_context anz_n j clause_words2.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_78_learnt_pure : solver_analyze_partial_solve_wit_78_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_clause_word_int_range_via_wf j clause_words2 Hlit.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_80_learnt_pure : solver_analyze_partial_solve_wit_80_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_word_range_context anz_n j clause_words2.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_86_learnt_pure : solver_analyze_partial_solve_wit_86_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_learnt_offset_congruence.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_93_learnt_pure : solver_analyze_partial_solve_wit_93_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_clause_word_int_range_via_wf j clause_words2 Hlit.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_190_pure : solver_analyze_partial_solve_wit_190_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hindex : 0 <= i - 0 < Zlength words_compact) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 (i - 0) PreH7 Hindex) as Hlit.
  unfold lit_wf_c in Hlit.
  match goal with
  | Hready : analysis_cancel_ready _ _ _ _ _ _ |- _ => pose proof Hready as Hready0
  end.
  unfold analysis_cancel_ready in Hready0.
  destruct Hready0 as [Mbase [Hprop [Hequiv _]]].
  unfold propagation_cancel_ready in Hprop.
  destruct Hprop as [Hweak _].
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as [_ Hweak].
  assert (Htwo_n : 2 * anz_n <= INT_MAX) by
    (destruct K as [A_inst | A_proc]; cbn in Hweak;
     [ pose proof (msw_shape Hweak) as Hshape;
       pose proof (msw_size Hweak) as Hsize;
       unfold solver_shape in Hshape;
       destruct Hshape as [_ [_ [Htwo _]]];
       rewrite Hsize; exact Htwo
     | pose proof (msa_shape Hweak) as Hshape;
       pose proof (msa_size Hweak) as Hsize;
       unfold solver_shape in Hshape;
       destruct Hshape as [_ [_ [Htwo _]]];
       rewrite Hsize; exact Htwo ]).
  split_pures; dump_pre_spatial; lia.
Qed.



Lemma proof_of_solver_analyze_safety_wit_13 : solver_analyze_safety_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  lazymatch goal with
  | H : Permutation (ms_tagged Mcur_2) (analyze_tags ?pending ?resolved ?learnt) |- _ =>
      pose proof (Zlength_perm_eq Z _ _ H) as Hlen;
      unfold analyze_tags in Hlen;
      rewrite !Zlength_app in Hlen;
      pose proof (Zlength_nonneg resolved);
      pose proof (Zlength_nonneg (map literal_var learnt))
  end.
  assert (Hbounds : cnt + 1 <= INT_MAX /\ INT_MIN <= cnt + 1) by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_safety_wit_46_learnt : solver_analyze_safety_wit_46_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pures.
 - dump_pre_spatial.
   msat_analyze_bound_scan_index_by_nodup anz_n Ccur j Hinv clause_words2.
 - dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_analyze_safety_wit_65 : solver_analyze_safety_wit_65.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmask :
    Z.land (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0) 31 <= 31 /\
    0 <= Z.land (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0) 31).
  { assert (Hland :
      Z.land (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0) 31 =
      Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0 mod 32).
    { change
        (Z.land (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0)
          (Z.ones 5) =
         Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0 mod 2 ^ 5).
      apply Z.land_ones. lia. }
    rewrite Hland.
    pose proof (Z.mod_pos_bound
      (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0) 32 ltac:(lia))
      as Hmod_bound.
    split; lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_18 : solver_analyze_which_implies_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hsize : ms_size ?Msol = ?n |-
      solver_rep_analyze_at ?s ?Msol ?reasons ?levels ?trail ?tags ?wl |-- _ =>
      sep_apply (solver_rep_analyze_at_open
        s Msol n reasons levels trail tags wl Hsize)
  end.
  Intros activity orderpos.
  Exists activity orderpos.
  unfold msat_false.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_27 : solver_analyze_which_implies_wit_27.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( msolver_seed_shadow Mmin_done ) as H_msolver_seed_shadow.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mmin_done anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analysis_tags_exact anz_n (ms_tags Mmin_done) (ms_tagged Mmin_done) ) as H_analysis_tags_exact.
  bind_fact ( analyze_clause_cert anz_n anz_F Mmin_done words_uip ) as H_analyze_clause_cert.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_done words_uip kept_done removed_done words_done T_done i j ) as
      H_analyze_minimize_loop_inv.
  set (stats_upd := replace_Znth 9 max_lits
    (replace_Znth 10 tot_lits (ms_stats Mmin_done))).
  set (Mstats_upd := msolver_with_cla_inc_stats Mmin_done
    (ms_cla_inc Mmin_done) stats_upd).
  assert (Hcore : analysis_core_equiv M0 Mstats_upd).
  { subst Mstats_upd. unfold analysis_core_equiv,
      msolver_with_cla_inc_stats in *.
    cbn in *. tauto. }
  assert (Hseed : msolver_seed_shadow Mstats_upd).
  { subst Mstats_upd. unfold msolver_seed_shadow,
      msolver_with_cla_inc_stats. cbn. exact H_msolver_seed_shadow. }
  assert (Hcancel : analysis_cancel_ready anz_n anz_F anz_A_arr K Mstats_upd anz_focus).
  { subst Mstats_upd. cbn [msolver_with_cla_inc_stats]. exact H_analysis_cancel_ready. }
  assert (Htags : analysis_tags_exact anz_n (ms_tags Mstats_upd)
      (ms_tagged Mstats_upd)).
  { subst Mstats_upd. cbn [msolver_with_cla_inc_stats]. exact H_analysis_tags_exact. }
  assert (Hcert : analyze_clause_cert anz_n anz_F Mstats_upd words_uip).
  { subst Mstats_upd. cbn [msolver_with_cla_inc_stats]. exact H_analyze_clause_cert. }
  assert (Hloop : analyze_minimize_loop_inv anz_n Mstats_upd words_uip
      kept_done removed_done words_done T_done i j).
  { subst Mstats_upd. cbn [msolver_with_cla_inc_stats]. exact H_analyze_minimize_loop_inv. }
  Exists Mstats_upd.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_literal_stats_frame_at.
  cancel.
  Intros act asg opos.
  cancel.
  assert (Hstats_len : Zlength (ms_stats Mmin_done) = 11).
  { unfold solver_shape in H; tauto. }
  assert (Hznth : forall k, 0 <= k < 9 ->
    Znth k stats_upd 0 = Znth k (ms_stats Mmin_done) 0).
  { unfold stats_upd.
    exact (proj1 (stats_pair_update_slots (ms_stats Mmin_done)
      max_lits tot_lits Hstats_len)). }
  cancel.
  Exists act asg opos.
  split_pure_spatial.
  - unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at.
    cbn.
    assert (Hsc : solver_scalars_rep s Mstats_upd =
        solver_scalars_rep s Mmin_done).
    { unfold solver_scalars_rep, Mstats_upd,
        msolver_with_cla_inc_stats. cbn. reflexivity. }
    rewrite Hsc.
    cancel.
    assert (Hfp : solver_fp_rep s Mstats_upd =
        solver_fp_rep s Mmin_done).
    { unfold solver_fp_rep, Mstats_upd,
        msolver_with_cla_inc_stats. cbn. reflexivity. }
    rewrite Hfp.
    cancel.
    assert (Hvec : solver_vecs_rep s Mstats_upd =
        solver_vecs_rep s Mmin_done).
    { unfold solver_vecs_rep, Mstats_upd,
        msolver_with_cla_inc_stats. cbn. reflexivity. }
    rewrite Hvec.
    cancel.
    set (P8 :=
      &(s # "solver_t" ->ₛ "wlists") # Ptr |-> anz_wl **
      &(s # "solver_t" ->ₛ "activity") # Ptr |-> act **
      &(s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
      &(s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
      &(s # "solver_t" ->ₛ "reasons") # Ptr |-> reasons **
      &(s # "solver_t" ->ₛ "trail") # Ptr |-> trail **
      &(s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary Mmin_done **
      &(s # "solver_t" ->ₛ "tags") # Ptr |-> tags).
    set (A0tail :=
      PtrArray.seg reasons 0 (ms_size Mmin_done)
        (ms_reason_words Mmin_done) **
      PtrArray.undef_seg reasons (ms_size Mmin_done) (ms_cap Mmin_done) **
      CharArray.seg tags 0 (ms_size Mmin_done) (ms_tags Mmin_done) **
      CharArray.undef_seg tags (ms_size Mmin_done) (ms_cap Mmin_done)).
    set (A0 :=
      DoubleArray.seg act 0 (ms_size Mmin_done) (ms_activity Mmin_done) **
      DoubleArray.undef_seg act (ms_size Mmin_done) (ms_cap Mmin_done) **
      CharArray.seg asg 0 (ms_size Mmin_done)
        (mt_assigns (ms_core Mmin_done)) **
      CharArray.undef_seg asg (ms_size Mmin_done) (ms_cap Mmin_done) **
      IntArray.seg opos 0 (ms_size Mmin_done) (ms_orderpos Mmin_done) **
      IntArray.undef_seg opos (ms_size Mmin_done) (ms_cap Mmin_done) **
      A0tail).
    set (L0 :=
      &(s # "solver_t" ->ₛ "levels") # Ptr |-> levels **
      IntArray.seg levels 0 (ms_size Mmin_done)
        (mt_levels (ms_core Mmin_done)) **
      IntArray.undef_seg levels (ms_size Mmin_done) (ms_cap Mmin_done)).
    assert (Htrail : solver_trail_array_rep Mstats_upd trail =
        solver_trail_array_rep Mmin_done trail).
    { unfold solver_trail_array_rep, Mstats_upd,
        msolver_with_cla_inc_stats. cbn. reflexivity. }
    assert (Hmax_slot : Znth 9 stats_upd 0 = max_lits).
    { unfold stats_upd.
      exact (proj1 (proj2 (stats_pair_update_slots (ms_stats Mmin_done)
        max_lits tot_lits Hstats_len))). }
    assert (Htot_slot : Znth 10 stats_upd 0 = tot_lits).
    { unfold stats_upd.
      exact (proj2 (proj2 (stats_pair_update_slots (ms_stats Mmin_done)
        max_lits tot_lits Hstats_len))). }
    set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
    assert (Hmax_addr :
        &(s # "solver_t" ->ₛ "stats" .ₛ "max_literals") =
        &(stats_ptr # "stats_t" ->ₛ "max_literals"))
      by (unfold stats_ptr; csimpl; reflexivity).
    assert (Htot_addr :
        &(s # "solver_t" ->ₛ "stats" .ₛ "tot_literals") =
        &(stats_ptr # "stats_t" ->ₛ "tot_literals"))
      by (unfold stats_ptr; csimpl; reflexivity).
    unfold stats_rep, stats_analyze_frame, stats_starts, stats_decisions, stats_propagations, stats_inspects,
      stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
      stats_learnts_literals, stats_max_literals, stats_tot_literals.
    rewrite !Hznth by lia.
    rewrite Hmax_slot, Htot_slot.
    unfold stats_upd. rewrite !Zlength_replace_Znth.
    msat_cancel_sound.

    rewrite Htrail.
    rewrite Hmax_addr, Htot_addr.
    unfold P8, A0, A0tail, L0, solver_ptrs_rep,
      solver_var_arrays_rep.
    unfold DoubleArray.seg, IntArray.seg, PtrArray.seg, CharArray.seg.
    unfold StoreDoubleAsElement.storeA, StoreIntAsElement.storeA,
      StorePtrAsElement.storeA, StoreCharAsElement.storeA.
    unfold store_double.
    unfold bits_of_double_value.
    cbn.
    msat_cancel_sound.
    msat_manual_entailer_with ltac:(lia).
  - dump_pre_spatial.
    assert (Hlen_upd : Zlength stats_upd = 11).
    { unfold stats_upd. rewrite !Zlength_replace_Znth.
      exact Hstats_len. }
    unfold solver_shape in H |- *.
    cbn in *.
    rewrite Hlen_upd.
    tauto.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_27_pure : solver_lit_removable_partial_solve_wit_27_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now - 1) stack_now 0) (Znth (Znth (Zlength
      stack_now - 1) stack_now 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  bind_fact ( is_tag (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) = msat_true ) as H_is_tag.
  bind_fact ( retval = Zlength stack_now ) as H_retval.
  rewrite H_retval.
  unfold removable_reason_focus, reason_target_wf, tagged_word in *.
  destruct H_removable_reason_focus as [_ [_ [_ [_ Hkind]]]].
  destruct Hkind as [[Htag [Hpositive Hlit]] | [co [Htag [_ [_ _]]]]].
  - unfold lit_wf_c in Hlit.
    split_pures;
    (dump_pre_spatial;
     lazymatch goal with
     | |- is_tag _ = _ => exact Htag
     | |- _ => lia
     end).
  - unfold msat_true in H_is_tag.
    rewrite Htag in H_is_tag. discriminate.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_43_pure : solver_lit_removable_partial_solve_wit_43_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( removable_rollback_inv lrm_n top j (ms_tagged M0) (ms_tags M0) tags_now tagged_now tags_rollback ) as
      H_removable_rollback_inv.
  unfold removable_rollback_inv in H_removable_rollback_inv.
  split_pures;
    pose proof (Zlength_nonneg (ms_tagged M0)); dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_46_pure : solver_lit_removable_partial_solve_wit_46_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply clause_hdr_word_nonneg.
  apply Zlength_nonneg.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_7 : solver_lit_removable_which_implies_wit_7.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
    bind_fact ( removable_reason_focus lrm_n M0 v c Cnext ) as H_removable_reason_focus;
    bind_fact ( is_tag c = msat_true ) as H_is_tag;
    pose proof
    (removable_reason_focus_tag_range__lit_removable
      lrm_n M0 v c Cnext H_removable_reason_focus H_is_tag) as Hrange;
    destruct Hrange as [Hlo Hhi];
    msat_manual_entailer_with ltac:(lia).
Qed.


