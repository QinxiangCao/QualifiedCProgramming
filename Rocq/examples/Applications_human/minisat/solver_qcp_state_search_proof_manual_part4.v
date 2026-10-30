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
Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_state_search_proof_manual_part3.

Lemma proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst l_pre.
  prop_rewrite (store_int_range (&( "l")) l0).
  Intros_p Hl_range.
  change (-2147483648 <= l0 <= 2147483647) in Hl_range.
  subst retval.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_enqueue_return_wit_5 : enqueue_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (retval_2 = lit_sign_c l_pre) as Hrv.
  try rewrite replace_Znth_Znth in *.
  assert (Hsig : lit_sig l0 = 1)
    by (subst l_pre; unfold lit_sign_c in Hrv; unfold lit_sig;
        destruct (Z.odd l0); lia).
  destruct (Z.eq_dec (Znth (lit_var_c l0) assigns 0) (lit_sig l0))
    as [Heq | Heq];
  msat_enqueue_assign_frame qtail assigns levels0 reasons0 trail rsn trl asg n Hsig Heq;
  lazymatch type of Heq with
  | _ <> _ => right; left
  | _ = _ => left
  end;
  solve [repeat split; auto; lia].
Qed.


Lemma proof_of_enqueue_return_wit_6 : enqueue_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_enqueue_assign_keep_close 1 retval_2 l_pre l0 assigns qtail levels0 reasons0 trail rsn trl asg n.
Qed.


Lemma proof_of_enqueue_partial_solve_wit_5_pure : enqueue_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (enqueue_input n l0 qtail assigns levels0 reasons0 trail) as Hin.
  unfold enqueue_input, lit_wf_c in Hin.
  destruct Hin as (Hlit & _).
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_enqueue_which_implies_wit_3_split_goal_spatial : enqueue_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (lit_var_c l0) assigns 0 = 0 ) as H_Znth.
  bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as (Hlit & Htwice & Hassigns & Hlevels & Hreasons &
    Htrail & Hqtail & Hroom & Hvals).
  assert (Hrange : 0 <= lit_var_c l0 < n)
    by (apply lit_var_c_in_range; exact Hlit).
  assert (Htail : qtail < n)
    by (apply Hroom; exact H_Znth).
  sep_apply_l_atomic
    (IntArray.seg_split_to_missing_i lvl 0 (lit_var_c l0) n levels0 0).
  - dump_pre_spatial. exact Hrange.
  - sep_apply_l_atomic
      (PtrArray.seg_split_to_missing_i rsn 0 (lit_var_c l0) n reasons0 0).
    + dump_pre_spatial. exact Hrange.
    + replace (lit_var_c l0 - 0) with (lit_var_c l0) by lia.
      msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_enqueue_which_implies_wit_3_split_goal_1 : enqueue_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (lit_var_c l0) assigns 0 = 0 ) as H_Znth.
  bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as (Hlit & Htwice & Hassigns & Hlevels & Hreasons &
    Htrail & Hqtail & Hroom & Hvals).
  assert (Hrange : 0 <= lit_var_c l0 < n)
    by (apply lit_var_c_in_range; exact Hlit).
  assert (Htail : qtail < n)
    by (apply Hroom; exact H_Znth).
  dump_pre_spatial; lia.
Qed.


Lemma proof_of_enqueue_which_implies_wit_3_split_goal_2 : enqueue_which_implies_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (lit_var_c l0) assigns 0 = 0 ) as H_Znth.
  bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as (Hlit & Htwice & Hassigns & Hlevels & Hreasons &
    Htrail & Hqtail & Hroom & Hvals).
  assert (Hrange : 0 <= lit_var_c l0 < n)
    by (apply lit_var_c_in_range; exact Hlit).
  assert (Htail : qtail < n)
    by (apply Hroom; exact H_Znth).
  dump_pre_spatial; lia.
Qed.


Lemma proof_of_enqueue_which_implies_wit_3_split_goal_3 : enqueue_which_implies_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (lit_var_c l0) assigns 0 = 0 ) as H_Znth.
  bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as (Hlit & Htwice & Hassigns & Hlevels & Hreasons &
    Htrail & Hqtail & Hroom & Hvals).
  assert (Hrange : 0 <= lit_var_c l0 < n)
    by (apply lit_var_c_in_range; exact Hlit).
  assert (Htail : qtail < n)
    by (apply Hroom; exact H_Znth).
  dump_pre_spatial; lia.
Qed.


Lemma proof_of_enqueue_which_implies_wit_3 : enqueue_which_implies_wit_3.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_enqueue_which_implies_wit_3_split_goal_spatial trail reasons0 levels0 assigns l0 qtail cap n lvl rsn trl physical PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
- Goal_apply (proof_of_enqueue_which_implies_wit_3_split_goal_1 trail reasons0 levels0 assigns l0 qtail cap n lvl rsn trl physical PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
- Goal_apply (proof_of_enqueue_which_implies_wit_3_split_goal_2 trail reasons0 levels0 assigns l0 qtail cap n lvl rsn trl physical PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
- Goal_apply (proof_of_enqueue_which_implies_wit_3_split_goal_3 trail reasons0 levels0 assigns l0 qtail cap n lvl rsn trl physical PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
Qed.


Lemma proof_of_solver_addclause_entail_wit_4_2 : solver_addclause_entail_wit_4_2.
Proof.
  (* The comparison guard is false: here [pre] is non-empty and l
     is inserted after it.  The invariant does not record [Forall (y <= l) pre];
     it comes from the break condition, which compares the LAST element of the
     sorted prefix -- [Znth (Zlength pre - 1) (pre ++ _) 0] is [last pre 0] for
     ANY tail, which is what lets the array's spelling and the invariant's
     spelling meet. *)
  LLM_pre_process ltac:(lia || int_auto).
  replace (p - 1) with (p + -1 - 0) in * by lia.
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  match goal with H : addclause_sort_inner_inv _ _ _ _ |- _ =>
    pose proof (conj I H) as Hin end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout]; destruct Hin as [_ Hin].
  subst arr.
  assert (Hne : pre <> nil)
    by (intro Hn; rewrite Hn in *; rewrite Zlength_nil in *; lia).
  assert (Hlast : last pre 0 <= l).
  { rewrite <- (Znth_pred_app_last pre (junk :: suf ++ rest2) 0 Hne).
    replace (Zlength pre - 1) with (p + -1 - 0) by lia.
    assumption. }
  assert (Hple : Forall (fun y => y <= l) pre)
    by (apply (sorted_le_last_bound pre l 0);
        [ exact (sorted_le_app_l pre suf ltac:(assumption)) | exact Hne | exact Hlast ]).
  Exists rest2 (pre ++ l :: suf) (Zlength (pre ++ l :: suf)).
  try (rewrite replace_Znth_twice).
  replace p with (Zlength pre) by lia.
  rewrite (replace_Znth_hole pre junk (suf ++ rest2) l).
  rewrite <- app_assoc, <- app_comm_cons.
  sep_apply IntArray.full_to_seg.
  sep_apply (store_ptr_undef_store_ptr (&( "j"))).
  pose proof (addclause_sort_insert_outer _ _ _ pre suf rest2 l Hout Hin Hple
                ltac:(assumption)) as Hout'.
  assert (Hlen : Zlength (pre ++ l :: suf) <= Zlength ac_input_addclause_spec).
  { (* the rewrite pair must be INTERLEAVED: splitting the append exposes a
       fresh cons node, and a single [?Zlength_cons] pass has already run by
       then, leaving [Zlength (junk :: suf ++ rest2)] as an opaque atom. *)
    rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_app, ?Zlength_cons in *;
      ac_zlen; lia. }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [auto | ac_close].
Qed.


Lemma proof_of_solver_addclause_entail_wit_8 : solver_addclause_entail_wit_8.
Proof.
  (* [ac_shape] keeps a FOLDED copy of the dedup invariant
     (its guarded arm), which is what the Assert wants back. *)
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign.
  assert (Hsortedlen : Zlength sortedf = Zlength ac_input_addclause_spec)
  by (eapply Permutation_Zlength_Z; eassumption).
assert (Hprefix : addclause_prefix_equiv ac_F_addclause_spec
    ac_input_addclause_spec kept_2).
{ eapply addclause_prefix_permutation; [eassumption |].
  match goal with
  | Hp : addclause_prefix_equiv _ (sublist 0 ?k sortedf) kept_2 |- _ =>
      assert (Hend : k = Zlength sortedf) by ac_arith;
      rewrite Hend, sublist_self in Hp by reflexivity; exact Hp
  end. }
Exists tail_2 kept_2 q_2.
  sep_apply (store_ptr_undef_store_ptr (&( "i"))).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: ac_close.
Qed.


Lemma proof_of_solver_addclause_partial_solve_wit_4_pure : solver_addclause_partial_solve_wit_4_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  assert (Hn2 : 2 * ac_n_addclause_spec <= 2147483647).
  { change (ac_n_addclause_spec <= Z.max (ms_cap ac_M_addclause_spec) 536870911) in PreH12.
    destruct (Z_le_gt_dec (ms_cap ac_M_addclause_spec) 536870911) as [Hcap | Hcap].
    - rewrite Z.max_r in PreH12 by lia. lia.
    - rewrite Z.max_l in PreH12 by lia. lia. }
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    dump_pre_spatial; first [assumption | lia].
Qed.


Lemma proof_of_solver_addclause_partial_solve_wit_25_pure : solver_addclause_partial_solve_wit_25_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH10 as Hd.
  unfold addclause_dedup_inv in Hd.
  destruct Hd as (_ & _ & _ & _ & Hwf & _ & _ & Hlast & Hlb).
  pose proof PreH36 as Hsh.
  unfold solver_shape in Hsh.
  destruct Hsh as (_ & _ & Hsz2 & _).
  assert (Hub : last <= 2147483647).
  { destruct kept as [| a r].
    - simpl in Hlast. lia.
    - pose proof (@app_removelast_last Z (a :: r) (-2) ltac:(discriminate)) as Heq.
      rewrite <- Hlast in Heq.
      assert (Hin : In last (a :: r))
        by (rewrite Heq; apply in_or_app; right; left; reflexivity).
      rewrite Forall_forall in Hwf.
      specialize (Hwf _ Hin).
      unfold lit_wf_c in Hwf.
      lia. }
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_canceluntil_return_wit_1 : solver_canceluntil_return_wit_1.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_cancel_post.
  Left.
  unfold solver_cancel_owned, solver_cancel_frame.
  Intros tgs.
  Exists activity_ptr assigns_ptr orderpos_ptr reasons_ptr trail_ptr tgs.
  apply _derivable1_andp_intros.
  - unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_vecs_rep,
      solver_trail_array_rep, solver_cancel_undef_tail.
    Intros.
    cancel.
  - apply _derivable1_andp_intros; dump_pre_spatial; [lia | assumption].
Qed.


Lemma proof_of_solver_canceluntil_entail_wit_2 : solver_canceluntil_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_cancel_open_at in *.
  bind_fact ( retval = lit_var_c (Znth (c - 0) (mt_trail (ms_core M0)) 0) ) as H_retval.
  bind_fact ( cancel_clear_loop_inv M0 level_pre c assigns_now_2 reasons_now_2 ) as H_cancel_clear_loop_inv.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  replace (c - 0) with c in H_retval by lia.
  subst retval.
  unfold cancel_clear_loop_inv in H_cancel_clear_loop_inv.
  destruct H_cancel_clear_loop_inv as (Hlevel & Hc & Hass & Hreason).
  pose proof H_solver_shape as Hshape.
  unfold solver_shape in Hshape.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Hinv : cancel_clear_loop_inv M0 level_pre (c - 1)
    (replace_Znth (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) 0 assigns_now_2)
    (replace_Znth (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) 0 reasons_now_2)).
  { unfold cancel_clear_loop_inv.
    repeat split; try lia.
    - rewrite Hass.
      replace (c - 1 + 1) with c by lia.
      apply clear_vars_sublist_step__assume; lia.
    - rewrite Hreason.
      replace (c - 1 + 1) with c by lia.
      apply clear_vars_sublist_step__assume; lia. }
  Exists
    (replace_Znth (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) 0 assigns_now_2)
    (replace_Znth (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) 0 reasons_now_2).
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full reasons_ptr
      (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) (ms_size M0) 0
      reasons_now_2).
  - dump_pre_spatial. lia.
  - sep_apply_l_atomic
      (CharArray.missing_i_merge_to_full assigns_ptr
        (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) (ms_size M0) 0
        assigns_now_2).
    + dump_pre_spatial. lia.
    + msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_canceluntil_entail_wit_4 : solver_canceluntil_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_cancel_open_at in *.
  bind_fact ( order_unassigned_post (ms_size M0) retval order_now_2 orderpos_now_2 heap1
      orderpos1 ) as H_order_unassigned_post.
  bind_fact ( retval = lit_var_c (Znth (c - 0) (mt_trail (ms_core M0)) 0) ) as H_retval.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  bind_fact ( 0 <= lit_var_c (Znth c (mt_trail (ms_core M0)) 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth c (mt_trail (ms_core M0)) 0) < ms_size M0 ) as H_lit_var_c_2.
  bind_fact ( cancel_reinsert_loop_inv M0 level_pre c assigns_now_2 reasons_now_2 order_now_2
      orderpos_now_2 ) as H_cancel_reinsert_loop_inv.
  replace (c - 0) with c in H_retval by lia. subst retval.
  unfold cancel_reinsert_loop_inv in H_cancel_reinsert_loop_inv.
  destruct H_cancel_reinsert_loop_inv as
    (Hassigns & Hreasons & Hlevel & Hcrange & Hwf & Horig & Hreinserted).
  pose proof (order_unassigned_post_members__assume
    (ms_size M0) (lit_var_c (Znth c (mt_trail (ms_core M0)) 0))
    order_now_2 orderpos_now_2 heap1 orderpos1
    H_order_unassigned_post Hwf (conj H_lit_var_c H_lit_var_c_2)) as Hmembers.
  destruct Hmembers as (Hincl & Hhit).
  unfold order_unassigned_post in H_order_unassigned_post.
  destruct H_order_unassigned_post as (Hwfnew & Hcases).
  change (heap_wf (ms_size M0) (heap_of_lists heap1 orderpos1)) in Hwfnew.
  pose proof H_solver_shape as Hshape.
  unfold solver_shape in Hshape.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Hreinserted' :
    cancel_reinserted (heap_of_lists heap1 orderpos1)
      (mt_trail (ms_core M0)) c (mt_qhead (ms_core M0))).
  { intros i Hi.
    destruct (Z.eq_dec i c) as [->|Hne]; [exact Hhit|].
    assert (Hvrange :
      0 <= lit_var_c (Znth i (mt_trail (ms_core M0)) 0) < ms_size M0).
    { apply trail_var_range with (t := ms_core M0); [exact H_mtrail_wf|].
      apply in_map. apply Znth_In. lia. }
    apply (proj1 (heap_wf_in_iff (ms_size M0)
      (heap_of_lists heap1 orderpos1)
      (lit_var_c (Znth i (mt_trail (ms_core M0)) 0)) Hwfnew Hvrange)).
    apply Hincl.
    apply (proj2 (heap_wf_in_iff (ms_size M0)
      (heap_of_lists order_now_2 orderpos_now_2)
      (lit_var_c (Znth i (mt_trail (ms_core M0)) 0)) Hwf Hvrange)).
    apply Hreinserted. lia. }
  Exists assigns_now_2 reasons_now_2 heap1 orderpos1.
  split_pure_spatial.
  - cancel (solver_cancel_frame s_pre M0 wl).
    cancel.
  - split_pures; dump_pre_spatial.
    1-4: assumption.
    unfold cancel_reinsert_loop_inv.
    split; [exact Hassigns|].
    split; [exact Hreasons|].
    split; [lia|].
    split; [lia|].
    split; [exact Hwfnew|].
    split.
    + intros x Hx. apply Hincl. apply Horig. exact Hx.
    + replace (c - 1 + 1) with c by lia. exact Hreinserted'.
Qed.


Lemma proof_of_solver_canceluntil_partial_solve_wit_9_pure : solver_canceluntil_partial_solve_wit_9_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
    replace (c - 0) with c in * by lia; subst retval; msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_nconflicts_solver_nconflicts_spec_entail_solver_nconflicts_incremental_spec :
  solver_nconflicts_solver_nconflicts_spec_entail_solver_nconflicts_incremental_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_conflict_count_cell.
  Exists (stats_conflicts (ms_stats M_solver_nconflicts_incremental_spec)).
  sep_apply (solver_incremental_conflicts_cell_frame__public
    s_pre M_solver_nconflicts_incremental_spec
    (solver_conflict_count_cell s_pre
      (stats_conflicts (ms_stats M_solver_nconflicts_incremental_spec)))
    (solver_incremental_ownership_at s_pre
      M_solver_nconflicts_incremental_spec)).
  cancel.
  Intros_r retval.
  pre_process_default.
  entailer_with ltac:(tauto).
  unfold solver_conflict_count_cell.
  sep_apply derivable1_wand_elim1.
  all: unfold solver_conflict_count_cell; cancel.
Qed.


Lemma proof_of_solver_record_entail_wit_1_2 : solver_record_entail_wit_1_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst. assert (Halloc : record_allocated rec_n rec_F rec_A_arr rec_A_inst M0 rec_words 0 M0).
 { unfold record_allocated. split; [left; repeat split; try reflexivity; lia|]. repeat first [assumption | reflexivity | split]. }
 sep_apply record_rep_open. Exists M0.
 split_pure_spatial.
 - sep_apply (store_ptr_undef_store_ptr (&( "endvar")) (learnt_ptr + Zlength rec_words * sizeof ( INT ))).
   cancel.
 - split_pures; dump_pre_spatial; first [exact Halloc | lia].
Qed.



Lemma proof_of_solver_record_which_implies_wit_4 : solver_record_which_implies_wit_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
pose proof
    (record_enqueue_success_intro__record
      rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage PreH1) as Hsuccess.
  pose proof
    (msolver_inv_record_enqueue__record
      rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage PreH1) as Hinv_enq.
  pose proof (msi_shape Hinv_enq) as Hshape.
  change (solver_shape
    (msolver_enqueue_fresh Mstage (Znth 0 rec_words 0) c
      (record_reason_opt rec_words c))) in Hshape.
  pose proof PreH1 as Halloc.
  destruct Halloc as
    [Hkind [Hcert [Hinv [Hq [Hpending [Hseed Hmodel]]]]]].
  unfold record_clause_cert, record_ready_cert in Hcert.
  destruct Hcert as [_ [_ [_ [_ [Hfresh _]]]]].
  Exists (msolver_record_enqueue Mstage rec_words c).
  split.
  - exact Hsuccess.
  - pose proof
      (record_enqueue_refold
        s assigns_ptr levels_ptr
        (Znth 0 rec_words 0) c
        (ms_size Mstage) (ms_cap Mstage) (ms_qtail Mstage)
        (mt_assigns (ms_core Mstage)) (mt_levels (ms_core Mstage))
        (ms_reason_words Mstage) (mt_trail (ms_core Mstage))
        (mt_lim (ms_core Mstage))
        Mstage (record_reason_opt rec_words c) rec_wl (db_words (ms_learnt M0))) as Hrefold.
    specialize
      (Hrefold eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        eq_refl eq_refl Hshape Hfresh).
    exact (Hrefold m H).
Qed.


Lemma proof_of_solver_search_entail_wit_3_1_split_goal_1 : solver_search_entail_wit_3_1_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_search_close_conflict_count_nonneg.
Qed.


Lemma proof_of_solver_search_entail_wit_3_1 : solver_search_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_solver_search_entail_wit_3_1_split_goal_1 M0 A_inst A_arr F n conflict_count_value Mcur learnt_words retval propagation_result result_focus result_clause Mconf p focus Cconf retval_2 Manalyze Manalyzed words backjump p_2 retval_3 retval_4 cap retval_5 Mback Mrecord cla_inc1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77 PreH78 PreH79 PreH80 PreH81 PreH82 PreH83 PreH84 PreH85 PreH86 PreH87 PreH88 PreH89 PreH90 PreH91 PreH92 PreH93 PreH94).
Qed.



Lemma proof_of_solver_search_which_implies_wit_7 : solver_search_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_search_loop, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_rep_assigns_levels_at,
    solver_rep_at.
  Intros M words.
  Intros act asg opos rsn trl tgs.
  Exists words asg M.
  Exists act opos rsn trl tgs.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_search_which_implies_wit_8 : solver_search_which_implies_wit_8.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Exists result_clause result_focus propagation_result.
assert (Hframe : propagation_caller_frame Mcur propagation_result) by assumption.
destruct Hframe as [Hlim [Hroot [Hmodel [Hdecay Hcap]]]].
assert (Hreuse : minisat_base_watch_completed M0 -> minisat_watch_conflict_ready n propagation_result).
{ intro Hbase. apply PreH8. apply PreH3. exact Hbase. }
assert (Hmodel_nil : ms_model propagation_result = nil) by (rewrite Hmodel; assumption).
assert (Hdecay_positive : msat_fp32_positive_finite (ms_cla_decay propagation_result)) by (rewrite Hdecay; assumption).
unfold msat_fp32_same. msat_manual_entailer_with ltac:(lia || tauto).
Qed.


Lemma proof_of_solver_search_which_implies_wit_23 : solver_search_which_implies_wit_23.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst Mstable ) as H_msolver_inv.
  bind_fact ( mt_qhead (ms_core Mstable) = ms_qtail Mstable ) as H_mt_qhead.
  bind_fact ( ms_capacity_root_propagation_pending Mstable = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( msolver_seed_shadow Mstable ) as H_msolver_seed_shadow.
  bind_fact ( ms_model Mstable = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mstable) ) as H_msat_fp32_positive_finite.
  pose (Mnew := msolver_runtime_update Mstable (ms_model Mstable) (ms_var_inc Mstable) (ms_var_decay Mstable)
    (ms_cla_inc Mstable) (ms_cla_decay Mstable) progress_now (ms_stats Mstable)).

  assert (Hweak : msolver_inv_weak n F A_arr A_inst Mnew).
  { destruct (msi_weak H_msolver_inv). constructor; assumption. }
  assert (Hinv : msolver_inv n F A_arr A_inst Mnew).
  { constructor.
    - exact Hweak.
    - exact (msi_prop_level H_msolver_inv).
    - exact (msi_watch_frontier H_msolver_inv).
    - exact (msi_heap_covers H_msolver_inv).
    - exact (msi_reasonless_current H_msolver_inv). }
  lazymatch goal with
  | Hentry : solver_search_reuse ?entry Mstable |- _ =>
      assert (Hreuse_new : solver_search_reuse entry Mnew)
        by (change (solver_search_reuse entry Mstable); exact Hentry)
  end.
  Exists Mnew.
  unfold solver_search_progress_frame_at,
    solver_rep_assigns_levels_at, solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    clause_new_scalars_frame, solver_scalars_rep,
    solver_fp_rep, solver_fp_without_progress_rep, solver_vecs_rep,
    solver_trail_array_rep.
  Intros act opos rsn trl tgs.
  Exists act opos rsn trl tgs.
  unfold Mnew, msolver_runtime_update. cbn [ms_size ms_cap ms_qtail ms_capacity_pending_qhead ms_capacity_root_propagation_pending ms_core ms_root_level ms_reason_words ms_reason_of ms_prob ms_learnt ms_binary ms_binary_lits ms_wm ms_activity ms_orderpos ms_order ms_model ms_tags ms_tagged ms_stack ms_var_inc ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed ms_progress ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats].
  repeat lazymatch goal with
  | |- _ |-- _ && _ => apply _derivable1_andp_intros
  end;
  lazymatch goal with
  | |- _ |-- “ _ ” =>
      apply dump_spatial_left;
      solve
        [ lia | exact Hreuse_new | exact Hinv | exact H_mt_qhead
        | exact H_ms_capacity_root_propagation_pending
        | exact H_msolver_seed_shadow | exact H_ms_model
        | exact H_msat_fp32_positive_finite | exact (msi_shape Hinv) ]
  | |- _ |-- _ =>
      msat_cancel_sound; change (emp |-- emp); cancel
  end.
Qed.


Lemma proof_of_solver_search_which_implies_wit_32 : solver_search_which_implies_wit_32.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_decisions in *.
  bind_fact (msolver_seed_shadow Mdb) as Hseed_entry.
  unfold msolver_seed_shadow in Hseed_entry.
  destruct Hseed_entry as [seed_shadow [Hseed Hbounds]].
  assert (Hfp : fp64_eq (ms_random_seed Mdb) (Z_to_fp64 seed_shadow)).
  { rewrite Hseed. apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; unfold seed_ok in Hbounds; lia. }
  set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
  assert (Hdecaddr :
    &(s # "solver_t" ->ₛ "stats" .ₛ "decisions") =
    &(stats_ptr # "stats_t" ->ₛ "decisions")).
  { unfold stats_ptr. csimpl. reflexivity. }
  pose proof msat_stats_rep_open_decisions as Hstats_split.
  unfold solver_rep_levels_wl_at, solver_cancel_owned.
  Intros act asg opos rsn trl tgs.
  Exists opos asg act seed_shadow.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_search_order_frame_at.
  cancel.
  Exists rsn trl tgs.
  unfold solver_scalars_rep, clause_new_scalars_frame,
    solver_fp_rep, solver_fp_without_seed_rep,
    solver_vecs_rep, solver_vecs_without_order_rep,
    stats_rep, stats_without_decisions_rep,
    solver_trail_array_rep, solver_levels_slice_at.
  fold stats_ptr.
  rewrite Hdecaddr.
  fold (stats_rep stats_ptr (ms_stats Mdb)).
  fold (stats_without_decisions_rep stats_ptr (ms_stats Mdb)).
  apply _derivable1_andp_intros.
  - msat_cancel_sound.
    exact (Hstats_split stats_ptr (ms_stats Mdb)).
  - repeat lazymatch goal with
    | |- _ |-- _ && _ => apply _derivable1_andp_intros
    end.
    all: lazymatch goal with
    | |- _ |-- “ _ ” =>
        apply dump_spatial_left;
        solve [assumption | unfold seed_ok in Hbounds; lia]
    end.
Qed.


Lemma proof_of_solver_setnvars_which_implies_wit_5 : solver_setnvars_which_implies_wit_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 unfold solver_double_tail, solver_array_tail. Intros physical. sep_apply (proj1 (DoubleArray.undef_seg_unfold actc var physical ltac:(lia))). Exists physical. unfold StoreDoubleAsElement.undefstoreA. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_solve_entail_wit_6_2 : solver_solve_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) Mcur ) as H_msolver_inv_assuming_strong.
  bind_fact ( A_arr = assumption_prefix raw (Zlength raw) ) as H_A_arr.
  bind_fact ( Forall (lit_wf_c n) raw ) as H_Forall.
  set (current := Znth k raw 0).
  pose proof (msas_weak H_msolver_inv_assuming_strong) as Hweak.
  pose proof (msa_trail_wf Hweak) as Hwf.
  assert (Hcurrent_wf : lit_wf_c n current).
  { unfold current.
    apply (Forall_Znth_elim Z (lit_wf_c n) raw 0 k H_Forall).
    lia. }
  assert (Hrange : 0 <= lit_var_c current < n) by exact (lit_var_c_in_range _ _ Hcurrent_wf).
  assert (Hcell : lbool_cell (Znth (lit_var_c current) (mt_assigns (ms_core Mcur)) 0)).
  { apply Forall_Znth_elim; [exact (mtw_cells Hwf)|]. rewrite (mtw_assigns_len Hwf). exact Hrange. }
  assert (Hfalse : lit_false (mt_assigns (ms_core Mcur)) current).
  { unfold lit_false, lit_sig, current. unfold current in Hcell. unfold lbool_cell in Hcell.
    unfold lit_sign_c in PreH17, PreH18. destruct (Z.odd (Znth k raw 0)); cbn [Z.mul] in PreH17, PreH18; unfold lit_var_c in *; intuition nia. }
  assert (Hneg_true :
      lit_true (mt_assigns (ms_core Mcur)) (lit_neg_c current)).
  { apply lit_false_neg_true. exact Hfalse. }
  pose proof (mtrail_wf_trail_covers n (ms_core Mcur) Hwf) as Hcovers.
  destruct (Hcovers (lit_neg_c current)
    (lit_neg_c_wf n current Hcurrent_wf) Hneg_true) as [i [Hi Hlit]].
  assert (HA : A_arr = lits_denote raw).
  { rewrite H_A_arr.
    unfold assumption_prefix.
    rewrite sublist_self by reflexivity.
    reflexivity. }
  assert (Hin : In (lit_denote current) A_arr).
  { rewrite HA. unfold lits_denote.
    apply in_map. unfold current. apply Znth_In. lia. }
  assert (Hunsat : cnf_unsat n (cnf_with_units F A_arr)).
  { eapply assuming_false_assumption_unsat with
      (A_proc := assumption_prefix raw k)
      (a := lit_denote current) (i := i); eauto.
    rewrite Hlit.
    apply lit_denote_neg.
    destruct Hcurrent_wf. lia. }

  sep_apply (store_ptr_undef_store_ptr (&( "i"))).
  sep_apply (store_char_undef_store_char (&( "assumption_status"))).
  Exists 0 0 Mcur.
  unfold assumptions_array. Exists raw.
  unfold solver_rep_assigns_levels_at, solver_rep_at, solver_rep_levels_wl_at,
    solver_assigns_focus_frame_wl_at, solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs. Exists act opos rsn trl tgs.
  rewrite PreH9.
  split_pure_spatial.
  - cancel (solver_levels_slice_at s_pre Mcur levels_ptr).
    cancel (IntArray.seg begin_pre 0 (Zlength raw) raw).
    unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_ptrs_rep, solver_var_arrays_rep.
    rewrite PreH9. msat_manual_entailer_with ltac:(lia || tauto).
  - msat_manual_entailer_with ltac:(lia || tauto).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_11 : solver_solve_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( assumption_propagation_success n F A_arr raw (k + 1) Mprop ) as H_assumption_propagation_success.
  unfold assumption_propagation_success in H_assumption_propagation_success.
  destruct H_assumption_propagation_success as (Hstrong & Hdrained & Hpending & Hseed).
  pose proof (msas_weak Hstrong) as Hweak.
  assert (Hsize : ms_size Mprop = n) by
    (pose proof (msa_size Hweak); lia).
  pose proof (msa_shape Hweak) as Hshape.
  subst n.
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_assigns_focus_frame_wl_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  Exists act opos rsn trl tgs.
  split_pure_spatial.
  - cancel (DoubleArray.seg act 0 (ms_size Mprop) (ms_activity Mprop)).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: unfold solver_shape in Hshape; solve [assumption | lia].
Qed.


Lemma proof_of_solver_solve_which_implies_wit_16 : solver_solve_which_implies_wit_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  set (L := Zlength (mt_lim (ms_core Mcur))).
  set (Mroot := msolver_set_root Mcur L).
  set (A_inst := decisions_upto (ms_core Mcur) L).
  assert (Hinstall : assumption_root_install n F A_arr Mcur Mroot A_inst).
  { unfold Mroot, A_inst, L.
    apply assumption_root_install_intro__solve; assumption. }
  pose proof Hinstall as Hinstall_copy.
  unfold assumption_root_install in Hinstall_copy.
  destruct Hinstall_copy as
    (HA & HM & Hinv & Hroot & Hpending & Hseed).
  lazymatch goal with
  | Hreuse : solver_query_reuse ?entry Mcur |- _ =>
      assert (Hreuse_root : solver_query_reuse entry Mroot)
        by (intro Hready; exact (Hreuse Hready))
  end.
  Exists A_inst Mroot.
  split_pure_spatial.
  - pose proof (msi_shape Hinv) as Hshape.
    sep_apply (store_ptr_undef_store_ptr &("values") values).
    unfold solver_root_install_frame_at, solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
    Intros act opos rsn trl tgs.
    unfold solver_rep_wl, solver_rep_levels_wl_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_trail_array_rep.
    Exists levels_ptr act values opos rsn trl tgs.
    unfold Mroot, L.
    rewrite fp_rep_set_root_eq, vecs_rep_set_root_eq.
    sep_apply join_vecs_trail_lim.
    sep_apply join_scalars_set_root.
    unfold msolver_set_root, msolver_core_heap_update in Hshape |- *.
    cbn -[DoubleArray.seg IntArray.seg PtrArray.seg CharArray.seg] in Hshape |- *.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. exact Hshape.
  - msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_assume_partial_solve_wit_3_pure : assume_partial_solve_wit_3_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
    bind_fact ( l_pre = l0 ) as H_l_pre;
    bind_fact ( enqueue_input n l0 qtail assigns levels reasons trail ) as H_enqueue_input;
    unfold enqueue_input in H_enqueue_input;
    pose proof (lit_var_c_in_range n l0 ltac:(tauto)) as Hrange;
    destruct Hrange as [Hlo Hhi];
    rewrite H_l_pre;
    msat_manual_entailer_with lia.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_11 : solver_addclause_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (addclause_stats_open_wl_noshape s Mclause wlg lvlp).
  sep_apply (stats_rep_open_dotted s (ms_stats Mclause)).
  msat_manual_entailer_with lia.
Qed.


Lemma proof_of_solver_canceluntil_partial_solve_wit_16_pure : solver_canceluntil_partial_solve_wit_16_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( cancel_reinsert_loop_inv M0 level_pre c assigns_now reasons_now order_now orderpos_now )
      as H_cancel_reinsert_loop_inv.
  unfold cancel_reinsert_loop_inv in H_cancel_reinsert_loop_inv.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_nvars_solver_nvars_spec_entail_solver_nvars_incremental_spec :
  solver_nvars_solver_nvars_spec_entail_solver_nvars_incremental_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_size_cell.
  Exists (ms_size M_solver_nvars_incremental_spec).
  sep_apply (solver_incremental_size_cell_frame__public
    s_pre M_solver_nvars_incremental_spec
    (solver_size_cell s_pre (ms_size M_solver_nvars_incremental_spec))
    (solver_incremental_ownership_at s_pre M_solver_nvars_incremental_spec)).
  cancel.
  Intros_r retval.
  pre_process_default.
  entailer_with ltac:(tauto).
  unfold solver_size_cell.
  sep_apply derivable1_wand_elim1.
  all: unfold solver_size_cell; cancel.
Qed.


Lemma proof_of_solver_record_partial_solve_wit_5_pure : solver_record_partial_solve_wit_5_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst.

 match goal with H : msolver_inv _ _ _ _ M0 |- _ => pose proof H as Hinv end.
 match goal with H : record_clause_cert _ _ M0 rec_words |- _ => pose proof H as Hcert end.
 pose proof (msi_shape Hinv) as Hshape.
 pose proof (msi_weak Hinv) as Hweak.
 pose proof (msolver_inv_literal_bound _ _ _ _ _ Hweak) as Hbound.
 pose proof (msw_size Hweak) as Hsize.
 destruct Hcert as [Hlen [Hwf [Hnd Hrest]]].
 pose proof (msat_map_lit_var_c_in_range rec_n rec_words Hwf) as Hall.
 pose proof (NoDup_Z_bounded_length (map lit_var_c rec_words) rec_n (msw_n_range Hweak) Hnd Hall) as Hwords.
 assert (Hwordn : Zlength rec_words <= rec_n).
 { rewrite Zlength_correct. rewrite <- length_map with (f := lit_var_c). exact Hwords. }
 unfold solver_support_inv, clause_install_pending_cert.
 rewrite ?sel_learnt_learnt, ?msolver_set_root_self__api_reentry.
 cbn [solver_selected_is_learnt].
 rewrite ?msolver_set_root_self__api_reentry.

 msat_scalar_side_conditions.
Qed.


Lemma proof_of_solver_search_entail_wit_2_3_split_goal_1 : solver_search_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analyze_backjump_cert n Manalyzed words backjump ) as H_analyze_backjump_cert.
  unfold analyze_backjump_cert in H_analyze_backjump_cert.
  destruct H_analyze_backjump_cert as [_ [Hback _]].
  assert (Hnot : Z.ltb 1 (Zlength words) = false).
  { apply Z.ltb_ge. lia. }
  rewrite Hnot in Hback.
  symmetry.
  exact Hback.
Qed.


Lemma proof_of_solver_search_entail_wit_2_3 : solver_search_entail_wit_2_3.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_search_entail_wit_2_3_split_goal_1 M0 A_inst A_arr F n conflict_count_value Mcur learnt_words retval propagation_result result_focus result_clause Mconf p focus Cconf retval_2 Manalyze Manalyzed words backjump retval_3).
Qed.



Lemma proof_of_solver_search_entail_wit_5_1 : solver_search_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_reducedb_post_at.
  Intros Mreduced.
  match goal with
  | Hpost : msolver_inv n F A_arr A_inst Mreduced /\ _ |- _ =>
      destruct Hpost as (Hinv & Hq & Hp & Hseed & Hmodel & Hdecay & Hcap & Hreuse)
  end.
  assert (Hmodel_nil : ms_model Mreduced = nil)
    by (rewrite Hmodel; exact PreH11).
  assert (Hdecay_pos : msat_fp32_positive_finite (ms_cla_decay Mreduced))
    by (rewrite Hdecay; exact PreH12).
  lazymatch type of PreH6 with
  | solver_search_reuse ?entry Mclean =>
      assert (Hreuse_out : solver_search_reuse entry Mreduced)
        by (intro Hbase; exact (Hreuse (PreH6 Hbase)))
  end.
  Exists Mreduced.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (int_auto)] ..]).
Qed.



Lemma proof_of_solver_search_entail_wit_7 : solver_search_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_search_model_ready n F A_arr A_inst Mselected ) as H_solver_search_model_ready.
  bind_fact ( model_copy_progress n Mselected model_words_2 i ) as H_model_copy_progress.
  assert (Hready : solver_search_model_ready n F A_arr A_inst Mselected) by
    exact H_solver_search_model_ready.
  unfold solver_search_model_ready in H_solver_search_model_ready.
  destruct H_solver_search_model_ready as (Hinv & _ & _ & _ & _ & _).
  assert (Hn : 0 <= n) by exact (msi_n_range Hinv).
  assert (Hsize : ms_size Mselected = n) by
    (symmetry; exact (msi_size Hinv)).
  assert (Hassigns : Zlength (mt_assigns (ms_core Mselected)) = n) by
    (rewrite (solver_shape_assigns_len Mselected (msi_shape Hinv)); exact Hsize).
  destruct H_model_copy_progress as (Hi & Hlen & Hmodel).
  Exists (app model_words_2 (cons (Znth i (replace_Znth i
    (Znth i (mt_assigns (ms_core Mselected)) 0)
    (mt_assigns (ms_core Mselected))) 0) nil)).
  rewrite replace_Znth_Znth in *.
  sep_apply CharArray.full_to_seg.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil in *; try solve [assumption | lia].
    unfold model_copy_progress.
    repeat split.
    + lia.
    + lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
    + rewrite Hmodel.
      rewrite (sublist_split 0 (i + 1) i
        (mt_assigns (ms_core Mselected))) by lia.
      rewrite (sublist_single 0 i
        (mt_assigns (ms_core Mselected))) by lia.
      reflexivity.
Qed.


Lemma proof_of_solver_search_partial_solve_wit_10_pure : solver_search_partial_solve_wit_10_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  split_pures; dump_pre_spatial.
  all: first [ assumption
             | exact MSatFloatFacts.fp32_search_decay_positive_finite
             | lia ].
Qed.


Lemma proof_of_solver_search_partial_solve_wit_46_pure : solver_search_partial_solve_wit_46_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact (solver_search_backjump_ready n F A_arr A_inst Mcur Mback words) as Hback.
pose proof Hback as Hframe. unfold solver_search_backjump_ready in Hframe.
destruct Hframe as [_ [_ [_ [_ [_ [_ [Hmodel [_ _]]]]]]]].
assert (Hmodel_nil : ms_model Mback = nil) by (rewrite Hmodel; assumption).
msat_manual_entailer_with ltac:(assumption || lia).
Qed.


Lemma proof_of_solver_search_partial_solve_wit_47_pure : solver_search_partial_solve_wit_47_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact (solver_search_backjump_ready n F A_arr A_inst Mcur Mback words) as Hback.
pose proof Hback as Hframe. unfold solver_search_backjump_ready in Hframe.
destruct Hframe as [_ [_ [_ [_ [_ [_ [Hmodel [_ _]]]]]]]].
assert (Hmodel_nil : ms_model Mback = nil) by (rewrite Hmodel; assumption).
msat_manual_entailer_with ltac:(assumption || lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_15 : solver_search_which_implies_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analysis_cancel_ready n F A_arr (PropagationStable A_inst) Manalyzed focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_backjump_cert n Manalyzed words blevel ) as H_analyze_backjump_cert.
  unfold solver_rep_levels_wl_at at 1.
  Intros act asg opos rsn trl tgs.
  pose proof H_analysis_cancel_ready as Hready.
  unfold analysis_cancel_ready in Hready.
  destruct Hready as
    [Mbase [Hcancel [Hequiv [Hheap [Hcovers [Hcurrent [Hfocus Hcla]]]]]]].
  destruct Hcancel as
    [Hweak [Hprop [Hfocuswf [Hprocessed [Hlevel
      [Hfront [Hheapbase [Hcovbase Hreason]]]]]]]].
  destruct Hweak as [_ Hinv].
  assert (Esize : ms_size Manalyzed = ms_size Mbase).
  { unfold analysis_core_equiv in Hequiv. tauto. }
  assert (Ecore : ms_core Manalyzed = ms_core Mbase).
  { unfold analysis_core_equiv in Hequiv. tauto. }
  assert (Eroot : ms_root_level Manalyzed = ms_root_level Mbase).
  { unfold analysis_core_equiv in Hequiv. tauto. }
  assert (Hwf : mtrail_wf (ms_size Manalyzed) (ms_core Manalyzed)).
  { rewrite Esize, Ecore, <- (msw_size Hinv).
    exact (msw_trail_wf Hinv). }
  assert (Hprop_cur : prop_level (ms_core Manalyzed)).
  { rewrite Ecore. exact Hprop. }
  assert (Hsize : ms_size Manalyzed = n).
  { rewrite Esize. symmetry. exact (msw_size Hinv). }
  assert (Hheap_cur : heap_wf (ms_size Manalyzed) (msolver_heap Manalyzed)).
  { rewrite Hsize. exact Hheap. }
  destruct H_analyze_backjump_cert as
    [Hwords [Hbeq [Hrootle [Hblevel [Hfocuslevel Htail]]]]].
  assert (Hrootnonneg : 0 <= ms_root_level Manalyzed).
  { rewrite Eroot. exact (proj1 (msw_root_range Hinv)). }
  assert (Hblevel_range :
      0 <= blevel < Zlength (mt_lim (ms_core Manalyzed))).
  { lia. }
  assert (Hbound :
      Znth blevel (mt_lim (ms_core Manalyzed)) 0 <=
        mt_qhead (ms_core Manalyzed)).
  { eapply Forall_Znth_elim; [exact Hprop_cur|exact Hblevel_range]. }
  assert (Hcancelbound : cancel_bound_ready Manalyzed blevel).
  { right. exact Hbound. }
  unfold solver_cancel_pre, solver_cancel_owned.
  Exists act asg opos rsn trl tgs.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_35 : solver_search_which_implies_wit_35.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( ms_size Mselected = n ) as H_ms_size.
  bind_fact ( ms_model Mselected = nil ) as H_ms_model.
  unfold solver_rep_levels_wl_at, solver_cancel_owned,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_model_copy_frame_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at, solver_scalars_rep,
    solver_scalars_without_size_rep, clause_new_scalars_frame, solver_vecs_rep,
    solver_vecs_without_model_rep, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  Exists asg act opos rsn trl tgs.
  rewrite <- H_ms_size, H_ms_model.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_37 : solver_search_which_implies_wit_37.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_search_model_ready n F A_arr A_inst Mselected ) as H_solver_search_model_ready.
  bind_fact ( ms_size Mselected = n ) as H_ms_size.
  bind_fact ( model_copy_progress n Mselected model_words_now i ) as H_model_copy_progress.
  unfold solver_search_model_ready in H_solver_search_model_ready.
  destruct H_solver_search_model_ready as (Hinv & Hqhead & Horder & Hpending & Hseed & Hmodel0).
  unfold model_copy_progress in H_model_copy_progress.
  destruct H_model_copy_progress as (Hirange & Hmodellength & Hmodelwords).
  assert (Hi : i = n) by lia. subst i.
  set (Mdone := msolver_with_model Mselected model_words_now).
  assert (Hseed_done : msolver_seed_shadow Mdone) by exact Hseed.
  assert (Hcap_done : ms_cap Mdone = ms_cap Mselected) by reflexivity.
  lazymatch goal with
  | Hreuse : solver_search_reuse ?entry Mselected |- _ =>
      assert (Hreuse_done : solver_search_reuse entry Mdone) by exact Hreuse
  end.
  assert (Hweakdone : msolver_inv_weak n F A_arr A_inst Mdone).
  { unfold Mdone, msolver_with_model.
    destruct (msi_weak Hinv). constructor; assumption. }
  assert (Hinvdone : msolver_inv n F A_arr A_inst Mdone).
  { unfold Mdone, msolver_with_model.
    destruct Hinv as [Hweak Hprop Hwatch Hheap Hreason].
    constructor; [exact Hweakdone | exact Hprop | exact Hwatch |
      exact Hheap | exact Hreason]. }
  assert (Hcopy : model_copies n Mdone).
  { unfold model_copies, Mdone, msolver_with_model. simpl.
    split; [lia|]. intros v Hv.
    rewrite Hmodelwords, Znth_sublist by lia.
    replace (v + 0) with v by lia. reflexivity. }
  assert (Hfix : mt_qhead (ms_core Mdone) =
      Zlength (mt_trail (ms_core Mdone))).
  { unfold Mdone, msolver_with_model. simpl.
    pose proof (msi_shape Hinv) as Hshape.
    unfold solver_shape in Hshape. rewrite Hqhead. lia. }
  assert (Hsaved : model_saved n F A_arr Mdone).
  { eapply sat_endgame_model with (A_inst := A_inst).
    - exact Hweakdone.
    - exact (msi_watch_frontier Hinvdone).
    - exact (msi_heap_covers Hinvdone).
    - exact Hfix.
    - unfold Mdone, msolver_with_model. exact Horder.
    - exact Hcopy. }
  Exists model_words_now Mdone.
  sep_apply (store_int_undef_store_int &( "i")).
  split_pure_spatial.
  - unfold model_copy_finish. cancel.
    unfold solver_model_copy_frame_at, solver_without_assigns_frame_wl_at,
      solver_without_assigns_cells_at, solver_rep_assigns_levels_at,
      solver_rep_at, solver_nonlevel_rep_at,
      solver_nonlevel_rep_nostats_at, solver_scalars_without_size_rep,
      solver_vecs_without_model_rep, solver_scalars_rep, solver_vecs_rep,
      clause_new_scalars_frame, solver_fp_rep, solver_levels_slice_at,
      solver_trail_array_rep.
    Intros act opos rsn trl tgs.
    Exists act opos rsn trl tgs.
    unfold Mdone, msolver_with_model. simpl.
    apply _derivable1_andp_intros.
    + apply dump_spatial_left. exact (msi_shape Hinvdone).
    + rewrite H_ms_size.
      msat_cancel_sound. change (emp |-- emp). cancel.
  - unfold model_copy_finish. msat_manual_entailer_with ltac:(first [assumption | lia]).
Qed.
