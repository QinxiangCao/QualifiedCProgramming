From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Import vec_qcp_goal.
From SimpleC.EE.Applications_human.minisat Require Import vec_qcp_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.vec_qcp_lib.
Local Open Scope sac.

Lemma proof_of_veci_new_return_wit_1 : veci_new_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Veci.header_fold v_pre 0 0 0).
  sep_apply (Veci.rep_empty_intro v_pre).
  cancel.
Qed.

Lemma proof_of_veci_delete_partial_solve_wit_2_pure : veci_delete_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_veci_resize_return_wit_1 : veci_resize_return_wit_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rewrite Zlength_sublist by lia.
  sep_apply (Veci.header_fold v_pre p k_pre cap).
  sep_apply (Veci.rep_at_truncate v_pre p l cap k_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  sep_apply (Veci.rep_at_rep_ptr v_pre p (sublist 0 k_pre l) cap).
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia ..].
Qed.

Lemma proof_of_veci_push_entail_wit_1_5_split_goal_1 : veci_push_entail_wit_1_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_veci_push_entail_wit_1_5 : veci_push_entail_wit_1_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_veci_push_entail_wit_1_5_split_goal_1.
Qed.

Lemma proof_of_veci_push_return_wit_1 : veci_push_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Veci.header_fold v_pre retval_2 (Zlength l + 1) actual).
  sep_apply (Veci.rep_intro v_pre retval_2 (l ++ e_pre :: nil) actual (Zlength l + 1) (cap + 1) (cap + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_veci_push_return_wit_2 : veci_push_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Veci.header_fold v_pre retval_2 (Zlength l + 1) actual).
  sep_apply (Veci.rep_intro v_pre retval_2 (l ++ e_pre :: nil) actual (Zlength l + 1) (cap + 1) (cap + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_veci_push_return_wit_3 : veci_push_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Veci.header_fold v_pre retval_2 (Zlength l + 1) actual).
  sep_apply (Veci.rep_intro v_pre retval_2 (l ++ e_pre :: nil) actual (Zlength l + 1) (cap + 1) (cap + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_veci_push_return_wit_4 : veci_push_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Veci.header_fold v_pre retval_2 (Zlength l + 1) actual).
  sep_apply (Veci.rep_intro v_pre retval_2 (l ++ e_pre :: nil) actual (Zlength l + 1) (cap + 1) (cap + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_veci_push_return_wit_5 : veci_push_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Veci.header_fold v_pre p (Zlength l + 1) cap).
  sep_apply (Veci.rep_intro v_pre p (l ++ e_pre :: nil) cap (Zlength l + 1) (Zlength l + 1) (Zlength l + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_veci_push_partial_solve_wit_3_pure : veci_push_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_vecp_new_return_wit_1 : vecp_new_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (PtrArray.undef_full_to_undef_seg retval 4).
  sep_apply (Vecp.header_fold v_pre retval 0 4).
  sep_apply (Vecp.rep_nil_intro v_pre retval 4).
  all: solve [cancel | lia | vec_buf_solve].
Qed.

Lemma proof_of_vecp_delete_partial_solve_wit_2_pure : vecp_delete_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_vecp_resize_return_wit_1 : vecp_resize_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.header_fold v_pre p k_pre cap).
  sep_apply (Vecp.rep_at_truncate v_pre p l cap k_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  sep_apply (Vecp.rep_at_rep_ptr v_pre p (sublist 0 k_pre l) cap).
  split_pure_spatial;
    [cancel | split_pures; dump_pre_spatial; rewrite Zlength_sublist by lia; lia ..].
Qed.

Lemma proof_of_vecp_push_entail_wit_1_5_split_goal_1 : vecp_push_entail_wit_1_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_vecp_push_entail_wit_1_5 : vecp_push_entail_wit_1_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_vecp_push_entail_wit_1_5_split_goal_1.
Qed.

Lemma proof_of_vecp_push_return_wit_1 : vecp_push_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.header_fold v_pre retval_2 (Zlength l + 1) actual).
  sep_apply (Vecp.rep_intro v_pre retval_2 (l ++ e_pre :: nil) actual (Zlength l + 1) (cap + 1) (cap + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_vecp_push_return_wit_2 : vecp_push_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.header_fold v_pre retval_2 (Zlength l + 1) actual).
  sep_apply (Vecp.rep_intro v_pre retval_2 (l ++ e_pre :: nil) actual (Zlength l + 1) (cap + 1) (cap + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_vecp_push_return_wit_3 : vecp_push_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.header_fold v_pre retval_2 (Zlength l + 1) actual).
  sep_apply (Vecp.rep_intro v_pre retval_2 (l ++ e_pre :: nil) actual (Zlength l + 1) (cap + 1) (cap + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_vecp_push_return_wit_4 : vecp_push_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.header_fold v_pre retval_2 (Zlength l + 1) actual).
  sep_apply (Vecp.rep_intro v_pre retval_2 (l ++ e_pre :: nil) actual (Zlength l + 1) (cap + 1) (cap + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_vecp_push_return_wit_5 : vecp_push_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.header_fold v_pre p (Zlength l + 1) cap).
  sep_apply (Vecp.rep_intro v_pre p (l ++ e_pre :: nil) cap (Zlength l + 1) (Zlength l + 1) (Zlength l + 1)).
  all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
Qed.

Lemma proof_of_vecp_push_partial_solve_wit_3_pure : vecp_push_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_vecp_remove_safety_wit_4 : vecp_remove_safety_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.rep_ptr_bounds v_pre ws words_now). Intros.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_vecp_remove_safety_wit_7 : vecp_remove_safety_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.rep_ptr_bounds v_pre ws words_now). Intros.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_vecp_remove_safety_wit_9 : vecp_remove_safety_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.rep_ptr_bounds v_pre ws words_now). Intros.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_vecp_remove_entail_wit_1_split_goal_1 : vecp_remove_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct l as [|a l]; [contradiction |].
  rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed.

Lemma proof_of_vecp_remove_entail_wit_1_split_goal_2 : vecp_remove_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold vecp_remove_scan_inv.
  repeat split.
  + lia.
  + destruct l as [|a l]; [contradiction |].
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
  + rewrite sublist_self by reflexivity. assumption.
  + simpl. constructor.
Qed.

Lemma proof_of_vecp_remove_entail_wit_1 : vecp_remove_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_vecp_remove_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_vecp_remove_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_vecp_remove_entail_wit_2_split_goal_1 : vecp_remove_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hne : Znth (j - 0) l 0 <> e_pre, Hscan : vecp_remove_scan_inv e_pre l j |- _ =>
      replace (j - 0) with j in Hne by lia;
      pose proof (vecp_remove_scan_step e_pre l j Hscan Hne) as Hstep
  end.
  destruct Hstep as ((_ & Hlt) & _). exact Hlt.
Qed.

Lemma proof_of_vecp_remove_entail_wit_2_split_goal_2 : vecp_remove_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hne : Znth (j - 0) l 0 <> e_pre, Hscan : vecp_remove_scan_inv e_pre l j |- _ =>
      replace (j - 0) with j in Hne by lia;
      pose proof (vecp_remove_scan_step e_pre l j Hscan Hne) as Hstep
  end.
  exact Hstep.
Qed.

Lemma proof_of_vecp_remove_entail_wit_2 : vecp_remove_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_vecp_remove_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_vecp_remove_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_vecp_remove_entail_wit_3 : vecp_remove_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists j l.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try solve [assumption | reflexivity | lia].
    replace (j - 0) with j in * by lia.
    apply vecp_remove_shift_init; assumption.
Qed.

Lemma proof_of_vecp_remove_entail_wit_4 : vecp_remove_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (w := replace_Znth j (Znth (j + 1 - 0) words_now_2 0) words_now_2).
  assert (Hlen : Zlength w = Zlength words_now_2)
    by (unfold w; apply Zlength_replace_Znth).
  assert (Hstep : vecp_remove_shift_inv e_pre l found_2 (j + 1) w).
  { unfold w. replace (j + 1 - 0) with (j + 1) by lia.
    apply vecp_remove_shift_step; [exact PreH7 | lia]. }
  Exists found_2 w.
  sep_apply_l_atomic (PtrArray.full_to_seg ws (Zlength words_now_2) w).
  sep_apply (Vecp.rep_ptr_intro v_pre ws w cap
    (Zlength words_now_2) (Zlength words_now_2) (Zlength words_now_2));
    [ | first [lia | vec_buf_solve] .. ].
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [auto | lia].
Qed.

Lemma proof_of_vecp_remove_return_wit_1 : vecp_remove_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists found.
  subst retval_2. rewrite PreH5.
  sep_apply (Vecp.rep_ptr_rep v_pre ws (remove_nth found l)).
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia] ..].
Qed.

Lemma proof_of_vecp_remove_which_implies_wit_1 : vecp_remove_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (vecp_remove_shift_done e l found j words_now PreH1 PreH2 PreH3)
    as (Hfirst & Hlen & Hsub).
  sep_apply_l_atomic (store_int_undef_store_int (&( "j")) j).
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia] ..].
Qed.
