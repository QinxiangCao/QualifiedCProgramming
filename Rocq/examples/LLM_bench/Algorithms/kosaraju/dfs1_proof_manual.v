From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import dfs1_goal.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import dfs1_proof_auto.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.dfs1_lib.
Local Open Scope sac.

Ltac dfs1_destruct_known_csr_wf1 :=
  repeat match goal with
  | H : csr_wf1 _ _ _ _ _ |- _ =>
      unfold csr_wf1 in H;
      destruct H as
        [? [? [? [? [? [? [? [? [? ?]]]]]]]]]
  end.

Ltac dfs1_rewrite_same_replace :=
  repeat match goal with
  | |- context [Znth ?i (replace_Znth ?i ?v ?l) ?d] =>
      rewrite (Znth_replace_eq l i v d) by lia
  | H : context [Znth ?i (replace_Znth ?i ?v ?l) ?d] |- _ =>
      rewrite (Znth_replace_eq l i v d) in H by lia
  | |- context [Zlength (replace_Znth ?i ?v ?l)] =>
      rewrite Zlength_replace_Znth
  | H : context [Zlength (replace_Znth ?i ?v ?l)] |- _ =>
      rewrite Zlength_replace_Znth in H
  end.

Ltac dfs1_solve_replace_neq_once :=
  match goal with
  | |- context [Znth ?w (replace_Znth ?r ?v ?l) ?d] =>
      destruct (Z.eq_dec w r) as [-> | ?];
      [ rewrite (Znth_replace_eq l r v d) by lia
      | rewrite (Znth_replace_neq l w r v d) by lia ]
  | H : context [Znth ?w (replace_Znth ?r ?v ?l) ?d] |- _ =>
      destruct (Z.eq_dec w r) as [-> | ?];
      [ rewrite (Znth_replace_eq l r v d) in H by lia
      | rewrite (Znth_replace_neq l w r v d) in H by lia ]
  end.

Ltac dfs1_solve_current_index :=
  match goal with
  | Hlen : Zlength ?l = adj_verts ?g,
    Hn : adj_verts ?g = ?n |- (0 <= ?u < Zlength ?l)%Z =>
      rewrite Hlen; rewrite Hn; lia
  | Hlen : Zlength ?l = adj_verts ?g |- (0 <= ?u < Zlength ?l)%Z =>
      rewrite Hlen; lia
  | Hlen : Zlength ?l = ?n |- (0 <= ?u < Zlength ?l)%Z =>
      rewrite Hlen; lia
  | _ => lia
  end.

Ltac dfs1_solve_split :=
  subst;
  repeat match goal with
  | H : dfs1_sequence_state_ready _ _ _ _ _ _ |- _ =>
      unfold dfs1_sequence_state_ready in H
  | H : dfs1_sequence_extension _ _ _ _ _ _ _ _ |- _ =>
      unfold dfs1_sequence_extension in H
  | H : dfs1_active_timer_surplus _ _ _ _ |- _ =>
      unfold dfs1_active_timer_surplus in H
  | H : dfs1_timer_surplus_preserved _ _ _ _ |- _ =>
      unfold dfs1_timer_surplus_preserved in H
  | |- dfs1_sequence_state_ready _ _ _ _ _ _ =>
      unfold dfs1_sequence_state_ready
  | |- dfs1_sequence_extension _ _ _ _ _ _ _ _ =>
      unfold dfs1_sequence_extension
  | |- dfs1_active_timer_surplus _ _ _ _ =>
      unfold dfs1_active_timer_surplus
  | |- dfs1_timer_surplus_preserved _ _ _ _ =>
      unfold dfs1_timer_surplus_preserved
  end;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- forall _, _ => intro
  | |- _ -> _ => intro
  end;
  try dfs1_rewrite_same_replace;
  try solve
    [ rewrite count_nonzero_replace_Znth01 by dfs1_solve_current_index; lia
    | eapply dfs1_entry_close; eauto; lia
    | eapply dfs1_entry_sequence_close__dfs1_active; eauto; lia
    | eapply dfs1_skip_close; eauto; lia
    | eapply dfs1_skip_sequence_close__dfs1_active; eauto; lia
    | eapply dfs1_recurse_close; eauto; lia
    | assumption | reflexivity | congruence | lia | eauto ];
  dfs1_destruct_known_csr_wf1;
  try dfs1_rewrite_same_replace;
  try solve
    [ rewrite count_nonzero_replace_Znth01 by dfs1_solve_current_index; lia
    | eapply dfs1_entry_close; eauto; lia
    | eapply dfs1_entry_sequence_close__dfs1_active; eauto; lia
    | eapply dfs1_skip_close; eauto; lia
    | eapply dfs1_skip_sequence_close__dfs1_active; eauto; lia
    | eapply dfs1_recurse_close; eauto; lia
    | assumption | reflexivity | congruence | lia | eauto ];
  repeat (try dfs1_solve_replace_neq_once; try dfs1_rewrite_same_replace;
          try solve
            [ rewrite count_nonzero_replace_Znth01 by dfs1_solve_current_index; lia
            | eapply dfs1_entry_close; eauto; lia
            | eapply dfs1_entry_sequence_close__dfs1_active; eauto; lia
            | eapply dfs1_skip_close; eauto; lia
            | eapply dfs1_skip_sequence_close__dfs1_active; eauto; lia
            | eapply dfs1_recurse_close; eauto; lia
            | assumption | reflexivity | congruence | lia | eauto ]).

Lemma proof_of_dfs1_entail_wit_1_split_goal_1 : dfs1_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_2 : dfs1_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_3 : dfs1_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_4 : dfs1_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_5 : dfs1_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_6 : dfs1_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_7 : dfs1_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_8 : dfs1_entail_wit_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_9 : dfs1_entail_wit_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_10 : dfs1_entail_wit_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_11 : dfs1_entail_wit_1_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_12 : dfs1_entail_wit_1_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply dfs1_active_sequence_extension_entry.
  - unfold dfs1_sequence_state_ready in PreH4.
    destruct PreH4 as [_ [_ Htimer]].
    exact Htimer.
  - unfold csr_wf1 in PreH1.
    destruct PreH1 as [_ [_ [Hvis _]]].
    exact Hvis.
  - rewrite PreH3. lia.
  - exact PreH10.
  - rewrite PreH3. exact PreH5.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_13 : dfs1_entail_wit_1_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hvis_len : Zlength vis1_l_low_level_spec = n_pre).
  { unfold csr_wf1 in PreH1.
    destruct PreH1 as [_ [_ [Hvis _]]].
    rewrite <- PreH3.
    exact Hvis. }
  unfold dfs1_finish_prefix_marked in *.
  intros t Ht.
  specialize (PreH5 t Ht) as [Hrange Hvis].
  split; [exact Hrange |].
  destruct (Z.eq_dec (Znth t fin_l_low_level_spec 0) u_pre) as [Heq | Hne].
  - subst.
    rewrite PreH10 in Hvis.
    contradiction.
  - rewrite (Znth_replace_neq vis1_l_low_level_spec
      (Znth t fin_l_low_level_spec 0) u_pre 1 0) by lia.
    exact Hvis.
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_14 : dfs1_entail_wit_1_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold dfs1_sequence_state_ready.
  split.
  - unfold csr_wf1 in *.
    destruct PreH1 as
      [Hvalid [Hrow [Hvis [Hfin [Hm [Hlo [Hhi [Hcol [Hroword Hcap]]]]]]]]].
    repeat (split; try assumption).
    rewrite Zlength_replace_Znth.
    exact Hvis.
  - split; [assumption | lia].
Qed.

Lemma proof_of_dfs1_entail_wit_1_split_goal_15 : dfs1_entail_wit_1_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold csr_wf1 in *.
  destruct PreH1 as
    [Hvalid [Hrow [Hvis [Hfin [Hm [Hlo [Hhi [Hcol [Hroword Hcap]]]]]]]]].
  repeat (split; try assumption).
  rewrite Zlength_replace_Znth.
  exact Hvis.
Qed.

Lemma proof_of_dfs1_entail_wit_1 : dfs1_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_7.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_8.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_9.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_10.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_11.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_12.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_13.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_14.
  - Goal_apply proof_of_dfs1_entail_wit_1_split_goal_15.
Qed.

Lemma proof_of_dfs1_entail_wit_2_split_goal_1 : dfs1_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold csr_wf1 in PreH2.
  destruct PreH2 as
    [_ [_ [_ [_ [_ [_ [_ [Hcol [_ _]]]]]]]]].
  specialize (Hcol i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_dfs1_entail_wit_2_split_goal_2 : dfs1_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold csr_wf1 in PreH2.
  destruct PreH2 as
    [_ [_ [_ [_ [_ [_ [_ [Hcol [_ _]]]]]]]]].
  specialize (Hcol i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_dfs1_entail_wit_2_split_goal_3 : dfs1_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_dfs1_entail_wit_2 : dfs1_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dfs1_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_dfs1_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_dfs1_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_dfs1_entail_wit_3_1_split_goal_1 : dfs1_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold dfs1_active_timer_surplus, dfs1_timer_surplus_preserved in *.
  intros spare Hspare Hbound.
  specialize (PreH10 (spare + 1) ltac:(lia)) as Hpreserve.
  replace (timer_v_ + spare + 1) with (timer_v_ + (spare + 1)) by lia.
  apply Hpreserve.
  replace (timer_m_2 + (spare + 1)) with (timer_m_2 + spare + 1) by lia.
  apply PreH36; lia.
Qed.

Lemma proof_of_dfs1_entail_wit_3_1_split_goal_2 : dfs1_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11.
  split; [lia |].
  apply PreH35.
  exact H.
Qed.

Lemma proof_of_dfs1_entail_wit_3_1_split_goal_3 : dfs1_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_dfs1_entail_wit_3_1_split_goal_4 : dfs1_entail_wit_3_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold dfs1_timer_surplus_preserved in PreH10.
  specialize (PreH10 1 ltac:(lia) PreH32).
  lia.
Qed.

Lemma proof_of_dfs1_entail_wit_3_1_split_goal_5 : dfs1_entail_wit_3_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold dfs1_timer_surplus_preserved in PreH10.
  pose proof (PreH10 1 ltac:(lia) PreH32) as Hnonzero.
  pose proof (count_nonzero_le_Zlength vis1_l_) as Hcount.
  unfold csr_wf1 in PreH1.
  destruct PreH1 as
    [_ [_ [Hvis_len [_ [_ [_ [_ [_ [_ _]]]]]]]]].
  rewrite Hvis_len in Hcount.
  rewrite PreH2 in Hcount.
  lia.
Qed.

Lemma proof_of_dfs1_entail_wit_3_1_split_goal_6 : dfs1_entail_wit_3_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_dfs1_entail_wit_3_1_split_goal_7 : dfs1_entail_wit_3_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Htimer0 : (0 <= timer_v_low_level_spec)%Z).
  { unfold dfs1_active_sequence_extension, dfs1_sequence_extension in PreH18.
    destruct PreH18 as [[[Htimer0 _] _] _].
    exact Htimer0. }
  eapply dfs1_active_sequence_extension_recurse.
  - exact Htimer0.
  - rewrite PreH2. lia.
  - exact PreH18.
  - exact PreH4.
Qed.

Lemma proof_of_dfs1_entail_wit_3_1 : dfs1_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dfs1_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_dfs1_entail_wit_3_1_split_goal_2.
  - Goal_apply proof_of_dfs1_entail_wit_3_1_split_goal_3.
  - Goal_apply proof_of_dfs1_entail_wit_3_1_split_goal_4.
  - Goal_apply proof_of_dfs1_entail_wit_3_1_split_goal_5.
  - Goal_apply proof_of_dfs1_entail_wit_3_1_split_goal_6.
  - Goal_apply proof_of_dfs1_entail_wit_3_1_split_goal_7.
Qed.

Lemma proof_of_dfs1_entail_wit_3_2_split_goal_1 : dfs1_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_dfs1_entail_wit_3_2_split_goal_2 : dfs1_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dfs1_solve_split.
Qed.

Lemma proof_of_dfs1_entail_wit_3_2 : dfs1_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dfs1_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_dfs1_entail_wit_3_2_split_goal_2.
Qed.

Lemma proof_of_dfs1_return_wit_1_split_goal_1 : dfs1_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_dfs1_return_wit_1_split_goal_2 : dfs1_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros spare Hspare Hbound.
  specialize (PreH26 spare Hspare Hbound).
  lia.
Qed.

Lemma proof_of_dfs1_return_wit_1_split_goal_3 : dfs1_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH7 as [_ Hfresh].
  eapply (dfs1_return_close_sequence_active
    g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec
    u_pre i vis1_m fin_m timer_m X_low_level_spec).
  - rewrite PreH4. lia.
  - rewrite PreH4. lia.
  - unfold csr_wf1 in PreH2.
    destruct PreH2 as
      [_ [_ [_ [Hfin [_ [_ [_ [_ [_ _]]]]]]]]].
    exact Hfin.
  - exact Hfresh.
  - rewrite <- PreH10. lia.
  - exact PreH8.
Qed.

Lemma proof_of_dfs1_return_wit_1_split_goal_4 : dfs1_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply dfs1_finish_prefix_marked_extend; eauto; try lia.
  unfold csr_wf1 in PreH2.
  destruct PreH2 as
    [_ [_ [_ [Hfin [_ [_ [_ [_ [_ _]]]]]]]]].
  rewrite PreH4 in Hfin.
  exact Hfin.
Qed.

Lemma proof_of_dfs1_return_wit_1_split_goal_5 : dfs1_return_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Htimer0 : (0 <= timer_v_low_level_spec)%Z).
  { pose proof PreH7 as Hactive.
    unfold dfs1_active_sequence_extension, dfs1_sequence_extension in Hactive.
    destruct Hactive as [[[Htimer0 _] _] _].
    exact Htimer0. }
  eapply (dfs1_sequence_extension_close_active
    g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec
    timer_v_low_level_spec vis1_m fin_m timer_m u_pre).
  - exact PreH7.
  - unfold csr_wf1 in PreH2.
    destruct PreH2 as
      [_ [_ [_ [Hfin [_ [_ [_ [_ [_ _]]]]]]]]].
    exact Hfin.
  - exact Htimer0.
  - rewrite PreH4. lia.
  - exact PreH23.
Qed.

Lemma proof_of_dfs1_return_wit_1_split_goal_6 : dfs1_return_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold dfs1_sequence_state_ready in *.
  destruct PreH5 as [_ [Hfaith _]].
  unfold csr_wf1 in PreH2.
  destruct PreH2 as
    [Hvalid [Hrow [Hvis [Hfin [Hm [Hlo [Hhi [Hcol [Hroword Hcap]]]]]]]]].
  pose proof (count_nonzero_le_Zlength vis1_m) as Hcount.
  rewrite Hvis in Hcount.
  rewrite PreH4 in Hcount.
  split.
  - unfold csr_wf1.
    repeat (split; try assumption).
    rewrite Zlength_replace_Znth.
    exact Hfin.
  - split; [exact Hfaith | lia].
Qed.

Lemma proof_of_dfs1_return_wit_1_split_goal_7 : dfs1_return_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold csr_wf1 in PreH2.
  destruct PreH2 as
    [Hvalid [Hrow [Hvis [Hfin [Hm [Hlo [Hhi [Hcol [Hroword Hcap]]]]]]]]].
  repeat (split; try assumption).
  rewrite Zlength_replace_Znth.
  exact Hfin.
Qed.

Lemma proof_of_dfs1_return_wit_1 : dfs1_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dfs1_return_wit_1_split_goal_1.
  - Goal_apply proof_of_dfs1_return_wit_1_split_goal_2.
  - Goal_apply proof_of_dfs1_return_wit_1_split_goal_3.
  - Goal_apply proof_of_dfs1_return_wit_1_split_goal_4.
  - Goal_apply proof_of_dfs1_return_wit_1_split_goal_5.
  - Goal_apply proof_of_dfs1_return_wit_1_split_goal_6.
  - Goal_apply proof_of_dfs1_return_wit_1_split_goal_7.
Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure_split_goal_1 : dfs1_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r.
  rewrite PreH43 in PreH15 |- *.
  eapply (dfs1_recurse_sequence_close__dfs1_active
    g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec
    u_pre i vis1_m fin_m timer_m X_low_level_spec).
  - rewrite <- PreH24. exact PreH27.
  - rewrite <- PreH43.
    rewrite PreH18.
    lia.
  - exact PreH15.
  - exact PreH22.
Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure : dfs1_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dfs1_partial_solve_wit_6_pure_split_goal_1.
Qed.

Lemma proof_of_dfs1_low_level_spec_entail_bind_spec : dfs1_low_level_spec_entail_bind_spec.
Proof.
  unfold dfs1_low_level_spec_entail_bind_spec.
  intros B u n_pre radj_col_pre radj_row_pre vis1_pre fin_pre timer_p_pre g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec vis1_l_bind_spec fin_l_bind_spec timer_v_bind_spec X_bind_spec f_bind_spec.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | Hsafe : safeExec _ (bind _ _) _ |- _ =>
      apply safeExec_bind in Hsafe as
        (X_low_level_spec & Hsafe_first & Hsafe_cont)
  end.
  Exists g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec
    vis1_l_bind_spec fin_l_bind_spec timer_v_bind_spec X_low_level_spec.
  split_pure_spatial.
  - cancel (IntArray.full radj_col_pre
      (m_of radj_row_l_bind_spec) radj_col_l_bind_spec).
    cancel (IntArray.full radj_row_pre
      (n_pre + 1) radj_row_l_bind_spec).
    cancel (IntArray.full vis1_pre n_pre vis1_l_bind_spec).
    cancel (IntArray.full fin_pre n_pre fin_l_bind_spec).
    cancel ((timer_p_pre) # Int |-> timer_v_bind_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros timer_v_out vis1_l_out fin_l_out.
    Exists timer_v_out vis1_l_out fin_l_out.
    split_pure_spatial.
    + cancel (IntArray.full radj_col_pre
        (m_of radj_row_l_bind_spec) radj_col_l_bind_spec).
      cancel (IntArray.full radj_row_pre
        (n_pre + 1) radj_row_l_bind_spec).
      cancel (IntArray.full vis1_pre n_pre vis1_l_out).
      cancel (IntArray.full fin_pre n_pre fin_l_out).
      cancel ((timer_p_pre) # Int |-> timer_v_out).
    + split_pures; dump_pre_spatial; try assumption.
      match goal with
      | Hret : safeExec _ (return tt) X_low_level_spec |- _ =>
          exact (Hsafe_cont _ tt Hret)
      end.
  - split_pures; dump_pre_spatial; try assumption.
Qed. 

Lemma proof_of_dfs1_low_level_spec_entail_high_level_spec : dfs1_low_level_spec_entail_high_level_spec.
Proof.
  unfold dfs1_low_level_spec_entail_high_level_spec.
  intros u n_pre radj_col_pre radj_row_pre vis1_pre fin_pre timer_p_pre g_high_level_spec radj_col_l_high_level_spec radj_row_l_high_level_spec vis1_l_high_level_spec fin_l_high_level_spec timer_v_high_level_spec X_high_level_spec.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists g_high_level_spec radj_col_l_high_level_spec
    radj_row_l_high_level_spec vis1_l_high_level_spec
    fin_l_high_level_spec timer_v_high_level_spec X_high_level_spec.
  split_pure_spatial.
  - cancel (IntArray.full radj_col_pre
      (m_of radj_row_l_high_level_spec) radj_col_l_high_level_spec).
    cancel (IntArray.full radj_row_pre
      (n_pre + 1) radj_row_l_high_level_spec).
    cancel (IntArray.full vis1_pre n_pre vis1_l_high_level_spec).
    cancel (IntArray.full fin_pre n_pre fin_l_high_level_spec).
    cancel ((timer_p_pre) # Int |-> timer_v_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros timer_v_out vis1_l_out fin_l_out.
    Exists vis1_l_out fin_l_out timer_v_out.
    split_pure_spatial.
    + cancel (IntArray.full radj_col_pre
        (m_of radj_row_l_high_level_spec) radj_col_l_high_level_spec).
      cancel (IntArray.full radj_row_pre
        (n_pre + 1) radj_row_l_high_level_spec).
      cancel (IntArray.full vis1_pre n_pre vis1_l_out).
      cancel (IntArray.full fin_pre n_pre fin_l_out).
      cancel ((timer_p_pre) # Int |-> timer_v_out).
    + split_pures; dump_pre_spatial; assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed. 
