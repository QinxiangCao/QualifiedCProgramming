Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import kosaraju_rel_goal.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import kosaraju_rel_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
From MonadLib.MonadErr Require Import MonadErrHoare.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.Kosaraju.
Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.kosaraju_rel_lib.
Local Open Scope sac.

Lemma dfs2_safeExec_from_Hoare :
  forall {A : Type} (P : KSt -> Prop) (c : program KSt A)
         (X : A -> KSt -> Prop) (st : KSt),
    P st ->
    Hoare (fun st' => st' = st) c X ->
    safeExec P c X.
Proof.
  intros A P c X st Hpre [Hnrm Herr].
  exists st.
  split; [exact Hpre |].
  unfold safe, weakestpre.
  split.
  - intro Hc_err. exact (Herr st eq_refl Hc_err).
  - intros a st' Hc_nrm.
    exact (Hnrm a st st' eq_refl Hc_nrm).
Qed.

Lemma dfs2_pre_state :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l vis2_l sid_l : list Z)
         (root_v n : Z),
    adj_verts g = n ->
    pre_dfs2 g fadj_col_l fadj_row_l vis2_l sid_l root_v
      (dfs2_phase2_state nil vis2_l sid_l n).
Proof.
  intros g fadj_col_l fadj_row_l vis2_l sid_l root_v n Hverts.
  unfold pre_dfs2, dfs2_phase2_state.
  simpl.
  split.
  - intros u Hu.
    rewrite Hverts in Hu.
    tauto.
  - intros u Hu.
    reflexivity.
Qed.

Lemma dfs2_safeExec_true :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l vis2_l sid_l : list Z)
         (root u root_v n : Z),
    csr_wf2 g fadj_col_l fadj_row_l vis2_l sid_l ->
    adj_verts g = n ->
    0 <= u < n ->
    safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_l sid_l root_v)
      (dfs_scc g root u) (fun _ _ => True).
Proof.
  intros g fadj_col_l fadj_row_l vis2_l sid_l root u root_v n Hwf Hverts Hu.
  pose (st0 := dfs2_phase2_state nil vis2_l sid_l n).
  eapply dfs2_safeExec_from_Hoare with (st := st0).
  - unfold st0. apply dfs2_pre_state. exact Hverts.
  - unfold dfs_scc.
    pose proof (@DFS_scc_neighbor_visited_strong AdjGraph Z (Z * Z) KG
      g (proj1 Hwf) st0 root u) as Hdfs.
    unfold Hoare in *.
    destruct Hdfs as [Hnrm Herr].
    split.
    + intros a st st' Hst Hstep. exact I.
    + intros st Hst Hstep. eapply Herr; eauto.
Qed.

Ltac dfs2_destruct_known_csr_wf2 :=
  repeat match goal with
  | H : csr_wf2 _ _ _ _ _ |- _ =>
      unfold csr_wf2 in H;
      destruct H as
        [? [? [? [? [? [? [? [? [? ?]]]]]]]]]
  end.

Ltac dfs2_rewrite_same_replace :=
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

Ltac dfs2_solve_replace_neq_once :=
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

Ltac dfs2_solve_split :=
  LLM_pre_process ltac:(lia || nia || int_auto);
  subst;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- forall _, _ => intro
  | |- _ -> _ => intro
  end;
  try solve
    [ eapply csr_wf2_vis_sid_replace_Znth; eauto; lia
    | match goal with
      | |- safeExec _ (dfs_scc_from ?g ?fc ?fr ?root ?u (Znth ?u ?fr 0)) _ =>
          change (Znth u fr 0) with (csr_lo u fr);
          eapply dfs2_entry_close; eauto; lia
      end ];
  dfs2_destruct_known_csr_wf2;
  try dfs2_rewrite_same_replace;
  try solve [eapply dfs2_entry_close; eauto; lia];
  try solve [assumption | reflexivity | lia | eauto];
  repeat (try dfs2_solve_replace_neq_once; try dfs2_rewrite_same_replace;
          try solve [eapply dfs2_entry_close; eauto; lia |
                     assumption | reflexivity | congruence | lia | eauto]).


Lemma proof_of_transpose_safety_wit_5_split_goal_1 : transpose_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r.
  specialize (PreH21 v ltac:(lia)).
  lia.
Qed.

Lemma proof_of_transpose_safety_wit_5_split_goal_2 : transpose_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r.
  specialize (PreH21 v ltac:(lia)).
  lia.
Qed.

Lemma proof_of_transpose_safety_wit_5 : transpose_safety_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pures.
  - dump_pre_spatial.
    specialize (PreH21 v ltac:(lia)).
    lia.
  - dump_pre_spatial.
    specialize (PreH21 v ltac:(lia)).
    lia.
Qed. 

Lemma proof_of_transpose_entail_wit_1_split_goal_1 : transpose_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_transpose_entail_wit_1 : transpose_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists radj_row_l_low_level_spec.
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_low_level_spec) fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_low_level_spec) radj_col_l_low_level_spec).
    cancel (IntArray.full radj_row_pre (n_pre + 1) radj_row_l_low_level_spec).
    cancel (IntArray.full pos_pre n_pre pos_l_low_level_spec).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_transpose_entail_wit_2_split_goal_1 : transpose_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH16.
Qed.

Lemma proof_of_transpose_entail_wit_2 : transpose_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (replace_Znth v 0 rr_m_2).
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_low_level_spec) fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_low_level_spec) radj_col_l_low_level_spec).
    cancel (IntArray.full radj_row_pre (n_pre + 1) (replace_Znth v 0 rr_m_2)).
    cancel (IntArray.full pos_pre n_pre pos_l_low_level_spec).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + rewrite Zlength_replace_Znth. exact PreH16.
    + intros k Hk.
      destruct (Z.eq_dec k v) as [-> | Hneq].
      * rewrite Znth_replace_Znth_Same by lia. reflexivity.
      * rewrite Znth_replace_Znth_Diff by lia.
        apply PreH17. lia.
Qed. 

Lemma proof_of_transpose_entail_wit_3_split_goal_1 : transpose_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH17 k ltac:(lia)).
  rewrite PreH17.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_3_split_goal_2 : transpose_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply transpose_count_values_zero.
  intros k0 Hk0. apply PreH17. lia.
Qed.

Lemma proof_of_transpose_entail_wit_3_split_goal_3 : transpose_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply transpose_count_ready_zero; [lia|].
  intros k0 Hk0. apply PreH17. lia.
Qed.

Lemma proof_of_transpose_entail_wit_3 : transpose_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists rr_m_2.
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_low_level_spec) fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_low_level_spec) radj_col_l_low_level_spec).
    cancel (IntArray.full radj_row_pre (n_pre + 1) rr_m_2).
    cancel (IntArray.full pos_pre n_pre pos_l_low_level_spec).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + apply transpose_count_ready_zero; [lia|].
      intros k0 Hk0. apply PreH17. lia.
    + apply transpose_count_values_zero.
      intros k0 Hk0. apply PreH17. lia.
    + intros k0 Hk0. specialize (PreH17 k0 ltac:(lia)). lia.
Qed. 

Lemma proof_of_transpose_entail_wit_4_split_goal_1 : transpose_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH19 k H).
Qed.

Lemma proof_of_transpose_entail_wit_4_split_goal_2 : transpose_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH9 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [Hcol _]]]]]].
  specialize (Hcol j ltac:(rewrite <- PreH3; lia)).
  rewrite PreH13 in Hcol.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_4_split_goal_3 : transpose_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH9 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [Hcol _]]]]]].
  specialize (Hcol j ltac:(rewrite <- PreH3; lia)).
  rewrite PreH13 in Hcol.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_4 : transpose_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH9 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [Hcol _]]]]]].
  specialize (Hcol j ltac:(rewrite <- PreH3; lia)).
  rewrite PreH13 in Hcol.
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_low_level_spec) fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_low_level_spec) radj_col_l_low_level_spec).
    cancel (IntArray.full radj_row_pre (n_pre + 1) rr_m).
    cancel (IntArray.full pos_pre n_pre pos_l_low_level_spec).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_transpose_entail_wit_5_split_goal_1 : transpose_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Znth_replace_old_or_new rr_m_2 k v (Znth v rr_m_2 0 + 1) 0)
    as [Hnew | Hold].
  - rewrite Hnew.
    specialize (PreH21 v ltac:(lia)).
    lia.
  - rewrite Hold.
    specialize (PreH21 k H).
    lia.
Qed.

Lemma proof_of_transpose_entail_wit_5_split_goal_2 : transpose_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply transpose_count_values_step.
  - exact PreH20.
  - lia.
  - lia.
  - lia.
  - lia.
  - symmetry. exact PreH9.
Qed.

Lemma proof_of_transpose_entail_wit_5_split_goal_3 : transpose_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply transpose_count_ready_step.
  - lia.
  - lia.
  - lia.
  - exact PreH19.
Qed.

Lemma proof_of_transpose_entail_wit_5_split_goal_4 : transpose_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH18.
Qed.

Lemma proof_of_transpose_entail_wit_5 : transpose_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength radj_row_pre (n_pre + 1)
    (replace_Znth v (Znth v rr_m_2 0 + 1) rr_m_2)).
  Intros_p Hlen.
  rewrite Zlength_replace_Znth in Hlen.
  Exists (replace_Znth v (Znth v rr_m_2 0 + 1) rr_m_2).
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_low_level_spec) fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_low_level_spec) radj_col_l_low_level_spec).
    cancel (IntArray.full radj_row_pre (n_pre + 1)
      (replace_Znth v (Znth v rr_m_2 0 + 1) rr_m_2)).
    cancel (IntArray.full pos_pre n_pre pos_l_low_level_spec).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + rewrite Zlength_replace_Znth.
      exact PreH18.
    + eapply transpose_count_ready_step.
      * lia.
      * lia.
      * lia.
      * exact PreH19.
    + eapply transpose_count_values_step.
      * exact PreH20.
      * lia.
      * lia.
      * lia.
      * lia.
      * symmetry. exact PreH9.
    + intros k0 Hk0.
      destruct (Z.eq_dec k0 v) as [->|Hneq].
      * rewrite Znth_replace_Znth_Same by lia.
        specialize (PreH21 v ltac:(lia)). lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        specialize (PreH21 k0 Hk0). lia.
Qed. 

Lemma proof_of_transpose_entail_wit_6 : transpose_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength radj_row_pre (n_pre + 1) rr_m_2).
  Intros_p Hrr_len.
  prop_apply_p (IntArray.full_Zlength pos_pre n_pre pos_l_low_level_spec).
  Intros_p Hpos_len.
  assert (j = m) as Hjm by lia.
  subst j.
  assert (Hpref : transpose_prefix_inv n_pre m 0 0 rr_m_2 rr_m_2).
  { apply transpose_count_ready_prefix_start; assumption || lia. }
  assert (Hoffs :
    transpose_prefix_offsets n_pre 0 rr_m_2 pos_l_low_level_spec rr_m_2).
  { apply transpose_prefix_offsets_start; try lia. }
  pose proof (PreH19 0 ltac:(lia)) as Hzero_bound.
  Exists rr_m_2 rr_m_2 pos_l_low_level_spec.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_transpose_entail_wit_7 : transpose_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrr_n : n_pre <= Zlength rr_m_2) by lia.
  assert (Hrr_v : 0 <= v < Zlength rr_m_2) by lia.
  pose proof PreH16 as Hinv_parts.
  unfold transpose_prefix_inv in Hinv_parts.
  destruct Hinv_parts as [Htotal [Hsum [Hnonneg Htail]]].
  assert (Hpref' :
    transpose_prefix_inv n_pre m (v + 1) (sum + Znth v rr_m_2 0)
      (replace_Znth v sum rr_m_2) cnt_m_2).
  { eapply transpose_prefix_inv_step.
    - lia.
    - exact Hrr_v.
    - exact Hrr_n.
    - exact PreH16. }
  assert (Hoffs' :
    transpose_prefix_offsets n_pre (v + 1)
      (replace_Znth v sum rr_m_2) (replace_Znth v sum pos_m_2) cnt_m_2).
  { apply transpose_prefix_offsets_step with (deg := Znth v cnt_m_2 0).
    - exact PreH18.
    - lia.
    - exact Hsum.
    - reflexivity. }
  pose proof (transpose_prefix_inv_sum_bounds n_pre m (v + 1)
    (sum + Znth v rr_m_2 0) (replace_Znth v sum rr_m_2) cnt_m_2
    ltac:(lia) Hpref') as Hsum_bounds.
  assert (Hnext_bound :
    v + 1 < n_pre ->
    sum + Znth v rr_m_2 0 +
      Znth (v + 1) (replace_Znth v sum rr_m_2) 0 <= m).
  { intro Hvnext.
    apply (transpose_prefix_inv_next_bound n_pre m (v + 1)
      (sum + Znth v rr_m_2 0) (replace_Znth v sum rr_m_2) cnt_m_2);
      [lia | exact Hpref']. }
  assert (Hlo0 : 0 < v + 1 ->
    csr_lo 0 (replace_Znth v sum rr_m_2) = 0).
  { intros _.
    unfold csr_lo.
    destruct (Z.eq_dec v 0) as [-> | Hne].
    - rewrite Znth_replace_Znth_Same by lia.
      eapply transpose_prefix_inv_zero_sum in PreH16.
      exact PreH16.
    - rewrite Znth_replace_Znth_Diff by lia.
      apply PreH20. lia. }
  assert (Hrow_bounds : forall k, 0 <= k < n_pre ->
    0 <= Znth k (replace_Znth v sum rr_m_2) 0 <= m).
  { intros k0 Hk0.
    destruct (Z.eq_dec k0 v) as [-> | Hne].
    - rewrite Znth_replace_Znth_Same by lia. split; assumption.
    - rewrite Znth_replace_Znth_Diff by lia. apply PreH24. exact Hk0. }
  Exists (replace_Znth v sum rr_m_2) cnt_m_2 (replace_Znth v sum pos_m_2).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    rewrite Zlength_replace_Znth. exact PreH15.
    rewrite Zlength_replace_Znth. exact PreH19.
Qed. 

Lemma proof_of_transpose_entail_wit_8_split_goal_1 : transpose_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply transpose_scatter_contents_start.
Qed.

Lemma proof_of_transpose_entail_wit_8_split_goal_2 : transpose_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (v = n_pre) as Hv by lia.
  subst v.
  pose proof PreH16 as Hinv_parts.
  unfold transpose_prefix_inv in Hinv_parts.
  destruct Hinv_parts as [Htotal [Hsum [Hnonneg Htail]]].
  assert (sum = m) as Hsum_m by lia.
  assert (Hrr_index : 0 <= n_pre < Zlength rr_m_2) by lia.
  assert (Hrr_last : Znth n_pre (replace_Znth n_pre sum rr_m_2) 0 = m).
  { rewrite Znth_replace_Znth_Same by exact Hrr_index. exact Hsum_m. }
  assert (Hpref' :
    transpose_prefix_inv n_pre m n_pre m
      (replace_Znth n_pre sum rr_m_2) cnt_m).
  { unfold transpose_prefix_inv.
    split; [exact Htotal|].
    split; [lia|].
    split; [exact Hnonneg|].
    intros k0 Hk0. lia. }
  assert (Hoffs' :
    transpose_prefix_offsets n_pre n_pre
      (replace_Znth n_pre sum rr_m_2) pos_m_2 cnt_m).
  { unfold transpose_prefix_offsets in PreH18 |- *.
    destruct PreH18 as [Hrr_n [Hpos_n [Hdone Htail_off]]].
    split.
    - rewrite Zlength_replace_Znth. exact Hrr_n.
    - split; [exact Hpos_n|].
      split.
      + intros k0 Hk0. specialize (Hdone k0 Hk0) as [Hrr Hpos].
        split; [|exact Hpos].
        rewrite Znth_replace_Znth_Diff by lia. exact Hrr.
      + intros k0 Hk0. lia. }
  eapply (transpose_scatter_rows_from_prefix n_pre m fadj_col_l_low_level_spec
    (replace_Znth n_pre sum rr_m_2) pos_m_2 cnt_m).
  - lia.
  - lia.
  - rewrite Zlength_replace_Znth. exact PreH19.
  - exact Hrr_last.
  - exact Hpref'.
  - exact PreH17.
  - exact Hoffs'.
Qed.

Lemma proof_of_transpose_entail_wit_8_split_goal_3 : transpose_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (v = n_pre) as Hv by lia.
  subst v.
  pose proof PreH16 as Hinv_parts.
  unfold transpose_prefix_inv in Hinv_parts.
  destruct Hinv_parts as [Htotal [Hsum [Hnonneg Htail]]].
  assert (sum = m) as Hsum_m by lia.
  assert (Hrr_index : 0 <= n_pre < Zlength rr_m_2) by lia.
  assert (Hrr_last : Znth n_pre (replace_Znth n_pre sum rr_m_2) 0 = m).
  { rewrite Znth_replace_Znth_Same by exact Hrr_index. exact Hsum_m. }
  assert (Hpref' :
    transpose_prefix_inv n_pre m n_pre m
      (replace_Znth n_pre sum rr_m_2) cnt_m).
  { unfold transpose_prefix_inv.
    split; [exact Htotal|].
    split; [lia|].
    split; [exact Hnonneg|].
    intros k0 Hk0. lia. }
  assert (Hoffs' :
    transpose_prefix_offsets n_pre n_pre
      (replace_Znth n_pre sum rr_m_2) pos_m_2 cnt_m).
  { unfold transpose_prefix_offsets in PreH18 |- *.
    destruct PreH18 as [Hrr_n [Hpos_n [Hdone Htail_off]]].
    split.
    - rewrite Zlength_replace_Znth. exact Hrr_n.
    - split; [exact Hpos_n|].
      split.
      + intros k0 Hk0. specialize (Hdone k0 Hk0) as [Hrr Hpos].
        split; [|exact Hpos].
        rewrite Znth_replace_Znth_Diff by lia. exact Hrr.
      + intros k0 Hk0. lia. }
  eapply (transpose_scatter_inv_from_prefix n_pre m fadj_col_l_low_level_spec
    (replace_Znth n_pre sum rr_m_2) pos_m_2 cnt_m).
  - lia.
  - exact Hpref'.
  - exact PreH17.
  - exact Hoffs'.
Qed.

Lemma proof_of_transpose_entail_wit_8_split_goal_4 : transpose_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (v = n_pre) as Hv by lia.
  subst v.
  unfold csr_lo.
  rewrite Znth_replace_Znth_Diff by lia.
  apply PreH20.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_8_split_goal_5 : transpose_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH19.
Qed.

Lemma proof_of_transpose_entail_wit_8_split_goal_6 : transpose_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (v = n_pre) as Hv by lia.
  subst v.
  pose proof PreH16 as Hinv_parts.
  unfold transpose_prefix_inv in Hinv_parts.
  destruct Hinv_parts as [Htotal [Hsum _]].
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_8 : transpose_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength radj_col_pre
    (m_of fadj_row_l_low_level_spec) radj_col_l_low_level_spec).
  Intros_p Hrc_len.
  assert (v = n_pre) as Hv by lia.
  subst v.
  pose proof PreH16 as Hinv_parts.
  unfold transpose_prefix_inv in Hinv_parts.
  destruct Hinv_parts as [Htotal [Hsum [Hnonneg Htail]]].
  assert (Hsum_m : sum = m) by lia.
  assert (Hrr_index : 0 <= n_pre < Zlength rr_m_2) by lia.
  assert (Hrr'_len : Zlength (replace_Znth n_pre sum rr_m_2) = n_pre + 1).
  { rewrite Zlength_replace_Znth. exact PreH19. }
  assert (Hrr_last : Znth n_pre (replace_Znth n_pre sum rr_m_2) 0 = m).
  { rewrite Znth_replace_Znth_Same by exact Hrr_index. exact Hsum_m. }
  assert (Hlo0 : csr_lo 0 (replace_Znth n_pre sum rr_m_2) = 0).
  { unfold csr_lo.
    rewrite Znth_replace_Znth_Diff by lia.
    apply PreH20. lia. }
  assert (Hpref' : transpose_prefix_inv n_pre m n_pre m
    (replace_Znth n_pre sum rr_m_2) cnt_m).
  { unfold transpose_prefix_inv.
    split; [exact Htotal|].
    split; [lia|].
    split; [exact Hnonneg|].
    intros k0 Hk0. lia. }
  assert (Hoffs' : transpose_prefix_offsets n_pre n_pre
    (replace_Znth n_pre sum rr_m_2) pos_m_2 cnt_m).
  { unfold transpose_prefix_offsets in PreH18 |- *.
    destruct PreH18 as [Hrr_n [Hpos_n [Hdone Htail_off]]].
    split.
    - rewrite Zlength_replace_Znth. exact Hrr_n.
    - split; [exact Hpos_n|].
      split.
      + intros k0 Hk0. specialize (Hdone k0 Hk0) as [Hrr Hpos].
        split; [|exact Hpos].
        rewrite Znth_replace_Znth_Diff by lia. exact Hrr.
      + intros k0 Hk0. lia. }
  assert (Hscatter : transpose_scatter_inv n_pre m 0
    fadj_col_l_low_level_spec (replace_Znth n_pre sum rr_m_2) pos_m_2).
  { eapply transpose_scatter_inv_from_prefix; eauto. }
  assert (Hrows : transpose_scatter_rows n_pre m fadj_col_l_low_level_spec
    (replace_Znth n_pre sum rr_m_2)).
  { eapply transpose_scatter_rows_from_prefix; eauto. }
  assert (Hcontents : transpose_scatter_contents g_low_level_spec n_pre 0
    fadj_row_l_low_level_spec fadj_col_l_low_level_spec
    (replace_Znth n_pre sum rr_m_2) radj_col_l_low_level_spec).
  { apply transpose_scatter_contents_start. }
  Exists (replace_Znth n_pre sum rr_m_2) pos_m_2 radj_col_l_low_level_spec.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: rewrite PreH10; assumption.
Qed. 

Lemma proof_of_transpose_entail_wit_9_split_goal_1 : transpose_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_transpose_entail_wit_9_split_goal_2 : transpose_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9.
  unfold csr_lo in PreH20.
  exact PreH20.
Qed.

Lemma proof_of_transpose_entail_wit_9_split_goal_3 : transpose_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH15 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [_ [Hhi _]]]]].
  pose proof (Hhi u ltac:(rewrite PreH19; lia)) as Huhi.
  unfold csr_hi in Huhi.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_9_split_goal_4 : transpose_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH15 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [_ [Horder _]]]]]]].
  pose proof (Horder u ltac:(rewrite PreH19; lia)) as Huorder.
  unfold csr_lo, csr_hi in Huorder.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_9_split_goal_5 : transpose_entail_wit_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH15 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [Hlo _]]]].
  pose proof (Hlo u ltac:(rewrite PreH19; lia)) as Hulo.
  unfold csr_lo in Hulo.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_9_split_goal_6 : transpose_entail_wit_9_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_transpose_entail_wit_9_split_goal_7 : transpose_entail_wit_9_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_transpose_entail_wit_9 : transpose_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH15 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [Hlo [Hhi [_ [Horder _]]]]]]].
  pose proof (Hlo u ltac:(rewrite PreH19; lia)) as Hulo.
  pose proof (Hhi u ltac:(rewrite PreH19; lia)) as Huhi.
  pose proof (Horder u ltac:(rewrite PreH19; lia)) as Huorder.
  Exists rr_m_2 pos_m_2 rc_m_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_transpose_entail_wit_10_split_goal_1 : transpose_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH14 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [Hcol _]]]]]].
  pose proof (Hcol j ltac:(lia)) as Hjcol.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_10_split_goal_2 : transpose_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH14 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [Hcol _]]]]]].
  pose proof (Hcol j ltac:(lia)) as Hjcol.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_10 : transpose_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH14 as Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [Hcol [_ _]]]]]]].
  pose proof (Hcol j ltac:(lia)) as Hjcol.
  rewrite PreH18 in Hjcol.
  Exists rr_m_2 pos_m_2 rc_m_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_transpose_entail_wit_11_split_goal_1 : transpose_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (transpose_scatter_inv_current_bound n_pre m j
    fadj_col_l_low_level_spec rr_m_2 pos_m v PreH29 ltac:(lia)
    ltac:(lia) ltac:(symmetry; exact PreH5)) as Hbound.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_11_split_goal_2 : transpose_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (transpose_scatter_inv_current_bound n_pre m j
    fadj_col_l_low_level_spec rr_m_2 pos_m v PreH29 ltac:(lia)
    ltac:(lia) ltac:(symmetry; exact PreH5)) as Hbound.
  lia.
Qed.

Lemma proof_of_transpose_entail_wit_11 : transpose_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hbound : 0 <= Znth v pos_m 0 < m).
  { eapply transpose_scatter_inv_current_bound; try eassumption; lia. }
  Exists rr_m_2 rc_m_2 pos_m.
  split_pure_spatial.
  - cancel (IntArray.full pos_pre n_pre pos_m).
    cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_low_level_spec)
      fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_low_level_spec) rc_m_2).
    cancel (IntArray.full radj_row_pre (n_pre + 1) rr_m_2).
  - split_pures; try (dump_pre_spatial; eauto; lia).
Qed. 

Lemma proof_of_transpose_entail_wit_12_split_goal_1 : transpose_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst p.
  eapply transpose_scatter_contents_step; try eassumption; try lia.
  intros src1 src2 t Hsrc1 Hsrc2 Hrow1 Hrow2.
  eapply csr_wf2_core_row_owner; eassumption.
Qed.

Lemma proof_of_transpose_entail_wit_12_split_goal_2 : transpose_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst p.
  eapply transpose_scatter_inv_step; try eassumption; lia.
Qed.

Lemma proof_of_transpose_entail_wit_12_split_goal_3 : transpose_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH19.
Qed.

Lemma proof_of_transpose_entail_wit_12_split_goal_4 : transpose_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH19.
Qed.

Lemma proof_of_transpose_entail_wit_12_split_goal_5 : transpose_entail_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  rewrite PreH14.
  exact PreH17.
Qed.

Lemma proof_of_transpose_entail_wit_12 : transpose_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcontents : transpose_scatter_contents g_low_level_spec n_pre (j + 1)
    fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2
    (replace_Znth p u rc_m_2)).
  { subst p.
    eapply transpose_scatter_contents_step; try eassumption; try lia.
    intros src1 src2 t Hsrc1 Hsrc2 Hrow1 Hrow2.
    eapply csr_wf2_core_row_owner; eassumption. }
  assert (Hinv : transpose_scatter_inv n_pre m (j + 1)
    fadj_col_l_low_level_spec rr_m_2
    (replace_Znth v (p + 1) pos_m_2)).
  { subst p.
    eapply transpose_scatter_inv_step; try eassumption; lia. }
  Exists rr_m_2 (replace_Znth v (p + 1) pos_m_2)
    (replace_Znth p u rc_m_2).
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_low_level_spec)
      fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_low_level_spec)
      (replace_Znth p u rc_m_2)).
    cancel (IntArray.full radj_row_pre (n_pre + 1) rr_m_2).
    cancel (IntArray.full pos_pre n_pre (replace_Znth v (p + 1) pos_m_2)).
  - split_pures; try (dump_pre_spatial; try rewrite Zlength_replace_Znth; eauto; lia).
Qed. 

Lemma proof_of_transpose_entail_wit_13_split_goal_1 : transpose_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcursor : csr_lo (u + 1) fadj_row_l_low_level_spec = j).
  { unfold csr_lo, csr_hi in *. lia. }
  rewrite Hcursor.
  exact PreH29.
Qed.

Lemma proof_of_transpose_entail_wit_13_split_goal_2 : transpose_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcursor : csr_lo (u + 1) fadj_row_l_low_level_spec = j).
  { unfold csr_lo, csr_hi in *. lia. }
  rewrite Hcursor.
  rewrite PreH9.
  exact PreH27.
Qed.

Lemma proof_of_transpose_entail_wit_13_split_goal_3 : transpose_entail_wit_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold transpose_scatter_rows in PreH28.
  tauto.
Qed.

Lemma proof_of_transpose_entail_wit_13 : transpose_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcursor : csr_lo (u + 1) fadj_row_l_low_level_spec = j).
  { unfold csr_lo, csr_hi in *. lia. }
  assert (Hrrlen : Zlength rr_m_2 = n_pre + 1).
  { unfold transpose_scatter_rows in PreH28. tauto. }
  Exists rr_m_2 pos_m_2 rc_m_2.
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_low_level_spec)
      fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_low_level_spec) rc_m_2).
    cancel (IntArray.full radj_row_pre (n_pre + 1) rr_m_2).
    cancel (IntArray.full pos_pre n_pre pos_m_2).
  - split_pures; try (dump_pre_spatial; try rewrite Hcursor; eauto; lia).
Qed. 



Lemma proof_of_transpose_return_wit_1 : transpose_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (u = n_pre) by lia. subst u.
  assert (Hspec : transpose_spec g_low_level_spec fadj_col_l_low_level_spec
    fadj_row_l_low_level_spec rc_m rr_m n_pre).
  { eapply (transpose_spec_from_completed_scatter__transpose_exit
      g_low_level_spec n_pre m fadj_col_l_low_level_spec
      fadj_row_l_low_level_spec rc_m rr_m pos_m); eassumption. }
  Exists pos_m rc_m rr_m.
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_low_level_spec)
      fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_low_level_spec) rc_m).
    cancel (IntArray.full radj_row_pre (n_pre + 1) rr_m).
    cancel (IntArray.full pos_pre n_pre pos_m).
  - split_pures; dump_pre_spatial; exact Hspec.
Qed. 

Lemma proof_of_kosaraju_entail_wit_1 : kosaraju_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength sid_pre n_pre sid_l_high_level_spec).
  Intros_p Hsid_len.
  assert (Hm : Znth n_pre fadj_row_l_high_level_spec 0 =
               m_of fadj_row_l_high_level_spec).
  { unfold csr_wf2_core in PreH11.
    destruct PreH11 as [_ [Hrow _]].
    unfold m_of.
    rewrite Hrow, PreH13.
    replace (n_pre + 1 - 1) with n_pre by lia.
    reflexivity. }
  Exists l_5 l_4 l_3 l_2 l l_6.
  split_pure_spatial.
  - rewrite <- Hm.
    repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_kosaraju_entail_wit_2_split_goal_1 : kosaraju_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_kosaraju_entail_wit_2_split_goal_2 : kosaraju_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_kosaraju_entail_wit_2 : kosaraju_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst m.
  prop_apply (IntArray.full_Zlength vis1 n_pre vis1_l0).
  Intros_p Hvis1_len.
  Exists vis2_l0 vis1_l0.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_kosaraju_entail_wit_3_split_goal_1 : kosaraju_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH11.
Qed.

Lemma proof_of_kosaraju_entail_wit_3_split_goal_2 : kosaraju_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH10.
Qed.

Lemma proof_of_kosaraju_entail_wit_3 : kosaraju_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst m.
  Exists (replace_Znth u 0 vm2_2) (replace_Znth u 0 vm_2).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption; try (rewrite Zlength_replace_Znth; lia).
    all: intros i Hi; destruct (Z.eq_dec i u) as [-> | Hne].
    all: try (rewrite Znth_replace_Znth_Same by (rewrite ?PreH10, ?PreH11; lia); reflexivity).
    all: rewrite Znth_replace_Znth_Diff by (rewrite ?PreH10, ?PreH11; lia).
    all: first [eapply PreH12 | eapply PreH13]; lia.
Qed. 

Lemma proof_of_kosaraju_entail_wit_4_split_goal_1 : kosaraju_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r.
  assert (u = n_pre) as Hu by lia.
  subst u.
  apply PreH13.
Qed.

Lemma proof_of_kosaraju_entail_wit_4_split_goal_2 : kosaraju_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r.
  assert (u = n_pre) as Hu by lia.
  subst u.
  apply PreH12.
Qed.

Lemma proof_of_kosaraju_entail_wit_4_split_goal_spatial : kosaraju_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH2.
  entailer!.
Qed.

Lemma proof_of_kosaraju_entail_wit_4 : kosaraju_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst m.
  prop_apply (IntArray.full_Zlength sid_pre n_pre sid_l_high_level_spec).
  Intros_p Hsid_len.
  Exists vm2 vm.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + intros i Hi. apply PreH12. lia.
    + intros i Hi. apply PreH13. lia.
Qed. 

Lemma proof_of_kosaraju_entail_wit_5 : kosaraju_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength fin n_pre fin_l0).
  Intros_p Hfin_len.
  pose proof (transpose_spec_m_of g_high_level_spec
    fadj_col_l_high_level_spec fadj_row_l_high_level_spec
    radj_col_l_ radj_row_l_ n_pre PreH1) as Hmof.
  assert (Hphase1 :
    phase1_sequence_refinement g_high_level_spec radj_col_l_ radj_row_l_
      vis1_zero fin_l0 vis1_zero fin_l0 timer n_pre 0).
  {
    rewrite PreH5.
    eapply phase1_sequence_refinement_init; eauto; lia.
  }
  assert (Hprefix0 :
    dfs1_finish_prefix_marked fin_l0 vis1_zero timer n_pre).
  {
    rewrite PreH5.
    unfold dfs1_finish_prefix_marked.
    intros t Ht.
    lia.
  }
  Exists pos_l_ radj_col_l_ fin_l0 vis1_zero radj_row_l_.
  split_pure_spatial.
  - rewrite <- Hmof.
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [assumption | reflexivity | lia | exact Hphase1 | exact Hprefix0].
Qed. 

Lemma proof_of_kosaraju_entail_wit_6_split_goal_1 : kosaraju_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH13 as [_ [Htimer_count _]].
  exact Htimer_count.
Qed.

Lemma proof_of_kosaraju_entail_wit_6_split_goal_2 : kosaraju_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH13 as [Hready _].
  destruct Hready as [_ [_ Htimer]].
  lia.
Qed.

Lemma proof_of_kosaraju_entail_wit_6_split_goal_3 : kosaraju_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH13 as [_ [_ Hsafe]].
  eapply dfs_finish_schedule_unvisited_step_safeExec_sequence; eauto; lia.
Qed.

Lemma proof_of_kosaraju_entail_wit_6_split_goal_4 : kosaraju_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (proj1 PreH13).
Qed.

Lemma proof_of_kosaraju_entail_wit_6_split_goal_5 : kosaraju_entail_wit_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH13 as [Hready _].
  exact (proj1 (proj2 Hready)).
Qed.

Lemma proof_of_kosaraju_entail_wit_6_split_goal_6 : kosaraju_entail_wit_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH13 as [Hready _].
  exact (proj1 Hready).
Qed.

Lemma proof_of_kosaraju_entail_wit_6_split_goal_7 : kosaraju_entail_wit_6_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_kosaraju_entail_wit_6 : kosaraju_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH13 as Hphase1.
  destruct Hphase1 as [Hready _].
  destruct Hready as [Hwf1 [Hfaith1 Htimer_bounds]].
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try solve [assumption | reflexivity | lia].
    + unfold dfs1_sequence_state_ready.
      exact (conj Hwf1 (conj Hfaith1 Htimer_bounds)).
    + exact (proof_of_kosaraju_entail_wit_6_split_goal_3
        n_pre sid_l_high_level_spec fadj_row_l_high_level_spec
        fadj_col_l_high_level_spec g_high_level_spec fin_l0 vis1_zero
        vis2_zero timer u m vis1_m fin_m radj_col_l radj_row_l
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
        PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
        PreH18 PreH19 PreH20).
    + exact (proof_of_kosaraju_entail_wit_6_split_goal_1
        n_pre sid_l_high_level_spec fadj_row_l_high_level_spec
        fadj_col_l_high_level_spec g_high_level_spec fin_l0 vis1_zero
        vis2_zero timer u m vis1_m fin_m radj_col_l radj_row_l
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
        PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
        PreH18 PreH19 PreH20).
Qed. 

Lemma proof_of_kosaraju_entail_wit_7_split_goal_1 : kosaraju_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold phase1_sequence_refinement.
  split; [exact PreH3 |].
  split; [exact PreH8 |].
  unfold applyf, dfs_finish_scheduleK in PreH6.
  replace (n_pre - (u + 1)) with (n_pre - u - 1) by lia.
  exact PreH6.
Qed.

Lemma proof_of_kosaraju_entail_wit_7_split_goal_2 : kosaraju_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_kosaraju_entail_wit_7_split_goal_3 : kosaraju_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_kosaraju_entail_wit_7 : kosaraju_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists vis1_l_ fin_l_.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try solve [assumption | reflexivity | lia].
    + exact (proof_of_kosaraju_entail_wit_7_split_goal_1
        n_pre sid_l_high_level_spec fadj_row_l_high_level_spec
        fadj_col_l_high_level_spec g_high_level_spec fin_l0 vis1_zero
        vis2_zero vis1_m fin_m radj_col_l radj_row_l m timer u
        timer_v_ vis1_l_ fin_l_ PreH1 PreH2 PreH3 PreH4 PreH5
        PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
        PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
        PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
        PreH30 PreH31 PreH32 PreH33).
Qed. 





Lemma proof_of_kosaraju_entail_wit_8_1 : kosaraju_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists pos_l_2 radj_col_l_2 fin_m_ vis1_m_ radj_row_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try solve [assumption | reflexivity | lia].
    match goal with
    | Hready : dfs1_sequence_state_ready _ _ _ vis1_m_ _ _ |- _ =>
        unfold dfs1_sequence_state_ready in Hready;
        destruct Hready as [Hwf _];
        unfold csr_wf1 in Hwf;
        destruct Hwf as [_ [_ [Hlen _]]];
        lia
    end.
Qed. 

Lemma proof_of_kosaraju_entail_wit_8_2_split_goal_1 : kosaraju_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold phase1_sequence_refinement in PreH13.
  destruct PreH13 as [Hready [Htimer_bound Hsafe]].
  unfold phase1_sequence_refinement.
  split; [exact Hready |].
  split; [exact Htimer_bound |].
  eapply dfs_finish_schedule_skip_safeExec_sequence; eauto; lia.
Qed.

Lemma proof_of_kosaraju_entail_wit_8_2 : kosaraju_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists pos_l_2 radj_col_l_2 fin_m_2 vis1_m_2 radj_row_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try solve [assumption | reflexivity | lia].
    exact (proof_of_kosaraju_entail_wit_8_2_split_goal_1
      n_pre sid_l_high_level_spec fadj_row_l_high_level_spec
      fadj_col_l_high_level_spec g_high_level_spec fin_l0 vis1_zero
      vis2_zero timer u m vis1_m_2 fin_m_2 radj_col_l_2 radj_row_l_2
      PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      PreH18 PreH19 PreH20).
Qed. 













Lemma proof_of_kosaraju_entail_wit_9 : kosaraju_entail_wit_9.
Proof.
  unfold kosaraju_entail_wit_9. left. intros.
  assert (u_2 = n_pre) by lia. subst u_2.
  pose proof PreH12 as Hphase1.
  unfold phase1_sequence_refinement in Hphase1.
  destruct Hphase1 as [Hready _].
  unfold dfs1_sequence_state_ready in Hready.
  destruct Hready as [Hwf _].
  unfold csr_wf1 in Hwf.
  destruct Hwf as [_ [_ [Hvis1_len [Hfin_len _]]]].
  rewrite PreH19 in Hvis1_len, Hfin_len.
  prop_apply (IntArray.full_Zlength pos n_pre pos_l).
  Intros_p Hpos_len.
  Exists radj_col_l_2 sid_l_high_level_spec vis2_zero vis1_m_2
    pos_l fin_m_2 radj_row_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [assumption | reflexivity | lia |
        intros u Hu; lia |
        eapply csr_wf2_of_core; eauto; lia].
Qed. 

Lemma proof_of_kosaraju_entail_wit_10_split_goal_1 : kosaraju_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH9.
Qed.

Lemma proof_of_kosaraju_entail_wit_10 : kosaraju_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists radj_col_l_2 sid_m_2 vis2_m_2 vis1_m_2
    (replace_Znth i (Znth (n_pre - 1 - i) fin_m_2 0) order_l_2)
    fin_m_2 radj_row_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [assumption | reflexivity | lia |
        rewrite Zlength_replace_Znth; assumption].
    intros u Hu.
    destruct (Z.eq_dec u i) as [Hu_i | Hu_i].
    + subst u.
      rewrite Znth_replace_Znth_Same by lia.
      reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply PreH14.
      lia.
Qed. 

Lemma proof_of_kosaraju_entail_wit_11_split_goal_1 : kosaraju_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  unfold phase2_sequence_residual_refinement.
  split; [exact PreH8 |].
  split; [exact PreH9 |].
  split; [exact PreH10 |].
  split; [exact PreH11 |].
  split; [exact PreH12 |].
  split.
  - unfold phase1_sequence_refinement in PreH15.
    destruct PreH15 as [Hready _].
    unfold dfs1_sequence_state_ready in Hready.
    destruct Hready as [_ [_ Htimer_bound]].
    rewrite PreH18 in Htimer_bound.
    exact Htimer_bound.
  - split; [exact PreH14 |].
    split.
    + eapply phase2_order_entries_from_reverse; [| exact PreH14].
      eapply phase1_sequence_refinement_done_fin_range; eauto; lia.
    + split.
      * eapply phase1_sequence_refinement_done_all_vis1; eauto; lia.
      * split; [lia |].
        split.
        -- eapply phase1_sequence_refinement_done_order_graph; eauto; lia.
        -- split.
           ++ eapply (phase2_order_spec_from_phase1_done
                g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2
                fin_m_2 vis1_zero fin_l0 timer_m order_l_2 n_pre);
                try exact PreH17; try exact PreH18; try exact PreH15;
                try exact PreH14; lia.
           ++ split.
              ** apply all_order_prefix_marked_zero.
              ** split.
                 --- apply phase2_prefix_complete_zero.
                 --- split.
                     +++ eapply sid_correct_on_marked_empty; eauto.
                     +++ split.
                         *** eapply sid_labels_in_order_prefix_empty; eauto.
                         *** intros Hzero.
                             lia.
Qed.

Lemma proof_of_kosaraju_entail_wit_11 : kosaraju_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  Exists radj_col_l_2 fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2
    radj_row_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [assumption | reflexivity | lia |
        intros u Hu; lia |
        intros Hzero; lia].
    exact (proof_of_kosaraju_entail_wit_11_split_goal_1
      n_pre fadj_row_l_high_level_spec fadj_col_l_high_level_spec
      g_high_level_spec fin_l0 vis1_zero radj_col_l_2 sid_m_2 vis2_m_2
      vis1_m_2 order_l_2 fin_m_2 timer_m n_pre radj_row_l_2 m
      PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      PreH18 PreH19 PreH20 PreH21).
Qed. 

Lemma proof_of_kosaraju_entail_wit_12_split_goal_1 : kosaraju_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold phase2_sequence_residual_refinement in PreH8.
  destruct PreH8 as [_ [_ [_ [_ [_ [_ [_ [Hrange _]]]]]]]].
  specialize (Hrange k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_kosaraju_entail_wit_12_split_goal_2 : kosaraju_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold phase2_sequence_residual_refinement in PreH8.
  destruct PreH8 as [_ [_ [_ [_ [_ [_ [_ [Hrange _]]]]]]]].
  specialize (Hrange k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_kosaraju_entail_wit_12 : kosaraju_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hroot_range : 0 <= Znth k order_l 0 < n_pre).
  {
    unfold phase2_sequence_residual_refinement in PreH8.
    destruct PreH8 as [_ [_ [_ [_ [_ [_ [_ [Hrange _]]]]]]]].
    apply Hrange.
    lia.
  }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try solve [assumption | reflexivity | lia].
Qed. 

Lemma proof_of_kosaraju_entail_wit_13_split_goal_1 : kosaraju_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH17 as Hwf.
  unfold csr_wf2 in Hwf.
  destruct Hwf as [_ [_ [_ [Hsid_len _]]]].
  rewrite Znth_replace_Znth_Same by (rewrite Hsid_len, PreH14; lia).
  reflexivity.
Qed.

Lemma proof_of_kosaraju_entail_wit_13_split_goal_2 : kosaraju_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply csr_wf2_sid_replace_Znth; eauto; lia.
Qed.

Lemma proof_of_kosaraju_entail_wit_13 : kosaraju_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsid_len : Zlength sid_m = n_pre).
  {
    pose proof PreH17 as Hwf.
    unfold csr_wf2 in Hwf.
    destruct Hwf as [_ [_ [_ [Hsid_len _]]]].
    lia.
  }
  Exists (replace_Znth root root sid_m).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [assumption | reflexivity | lia |
        rewrite Znth_replace_Znth_Same by (rewrite Hsid_len; lia); reflexivity |
        eapply csr_wf2_sid_replace_Znth; eauto; rewrite PreH14; lia].
Qed. 

Lemma proof_of_kosaraju_entail_wit_15_1_split_goal_1 : kosaraju_entail_wit_15_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold phase2_sequence_residual_refinement in PreH20.
  repeat (destruct PreH20 as [_ PreH20]).
  eapply PreH20; eauto.
Qed.

Lemma proof_of_kosaraju_entail_wit_15_1 : kosaraju_entail_wit_15_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists radj_col_l_2 fin_m_2 order_l_2 vis1_m_2 vis2_m_ sid_m_ radj_row_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [assumption | reflexivity | lia |
        let Hres := fresh "Hres" in
        pose proof PreH20 as Hres;
        unfold phase2_sequence_residual_refinement in Hres;
        repeat (destruct Hres as [_ Hres]);
        exact Hres].
Qed. 

Lemma proof_of_kosaraju_entail_wit_15_2_split_goal_1 : kosaraju_entail_wit_15_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstep :
    phase2_sequence_residual_refinement g_high_level_spec fin_m_2
      order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre (k + 1)).
  {
    eapply phase2_sequence_residual_step_from_marked; eauto; lia.
  }
  unfold phase2_sequence_residual_refinement in Hstep.
  repeat (destruct Hstep as [_ Hstep]).
  eapply Hstep; eauto.
Qed.

Lemma proof_of_kosaraju_entail_wit_15_2_split_goal_2 : kosaraju_entail_wit_15_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply phase2_sequence_residual_step_from_marked; eauto; lia.
Qed.

Lemma proof_of_kosaraju_entail_wit_15_2 : kosaraju_entail_wit_15_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstep :
    phase2_sequence_residual_refinement g_high_level_spec fin_m_2
      order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre (k + 1)).
  {
    eapply phase2_sequence_residual_step_from_marked; eauto; lia.
  }
  assert (Hfinal :
    (k + 1 = n_pre) ->
    forall u : Z, 0 <= u < n_pre ->
    forall v : Z, 0 <= v < n_pre ->
      (Znth u sid_m_2 0 = Znth v sid_m_2 0 ->
       mutually_reachable g_high_level_spec u v) /\
      (mutually_reachable g_high_level_spec u v ->
       Znth u sid_m_2 0 = Znth v sid_m_2 0)).
  {
    pose proof Hstep as Hres.
    unfold phase2_sequence_residual_refinement in Hres.
    repeat (destruct Hres as [_ Hres]).
    exact Hres.
  }
  Exists radj_col_l_2 fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 radj_row_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [assumption | reflexivity | lia | exact Hstep | exact Hfinal].
Qed. 

Lemma proof_of_kosaraju_entail_wit_16 : kosaraju_entail_wit_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (k = n_pre) by lia.
  subst k.
  Exists vis2_m_2 fin_m_2 vis1_m_2 order_l_2 radj_col_l_2 sid_m_2 radj_row_l_2.
  split_pure_spatial.
  - rewrite PreH3.
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try solve [assumption | reflexivity | lia | apply PreH15; reflexivity].
Qed. 

Lemma proof_of_kosaraju_return_wit_1_split_goal_1 : kosaraju_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply PreH5; eauto.
Qed.

Lemma proof_of_kosaraju_return_wit_1 : kosaraju_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists sid_m.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed. 

Lemma proof_of_kosaraju_partial_solve_wit_2_pure_split_goal_1 : kosaraju_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r.
  rewrite <- (csr_wf2_core_m_of_last g_high_level_spec
    fadj_col_l_high_level_spec fadj_row_l_high_level_spec n_pre PreH9 PreH11).
  exact PreH12.
Qed.

Lemma proof_of_kosaraju_partial_solve_wit_2_pure : kosaraju_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r.
  match goal with
  | Hcore : csr_wf2_core ?g ?fc ?fr,
    Hverts : adj_verts ?g = ?n,
    Hpos : m_of ?fr > 0 |- _ =>
      rewrite <- (csr_wf2_core_m_of_last g fc fr n Hcore Hverts);
      exact Hpos
  end.
Qed. 











Lemma proof_of_kosaraju_partial_solve_wit_10_pure : kosaraju_partial_solve_wit_10_pure.
Proof.
  unfold kosaraju_partial_solve_wit_10_pure.
  left.
  intros.
  prop_apply (IntArray.full_Zlength radj_col
    (m_of fadj_row_l_high_level_spec) radj_col_l0).
  Intros_p Hradj_col_len.
  prop_apply (IntArray.full_Zlength radj_row
    (n_pre + 1) radj_row_l0).
  Intros_p Hradj_row_len.
  prop_apply (IntArray.full_Zlength pos n_pre pos_l0).
  Intros_p Hpos_len.
  match goal with
  | Hcore : csr_wf2_core ?g ?fc ?fr,
    Hm : ?m = m_of ?fr |- _ =>
      pose proof (csr_wf2_core_m_of_bounds g fc fr Hcore)
  end.
  split_pures; dump_pre_spatial; try solve [assumption | reflexivity | lia].
Qed. 

Lemma proof_of_kosaraju_partial_solve_wit_12_pure_split_goal_1 : kosaraju_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r.
  assert (Zlength vis1_m = n_pre).
  {
    match goal with
    | Hwf : csr_wf1 _ _ _ vis1_m _ |- _ =>
        unfold csr_wf1 in Hwf;
        destruct Hwf as [_ [_ [Hvis_len _]]];
        lia
    end.
  }
  assert (count_nonzero vis1_m < n_pre).
  {
    match goal with
    | Hz : Znth u vis1_m 0 = 0 |- _ =>
        pose proof (count_nonzero_lt_Zlength_with_zero vis1_m u ltac:(lia) Hz);
        lia
    end.
  }
  lia.
Qed.

Lemma proof_of_kosaraju_partial_solve_wit_12_pure : kosaraju_partial_solve_wit_12_pure.
Proof.
  unfold kosaraju_partial_solve_wit_12_pure.
  left.
  intros.
  assert (Hvis_len : Zlength vis1_m = n_pre).
  {
    match goal with
    | Hwf : csr_wf1 _ _ _ vis1_m _ |- _ =>
        unfold csr_wf1 in Hwf;
        destruct Hwf as [_ [_ [Hvis_len _]]];
        lia
    end.
  }
  assert (Htimer_lt : timer < n_pre).
  {
    match goal with
    | Hz : Znth u vis1_m 0 = 0 |- _ =>
        pose proof (count_nonzero_lt_Zlength_with_zero vis1_m u ltac:(lia) Hz);
        lia
    end.
  }
  split_pures; dump_pre_spatial; try solve [assumption | reflexivity | lia].
Qed. 

Lemma proof_of_transpose_derive_high_level_spec_by_low_level_spec : transpose_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec
    radj_col_l_high_level_spec radj_row_l_high_level_spec pos_l_high_level_spec.
  eapply derivable1_trans.
  { apply derivable1_sepcon_emp_r. }
  apply derivable1_sepcon_mono.
  - split_pure_spatial.
    + repeat cancel.
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - apply derivable1_wand_sepcon_adjoint.
    Intros pos_l_ radj_col_l_ radj_row_l_.
    Exists pos_l_ radj_col_l_ radj_row_l_.
    split_pure_spatial.
    + repeat cancel.
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_dfs2_derive_bind_spec_by_low_level_spec : dfs2_derive_bind_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | Hsafe : safeExec _ (bind _ _) _ |- _ =>
      apply safeExec_bind in Hsafe as
        (X_low_level_spec & Hsafe_first & Hsafe_cont)
  end.
  Exists g_bind_spec fadj_col_l_bind_spec fadj_row_l_bind_spec
    vis2_l_bind_spec sid_l_bind_spec root_v_bind_spec X_low_level_spec
    root0_bind_spec n_pre u_pre fadj_col_pre fadj_row_pre vis2_pre sid_pre.
  eapply derivable1_trans.
  { apply derivable1_sepcon_emp_r. }
  apply derivable1_sepcon_mono.
  - Right.
    split_pure_spatial.
    + cancel (IntArray.full fadj_col_pre
        (m_of fadj_row_l_bind_spec) fadj_col_l_bind_spec).
      cancel (IntArray.full fadj_row_pre
        (n_pre + 1) fadj_row_l_bind_spec).
      cancel (IntArray.full vis2_pre n_pre vis2_l_bind_spec).
      cancel (IntArray.full sid_pre n_pre sid_l_bind_spec).
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - apply derivable1_wand_sepcon_adjoint.
    Intros vis2_l_out sid_l_out.
    Exists vis2_l_out sid_l_out.
    split_pure_spatial.
    + cancel (IntArray.full fadj_col_pre
        (m_of fadj_row_l_bind_spec) fadj_col_l_bind_spec).
      cancel (IntArray.full fadj_row_pre
        (n_pre + 1) fadj_row_l_bind_spec).
      cancel (IntArray.full vis2_pre n_pre vis2_l_out).
      cancel (IntArray.full sid_pre n_pre sid_l_out).
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
      match goal with
      | Hret : safeExec _ (return tt) X_low_level_spec |- _ =>
          exact (Hsafe_cont _ tt Hret)
      end.
Qed. 

Lemma proof_of_dfs2_derive_phase2_spec_by_low_level_spec : dfs2_derive_phase2_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists g_phase2_spec fadj_col_l_phase2_spec
    fadj_row_l_phase2_spec vis2_l_phase2_spec
    sid_l_phase2_spec root_pre
    (fun _ st' =>
       dfs2_phase2_state_post g_phase2_spec fin_l_phase2_spec
         vis2_l_phase2_spec sid_l_phase2_spec n_pre root_pre st')
    root_pre n_pre u_pre fadj_col_pre fadj_row_pre vis2_pre sid_pre.
  eapply derivable1_trans.
  { apply derivable1_sepcon_emp_r. }
  apply derivable1_sepcon_mono.
  - Left.
    split_pure_spatial.
    + cancel (IntArray.full fadj_col_pre
        (m_of fadj_row_l_phase2_spec) fadj_col_l_phase2_spec).
      cancel (IntArray.full fadj_row_pre
        (n_pre + 1) fadj_row_l_phase2_spec).
      cancel (IntArray.full vis2_pre n_pre vis2_l_phase2_spec).
      cancel (IntArray.full sid_pre n_pre sid_l_phase2_spec).
    + split_pures; dump_pre_spatial;
        try solve [assumption | reflexivity | lia |
          eapply dfs2_phase2_safeExec_state_post; eauto; lia].
  - apply derivable1_wand_sepcon_adjoint.
    Intros vis2_l_out sid_l_out.
    assert (Hphase2_pair :
      dfs2_phase2_post g_phase2_spec n_pre vis2_l_phase2_spec
        sid_l_phase2_spec vis2_l_out sid_l_out root_pre /\
      phase2_sequence_residual_refinement g_phase2_spec
        fin_l_phase2_spec order_l_phase2_spec vis1_l_phase2_spec
        vis2_l_out sid_l_out timer_v_phase2_spec n_pre
        (k_phase2_spec + 1)).
    {
      match goal with
      | Hret : safeExec
          (pre_dfs2 g_phase2_spec fadj_col_l_phase2_spec
            fadj_row_l_phase2_spec vis2_l_out sid_l_out _)
          (return tt)
          (fun _ st' =>
             dfs2_phase2_state_post g_phase2_spec fin_l_phase2_spec
               vis2_l_phase2_spec sid_l_phase2_spec n_pre root_pre st')
          |- _ =>
          eapply dfs2_phase2_post_and_residual_from_return; eauto; lia
      end.
    }
    assert (Hhigh :
      dfs2_high_level_post g_phase2_spec fadj_col_l_phase2_spec
        fadj_row_l_phase2_spec vis2_l_phase2_spec sid_l_phase2_spec
        vis2_l_out sid_l_out root_pre root_pre n_pre).
    {
      unfold dfs2_high_level_post.
      split; [assumption |].
      split; [assumption |].
      split; [assumption |].
      split; [lia |].
      split; [lia |].
      split.
      - destruct Hphase2_pair as [Hpost _].
        destruct Hpost as [_ [_ Hroot_complete]].
        apply Hroot_complete; [lia |].
        unfold mutually_reachable.
        split; reflexivity.
      - intros w Hw Hvis_old.
        destruct Hphase2_pair as [Hpost _].
        destruct Hpost as [Hold _].
        apply (proj1 (Hold w Hw Hvis_old)).
    }
    Exists vis2_l_out sid_l_out.
    split_pure_spatial.
    + cancel (IntArray.full fadj_col_pre
        (m_of fadj_row_l_phase2_spec) fadj_col_l_phase2_spec).
      cancel (IntArray.full fadj_row_pre
        (n_pre + 1) fadj_row_l_phase2_spec).
      cancel (IntArray.full vis2_pre n_pre vis2_l_out).
      cancel (IntArray.full sid_pre n_pre sid_l_out).
    + split_pures; dump_pre_spatial;
        try solve [assumption | reflexivity | lia |
          exact Hhigh |
          exact (proj1 Hphase2_pair) |
          exact (proj2 Hphase2_pair)].
Qed. 

Lemma proof_of_dfs2_derive_high_level_spec_by_low_level_spec : dfs2_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists g_high_level_spec fadj_col_l_high_level_spec
    fadj_row_l_high_level_spec vis2_l_high_level_spec
    sid_l_high_level_spec root_pre (fun _ _ => True)
    root_pre n_pre u_pre fadj_col_pre fadj_row_pre vis2_pre sid_pre.
  apply derivable1_orp_elim.
  - pre_process.
    eapply derivable1_trans.
    { apply derivable1_sepcon_emp_r. }
    apply derivable1_sepcon_mono.
    + Left.
      split_pure_spatial.
      * cancel (IntArray.full fadj_col_pre
          (m_of fadj_row_l_high_level_spec) fadj_col_l_high_level_spec).
        cancel (IntArray.full fadj_row_pre
          (n_pre + 1) fadj_row_l_high_level_spec).
        cancel (IntArray.full vis2_pre n_pre vis2_l_high_level_spec).
        cancel (IntArray.full sid_pre n_pre sid_l_high_level_spec).
      * split_pures; dump_pre_spatial;
          try solve [assumption | reflexivity | lia |
            eapply dfs2_safeExec_true; eauto; lia].
    + apply derivable1_wand_sepcon_adjoint.
      Intros vis2_l_out sid_l_out.
      Exists vis2_l_out sid_l_out.
      split_pure_spatial.
      * cancel (IntArray.full fadj_col_pre
          (m_of fadj_row_l_high_level_spec) fadj_col_l_high_level_spec).
        cancel (IntArray.full fadj_row_pre
          (n_pre + 1) fadj_row_l_high_level_spec).
        cancel (IntArray.full vis2_pre n_pre vis2_l_out).
        cancel (IntArray.full sid_pre n_pre sid_l_out).
      * split_pures; dump_pre_spatial;
          try solve [assumption | reflexivity | lia |
            eapply dfs2_low_level_to_high_level; eauto; lia].
  - pre_process.
    eapply derivable1_trans.
  { apply derivable1_sepcon_emp_r. }
    apply derivable1_sepcon_mono.
    + Right.
    split_pure_spatial.
      * cancel (IntArray.full fadj_col_pre
        (m_of fadj_row_l_high_level_spec) fadj_col_l_high_level_spec).
      cancel (IntArray.full fadj_row_pre
        (n_pre + 1) fadj_row_l_high_level_spec).
      cancel (IntArray.full vis2_pre n_pre vis2_l_high_level_spec).
      cancel (IntArray.full sid_pre n_pre sid_l_high_level_spec).
      * split_pures; dump_pre_spatial;
        try solve [assumption | reflexivity | lia |
          eapply dfs2_safeExec_true; eauto; lia].
    + apply derivable1_wand_sepcon_adjoint.
    Intros vis2_l_out sid_l_out.
    Exists vis2_l_out sid_l_out.
    split_pure_spatial.
      * cancel (IntArray.full fadj_col_pre
        (m_of fadj_row_l_high_level_spec) fadj_col_l_high_level_spec).
      cancel (IntArray.full fadj_row_pre
        (n_pre + 1) fadj_row_l_high_level_spec).
      cancel (IntArray.full vis2_pre n_pre vis2_l_out).
      cancel (IntArray.full sid_pre n_pre sid_l_out).
      * split_pures; dump_pre_spatial;
        try solve [assumption | reflexivity | lia |
          eapply dfs2_low_level_to_high_level; eauto; lia].
Qed. 

Lemma proof_of_dfs1_derive_bind_spec_by_low_level_spec : dfs1_derive_bind_spec_by_low_level_spec.
Proof.
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

Lemma proof_of_dfs1_derive_high_level_spec_by_low_level_spec : dfs1_derive_high_level_spec_by_low_level_spec.
Proof.
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

