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
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import dfs2_goal.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import dfs2_proof_auto.
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
Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.dfs2_lib.
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
Lemma proof_of_dfs2_entail_wit_1_1_split_goal_1 : dfs2_entail_wit_1_1_split_goal_1.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_2 : dfs2_entail_wit_1_1_split_goal_2.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_3 : dfs2_entail_wit_1_1_split_goal_3.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_4 : dfs2_entail_wit_1_1_split_goal_4.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_5 : dfs2_entail_wit_1_1_split_goal_5.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_6 : dfs2_entail_wit_1_1_split_goal_6.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_7 : dfs2_entail_wit_1_1_split_goal_7.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_8 : dfs2_entail_wit_1_1_split_goal_8.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_9 : dfs2_entail_wit_1_1_split_goal_9.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_10 : dfs2_entail_wit_1_1_split_goal_10.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_11 : dfs2_entail_wit_1_1_split_goal_11.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_12 : dfs2_entail_wit_1_1_split_goal_12.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1_split_goal_13 : dfs2_entail_wit_1_1_split_goal_13.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_1 : dfs2_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  Exists (replace_Znth root_pre 1 vis2_l_low_level_spec)
         (replace_Znth root_pre
            (Znth root_pre sid_l_low_level_spec 0)
            sid_l_low_level_spec).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try solve [assumption | reflexivity | lia | eauto].
    +
      unfold csr_wf2 in PreH1 |- *.
      destruct PreH1 as
        [Hvalid [Hrow [Hvis [Hsid [Hm [Hlo [Hhi [Hcol [Horder Hcap]]]]]]]]].
      assert (Hvis' :
        Zlength (replace_Znth root_pre 1 vis2_l_low_level_spec) =
        adj_verts g_low_level_spec).
      { rewrite Zlength_replace_Znth; exact Hvis. }
      assert (Hsid' :
        Zlength
          (replace_Znth root_pre
            (Znth root_pre sid_l_low_level_spec 0) sid_l_low_level_spec) =
        adj_verts g_low_level_spec).
      { rewrite Zlength_replace_Znth; exact Hsid. }
      repeat (split; [assumption |]); assumption.
    +
      eapply dfs2_entry_close; eauto; lia.
    +
      unfold csr_wf2 in PreH1.
      destruct PreH1 as
        [_ [_ [_ [_ [_ [Hlo [_ [_ [_ _]]]]]]]]].
      apply Hlo; lia.
    +
      unfold csr_wf2 in PreH1.
      destruct PreH1 as
        [_ [_ [_ [_ [_ [_ [_ [_ [Horder _]]]]]]]]].
      apply Horder; lia.
    +
      unfold csr_wf2 in PreH1.
      destruct PreH1 as
        [_ [_ [_ [_ [_ [_ [Hhi [_ [_ _]]]]]]]]].
      apply Hhi; lia.
    +
      rewrite (Znth_replace_eq vis2_l_low_level_spec root_pre 1 0).
      * discriminate.
      * unfold csr_wf2 in PreH1.
        destruct PreH1 as [_ [_ [Hlen _]]].
        rewrite Hlen; lia.
    +
      rewrite (Znth_replace_eq vis2_l_low_level_spec root_pre 1 0).
      * discriminate.
      * unfold csr_wf2 in PreH1.
        destruct PreH1 as [_ [_ [Hlen _]]].
        rewrite Hlen; lia.
    +
      intros w Hw Hvis.
      destruct (Z.eq_dec w root_pre) as [-> | Hne].
      * rewrite (Znth_replace_eq vis2_l_low_level_spec root_pre 1 0).
        -- discriminate.
        -- unfold csr_wf2 in PreH1.
           destruct PreH1 as [_ [_ [Hlen _]]].
           rewrite Hlen; lia.
      * rewrite (Znth_replace_neq vis2_l_low_level_spec w root_pre 1 0);
          try assumption; try lia.
        unfold csr_wf2 in PreH1.
        destruct PreH1 as [_ [_ [Hlen _]]].
        rewrite Hlen; lia.
    +
      intros w Hw Hvis.
      destruct (Z.eq_dec w root_pre) as [-> | Hne].
      * exfalso; apply Hvis; exact PreH11.
      * rewrite (Znth_replace_neq sid_l_low_level_spec w root_pre
          (Znth root_pre sid_l_low_level_spec 0) 0);
          try assumption; try lia.
        unfold csr_wf2 in PreH1.
        destruct PreH1 as [_ [_ [_ [Hlen _]]]].
        rewrite Hlen; lia.
    +
      intros w Hw Hvis_new Hvis_old.
      destruct (Z.eq_dec w root_pre) as [-> | Hne].
      * rewrite (Znth_replace_eq sid_l_low_level_spec root_pre
          (Znth root_pre sid_l_low_level_spec 0) 0).
        -- reflexivity.
        -- unfold csr_wf2 in PreH1.
           destruct PreH1 as [_ [_ [_ [Hlen _]]]].
           rewrite Hlen; lia.
      * assert (Hwlen : 0 <= w < Zlength vis2_l_low_level_spec).
        { unfold csr_wf2 in PreH1.
          destruct PreH1 as [_ [_ [Hlen _]]].
          rewrite Hlen; exact Hw. }
        rewrite (Znth_replace_neq vis2_l_low_level_spec w root_pre 1 0
          Hwlen ltac:(lia) Hne) in Hvis_new.
        exfalso; exact (Hvis_new Hvis_old).
Qed. 

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_1 : dfs2_entail_wit_1_2_split_goal_1.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_2 : dfs2_entail_wit_1_2_split_goal_2.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_3 : dfs2_entail_wit_1_2_split_goal_3.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_4 : dfs2_entail_wit_1_2_split_goal_4.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_5 : dfs2_entail_wit_1_2_split_goal_5.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_6 : dfs2_entail_wit_1_2_split_goal_6.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_7 : dfs2_entail_wit_1_2_split_goal_7.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_8 : dfs2_entail_wit_1_2_split_goal_8.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_9 : dfs2_entail_wit_1_2_split_goal_9.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_10 : dfs2_entail_wit_1_2_split_goal_10.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_11 : dfs2_entail_wit_1_2_split_goal_11.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_12 : dfs2_entail_wit_1_2_split_goal_12.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2_split_goal_13 : dfs2_entail_wit_1_2_split_goal_13.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_1_2 : dfs2_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst.
  Exists (replace_Znth u_pre 1 vis2_l_low_level_spec)
         (replace_Znth u_pre
            (Znth root_pre sid_l_low_level_spec 0)
            sid_l_low_level_spec).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try solve [assumption | reflexivity | lia | eauto].
    + unfold csr_wf2 in PreH1 |- *.
      destruct PreH1 as
        [Hvalid [Hrow [Hvis [Hsid [Hm [Hlo [Hhi [Hcol [Horder Hcap]]]]]]]]].
      assert (Hvis' :
        Zlength (replace_Znth u_pre 1 vis2_l_low_level_spec) =
        adj_verts g_low_level_spec).
      { rewrite Zlength_replace_Znth; exact Hvis. }
      assert (Hsid' :
        Zlength
          (replace_Znth u_pre
            (Znth root_pre sid_l_low_level_spec 0) sid_l_low_level_spec) =
        adj_verts g_low_level_spec).
      { rewrite Zlength_replace_Znth; exact Hsid. }
      repeat (split; [assumption |]); assumption.
    + eapply dfs2_entry_close; eauto; lia.
    + unfold csr_wf2 in PreH1.
      destruct PreH1 as
        [_ [_ [_ [_ [_ [Hlo [_ [_ [_ _]]]]]]]]].
      apply Hlo; lia.
    + unfold csr_wf2 in PreH1.
      destruct PreH1 as
        [_ [_ [_ [_ [_ [_ [_ [_ [Horder _]]]]]]]]].
      apply Horder; lia.
    + unfold csr_wf2 in PreH1.
      destruct PreH1 as
        [_ [_ [_ [_ [_ [_ [Hhi [_ [_ _]]]]]]]]].
      apply Hhi; lia.
    + rewrite (Znth_replace_eq vis2_l_low_level_spec u_pre 1 0).
      * discriminate.
      * unfold csr_wf2 in PreH1.
        destruct PreH1 as [_ [_ [Hlen _]]].
        rewrite Hlen; lia.
    + assert (Hru : root_pre <> u_pre).
      { intro Heq; subst root_pre; contradiction. }
      assert (Hrlen : 0 <= root_pre < Zlength vis2_l_low_level_spec).
      { unfold csr_wf2 in PreH1.
        destruct PreH1 as [_ [_ [Hlen _]]].
        rewrite Hlen; lia. }
      rewrite (Znth_replace_neq vis2_l_low_level_spec root_pre u_pre 1 0
        Hrlen ltac:(lia) Hru).
      exact PreH18.
    + intros w Hw Hvis.
      destruct (Z.eq_dec w u_pre) as [-> | Hne].
      * rewrite (Znth_replace_eq vis2_l_low_level_spec u_pre 1 0).
        -- discriminate.
        -- unfold csr_wf2 in PreH1.
           destruct PreH1 as [_ [_ [Hlen _]]].
           rewrite Hlen; lia.
      * rewrite (Znth_replace_neq vis2_l_low_level_spec w u_pre 1 0);
          try assumption; try lia.
        unfold csr_wf2 in PreH1.
        destruct PreH1 as [_ [_ [Hlen _]]].
        rewrite Hlen; lia.
    + intros w Hw Hvis.
      destruct (Z.eq_dec w u_pre) as [-> | Hne].
      * exfalso; apply Hvis; exact PreH11.
      * rewrite (Znth_replace_neq sid_l_low_level_spec w u_pre
          (Znth root_pre sid_l_low_level_spec 0) 0);
          try assumption; try lia.
        unfold csr_wf2 in PreH1.
        destruct PreH1 as [_ [_ [_ [Hlen _]]]].
        rewrite Hlen; lia.
    + intros w Hw Hvis_new Hvis_old.
      destruct (Z.eq_dec w u_pre) as [-> | Hne].
      * rewrite (Znth_replace_eq sid_l_low_level_spec u_pre
          (Znth root_pre sid_l_low_level_spec 0) 0).
        -- reflexivity.
        -- unfold csr_wf2 in PreH1.
           destruct PreH1 as [_ [_ [_ [Hlen _]]]].
           rewrite Hlen; lia.
      * assert (Hwlen : 0 <= w < Zlength vis2_l_low_level_spec).
        { unfold csr_wf2 in PreH1.
          destruct PreH1 as [_ [_ [Hlen _]]].
          rewrite Hlen; exact Hw. }
        rewrite (Znth_replace_neq vis2_l_low_level_spec w u_pre 1 0
          Hwlen ltac:(lia) Hne) in Hvis_new.
        exfalso; exact (Hvis_new Hvis_old).
Qed. 

Lemma proof_of_dfs2_entail_wit_2_split_goal_1 : dfs2_entail_wit_2_split_goal_1.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_2 : dfs2_entail_wit_2_split_goal_2.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_3 : dfs2_entail_wit_2_split_goal_3.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_4 : dfs2_entail_wit_2_split_goal_4.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_5 : dfs2_entail_wit_2_split_goal_5.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_6 : dfs2_entail_wit_2_split_goal_6.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_2 : dfs2_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try solve [assumption | reflexivity | lia | eauto].
    all: unfold csr_wf2 in PreH2;
      destruct PreH2 as
        [_ [_ [_ [_ [_ [_ [_ [Hcol [_ _]]]]]]]]];
      specialize (Hcol i ltac:(lia)); lia.
Qed. 

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_1 : dfs2_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec (Znth w_3 vis2_m_2 0) 0) as [Hmid_zero | Hmid_marked].
  - pose proof (PreH7 w_3 H H0 Hmid_zero) as Hsid_out_midroot.
    assert (Hsid_midroot_oldroot :
      Znth root0_low_level_spec sid_m_2 0 =
      Znth root0_low_level_spec sid_l_low_level_spec 0).
    { destruct (Z.eq_dec
        (Znth root0_low_level_spec vis2_l_low_level_spec 0) 0)
        as [Hroot_old_zero | Hroot_old_marked].
      - apply PreH29; try assumption; lia.
      - apply PreH28; try assumption; lia. }
    congruence.
  - pose proof (PreH6 w_3 H Hmid_marked) as Hsid_out_mid.
    pose proof (PreH29 w_3 H Hmid_marked H1) as Hsid_mid_oldroot.
    congruence.
Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_2 : dfs2_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH27 w_2 H H0) as Hmid_marked.
  pose proof (PreH6 w_2 H Hmid_marked) as Hout_mid.
  pose proof (PreH28 w_2 H H0) as Hmid_old.
  congruence.
Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_3 : dfs2_entail_wit_3_1_split_goal_3.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_4 : dfs2_entail_wit_3_1_split_goal_4.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_5 : dfs2_entail_wit_3_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
  - apply PreH5.
    + unfold csr_wf2 in PreH9.
      destruct PreH9 as
        [_ [_ [_ [_ [_ [_ [_ [Hcol [_ _]]]]]]]]].
      rewrite <- PreH11.
      apply Hcol.
      lia.
    + apply PreH25; lia.
  - assert (j = i) by lia.
    subst j.
    rewrite <- PreH32.
    exact PreH4.
Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_6 : dfs2_entail_wit_3_1_split_goal_6.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_7 : dfs2_entail_wit_3_1_split_goal_7.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_3_1 : dfs2_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists vis2_l_ sid_l_.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try solve [assumption | reflexivity | lia | eauto].
    + intros j Hj.
      destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
      * apply PreH5.
        -- unfold csr_wf2 in PreH9.
           destruct PreH9 as
             [_ [_ [_ [_ [_ [_ [_ [Hcol [_ _]]]]]]]]].
           rewrite <- PreH11; apply Hcol; lia.
        -- apply PreH25; lia.
      * assert (j = i) by lia; subst j.
        rewrite <- PreH32; exact PreH4.
    + intros w Hw Hvis_old.
      pose proof (PreH27 w Hw Hvis_old) as Hvis_mid.
      pose proof (PreH6 w Hw Hvis_mid) as Hsid_new_mid.
      pose proof (PreH28 w Hw Hvis_old) as Hsid_mid_old.
      congruence.
    + intros w Hw Hvis_new Hvis_old.
      destruct (Z.eq_dec (Znth w vis2_m_2 0) 0) as [Hmid_zero | Hmid_marked].
      * pose proof (PreH7 w Hw Hvis_new Hmid_zero) as Hsid_new_root_mid.
        assert (Hsid_root_mid_old :
          Znth root0_low_level_spec sid_m_2 0 =
          Znth root0_low_level_spec sid_l_low_level_spec 0).
        { destruct (Z.eq_dec
            (Znth root0_low_level_spec vis2_l_low_level_spec 0) 0)
            as [Hroot_old_zero | Hroot_old_marked].
          - apply PreH29; try assumption; lia.
          - apply PreH28; try assumption; lia. }
        congruence.
      * pose proof (PreH6 w Hw Hmid_marked) as Hsid_new_mid.
        pose proof (PreH29 w Hw Hmid_marked Hvis_old) as Hsid_mid_root_old.
        congruence.
Qed. 

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_1 : dfs2_entail_wit_3_2_split_goal_1.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_2 : dfs2_entail_wit_3_2_split_goal_2.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_3 : dfs2_entail_wit_3_2_split_goal_3.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_4 : dfs2_entail_wit_3_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
  - apply PreH19; lia.
  - assert (j = i) by lia.
    subst j.
    rewrite <- PreH26.
    exact PreH1.
Qed.

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_5 : dfs2_entail_wit_3_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply dfs2_skip_close.
  - rewrite <- PreH7. exact PreH10.
  - rewrite PreH4. lia.
  - rewrite <- PreH26. exact PreH1.
  - exact PreH5.
Qed.

Lemma proof_of_dfs2_entail_wit_3_2 : dfs2_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hnext :
    safeExec
      (pre_dfs2 g_low_level_spec fadj_col_l_low_level_spec
         fadj_row_l_low_level_spec vis2_m_2 sid_m_2 root_v_low_level_spec)
      (dfs_scc_from g_low_level_spec fadj_col_l_low_level_spec
         fadj_row_l_low_level_spec root0_low_level_spec u0_low_level_spec
         (i + 1)) X_low_level_spec).
  { eapply dfs2_skip_close.
    - rewrite <- PreH7. exact PreH10.
    - rewrite PreH4. lia.
    - rewrite <- PreH26. exact PreH1.
    - exact PreH5. }
  assert (Hscan : forall j : Z,
    lo <= j < i + 1 ->
    Znth (Znth j fadj_col_l_low_level_spec 0) vis2_m_2 0 <> 0).
  { intros j Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    - apply PreH19. lia.
    - assert (j = i) by lia. subst j.
      rewrite <- PreH26. exact PreH1. }
  Exists vis2_m_2 sid_m_2.
  split_pure_spatial.
  - cancel (IntArray.full fadj_col0_low_level_spec
      (m_of fadj_row_l_low_level_spec) fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row0_low_level_spec
      (n0_low_level_spec + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m_2).
    cancel (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m_2).
  - split_pures.
      all: dump_pre_spatial; first [assumption | reflexivity | lia].
Qed. 

Lemma proof_of_dfs2_return_wit_1_split_goal_1 : dfs2_return_wit_1_split_goal_1.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_return_wit_1_split_goal_2 : dfs2_return_wit_1_split_goal_2.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_return_wit_1_split_goal_3 : dfs2_return_wit_1_split_goal_3.
Proof.
  dfs2_solve_split.
Qed.

Lemma proof_of_dfs2_return_wit_1_split_goal_4 : dfs2_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply (dfs2_return_close g_low_level_spec fadj_col_l_low_level_spec
    fadj_row_l_low_level_spec root0_low_level_spec u0_low_level_spec i
    vis2_m sid_m root_v_low_level_spec X_low_level_spec).
  - rewrite <- PreH7. lia.
  - exact PreH5.
Qed.

Lemma proof_of_dfs2_return_wit_1 : dfs2_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hret :
    safeExec
      (pre_dfs2 g_low_level_spec fadj_col_l_low_level_spec
         fadj_row_l_low_level_spec vis2_m sid_m root_v_low_level_spec)
      (ret tt) X_low_level_spec).
  { eapply (dfs2_return_close g_low_level_spec fadj_col_l_low_level_spec
      fadj_row_l_low_level_spec root0_low_level_spec u0_low_level_spec i
      vis2_m sid_m root_v_low_level_spec X_low_level_spec).
    - rewrite <- PreH7. lia.
    - exact PreH5. }
  Exists vis2_m sid_m.
  split_pure_spatial.
  - cancel (IntArray.full fadj_col0_low_level_spec
      (m_of fadj_row_l_low_level_spec) fadj_col_l_low_level_spec).
    cancel (IntArray.full fadj_row0_low_level_spec
      (n0_low_level_spec + 1) fadj_row_l_low_level_spec).
    cancel (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m).
    cancel (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m).
  - split_pures.
      all: dump_pre_spatial; try assumption; try reflexivity.
Qed. 

Lemma proof_of_dfs2_partial_solve_wit_13_pure_split_goal_1 : dfs2_partial_solve_wit_13_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hrecurse :
    safeExec
      (pre_dfs2 g_low_level_spec fadj_col_l_low_level_spec
         fadj_row_l_low_level_spec vis2_m sid_m root_v_low_level_spec)
      (bind (dfs_scc g_low_level_spec root0_low_level_spec
        (Znth i fadj_col_l_low_level_spec 0))
        (dfs_scc_fromK g_low_level_spec fadj_col_l_low_level_spec
          fadj_row_l_low_level_spec root0_low_level_spec
          u0_low_level_spec (i + 1))) X_low_level_spec).
  { eapply (dfs2_recurse_close g_low_level_spec fadj_col_l_low_level_spec
      fadj_row_l_low_level_spec root0_low_level_spec u0_low_level_spec i
      vis2_m sid_m root_v_low_level_spec X_low_level_spec).
    - rewrite <- PreH21. exact PreH24.
    - rewrite PreH18. lia.
    - exact PreH15.
    - exact PreH19. }
  split_pures.
  all: dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_dfs2_partial_solve_wit_13_pure : dfs2_partial_solve_wit_13_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hrecurse :
    safeExec
      (pre_dfs2 g_low_level_spec fadj_col_l_low_level_spec
         fadj_row_l_low_level_spec vis2_m sid_m root_v_low_level_spec)
      (bind (dfs_scc g_low_level_spec root0_low_level_spec
        (Znth i fadj_col_l_low_level_spec 0))
        (dfs_scc_fromK g_low_level_spec fadj_col_l_low_level_spec
          fadj_row_l_low_level_spec root0_low_level_spec
          u0_low_level_spec (i + 1))) X_low_level_spec).
  { eapply (dfs2_recurse_close g_low_level_spec fadj_col_l_low_level_spec
      fadj_row_l_low_level_spec root0_low_level_spec u0_low_level_spec i
      vis2_m sid_m root_v_low_level_spec X_low_level_spec).
    - rewrite <- PreH7. exact PreH10.
    - rewrite PreH4. lia.
    - exact PreH1.
    - exact PreH5. }
  split_pures.
  all: dump_pre_spatial; try assumption; try reflexivity.
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
