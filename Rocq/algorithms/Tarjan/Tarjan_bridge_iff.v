Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From TraceLib Require Import TraceBasic TraceLogic TraceRecur CommonTactics MapLib.
From GraphLib Require Import GraphLib tarjan.
From Algorithms Require Import Tarjan Tarjan_tactics Tarjan_basics Tarjan_set_tree Tarjan_no_cross_edge.

Import SetsNotation.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope sets.
Local Open Scope map_scope.

Section BRIDGE_IFF.


Context {V E: Type}
        (root: V)
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V E)
        {origin_gvalid: OriginalGraph_gvalid g}
        (g_vvalid_root: vvalid g root).

Ltac same_tree_from_state_subst s1 s2 H:=
    let Hs := fresh "Hs" in
    assert (state_to_rootedtree g root s1 = state_to_rootedtree g root s2) as Hs; 
    [ unfold state_to_rootedtree; simpl; rewrite H; auto | ];
    try rewrite Hs; auto.

Notation T := (state_to_rootedtree g root).

Definition add_bridge_iff_top_down : V -> St -> Prop :=
  fun u s => forall x y e, 
    reachable (T s) u x ->
    step_aux (T s) e x y ->
    List.In e s.(bridges) <-> 
    dfn s x < low s y.

Definition add_bridge_iff_top_down_except : V -> V -> St -> Prop :=
  fun u v s => forall x y e,
    y <> v ->
    reachable (T s) u x ->
    step_aux (T s) e x y ->
    List.In e s.(bridges) <-> 
    dfn s x < low s y. 

Lemma isleaf_satisfies_bridge_iff (u: V) (s: St): 
  isleaf (T s) u ->
  add_bridge_iff_top_down u s.
Proof.
  intros; intros x y; intros; exfalso.
  apply reachable_1n in H0 as [[? []]|]; [|subst];
  eapply H; [|eexists]; eauto.
Qed.

Lemma Tarjan_preloop_add_bridge_iff (u: V):
  Hoare (fun s => isleaf (T s) u)
        (preloop u)
        (fun _ => add_bridge_iff_top_down u).
Proof.
  unfold preloop; unfold_op.
  intro_state.
  hoare_auto_s.
  apply isleaf_satisfies_bridge_iff; auto.
  same_tree_from_state_subst s s0 H0.
Qed.

Record Tarjan_bridge_iff_inductive_hypotheses (W: V -> program St unit) := {
  IH_tree : forall u, 
    Hoare (fun s => tree_sub_conj_P root g u s) 
          (W u) 
          (fun _ s => tree_sub_conj_P root g u s);
  IH_bridge : forall u e, 
    Hoare (fun s => List.In e s.(bridges)) 
          (W u) 
          (fun _ s => List.In e s.(bridges));
  IH_nobridge : forall u x y e, 
    Hoare (fun s => step_aux g e x y /\ x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ List.In e s.(bridges)) 
          (W u) 
          (fun _ s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ List.In e s.(bridges));
  IH_nostep : forall u x y e, 
    Hoare (fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y) 
          (W u) 
          (fun _ s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y);
  IH_nooffspring : forall u x y, 
    Hoare (fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ offspring (T s) x y /\ tree_sub_conj_P root g u s) 
          (W u) 
          (fun _ s => ~ offspring (T s) x y);
  IH_dfnlow : forall u x y, 
    Hoare (fun s => u <> x /\ u <> y /\ x ∈ s.(visited) /\ y ∈ s.(visited) /\ s.(dfn) x < s.(low) y) 
          (W u) 
          (fun _ s => s.(dfn) x < s.(low) y);
  IH_dfnlow' : forall u x y, 
    Hoare (fun s => u <> x /\ u <> y /\ x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ s.(dfn) x < s.(low) y) 
          (W u) 
          (fun _ s => ~ s.(dfn) x < s.(low) y);
  IH_nocrossedge : forall u v, 
    Hoare (fun s => u ∈ s.(visited) /\ ~ v ∈ s.(visited)) 
          (W u) 
          (fun _ s => ( u ∈ s.(visited) /\ ~ v ∈ s.(visited)) \/ (v ∈ s.(visited) /\ offspring (T s) u v));
}.


Theorem Tarjan_W_add_bridge_iff (u v: V) 
  (W: V -> program St unit):
  Tarjan_bridge_iff_inductive_hypotheses W ->
  (forall u, 
    Hoare (fun s => add_bridge_iff_top_down u s /\ isleaf (T s) u /\ tree_sub_conj_P root g u s /\ forall e: E, List.In e s.(bridges) -> evalid (T s) e)
          (W u)
          (fun _ => add_bridge_iff_top_down u)) 
  ->
    Hoare (fun s => add_bridge_iff_top_down_except u v s /\ step (T s) u v /\ tree_sub_conj_P root g u s /\ isleaf (T s) v /\ forall e: E, List.In e s.(bridges) -> evalid (T s) e)
          (W v)
          (fun _ s => add_bridge_iff_top_down_except u v s).
Proof.
  intros [IH_tree IH_bridge IH_nobridge IH_nostep IH_nooffspring IH_dfnlow IH_dfnlow' IH_nocrossedge] IH.
  apply hoare_bind_forall; intros x.
  apply hoare_bind_forall; intros y.
  apply hoare_bind_forall; intros e.
  apply hoare_bind_forall; intros.
  eapply Hoare_implies with (Q:= fun s => tree_sub_conj_P root g v s).
  {
    hoare_cons_pre IH_tree.
    intros s [Hiff [Hstep [Htree _]]].
    eapply tree_easy; [|destruct Hstep as [? []]]; eauto.
  }
  eapply Hoare_implies with (Q:= fun s => add_bridge_iff_top_down v s).
  {
    hoare_cons_pre IH.
    intros s [Hiff [Hstep [Htree [Hleaf Hein]]]].
    split_r 3; auto.
    * apply isleaf_satisfies_bridge_iff; auto.
    * eapply tree_easy; [|destruct Hstep as [? []]]; eauto.
  }
  eapply Hoare_exclude_middle with (R:= fun s => visited s x). 
  { 
    hoare_cons (IH_nocrossedge v x).
    { intros s [[? []]]; split; auto; destruct H0 as [? []]; auto. }
    intros _; intros.
    destruct H as [[]|[]].
    * exfalso; destruct H3; auto.
    * eapply H0; eauto.  
  }
  destruct (classic (x = v)); subst.
  {
    hoare_cons IH.
    { 
      intros s [[Hiff [Hstep [Htree [Hleaf Hein]]]] _]; split_r 3; auto.
      * apply isleaf_satisfies_bridge_iff; auto.
      * eapply tree_easy; [|destruct Hstep as [? []]]; eauto.
    }
    { intros; eapply H; eauto; reflexivity. } 
  } 
  eapply Hoare_exclude_middle with (R:= fun s => visited s y). 
  { 
    hoare_cons (IH_nocrossedge v y).
    { intros s Hc; my_destruct Hc; split; destruct H2 as [? []]; auto. }
    intros _; intros.
    destruct H0 as [[]|[]].
    * exfalso; destruct H4; auto.
    * eapply H1; eauto.  
      eapply one_reachable_down_up; eauto.
      eexists; eauto.
      Unshelve. apply H2.
  }
  eapply Hoare_exclude_middle with (R:= fun s => offspring (T s) u x).
  { 
    hoare_cons (IH_nooffspring v u x).
    intros; my_destruct H0; split_r 3; auto. 
    * destruct H4 as [? []]; auto. 
    * eapply tree_easy; [|destruct H4 as [? []]]; eauto.
  }
  eapply Hoare_exclude_middle with (R:= fun s => step_aux (T s) e x y).
  { hoare_cons (IH_nostep v x y e). }
  eapply Hoare_conseq_post with (Q2:= fun _ s => List.In e (bridges s) <-> dfn s x < low s y).
  { intros; auto. }
  eapply Hoare_conj.
  * eapply Hoare_exclude_middle with (R:= fun s => List.In e (bridges s)).
    { 
      hoare_cons (IH_nobridge v x y e).
      intros. my_destruct H0. split; auto; apply H7; auto.
    }
    { 
      hoare_cons (IH_dfnlow v x y).
      intros. my_destruct H0. repeat split; auto.
      eapply H0; eauto.
    }
  * eapply Hoare_exclude_middle with (R:= fun s => dfn s x < low s y).
    {
      hoare_cons (IH_dfnlow' v x y).
      intros; my_destruct H0; repeat split; auto.
    }
    {
      hoare_cons (IH_bridge v e).
      intros; my_destruct H0. 
      eapply H0 in H1; eauto. 
    }
Qed. 

Lemma Tarjan_set_tree_add_bridge_iff_inv (u v: V) (e: E):
  Hoare (fun s => add_bridge_iff_top_down u s /\ ~ v ∈ s.(visited) /\ step_aux g e u v /\ tree_sub_conj_P root g u s)
        (set_tree u v e)
        (fun _ s => add_bridge_iff_top_down_except u v s /\ step_aux (T s) e u v /\ tree_sub_conj_P root g u s /\ isleaf (T s) v).
Proof.
  eapply Hoare_implies. 
  { hoare_cons_pre Tarjan_set_tree_keep_tree_sub_conj; eauto; tauto. } 
  unfold set_tree.
  intro_state.
  hoare_auto_s.
  my_destruct H; my_destruct H1.
  assert (isleaf (T s) v) as Hleaf. {
    subst; apply tree_add_vertex_is_leaf; auto; apply H4.
  }
  split_r 3; auto.
  * intros x y e0; intros.
    assert (x <> v) as Hxnv. 
    {
      unfold not; intros; subst.
      eapply Hleaf; eexists; eauto.
    }
    rewrite H0; simpl. 
    subst; destruct H4 as [is_rt []].
    eapply H; eauto.
    ** eapply tree_keep_offspring'; eauto; try tauto.
    ** eapply tree_keep_step_aux'; eauto.
  * subst; apply step_easy; auto; apply H4.
  * eapply tree_easy; eauto. 
Qed.

Lemma Tarjan_post_rec_add_bridge_iff_inv (u v: V) (e: E):
  Hoare (fun s => add_bridge_iff_top_down_except u v s /\ ~ List.In e s.(bridges) /\ step_aux (T s) e u v /\ tree_sub_conj_P root g u s)
        (post_rec e u v)
        (fun _ s => add_bridge_iff_top_down u s /\ tree_sub_conj_P root g u s).
Proof.
  apply Hoare_conj.
  { 
    unfold post_rec; unfold_op.
    intro_state.
    hoare_auto_s;
    [|destruct H0 as [H1 H0]];
    same_tree_from_state_subst s s0 H1;
    destruct H as [Hiff [Hein [Hstep [is_rt [sub Hu]]]]];
    intros x y; intros.
    * destruct (classic (e = e0)).
      {
        subst e0. 
        rewrite <- Hs in *.
        eapply step_aux_unique in Hstep as []; eauto; subst x y.
        rewrite H1; simpl; split; auto.
      }
      {
        assert (y <> u) as Hynu. 
        {
          unfold not; intros; subst y.
          eapply offspring_not_father; eauto.
          eexists; eauto.
        }
        assert (y <> v) as Hynv. 
        {
          unfold not; intros; subst y.
          rewrite <- Hs in *.
          eapply father_eunique in H2; eauto.
        } 
        rewrite H1; simpl; split; intros.
        * destruct H4; try congruence.
          unfold t_set; equiv_dec_simpl u y.
          rewrite Hs in *.
          eapply Hiff; eauto.
        * right.
          unfold t_set in H4; equiv_dec_simpl u y.
          rewrite Hs in *.
          eapply Hiff; eauto. 
      }
    * assert (y <> u) as Hynu. {
        unfold not; intros; subst y.
        eapply offspring_not_father; eauto.
        eexists; eauto.
      }
      rewrite H1; simpl.
      destruct (classic (y = v)) as [Hyv|Hynv].
      {
        subst y; rewrite Hs in *.
        assert (x = u) as Hxu by (eapply father_vunique; eexists; eauto); subst x.
        assert (e = e0) as Hee0 by (eapply father_eunique; eauto); subst e0.
        unfold t_set; equiv_dec_simpl u v; intros; exfalso.
        unfold t_set in H0; equiv_dec_simpl u v.
      }
      { 
        rewrite Hs in *.
        unfold t_set; equiv_dec_simpl u y.
      }
      Unshelve. 
      rewrite Hs in *; auto.
      rewrite Hs in *; auto.
      auto.
  }
  { hoare_cons_pre Tarjan_post_rec_keep_tree_sub_conj; intros; apply H. }
Qed.

Lemma Tarjan_for_branch2_add_bridge_iff_inv (u v: V):
  Hoare (fun s => add_bridge_iff_top_down u s /\ tree_sub_conj_P root g u s)
        (for_branch2 u v)
        (fun _ s => add_bridge_iff_top_down u s).
Proof.
  intro_state.
  unfold for_branch2; unfold_op.
  hoare_auto_s.
  intros x y; intros.
  same_tree_from_state_subst s s0 H0.
  rewrite Hs in *. 
  rewrite H0; simpl. 
  assert (y <> u) as Hynu. {
    unfold not; intros; subst y.
    eapply offspring_not_father; eauto.
    eexists; eauto.
  }
  equiv_dec_simpl u y;
  eapply H; eauto.
  Unshelve. apply H.
Qed.

Lemma Tarjan_add_bridge_iff_inv (u: V):
  Hoare (fun s => (
        (add_bridge_iff_top_down u s /\ 
        isleaf (T s) u) /\ 
        tree_sub_conj_P root g u s) /\ 
        forall e: E, List.In e s.(bridges) -> evalid (T s) e)
        (tarjan g u)
        (fun _ => add_bridge_iff_top_down u).
Proof.
  unfold tarjan.
  hoare_fix_nolv_fs_auto V.
  {
    forall_n 12. 
    * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_subgraph_inv unit @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_bridge_inv E @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_nobridge_inv_prod ((V * V) * E)%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_step_aux_inv_prod ((V * V) * E)%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_nostep_aux_inv_prod ((V * V) * E)%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_nooffspring_inv_prod (V * V)%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_dfn_low_order_inv_prod (V * V)%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_dfn_low_order_inv_prod' (V * V)%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv V @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_edge_inv E @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_bridge_is_tree_edge_inv unit @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_visit_is_offspring V @tarjan. 
  }
  intros. unfold_Forall H.
  clear u; rename a into u.
  unfold tarjan_f.
  eapply Hoare_bind.
  {
    apply Hoare_conj; [apply Hoare_conj|].
    * hoare_cons_pre Tarjan_preloop_add_bridge_iff.
    * hoare_cons_pre Tarjan_preloop_keep_tree_sub_conj; intros; apply H. 
    * hoare_cons_pre (Tarjan_preloop_bridge_is_tree_edge root g).
  }
  simpl; intros _.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  simpl; intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state; destruct H as [[Hiff Htree] Hein].
  hoare_auto_s.
  - rename a0 into v; rename a into e.
    hoare_bind'' IH0.
    unfold for_branch1. 
    destruct Htree as [is_rt [sub Hu]].
    destruct (classic (List.In e (bridges s0))) as [Hin|Hout].
    {
      exfalso; apply Hein in Hin.
      eapply evalid_sub_vvalid1 in H1; eauto; try tauto.
      apply Rootedtree_noemptyedge.
      apply OriginalGraph_stepuniqueundirected.
    }
    eapply Hoare_bind.
    {
      hoare_conj_n 2.
      * hoare_cons_pre Tarjan_set_tree_add_bridge_iff_inv; eauto.
        intros; subst; split_r 3; auto.
        split_r 2; auto.
      * hoare_cons_pre Tarjan_set_tree_keep_nobridge; intros; subst; eauto.
      * hoare_cons_pre Tarjan_set_tree_bridge_is_tree_edge; intros; subst; tauto.
    }
    simpl; intros _.
    eapply Hoare_bind.
    2: 
    {
      intros. eapply Hoare_conj2.
      hoare_cons_post Tarjan_post_rec_add_bridge_iff_inv.
      apply Tarjan_post_rec_bridge_is_tree_edge.
    }
    apply Hoare_conj; [hoare_conj_n 3 | hoare_conj_n 1].
    {
      hoare_cons_pre Tarjan_W_add_bridge_iff; [|split|]; auto.
      * intros. my_destruct H3. split_r 2; auto.
        eexists; eauto.
      * intros. hoare_cons (IHa1 u0 ((x, y), e0)); eauto.
      * intros. hoare_cons (IHa3 u0 ((x, y), e0)); eauto.
      * intros. hoare_cons (IHa4 u0 (x, y)).
      * intros. hoare_cons (IHa5 u0 (x, y)).
      * intros. hoare_cons (IHa6 u0 (x, y)). 
      * intros; hoare_cons H0.
    }
    { 
      hoare_cons (IHa1 v ((u, v), e)); eauto.
      intros; my_destruct H3; split_r 3; auto;
      destruct H5; auto. 
    }
    { hoare_cons (IHa2 v ((u, v), e)); eauto; tauto. }
    {
      eapply Hoare_conseq_post.
      2: 
      { 
        apply Hoare_conj.
        * hoare_cons_pre IHa; intros; split_r 2; apply H3. 
        * hoare_cons_pre IHa7; intros; apply H3.
      }
      simpl; intros; split_r 2; apply H3.
    }
    { hoare_cons_pre IHa9. }
    { hoare_cons_pre IHa8. }
  - hoare_bind'' IH0.
    apply Hoare_conj; [apply Hoare_conj|].
    * hoare_cons_pre Tarjan_for_branch2_add_bridge_iff_inv.
      intros; subst; split; auto.
    * hoare_cons_pre Tarjan_for_branch2_keep_subgraph_inv.
      intros; subst; auto.
    * hoare_cons_pre Tarjan_for_branch2_bridge_is_tree_edge.
      intros; subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; tauto.
  Unshelve. auto. auto. auto. 
Qed.

Lemma add_bridge_iff_init_state: 
  add_bridge_iff_top_down root (initSt root).
Proof.
  intros x y; intros; exfalso.
  destruct H0; simpl in *.
  unfold t_empty in ve; inversion ve.
Qed.

Lemma root_isleaf_init_state:
  isleaf (T (initSt root)) root.
Proof.
  unfold isleaf; unfold not; intros x H.
  destruct H as [e []]; simpl in *.
  unfold t_empty in ve; inversion ve.
Qed.

Theorem Tarjan_bridge_iff:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => forall x y e, step_aux (T s) e x y ->
        List.In e s.(bridges) <-> dfn s x < low s y).
Proof.
  eapply Hoare_implies.
  { apply Tarjan_keep_tree_subgraph; auto. }
  simpl.
  hoare_cons Tarjan_add_bridge_iff_inv.
  {
    intros; subst; split; [split; [split|]|]; auto.
    * apply add_bridge_iff_init_state.
    * apply root_isleaf_init_state.
    * apply tree_subgraph_init_state; auto.
    * intros; inversion H.
  }
  intros.
  apply H; auto.
  destruct H0 as [is_rt [sub Hroot]].
  assert (vvalid (T s) x) as Hvx.
  { simpl. destruct H1; auto. }
  eapply root_is_root in Hvx; eauto.
Qed.

End BRIDGE_IFF.










