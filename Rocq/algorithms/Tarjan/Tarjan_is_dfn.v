
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From TraceLib Require Import TraceBasic TraceLogic TraceRecur CommonTactics MapLib.
From GraphLib Require Import GraphLib tarjan.
From Algorithms Require Import Tarjan Tarjan_tactics Tarjan_set_tree Tarjan_basics.

Import SetsNotation.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope sets.
Local Open Scope map_scope.

Section ISDFN.
    
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


Definition dfn_valid_except {V E: Type} (u: V) (dfstree: RootedTreeType V E) (dfn: V -> nat) := 
   forall x y, y <> u -> step dfstree x y -> dfn x < dfn y.

Lemma add_tree_edge_preserves_dfn_valid_except (s: St) (u v: V) (e: E)
  (is_rt: is_rooted_tree (state_to_rootedtree g root s)) : 
  ~ v ∈ s.(visited) ->
  dfn_valid (state_to_rootedtree g root s) s.(dfn) -> 
  dfn_valid_except v (state_to_rootedtree g root (set_tree' u v e s)) s.(dfn).
Proof.
  intros Hv Hdfn x y Hy Hstep.
  apply Hdfn.
  destruct Hstep as [e0 ?].
  destruct H; simpl in *.
  exists e0; split; simpl.
  - destruct vx; [|exfalso]; auto.
    sets_unfold in H; subst x; exfalso.
    unfold t_set in vp; destruct (equiv_dec v y); auto.
    destruct is_rt as [[] _]. 
    apply Hv; rewrite <- vp; apply parent_valid; auto.
    destruct vy; [| exfalso]; auto.
  - destruct vy; [| exfalso]; auto.
  - unfold t_set in ve; destruct (equiv_dec v y);
    [exfalso|]; auto.
  - unfold t_set in vp; destruct (equiv_dec v y); 
    [exfalso|]; auto.
Qed.

Lemma add_tree_edge_creates_leaf (s: St) (u v: V) (e: E)
  (is_rt: is_rooted_tree (state_to_rootedtree g root s)):
  u ∈ s.(visited) ->
  ~ v ∈ s.(visited) -> 
  isleaf (state_to_rootedtree g root (set_tree' u v e s)) v.
Proof.
  intros Hu Hv.
  unfold isleaf; unfold not; intros x H.
  pose proof H as [e0 []]; simpl in *.
  unfold t_set in vp; destruct (equiv_dec v x).
  * subst; auto.
  * destruct is_rt.
    apply Hv; rewrite <- vp; apply parent_valid; simpl.
    destruct vy; [|exfalso]; auto.
Qed.

Definition dfn_valid_conj_Pre (u: V) (s: St) :=
  dfn_valid_except u (state_to_rootedtree g root s) s.(dfn) /\ 
  isleaf (state_to_rootedtree g root s) u /\ 
  (forall v, s.(dfn) v < s.(timer)).
  
Definition dfn_valid_conj_Post (s: St) :=
  dfn_valid (state_to_rootedtree g root s) s.(dfn) /\ 
  (forall v, s.(dfn) v < s.(timer)). 

Lemma dfn_valid_init_state:
  dfn_valid_conj_Pre root (initSt root).
Proof.
  split; [|split]; simpl.
  * intros x y ? ?.
    destruct H0 as [e []]; simpl in *.
    unfold t_empty in ve; inversion ve.
  * unfold isleaf; unfold not; intros.
    destruct H as [x [e []]]; simpl in *.
    unfold t_empty in ve; inversion ve.
  * intros; unfold t_empty; lia.
Qed.

Lemma Tarjan_preloop_dfn_valid_inv (u v: V):
  Hoare (fun s => dfn_valid_conj_Pre u s)
        (preloop u)
        (fun _ s => dfn_valid_conj_Post s).
Proof.
  intro_state.
  unfold_preloop.
  destruct H as [? []].
  same_tree_from_state_subst s s0 H0.
  split.
  * intros x y Hstep.
    destruct (classic (x = u)).
    ** subst u; exfalso.
       eapply H1; rewrite <- Hs; eauto.
    ** destruct (classic (y = u)).
      *** subst u. rewrite H0; simpl.
          equiv_dec_refl y; clear e.
          equiv_dec_simpl y x.
      *** rewrite Hs in Hstep.
          apply H in Hstep; auto. 
          rewrite H0; simpl.
          equiv_dec_simpl u y.
          equiv_dec_simpl u x.
  * intros; rewrite H0; simpl; auto.
    equiv_dec_simpl u v0; try lia.
    specialize (H2 v0); lia.
Qed.

Lemma Tarjan_set_tree_keep_dfn_valid_inv (u v: V) (e: E):
  Hoare (fun s => dfn_valid_conj_Post s /\ tree_sub_conj_P root g u s /\ ~ v ∈ s.(visited))
        (set_tree u v e)
        (fun _ s => dfn_valid_conj_Pre v s).
Proof.
  unfold set_tree; unfold_op.
  intro_state; hoare_auto_s.
  repeat split.
  * assert (dfn s = dfn s0) as Heqdfn_ss0 by (subst s; auto). 
    rewrite Heqdfn_ss0. 
    subst; apply add_tree_edge_preserves_dfn_valid_except; 
    try apply H; auto.
  * subst; apply add_tree_edge_creates_leaf; try apply H; auto. 
  * subst; apply H.
Qed. 

Lemma Tarjan_post_rec_keep_dfn_valid_inv (u v: V) (e: E): 
  Hoare (fun s => dfn_valid_conj_Post s)
        (post_rec e u v)
        (fun _ s => dfn_valid_conj_Post s).
Proof.
  intro_state. destruct H as [dfnv tiemr].
  unfold post_rec; unfold_op.
  hoare_auto_s; [|destruct H as [H0 _]];
  same_tree_from_state_subst s s0 H0; split; 
  try rewrite Hs; try rewrite H0; auto.
Qed.

Lemma Tarjan_for_branch2_keep_dfn_valid_inv (u v : V):
  Hoare (fun s => dfn_valid (state_to_rootedtree g root s) (dfn s))
        (for_branch2 u v)
        (fun _ s => dfn_valid (state_to_rootedtree g root s) (dfn s)).
Proof.
  intro_state.
  unfold for_branch2; unfold_op.
  hoare_auto_s.
  rewrite H0; auto.
Qed.

Lemma Tarjan_dfn_valid_inv' (u: V) (W: V -> program St unit): 
      (forall v, 
      Hoare (fun s => u ∈ s.(visited)) 
            (W v)
            (fun _ s => u ∈ s.(visited)))
  ->
      (forall v, 
      Hoare (fun s => tree_sub_conj_P root g v s)
            (W v)
            (fun _ s => tree_sub_conj_P root g v s))
  -> 
      (forall v, 
      Hoare (fun s => dfn_valid_conj_Pre v s /\ tree_sub_conj_P root g v s)
            (W v)
            (fun _ s => dfn_valid_conj_Post s))
  -> 
      Hoare (fun s => dfn_valid_conj_Pre u s /\ tree_sub_conj_P root g u s)
            (tarjan_f g W u)
            (fun _ s => dfn_valid_conj_Post s).
Proof. 
  intros IH1 IH2 IH3.
  unfold tarjan_f.
  eapply Hoare_bind.
  { 
    apply Hoare_conj.
    hoare_cons_pre Tarjan_preloop_dfn_valid_inv.
    hoare_cons_pre Tarjan_preloop_keep_tree_sub_conj.
    intros s [_]. apply H. 
  }
  simpl; intros _.
  unfold loop_body.
  unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  simpl; intros W0 IH eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - hoare_bind'' IH. 
    apply Hoare_conj.
    * unfold for_branch1. 
      rewrite <- bind_assoc.
      hoare_bind'' Tarjan_post_rec_keep_dfn_valid_inv.
      hoare_bind'' IH3.
      apply Hoare_conj.
      ** hoare_cons_pre Tarjan_set_tree_keep_dfn_valid_inv. 
         intros; subst; split; [|split]; try tauto.
      ** hoare_cons Tarjan_set_tree_keep_tree_sub_conj; eauto; try tauto.
         intros; subst; split; tauto.
    * eapply Hoare_conseq; 
      [ | | apply Tarjan_for_branch1_keep_subgraph_inv'; eauto].
      ** intros; subst; split; auto; apply H.
      ** simpl; intros; simpl; split; [|split]; try apply H3.
  - hoare_bind'' IH.
    simpl; unfold for_branch2; unfold_op. 
    hoare_auto_s. subst; auto.
  - hoare_cons_pre IH.
    intros; subst; auto.
  - subst; apply H.
  (* 不变量3个分支，普通的Hoare Tripple 4个分支 *)
Qed.

Lemma Tarjan_dfn_valid_inv (u: V):
  Hoare (fun s => dfn_valid_conj_Pre u s /\ tree_sub_conj_P root g u s)
        (tarjan g u)
        (fun _ s => dfn_valid_conj_Post s).
Proof.
  unfold tarjan.
  hoare_fix_nolv_fs_auto V.
  * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    ** hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv V @tarjan.
    ** hoare_fix_nolv_ls_auto @Tarjan_keep_tree_subgraph_inv unit @tarjan.
  * intros.
    unfold_Forall H. 
    apply Tarjan_dfn_valid_inv'; auto.
Qed. 


Lemma Tarjan_dfn_valid:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => dfn_valid (state_to_rootedtree g root s) s.(dfn)).
Proof.
  hoare_cons (Tarjan_dfn_valid_inv root).
  * intros; subst; split;
  [apply dfn_valid_init_state|apply tree_subgraph_init_state]; auto.
  * intros; apply H. 
Qed.

End ISDFN.
