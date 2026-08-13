
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From TraceLib Require Import TraceBasic TraceLogic TraceRecur CommonTactics MapLib.
From GraphLib Require Import GraphLib tarjan.
From Algorithms Require Import Tarjan Tarjan_tactics Tarjan_set_tree.

Import SetsNotation.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope sets.
Local Open Scope map_scope.

Section BASICS.

Context {V E: Type}
        (root: V)
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V E)
        {origin_gvalid: OriginalGraph_gvalid g}
        (g_vvalid_root: vvalid g root).

Notation T := (state_to_rootedtree g root).

Ltac same_tree_from_state_subst s1 s2 H:=
    let Hs := fresh "Hs" in
    assert (T s1 = T s2) as Hs; 
    [ unfold state_to_rootedtree; simpl; rewrite H; auto | ];
    try rewrite Hs; auto.

Lemma Tarjan_preloop_keep_visited (u v: V):
  Hoare (fun s: (@St V E) => v ∈ s.(visited))
        (preloop u)
        (fun _ s => v ∈ s.(visited)).
Proof.
  unfold preloop; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
Qed.

Lemma Tarjan_set_tree_keep_visited (u v w: V) (e: E):
  Hoare (fun s => w ∈ s.(visited))
        (set_tree u v e)
        (fun _ s => w ∈ s.(visited)).
Proof.
  unfold set_tree, set_tree'; unfold_op.
  intro_state; hoare_auto_s; subst.
  left; auto.
Qed.

Lemma Tarjan_post_rec_keep_visited (u v w: V) (e: E):
  Hoare (fun s => w ∈ s.(visited))
        (post_rec e u v)
        (fun _ s => w ∈ s.(visited)).
Proof.
  unfold post_rec; unfold_op.
  intro_state; hoare_auto_s; [|destruct H0]; subst; auto.
Qed.


Lemma Tarjan_for_branch2_keep_visited (u v w: V):
  Hoare (fun s: (@St V E) => w ∈ s.(visited))
        (for_branch2 u v)
        (fun _ s => w ∈ s.(visited)).
Proof.
  unfold for_branch2; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
Qed.
    
Theorem Tarjan_keep_visited_inv (u v: V):
  Hoare (fun s => v ∈ s.(visited))
        (tarjan g u)
        (fun _ s => v ∈ s.(visited)).
Proof.
  unfold tarjan. 
  hoare_fix_nolv_auto V; intros.
  unfold tarjan_f.
  hoare_bind Tarjan_preloop_keep_visited; simpl; clear a0.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH eset.
  unfold forset_f, forset_body.
  hoare_auto_s.
  intro_state.
  hoare_auto_s.
  - unfold for_branch1.
    hoare_bind'' IH.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_keep_visited.
    hoare_bind'' H.
    hoare_cons_pre Tarjan_set_tree_keep_visited. 
    intros; subst; auto.
  - hoare_bind'' IH.
    hoare_cons_pre Tarjan_for_branch2_keep_visited.
    intros; subst; auto.
  - hoare_cons_pre IH. 
    intros; subst; tauto.
Qed.


Lemma Tarjan_preloop_keep_dfn (u v: V) (dfnv: nat):
  Hoare (fun s: (@St V E) => u <> v /\ v ∈ s.(visited) /\ s.(dfn) v = dfnv)
        (preloop u)
        (fun _ s => v ∈ s.(visited) /\ s.(dfn) v = dfnv).
Proof.
  intros; unfold preloop; unfold_op.
  intro_state.
  hoare_auto_s.
  my_destruct H.
  subst; simpl.
  equiv_dec_simpl u v.
Qed.

Lemma Tarjan_set_tree_keep_dfn (x y v: V) (e: E) (dfnv: nat):
  Hoare (fun s => ~ y ∈ s.(visited) /\ v ∈ s.(visited) /\ s.(dfn) v = dfnv)
        (set_tree x y e)
        (fun _ s => y <> v /\ v ∈ s.(visited) /\ s.(dfn) v = dfnv).
Proof.
  intros; unfold set_tree; unfold_op.
  intro_state; hoare_auto_s; subst; auto. 
  my_destruct H. 
  repeat split; simpl; auto.
  unfold not; intros; subst; auto.
  left; auto.
Qed.

Lemma Tarjan_post_rec_keep_dfn (x y v: V) (e: E) (dfnv: nat):
  Hoare (fun s => v ∈ s.(visited) /\ s.(dfn) v = dfnv)
        (post_rec e x y)
        (fun _ s => v ∈ s.(visited) /\ s.(dfn) v = dfnv).
Proof.
  intros; unfold post_rec; unfold_op.
  intro_state; my_destruct H.
  hoare_auto_s; [|destruct H0]; subst; auto.
Qed.

Lemma Tarjan_for_branch2_keep_dfn (u v w: V) (dfnw: nat):
  Hoare (fun s: (@St V E) => w ∈ s.(visited) /\ s.(dfn) w = dfnw)
        (for_branch2 u v)
        (fun _ s => w ∈ s.(visited) /\ s.(dfn) w = dfnw).
Proof.
  unfold for_branch2; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
Qed.

Theorem Tarjan_keep_dfn_inv (u v: V) (dfnv: nat):
  Hoare (fun s => u <> v /\ v ∈ s.(visited) /\ s.(dfn) v = dfnv)
        (tarjan g u)
        (fun _ s => v ∈ s.(visited) /\ s.(dfn) v = dfnv).
Proof.
  intros; unfold tarjan.
  hoare_fix_nolv_auto V.
  clear u.
  intros W IH u; simpl.
  unfold tarjan_f.
  hoare_bind Tarjan_preloop_keep_dfn; simpl; clear a.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  simpl; intros W0 IH0 eset.
  unfold forset_f, forset_body.
  hoare_auto_s.
  intro_state.
  hoare_auto_s.
  - unfold for_branch1. 
    hoare_bind'' IH0.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_keep_dfn.
    hoare_bind'' IH.
    hoare_cons_pre Tarjan_set_tree_keep_dfn.
    intros; subst; auto.
  - hoare_bind'' IH0.
    hoare_cons_pre Tarjan_for_branch2_keep_dfn.
    intros; subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
Qed.

Theorem Tarjan_keep_dfn_inv_prod (u: V) (p: V * nat):
  Hoare (fun s => u <> (fst p) /\ (fst p) ∈ s.(visited) /\ s.(dfn) (fst p) = snd p)
        (tarjan g u)
        (fun _ s => (fst p) ∈ s.(visited) /\ s.(dfn) (fst p) = snd p).
Proof.
  destruct p as (x, y); simpl.
  apply Tarjan_keep_dfn_inv.
Qed.

Lemma Tarjan_preloop_keep_low (u v: V) (lowv: nat):
  Hoare (fun s: (@St V E) => u <> v /\ v ∈ s.(visited) /\ s.(low) v = lowv)
        (preloop u)
        (fun _ s => u <> v /\ v ∈ s.(visited) /\ s.(low) v = lowv).
Proof.
  intros; unfold preloop; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
  my_destruct H.
  repeat split; simpl; auto.
  equiv_dec_simpl u v.
Qed.

Lemma Tarjan_set_tree_keep_low (x y v: V) (e: E) (lowv: nat): 
  Hoare (fun s => ~ y ∈ s.(visited) /\ v ∈ s.(visited) /\ s.(low) v = lowv)
        (set_tree x y e)
        (fun _ s => y <> v /\ v ∈ s.(visited) /\ s.(low) v = lowv).
Proof.
  intros; unfold set_tree; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
  my_destruct H.
  repeat split; simpl; auto.
  unfold not; intros; subst; auto.
  left; auto.
Qed.


Lemma Tarjan_post_rec_keep_low (x y v: V) (e: E) (lowv: nat):
  Hoare (fun s => x <> v /\ v ∈ s.(visited) /\ s.(low) v = lowv)
        (post_rec e x y)
        (fun _ s => x <> v /\ v ∈ s.(visited) /\ s.(low) v = lowv).
Proof.
  intros; unfold post_rec; unfold_op.
  intro_state; my_destruct H; hoare_auto_s; 
  [|destruct H1]; subst; simpl; split; auto. 
  equiv_dec_simpl x v.
  equiv_dec_simpl x v.
Qed.


Lemma Tarjan_for_branch2_keep_low (u v w: V) (loww: nat):
  Hoare (fun s: (@St V E) => u <> w /\ w ∈ s.(visited) /\ s.(low) w = loww)
        (for_branch2 u v)
        (fun _ s => u <> w /\ w ∈ s.(visited) /\ s.(low) w = loww).
Proof.
  unfold for_branch2; unfold_op.
  intro_state; hoare_auto_s; subst.
  my_destruct H. 
  repeat split; simpl; auto.
  equiv_dec_simpl u w.
Qed.

Theorem Tarjan_keep_low_inv (u v: V) (lowv: nat):
  Hoare (fun s => u <> v /\ v ∈ s.(visited) /\ s.(low) v = lowv)
        (tarjan g u)
        (fun _ s => v ∈ s.(visited) /\ s.(low) v = lowv).
Proof.
  intros; unfold tarjan.
  hoare_fix_nolv_auto V.
  clear u; simpl.
  intros W IH u; simpl.
  unfold tarjan_f.
  hoare_bind Tarjan_preloop_keep_low; simpl; clear a.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  simpl; intros W0 IH0 eset.
  unfold forset_f, forset_body.
  hoare_auto_s.
  intro_state.
  my_destruct H.
  hoare_auto_s.
  - unfold for_branch1. 
    hoare_bind'' IH0.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_keep_low.
    eapply Hoare_bind.
    hoare_cons_pre Tarjan_set_tree_keep_low. 
    { intros; subst; split; eauto. }
    simpl; intros _.
    hoare_cons_post IH.
  - hoare_bind'' IH0.
    hoare_cons_pre Tarjan_for_branch2_keep_low.
    intros; subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto. 
  - subst; tauto.
Qed.

Theorem Tarjan_keep_low_inv_prod (u: V) (p: V * nat):
  Hoare (fun s => u <> (fst p) /\ (fst p) ∈ s.(visited) /\ s.(low) (fst p) = snd p)
        (tarjan g u)
        (fun _ s => (fst p) ∈ s.(visited) /\ s.(low) (fst p) = snd p).
Proof.
  destruct p as (x, y); simpl.
  apply Tarjan_keep_low_inv.
Qed.

Theorem Tarjan_keep_dfn_low_order_inv (u x y: V):
  Hoare (fun s => u <> x /\ u <> y /\ x ∈ s.(visited) /\ y ∈ s.(visited) /\ s.(dfn) x < s.(low) y)
        (tarjan g u)
        (fun _ s => s.(dfn) x < s.(low) y).
Proof.
  intro_state. 
  my_destruct H.
  remember (dfn s0 x) as dfnx.
  remember (low s0 y) as lowy.
  eapply Hoare_conseq_post.
  2: 
  {
    eapply Hoare_conj;
    [hoare_cons (Tarjan_keep_dfn_inv u x dfnx)|hoare_cons (Tarjan_keep_low_inv u y lowy)].
    * intros; subst.
      repeat split; auto.
    * instantiate (1:=fun _ s => dfn s x = dfnx).
      simpl; intros; tauto.
    * intros; subst.
      repeat split; auto.
    * instantiate (1:=fun _ s => low s y = lowy).
      simpl; intros; tauto.
  }
  simpl; intros _ s [].
  rewrite H4, H5; auto.
Qed.

Theorem Tarjan_keep_dfn_low_order_inv' (u x y: V):
  Hoare (fun s => u <> x /\ u <> y /\ x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ s.(dfn) x < s.(low) y)
        (tarjan g u)
        (fun _ s => ~ s.(dfn) x < s.(low) y).
Proof.
  intro_state. 
  my_destruct H.
  remember (dfn s0 x) as dfnx.
  remember (low s0 y) as lowy.
  eapply Hoare_conseq_post.
  2: 
  {
    eapply Hoare_conj;
    [hoare_cons (Tarjan_keep_dfn_inv u x dfnx)|hoare_cons (Tarjan_keep_low_inv u y lowy)].
    * intros; subst.
      repeat split; auto.
    * instantiate (1:=fun _ s => dfn s x = dfnx).
      simpl; intros; tauto.
    * intros; subst.
      repeat split; auto.
    * instantiate (1:=fun _ s => low s y = lowy).
      simpl; intros; tauto.
  }
  simpl; intros _ s [].
  rewrite H4, H5; auto.
Qed.

Lemma Tarjan_keep_dfn_low_order_inv_prod (u: V) (p: V * V):
  Hoare (fun s => u <> (fst p) /\ u <> (snd p) /\ (fst p) ∈ s.(visited) /\ (snd p) ∈ s.(visited) /\ s.(dfn) (fst p) < s.(low) (snd p))
        (tarjan g u)
        (fun _ s => s.(dfn) (fst p) < s.(low) (snd p)).
Proof.
  destruct p as (x, y); simpl.
  apply Tarjan_keep_dfn_low_order_inv.
Qed.

Lemma Tarjan_keep_dfn_low_order_inv_prod' (u: V) (p: V * V):
  Hoare (fun s => u <> (fst p) /\ u <> (snd p) /\ (fst p) ∈ s.(visited) /\ (snd p) ∈ s.(visited) /\ ~ s.(dfn) (fst p) < s.(low) (snd p))
        (tarjan g u)
        (fun _ s => ~ s.(dfn) (fst p) < s.(low) (snd p)).
Proof.
  destruct p as (x, y); simpl.
  apply Tarjan_keep_dfn_low_order_inv'.
Qed.

Definition neighbor_visit (u: V) (s: @St V E) : Prop :=
  forall v, step g u v -> v ∈ s.(visited).

Definition eset_in_visited (u: V) (eset: E -> Prop) (s: @St V E): Prop := 
  forall v,  (exists e, step_aux g e u v /\ e ∈ eset) -> v ∈ s.(visited).

#[export]Instance eset_in_visited_proper (u: V): 
  Proper (Sets.equiv ==> eq ==> iff)
  (fun (eset : E -> Prop) (s : St) => eset_in_visited u eset s).
Proof.
  intros es1 es2 Heq1 s1 s2 Heq2; split;
  intros H x [e []]; subst;
  apply H; exists e; split; auto; 
  [rewrite Heq1|rewrite <- Heq1]; auto.
Qed.

Lemma Tarjan_keep_eset_in_visited_inv (u v: V) (done: E -> Prop):
  Hoare (eset_in_visited v done)
        (tarjan g u)
        (fun _ => eset_in_visited v done).
Proof.
  unfold tarjan. 
  hoare_fix_nolv_auto V; intros.
  unfold tarjan_f.
  unfold_preloop.
  apply Hoare_conseq_pre with 
    (P2:= eset_in_visited v done).
  { intros; subst s1; rewrite H2; auto. }
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH eset.
  unfold forset_f, forset_body.
  hoare_auto_s.
  intro_state.
  hoare_auto_s.
  - unfold for_branch1, post_rec; unfold_op.
    hoare_auto_s.
    intro_state.
    eapply Hoare_bind.
    { 
      hoare_cons_pre H.
      intros; subst; unfold set_tree', eset_in_visited; 
      intros x [e []]; simpl; left; apply H2; eexists; eauto. 
    }
    simpl; intros _.
    intro_state.
    hoare_auto_s;
    intro_state;
    hoare_cons_pre IH; 
    intros; subst s1;
    rewrite H8; auto.
  - unfold for_branch2; unfold_op.
    hoare_auto_s.
    intro_state.
    hoare_cons_pre IH.
    intros; subst; auto.
  - hoare_cons_pre IH. 
    intros; subst; tauto.
Qed.



Lemma Tarjan_keep_eset_in_visited_inv' (u: V) (p: V * (E -> Prop)):
  Hoare (eset_in_visited (fst p) (snd p))
        (tarjan g u)
        (fun _ => eset_in_visited (fst p) (snd p)).
Proof. destruct p; simpl. apply Tarjan_keep_eset_in_visited_inv. Qed.

Lemma Tarjan_visit_neighbor (u: V):
  Hoare ATrue
        (tarjan g u)
        (fun _ s => neighbor_visit u s).
Proof.
  unfold tarjan.
  hoare_fix_nolv_fs_auto V.
  {
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv V @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_eset_in_visited_inv' (V * (E -> Prop))%type @tarjan.
  }
  clear u; intros W IH0 IH u _.
  unfold_Forall IH0.
  unfold tarjan_f.
  unfold_preloop; clear s0 H H0.
  eapply Hoare_conseq.
  3: 
  {
    unfold loop_body.
    eapply Hoare_forset with (P := fun eset s => eset_in_visited u eset s).
    apply eset_in_visited_proper.
    intros; intro_state.
    unfold forset_body; hoare_auto_s.
    - unfold for_branch1.
      eapply Hoare_bind with (Q:=fun _ s => eset_in_visited u done s /\ a0 ∈ s.(visited)).
      {
        unfold set_tree, set_tree'.
        hoare_auto_s; split.
        * unfold eset_in_visited in *; subst; simpl.
          intros; left; apply H2; auto.
        * subst; simpl.
          right; reflexivity.
      }
      intros _.
      eapply Hoare_bind with (Q:=fun _ s => eset_in_visited u done s /\ a0 ∈ s.(visited)).
      {
        apply Hoare_conj.
        * hoare_cons_pre (IHa0 a0 (u, done)).
        * hoare_cons_pre IHa.
      }
      intros _.
      unfold post_rec; unfold_op.
      intro_state; hoare_auto_s;
      [|destruct H6];
      destruct H5; subst;
      intros x [e []]; simpl; (destruct H9; 
      [apply H5; eexists; eauto|
      sets_unfold in H9; subst;
      eapply step_aux_eunique_l in H3; eauto; 
      subst; auto]).
    - unfold for_branch2; unfold_op.
      hoare_auto_s; subst.
      intros x [e []]; simpl.
      destruct H7.
      * apply H2; eexists; eauto.
      * sets_unfold in H7; subst.
        eapply step_aux_eunique_l in H3; eauto. 
        subst; tauto. 
    - destruct H5; subst.
      intros x [e []].
      destruct H7.
      * apply H2; eexists; eauto.
      * sets_unfold in H7; subst.
        eapply step_aux_eunique_l in H3; eauto. 
        subst; tauto. 
  }
  {
    intros; subst.
    intros ? [e[]].
    exfalso; auto.
  }
  {
    intros b s Hu v Hs.
    apply Hu.
    destruct Hs.
    exists x; split; auto.
    exists v; auto.
  }
  Unshelve. auto. auto. auto. auto. 
Qed.

Lemma Tarjan_preloop_keep_offspring (u x y: V):
  Hoare (fun s => offspring (T s) x y)
        (preloop u)
        (fun _ s => offspring (T s) x y).
Proof.
  intro_state; unfold_preloop; subst; auto.
Qed.

Lemma Tarjan_set_tree_keep_offspring (u v x y: V) (e: E):
  Hoare (fun s => offspring (T s) x y /\ ~ v ∈ s.(visited))
        (set_tree u v e)
        (fun _ s => offspring (T s) x y).
Proof.
  unfold set_tree; unfold_op.
  intro_state.
  hoare_auto_s.
  my_destruct H. 
  subst; apply tree_keep_offspring; auto.
Qed.

Lemma Tarjan_post_rec_keep_offspring (u v x y: V) (e: E):
  Hoare (fun s => offspring (T s) x y)
        (post_rec e u v)
        (fun _ s => offspring (T s) x y).
Proof.
  unfold post_rec; unfold_op.
  intro_state.
  hoare_auto_s; [|destruct H0]; subst; auto.
Qed.

Lemma Tarjan_for_branch2_keep_offspring (u v x y: V):
  Hoare (fun s => offspring (T s) x y)
        (for_branch2 u v)
        (fun _ s => offspring (T s) x y).
Proof.
  unfold for_branch2; unfold_op.
  intro_state.
  hoare_auto_s.
  subst; auto.
Qed.

Theorem Tarjan_keep_offspring_inv (u x y: V):
  Hoare (fun s => offspring (T s) x y)
        (tarjan g u)
        (fun _ s => offspring (T s) x y).
Proof.
  unfold tarjan.
  hoare_fix_nolv_auto V. 
  intros W IH v; simpl.
  unfold tarjan_f.
  hoare_bind Tarjan_preloop_keep_offspring; simpl.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - unfold for_branch1.
    hoare_bind'' IH0.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_keep_offspring.
    hoare_bind'' IH.
    hoare_cons_pre Tarjan_set_tree_keep_offspring.
    intros; subst; auto.
  - unfold for_branch2; unfold_op.
    hoare_bind'' IH0.
    hoare_cons_pre Tarjan_for_branch2_keep_offspring.
    intros; subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; tauto.
Qed.


Lemma Tarjan_keep_offspring_inv_prod (u: V) (p: V * V):
  Hoare (fun s => offspring (T s) (fst p) (snd p))
        (tarjan g u)
        (fun _ s => offspring (T s) (fst p) (snd p)).
Proof. destruct p; simpl. apply Tarjan_keep_offspring_inv; auto. Qed.



Lemma Tarjan_preloop_keep_step_aux (u x y: V)(e: E):
  Hoare (fun s => step_aux (T s) e x y)
        (preloop u)
        (fun _ s => step_aux (T s) e x y).
Proof.
  intro_state; unfold_preloop; subst; auto.
Qed.


Lemma Tarjan_set_tree_keep_step_aux (u v x y: V) (e e0: E):
  Hoare (fun s => step_aux (T s) e x y /\ ~ v ∈ s.(visited))
        (set_tree u v e0)
        (fun _ s => step_aux (T s) e x y).
Proof.
  unfold set_tree; unfold_op.
  intro_state. 
  hoare_auto_s. 
  my_destruct H; destruct H; subst s; split; simpl in *.
  * left; auto.
  * left; auto.
  * equiv_dec_simpl v y.
    exfalso; auto.
  * equiv_dec_simpl v y.
    exfalso; auto.
Qed.


Lemma Tarjan_post_rec_keep_step_aux (u v x y: V) (e e0: E):
  Hoare (fun s => step_aux (T s) e x y)
        (post_rec e0 u v)
        (fun _ s => step_aux (T s) e x y).
Proof.
  unfold post_rec; unfold_op.
  intro_state; hoare_auto_s; [|destruct H0]; subst; auto.
Qed.

Lemma Tarjan_for_branch2_keep_step_aux (u v x y: V) (e: E):
  Hoare (fun s => step_aux (T s) e x y)
        (for_branch2 u v)
        (fun _ s => step_aux (T s) e x y).
Proof.
  unfold for_branch2; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
Qed.


Lemma Tarjan_keep_step_aux_inv (u x y: V)(e: E):
  Hoare (fun s => step_aux (T s) e x y)
        (tarjan g u)
        (fun _ s => step_aux (T s) e x y).
Proof.
  intros; unfold tarjan.
  hoare_fix_nolv_auto V.
  simpl; intros.
  unfold tarjan_f.
  hoare_bind Tarjan_preloop_keep_step_aux.
  unfold loop_body.
  unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state. 
  hoare_auto_s.
  - unfold for_branch1.
    hoare_bind'' IH0.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_keep_step_aux.
    hoare_bind'' H.
    hoare_cons_pre Tarjan_set_tree_keep_step_aux.
    intros; subst; auto.
  - unfold for_branch2; unfold_op.
    hoare_bind'' IH0.
    hoare_cons_pre Tarjan_for_branch2_keep_step_aux.
    intros; subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; auto.
Qed.


Lemma Tarjan_keep_step_aux_inv_prod (u: V) (p: V * V * E):
  Hoare (fun s => step_aux (T s) (snd p) (fst (fst p)) (snd (fst p)))
        (tarjan g u)
        (fun _ s => step_aux (T s) (snd p) (fst (fst p)) (snd (fst p))).
Proof. destruct p as ((x, y), e); simpl. apply Tarjan_keep_step_aux_inv; auto. Qed.



Lemma Tarjan_loop_body_keep_step_aux 
  (W: V -> program St unit):
  (forall u x y e, 
  Hoare (fun s => step_aux (T s) e x y)
        (W u)
        (fun _ s => step_aux (T s) e x y))
  ->
  (forall u eset x y e,
  Hoare (fun s => step_aux (T s) e x y)
        (Lfix (forset_f (forset_body g u W)) eset)
        (fun _ s => step_aux (T s) e x y)).
Proof.
  intros IH1.
  intros u eset x y e.
  hoare_fix_nolv_auto (E -> Prop).
  simpl; clear eset; intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - hoare_bind'' IH0.
    unfold for_branch1.
    eapply Hoare_bind.
    hoare_cons_pre (Tarjan_set_tree_keep_step_aux _ _ x y e); 
    intros; subst; tauto.
    simpl; intros _. 
    hoare_bind IH1; simpl.
    hoare_cons_pre (Tarjan_post_rec_keep_step_aux _ _ x y e).
  - hoare_bind'' IH0.
    unfold for_branch2.
    unfold_op; hoare_auto_s.
    subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; auto. 
Qed.


Lemma Tarjan_loop_body_keep_step_aux_prod
  (W: V -> program St unit):
  (forall u x y e, 
  Hoare (fun s => step_aux (T s) e x y)
        (W u)
        (fun _ s => step_aux (T s) e x y))
  ->
  (forall u eset p, 
  Hoare (fun s => step_aux (T s) (snd p) (fst (fst p)) (snd (fst p)))
        (Lfix (forset_f (forset_body g u W)) eset)
        (fun _ s => step_aux (T s) (snd p) (fst (fst p)) (snd (fst p)))).
Proof. intros; destruct p; simpl. apply Tarjan_loop_body_keep_step_aux; auto. Qed.

Lemma Tarjan_preloop_keep_edge (u: V)(e: E):
  Hoare (fun s => evalid (T s) e)
        (preloop u)
        (fun _ s => evalid (T s) e).
Proof.
  intro_state; unfold_preloop; subst; auto.
Qed.

Lemma Tarjan_set_tree_keep_edge (u v: V) (e e0: E):
  Hoare (fun s => evalid (T s) e /\ ~ v ∈ s.(visited))
        (set_tree u v e0)
        (fun _ s => evalid (T s) e).
Proof.
  unfold set_tree; unfold_op.
  intro_state.
  hoare_auto_s.
  my_destruct H; subst; apply tree_add_edge_keep; auto. 
Qed.


Lemma Tarjan_post_rec_keep_edge (u v: V) (e e0: E):
  Hoare (fun s => evalid (T s) e)
        (post_rec e0 u v)
        (fun _ s => evalid (T s) e).
Proof.
  unfold post_rec; unfold_op.
  intro_state; hoare_auto_s; [|destruct H0]; subst; auto.
Qed.

Lemma Tarjan_for_branch2_keep_edge (u v: V) (e: E):
  Hoare (fun s => evalid (T s) e)
        (for_branch2 u v)
        (fun _ s => evalid (T s) e).
Proof.
  unfold for_branch2; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
Qed.


Theorem Tarjan_keep_edge_inv (u: V)(e: E):
  Hoare (fun s => evalid (T s) e)
        (tarjan g u)
        (fun _ s => evalid (T s) e).
Proof.
  intros; unfold tarjan.
  hoare_fix_nolv_auto V; intros.
  unfold tarjan_f.
  hoare_bind Tarjan_preloop_keep_edge.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - unfold for_branch1.
    hoare_bind'' IH0.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_keep_edge.
    hoare_bind'' H.
    hoare_cons_pre Tarjan_set_tree_keep_edge.
    intros; subst; auto.
  - unfold for_branch2; unfold_op.
    hoare_bind'' IH0.
    hoare_cons_pre Tarjan_for_branch2_keep_edge.
    intros; subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; auto.
Qed.

Definition bridge_is_tree_edge: St -> Prop :=
  fun s => forall e: E, 
  List.In e s.(bridges) -> evalid (T s) e.

Lemma Tarjan_preloop_bridge_is_tree_edge (u: V):
  Hoare (fun s => bridge_is_tree_edge s)
        (preloop u)
        (fun _ s => bridge_is_tree_edge s).
Proof.
  intro_state; unfold_preloop; subst; apply H; auto.
Qed.

Lemma Tarjan_set_tree_bridge_is_tree_edge (u v: V) (e: E):
  Hoare (fun s => bridge_is_tree_edge s /\ ~ v ∈ s.(visited))
        (set_tree u v e)
        (fun _ s => bridge_is_tree_edge s /\ evalid (T s) e).
Proof.
  unfold set_tree; unfold_op.
  intro_state.
  hoare_auto_s.
  split; intros.
  * destruct H; subst; intros e0 He0in; apply tree_add_edge_keep; auto.
    apply H; auto.
  * subst; unfold set_tree';
    exists v; simpl; split;
    [right; reflexivity|equiv_dec_refl v].
Qed.

Lemma Tarjan_post_rec_bridge_is_tree_edge (u v: V) (e: E):
  Hoare (fun s => bridge_is_tree_edge s /\ evalid (T s) e)
        (post_rec e u v)
        (fun _ s => bridge_is_tree_edge s).
Proof.
  unfold post_rec; unfold_op.
  intro_state; hoare_auto_s;
  destruct H; intros e0 He0in.
  * same_tree_from_state_subst s s0 H1. 
    rewrite H1 in He0in; simpl in He0in.
    destruct He0in; [subst e0|]; auto.
  * destruct H0 as [H0 _].
    same_tree_from_state_subst s s0 H0.
    rewrite H0 in He0in; simpl in He0in.
    apply H; auto.
Qed.

Lemma Tarjan_for_branch2_bridge_is_tree_edge (u v: V):
  Hoare (fun s => bridge_is_tree_edge s)
        (for_branch2 u v)
        (fun _ s => bridge_is_tree_edge s).
Proof.
  unfold for_branch2; unfold_op.
  intro_state; hoare_auto_s. 
  same_tree_from_state_subst s s0 H0.
  intros e Hein; rewrite Hs; eapply H; subst; auto.
Qed.

Theorem Tarjan_bridge_is_tree_edge_inv (u: V):
  Hoare (fun s => bridge_is_tree_edge s)
        (tarjan g u)
        (fun _ s => bridge_is_tree_edge s).
Proof.
  unfold tarjan.
  hoare_fix_lv_auto_conj V unit tt.
  { apply Tarjan_keep_edge_inv. }
  simpl; intros W IH H a _.
  unfold tarjan_f.
  hoare_bind Tarjan_preloop_bridge_is_tree_edge.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state. 
  hoare_auto_s.
  - hoare_bind'' IH0. 
    unfold for_branch1.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_bridge_is_tree_edge.
    eapply Hoare_bind.
    { 
      hoare_cons_pre Tarjan_set_tree_bridge_is_tree_edge.
      intros; subst; split; auto.
    }
    simpl; intros _.
    apply Hoare_conj2; auto.
  - hoare_bind'' IH0.
    hoare_cons_pre Tarjan_for_branch2_bridge_is_tree_edge.
    intros; subst; auto; apply H0; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; firstorder.
Qed.

Definition tree_sub_conj_P (u: V) (s: Tarjan.St) :=
  is_rooted_tree (T s) /\ 
  subgraph (T s) g /\ 
  u ∈ s.(visited).


Lemma tree_easy (u v: V) (s: St): 
  tree_sub_conj_P u s ->
  v ∈ s.(visited) ->
  tree_sub_conj_P v s.
Proof.
  intros [is_rt [sub Hu]] Hv.
  split; [|split]; auto.
Qed.

Lemma Tarjan_preloop_keep_tree_sub_conj (u: V):
  Hoare (fun s => tree_sub_conj_P u s )
        (preloop u)
        (fun _ s => tree_sub_conj_P u s).
Proof.
  intro_state; unfold_preloop.
  destruct H; split; rewrite H0; auto.
Qed.

Lemma Tarjan_set_tree_keep_tree_sub_conj (u v: V) (e: E): 
  Hoare (fun s => tree_sub_conj_P u s /\ ~ v ∈ s.(visited) /\ step_aux g e u v)
        (set_tree u v e)
        (fun _ s => tree_sub_conj_P v s /\ u ∈ s.(visited)).
Proof.
  unfold set_tree, set_tree'.
  intro_state.
  hoare_auto_s; subst.
  destruct H as [[is_rt [sub Hu]] [Hv Hstep]].
  split; [split; [|split]|].
  * apply tree_property_keep; auto. 
    ** unfold not; intros; subst v; apply Hv. 
       destruct is_rt; simpl in *. 
       apply root_valid.
    ** eapply step_vvalid2; eauto.
    ** unfold not; intros. 
       destruct H as [x [? ?]].
       assert (evalid (T s0) e) by firstorder.
       eapply sub_reverse with (g2:=g) in H1; eauto.
       2: apply Rootedtree_noemptyedge.
       2: apply OriginalGraph_stepuniqueundirected.
       destruct H1; [destruct H1 as [_ ? _ _]|destruct H1 as [? _ _ _]]; auto.
  * apply tree_subgraph_keep; auto.
  * right; reflexivity.
  * left; auto.
Qed.

Lemma Tarjan_post_rec_keep_tree_sub_conj (u v w: V) (e: E):
  Hoare (fun s => tree_sub_conj_P w s )
        (post_rec e u v)
        (fun _ s => tree_sub_conj_P w s).
Proof.
  unfold post_rec; unfold_op.
  intro_state.
  hoare_auto_s; [|destruct H0]; subst; auto.
Qed.

Lemma Tarjan_for_branch1_keep_subgraph_inv' (u v: V) (e: E) (W: V -> program St unit):
  Hoare (fun s => u ∈ s.(visited)) 
        (W v)
        (fun _ s => u ∈ s.(visited))
  ->
  Hoare (fun s => tree_sub_conj_P v s)
        (W v)
        (fun _ s => tree_sub_conj_P v s)
  -> 
  Hoare (fun s => tree_sub_conj_P u s /\ ~ v ∈ s.(visited) /\ step_aux g e u v)
        (for_branch1 e u v W)
        (fun _ s => tree_sub_conj_P v s /\ u ∈ s.(visited)).
Proof.
  intros IH1 IH2.
  unfold for_branch1.
  hoare_bind Tarjan_set_tree_keep_tree_sub_conj.
  eapply Hoare_bind. 
  2: 
  {
    intros. apply Hoare_conj2.  
    * apply Tarjan_post_rec_keep_tree_sub_conj.
    * apply Tarjan_post_rec_keep_visited. 
  } simpl. 
  apply Hoare_conj; auto.
  hoare_cons_pre IH2.
  hoare_cons_pre IH1.
Qed.

Lemma Tarjan_for_branch2_keep_subgraph_inv (u v: V):
  Hoare (fun s => tree_sub_conj_P u s)
        (for_branch2 u v)
        (fun _ s => tree_sub_conj_P u s).
Proof.
  unfold for_branch2; unfold_op.
  intro_state.
  hoare_auto_s.
  rewrite H0; split; apply H.
Qed.

Lemma Tarjan_keep_tree_subgraph_inv (u: V):
  Hoare (fun s => tree_sub_conj_P u s)
        (tarjan g u)
        (fun _ s => tree_sub_conj_P u s).
Proof.
  unfold tarjan.
  hoare_fix_lv_auto_conj V unit tt.
  1: { apply Tarjan_keep_visited_inv. } 
  intros W IH H.
  simpl; intros a _.
  unfold tarjan_f.
  hoare_bind Tarjan_preloop_keep_tree_sub_conj; simpl.
  unfold loop_body.
  unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  hoare_auto_s.
  intro_state.
  destruct H0 as [is_rt [sub IHa]].
  hoare_auto_s.
  * hoare_bind'' IH0. 
    hoare_cons Tarjan_for_branch1_keep_subgraph_inv'; auto. 
    ** intros; subst; split; [|split]; auto.
       split; [|split]; auto.
    ** intros _ s [[? []]]. 
       split; [|split]; auto.
  * hoare_bind'' IH0.
    hoare_cons Tarjan_for_branch2_keep_subgraph_inv; auto.
    intros; subst; split; auto.
  * hoare_cons_pre IH0.
    intros; subst; split; tauto.
Qed.


Lemma Tarjan_for_branch1_keep_subgraph_inv (u v: V) (e: E)
  (W: V -> program St unit):
  (forall u v, 
  Hoare (fun s => v ∈ s.(visited))
        (W u)
        (fun _ s => v ∈ s.(visited)))
  ->
  (forall u, 
  Hoare (fun s => tree_sub_conj_P u s)
        (W u)
        (fun _ s => tree_sub_conj_P u s))
  ->
  Hoare (fun s => tree_sub_conj_P u s /\ ~ v ∈ s.(visited) /\ step_aux g e u v)
        (for_branch1 e u v W)
        (fun _ s => tree_sub_conj_P v s /\ u ∈ s.(visited)).
Proof.
  intros.
  apply Tarjan_for_branch1_keep_subgraph_inv'; auto.
Qed.

Lemma Tarjan_loop_body_keep_tree_subgraph_inv
  (W: V -> program (@St V E) unit) :
  (forall u v, 
  Hoare (fun s => v ∈ s.(visited))
        (W u)
        (fun _ s => v ∈ s.(visited)))
  ->
  (forall u, 
  Hoare (fun s => tree_sub_conj_P u s)
        (W u)
        (fun _ s => tree_sub_conj_P u s))
  ->
  forall u eset,
  Hoare (fun s => tree_sub_conj_P u s)
        (Lfix (forset_f (forset_body g u W)) eset)
        (fun _ s => tree_sub_conj_P u s).
Proof.
  intros IH1 IH2.
  intros u eset.
  hoare_fix_nolv_auto (E -> Prop).
  simpl; clear eset; intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - hoare_bind'' IH0.
    unfold for_branch1.
    eapply Hoare_bind.
    hoare_cons_pre (Tarjan_set_tree_keep_tree_sub_conj).
    intros; subst; tauto.
    simpl; intros _.
    eapply Hoare_bind. 
    { hoare_conj_n 1.
      * hoare_cons_pre (IH1 _ u).
      * hoare_cons_pre IH2. }
    simpl; intros _.
    hoare_cons_pre (Tarjan_post_rec_keep_tree_sub_conj).
    intros; subst; eapply tree_easy; apply H3.
  - hoare_bind'' IH0.
    unfold for_branch2.
    unfold_op; hoare_auto_s.
    subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; auto.
Qed. 

Lemma tree_subgraph_init_state: 
  tree_sub_conj_P root (initSt root).
Proof.
  intros; subst; simpl.
  split; [ |split]; auto.
  - Opaque clos_refl_trans.
    split; simpl; try easy.
    * intros; exfalso; auto.
    * intros; sets_unfold in H0; sets_unfold in H. subst; auto.
    * intros; sets_unfold in H. subst; reflexivity.
    * intros; sets_unfold in H. subst; apply original_finite_vertices; auto.
  - unfold subgraph; intros.
    destruct H; simpl in *.
    unfold t_empty in ve; inversion ve.
  - reflexivity.
Qed.


Theorem Tarjan_keep_tree_subgraph:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => tree_sub_conj_P root s).
Proof.
  hoare_cons_pre (Tarjan_keep_tree_subgraph_inv root).
  intros; subst; apply tree_subgraph_init_state.
Qed.

Lemma Tarjan_loop_body_keep_visit 
  (W: V -> program St unit):
  (forall u v, 
  Hoare (fun s => v ∈ s.(visited))
        (W u)
        (fun _ s => v ∈ s.(visited)))
  ->
  (forall u eset0 v, 
  Hoare (fun s => v ∈ s.(visited))
        (Lfix (forset_f (forset_body g u W)) eset0)
        (fun _ s => v ∈ s.(visited))).
Proof.
  intros IH1.
  intros u eset0 v.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  simpl; intros W0 IH eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - hoare_bind'' IH.
    unfold for_branch1.
    eapply Hoare_bind; [|intros; eapply Hoare_bind; [apply IH1|]].
    * unfold set_tree, set_tree'. 
      hoare_auto_s.
      subst; simpl.
      left; apply H.
    * simpl; intros _.
      unfold post_rec; unfold_op.
      intro_state. hoare_auto_s; 
      try destruct H4; subst; simpl; auto.
  - hoare_bind'' IH.
    unfold for_branch2.
    unfold_op; hoare_auto_s.
    subst; auto.
  - hoare_cons_pre IH.
    intros; subst; auto.
  - subst; auto. 
Qed.


Lemma Tarjan_loop_body_keep_offspring 
  (W: V -> program St unit):
  (forall x y u, 
  Hoare (fun s => offspring (T s) x y)
        (W u)
        (fun _ s => offspring (T s) x y))
  ->
  (forall x y u eset0, 
  Hoare (fun s => offspring (T s) x y)
        (Lfix (forset_f (forset_body g u W)) eset0)
        (fun _ s => offspring (T s) x y)).
Proof.
  intros IH1.
  intros x y u eset0.
  hoare_fix_nolv_auto (E -> Prop).
  simpl; intros W0 IH eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - hoare_bind'' IH.
    unfold for_branch1.
    eapply Hoare_bind; [|intros; eapply Hoare_bind; [apply IH1|]].
    * unfold set_tree.
      hoare_auto_s.
      subst.
      apply tree_keep_offspring; eauto. 
    * simpl; intros _.
      unfold post_rec; unfold_op.
      intro_state. hoare_auto_s; 
      try destruct H4; subst; simpl; auto.
  - hoare_bind'' IH.
    unfold for_branch2.
    unfold_op; hoare_auto_s.
    subst; auto.
  - hoare_cons_pre IH.
    intros; subst; auto.
  - subst; auto. 
Qed.


Lemma Tarjan_loop_body_keep_offspring_prod
  (W: V -> program St unit):
  (forall x y u, 
  Hoare (fun s => offspring (T s) x y)
        (W u)
        (fun _ s => offspring (T s) x y))
  ->
  (forall u eset0 p, 
  Hoare (fun s => offspring (T s) (fst p) (snd p))
        (Lfix (forset_f (forset_body g u W)) eset0)
        (fun _ s => offspring (T s) (fst p) (snd p))).
Proof. intros; destruct p; simpl. apply Tarjan_loop_body_keep_offspring; auto. Qed.

Theorem Tarjan_rooted_tree:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => is_rooted_tree (T s)).
Proof. hoare_cons_post (Tarjan_keep_tree_subgraph); firstorder. Qed.

Theorem Tarjan_subgraph:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => subgraph (T s) g).
Proof. hoare_cons_post (Tarjan_keep_tree_subgraph). intros; apply H. Qed.



(*to prove a simple lemma used in final proof*)

Lemma Tarjan_reachable_visited:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => reachable_visited g (T s)).
Proof.
  hoare_cons_post Tarjan_visited_reachable.
  intros _ s IH.
  intros u H.
  simpl in *; firstorder.
Qed.

Lemma bridge_is_tree_edge_init_state: 
  bridge_is_tree_edge (initSt root).
Proof.
  intros; subst; simpl.
  intros e Hein; subst; tauto.
Qed.

Theorem Tarjan_bridge_is_tree_edge:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => forall e: E, 
        List.In e s.(bridges) -> evalid (T s) e).
Proof.
  hoare_cons_pre Tarjan_bridge_is_tree_edge_inv.
  intros; subst; apply bridge_is_tree_edge_init_state.
Qed.





Lemma Tarjan_preloop_keep_nostep_aux (u x y: V)(e: E):
  Hoare (fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y)
        (preloop u)
        (fun _ s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y).
Proof.
  intro_state; unfold_preloop; subst; auto.
Qed.

Lemma Tarjan_set_tree_keep_nostep_aux (u v x y: V) (e e0: E):
  Hoare (fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y /\ ~ v ∈ s.(visited))
        (set_tree u v e0)
        (fun _ s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y).
Proof.
  apply Hoare_conj; [|apply Hoare_conj].
  hoare_cons_pre Tarjan_set_tree_keep_visited.
  hoare_cons_pre Tarjan_set_tree_keep_visited.
  unfold set_tree; unfold_op.
  intro_state. 
  hoare_auto_s. 
  destruct H as [Hx [Hy [Hnstep Hv]]].
  subst; unfold not; intros; subst; destruct H; apply Hnstep.
  split; simpl in *.
  * destruct vx; try congruence.
  * destruct vy; try congruence.
  * unfold t_set in ve; equiv_dec_simpl v y. 
  * unfold t_set in vp; equiv_dec_simpl v y. 
Qed.

Lemma Tarjan_post_rec_keep_nostep_aux (u v x y: V) (e e0: E):
  Hoare (fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y)
        (post_rec e0 u v)
        (fun _ s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y).
Proof.
  unfold post_rec; unfold_op.
  intro_state; hoare_auto_s; [|destruct H0]; subst; auto.
Qed.

Lemma Tarjan_for_branch2_keep_nostep_aux (u v x y: V) (e: E):
  Hoare (fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y)
        (for_branch2 u v)
        (fun _ s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y).
Proof.
  unfold for_branch2; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
Qed.

Theorem Tarjan_keep_nostep_aux_inv (u x y: V)(e: E):
  Hoare (fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y)
        (tarjan g u)
        (fun _ s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ step_aux (T s) e x y).
Proof.
  unfold tarjan.
  hoare_fix_nolv_auto V.
  intros W IH v; simpl.
  unfold tarjan_f.
  hoare_bind Tarjan_preloop_keep_nostep_aux.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - unfold for_branch1.
    hoare_bind'' IH0.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_keep_nostep_aux.
    hoare_bind'' IH.
    hoare_cons_pre Tarjan_set_tree_keep_nostep_aux.
    my_destruct H. 
    intros; subst; repeat split; auto.
  - hoare_bind'' IH0.
    unfold for_branch2.
    unfold_op; hoare_auto_s.
    subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; auto.
Qed.

Lemma Tarjan_keep_nostep_aux_inv_prod (u: V) (p: (V * V) * E):
  Hoare (fun s => (fst (fst p)) ∈ s.(visited) /\ (snd (fst p)) ∈ s.(visited) /\ ~ step_aux (T s) (snd p) (fst (fst p)) (snd (fst p)))
        (tarjan g u)
        (fun _ s => (fst (fst p)) ∈ s.(visited) /\ (snd (fst p)) ∈ s.(visited) /\ ~ step_aux (T s) (snd p) (fst (fst p)) (snd (fst p))).
Proof.
  destruct p as ((x, y), e); simpl.
  apply Tarjan_keep_nostep_aux_inv.
Qed.

Lemma Tarjan_preloop_keep_nooffspring (u x y: V):
  Hoare (fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ offspring (T s) x y)
        (preloop u)
        (fun _ s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ offspring (T s) x y).
Proof.
  intro_state; unfold_preloop.
  destruct H; subst; auto.
Qed.

Lemma Tarjan_set_tree_keep_nooffspring (u v x y: V) (e: E):
  Hoare (fun s => ~ offspring (T s) x y /\ tree_sub_conj_P u s /\ ~ v ∈ s.(visited) /\ y ∈ s.(visited))
        (set_tree u v e)
        (fun _ s => ~ offspring (T s) x y).
Proof.
  unfold set_tree; intro_state; hoare_auto_s; subst; auto.
  my_destruct H.
  destruct H0 as [is_rt [sub Hu]].
  unfold not; intros; apply H. 
  eapply tree_keep_offspring'; eauto; try tauto.
  unfold not; intros; subst; auto.
Qed.

Lemma Tarjan_post_rec_keep_nooffspring (u v x y: V) (e: E):
  Hoare (fun s => ~ offspring (T s) x y)
        (post_rec e u v)
        (fun _ s => ~ offspring (T s) x y).
Proof.
  unfold post_rec; unfold_op.
  intro_state; hoare_auto_s; [|destruct H0]; subst; auto.
Qed.

Lemma Tarjan_for_branch2_keep_nooffspring (u v x y: V) (e: E):
  Hoare (fun s => ~ offspring (T s) x y)
        (for_branch2 u v)
        (fun _ s => ~ offspring (T s) x y).
Proof.
  unfold for_branch2; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
Qed.


Lemma Tarjan_keep_nooffspring_inv (u x y: V):
  Hoare (fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ offspring (T s) x y /\ tree_sub_conj_P u s)
        (tarjan g u)
        (fun _ s => ~ offspring (T s) x y).
Proof.
  unfold tarjan.
  hoare_fix_nolv_fs_auto V.
  {
    forall_n 2.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv V @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_subgraph_inv unit @tarjan.
  }
  intros W IHa IH v; intros _.
  unfold_Forall IHa.
  unfold tarjan_f.
  eapply Hoare_bind.
  { 
    apply Hoare_conj.
    * hoare_cons_pre Tarjan_preloop_keep_nooffspring.
      intros; my_destruct H; split; [apply H|eauto].
    * hoare_cons_pre Tarjan_preloop_keep_tree_sub_conj.
  } 
  simpl; intros _.
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - my_destruct H.
    unfold for_branch1.
    hoare_bind'' IH0.
    eapply Hoare_bind. 
    { 
      do 2 apply Hoare_conj.
      * hoare_cons_pre (Tarjan_set_tree_keep_visited _ _ x). 
        intros; subst; auto.
      * hoare_cons_pre (Tarjan_set_tree_keep_visited _ _ y). 
        intros; subst; auto.
      * hoare_cons_pre (Tarjan_set_tree_keep_nooffspring _ _ x y).
        intros; subst; split; [|split; [|split]]; auto.
      * hoare_cons_pre (Tarjan_set_tree_keep_tree_sub_conj _).
        intros; subst; split; [|split]; auto.
    }
    simpl; intros _.
    eapply Hoare_bind.
    2:
    { intros. apply Hoare_conj2; [apply Hoare_conj2; [|apply Hoare_conj2]|]. 
      * apply Tarjan_post_rec_keep_visited.
      * apply Tarjan_post_rec_keep_visited.
      * apply Tarjan_post_rec_keep_nooffspring.
      * apply Tarjan_post_rec_keep_tree_sub_conj.
    }
    simpl. apply Hoare_conj; [apply Hoare_conj; [|apply Hoare_conj]|].
    * hoare_cons_pre IHa0.
    * hoare_cons_pre IHa0.
    * hoare_cons_pre IH.
    * apply Hoare_conj; [|apply Hoare_conj].
      ** hoare_cons IHa1; intros; apply H6.
      ** hoare_cons IHa1; intros; apply H6.
      ** hoare_cons_pre IHa0.
  - hoare_bind'' IH0.
    unfold for_branch2.
    unfold_op; hoare_auto_s.
    subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; tauto.
Qed.

Lemma Tarjan_keep_nooffspring_inv_prod (u: V) (p: V * V):
  Hoare (fun s => (fst p) ∈ s.(visited) /\ (snd p) ∈ s.(visited) /\ ~ offspring (T s) (fst p) (snd p) /\ tree_sub_conj_P u s)
        (tarjan g u)
        (fun _ s => ~ offspring (T s) (fst p) (snd p)).
Proof.
  destruct p as (x, y); simpl.
  apply Tarjan_keep_nooffspring_inv.
Qed.


Lemma Tarjan_keep_bridge_inv (u: V) (e: E):
  Hoare (fun s => List.In e s.(bridges))
        (tarjan g u)
        (fun _ s => List.In e s.(bridges)).
Proof.
  unfold tarjan.
  hoare_fix_nolv_auto V. 
  intros W IH1 v; simpl.
  unfold tarjan_f.
  unfold_preloop.
  apply Hoare_conseq_pre with 
    (P2:= fun s => List.In e s.(bridges)).
  { intros; subst s1; rewrite H1; simpl; auto. }
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - unfold for_branch1.
    hoare_bind'' IH0.
    eapply Hoare_bind; [|intros; eapply Hoare_bind; [apply IH1|]].
    { 
      unfold set_tree, set_tree'.
      hoare_auto_s.
      subst; auto.
    }
    simpl; intros _.
    unfold post_rec; unfold_op.
    intro_state.
    hoare_auto_s; destruct H5;
    intros; subst; simpl; auto.
  - hoare_bind'' IH0.
    unfold for_branch2.
    unfold_op; hoare_auto_s.
    subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; auto.
Qed.

Lemma Tarjan_set_tree_keep_nobridge (u v: V) (e e0: E):
  Hoare (fun s => ~ List.In e s.(bridges))
        (set_tree u v e0)
        (fun _ s => ~ List.In e s.(bridges)).
Proof.
  unfold set_tree; unfold_op.
  intro_state; hoare_auto_s; subst; auto.
Qed.

Lemma Tarjan_keep_nobridge_inv (u x y: V) (e: E):
  Hoare (fun s => step_aux g e x y /\ x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ List.In e s.(bridges))
        (tarjan g u)
        (fun _ s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ List.In e s.(bridges)).
Proof.
  unfold tarjan.
  hoare_fix_nolv_auto V.
  intros W IH1 v.
  unfold tarjan_f.
  unfold_preloop.
  my_destruct H.
  apply Hoare_conseq_pre with 
    (P2:= fun s => x ∈ s.(visited) /\ y ∈ s.(visited) /\ ~ List.In e s.(bridges)).
  { intros; subst; simpl; auto. }
  unfold loop_body, forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state.
  hoare_auto_s.
  - my_destruct H4.
    unfold for_branch1.
    hoare_bind'' IH0.
    eapply Hoare_bind; [|intros; eapply Hoare_bind; [apply IH1|]].
    { 
      unfold set_tree, set_tree'.
      hoare_auto_s.
      split; [|repeat split]; subst; simpl; try left; auto.
    }
    simpl; intros _.
    unfold post_rec; unfold_op.
    intro_state.
    my_destruct H9.
    hoare_auto_s; [|destruct H12];
    intros; subst; simpl; repeat split; auto.
    unfold not; intros; destruct H13.
    { 
      subst. eapply step_aux_unique_undirected in H as [[]|[]]; eauto;
      subst; congruence. 
    } 
    { congruence. }
  - hoare_bind'' IH0.
    unfold for_branch2.
    unfold_op; hoare_auto_s.
    subst; auto.
  - hoare_cons_pre IH0.
    intros; subst; auto.
  - subst; auto.
Qed.


Lemma Tarjan_keep_nobridge_inv_prod (u: V) (p: V * V * E):
  Hoare (fun s => step_aux g (snd p) (fst (fst p)) (snd (fst p)) /\ (fst (fst p)) ∈ s.(visited) /\ (snd (fst p)) ∈ s.(visited) /\ ~ List.In (snd p) s.(bridges))
        (tarjan g u)
        (fun _ s => (fst (fst p)) ∈ s.(visited) /\ (snd (fst p)) ∈ s.(visited) /\ ~ List.In (snd p) s.(bridges)).
Proof.
  destruct p as ((x, y), e); simpl.
  apply Tarjan_keep_nobridge_inv.
Qed.

End BASICS.
