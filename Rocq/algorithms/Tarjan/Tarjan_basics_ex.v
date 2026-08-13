
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From TraceLib Require Import TraceBasic TraceLogic TraceRecur CommonTactics MapLib.
From GraphLib Require Import GraphLib tarjan.
From Algorithms Require Import Tarjan Tarjan_tactics Tarjan_basics Tarjan_set_tree.

Import SetsNotation.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope sets.
Local Open Scope map_scope.
Local Open Scope trace_scope.

Section BASICS'.

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
Notation St := (@St V E).
Notation Tag := (@Tag V).
Notation TR := (@TR Tag St).

(*-------------------------------- just clean ghost code derived from basics.v --------------------------------*)

Lemma Tarjan_track_in_keep_tree_sub_conj' (u: V):
  Hoare ((fun '(s, _) => tree_sub_conj_P root g u s): St * TR -> Prop)
        (track (In u))
        (fun _ '(s, _) => tree_sub_conj_P root g u s).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
Qed.

Lemma Tarjan_preloop_keep_tree_sub_conj' (u: V):
  Hoare ((fun '(s, _) => tree_sub_conj_P root g u s): St * TR -> Prop)
        ((↑ (preloop u))%ghost)
        (fun _ '(s, _) => tree_sub_conj_P root g u s).
Proof. 
  eapply Hoare_toG.
  2: {apply Tarjan_preloop_keep_tree_sub_conj. } 
  eapply Gequiv_preloop.
  tauto.
Qed.

Lemma Tarjan_set_tree_keep_tree_sub_conj' (u v: V) (e: E):
  Hoare ((fun '(s, _) => tree_sub_conj_P root g u s /\ ~ v ∈ s.(visited) /\ step_aux g e u v): St * TR -> Prop)
        ((↑ (set_tree u v e))%ghost)
        (fun _ '(s, _) => tree_sub_conj_P root g v s /\ u ∈ s.(visited)).
Proof.
  eapply Hoare_toG.
  2: {apply Tarjan_set_tree_keep_tree_sub_conj; auto. } 
  eapply Gequiv_set_tree.
  tauto.
Qed.

Lemma Tarjan_post_rec_keep_tree_sub_conj' (u v w: V) (e: E):
  Hoare ((fun '(s, _) => tree_sub_conj_P root g w s): St * TR -> Prop)
        ((↑ (post_rec e u v))%ghost)
        (fun _ '(s, _) => tree_sub_conj_P root g w s).  
Proof.
  eapply Hoare_toG.
  2: {apply Tarjan_post_rec_keep_tree_sub_conj; auto. } 
  eapply Gequiv_post_rec.
  tauto.
Qed.

Lemma Tarjan_track_out_keep_tree_sub_conj' (u: V):
  Hoare ((fun '(s, _) => tree_sub_conj_P root g u s): St * TR -> Prop)
        (track (Out u))
        (fun _ '(s, _) => tree_sub_conj_P root g u s).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
Qed.

Lemma Tarjan_keep_tree_sub_conj' (u: V):
  Hoare ((fun '(s, _) => tree_sub_conj_P root g u s): St * TR -> Prop)
        (tarjan' g u)
        (fun _ '(s, _) => tree_sub_conj_P root g u s).
Proof.
  eapply Hoare_toG.
  2: {apply Tarjan_keep_tree_subgraph_inv; auto. }
  eapply Gequiv_tarjan.
  tauto.
Qed.

Theorem Tarjan_tree_sub_conj': 
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ '(s, _) => tree_sub_conj_P root g root s).
Proof.
  hoare_cons_pre Tarjan_keep_tree_sub_conj'.
  intros (s, tr); intros []; subst; simpl.
  apply tree_subgraph_init_state; auto.
Qed.

Lemma Tarjan_keep_visited_inv' (u v: V):
  Hoare ((fun '(s, _) => v ∈ s.(visited)): St * TR -> Prop)
        (tarjan' g u)
        (fun _ '(s, _) => v ∈ s.(visited)).
Proof.
  eapply Hoare_toG. 2: {apply Tarjan_keep_visited_inv; auto. }
  eapply Gequiv_tarjan. tauto.
Qed.

Lemma Tarjan_keep_step_aux_outv'_prod (u: V) (p: V * V * E):
  Hoare ((fun '(s, _) => step_aux (T s) (snd p) (fst (fst p)) (snd (fst p))): St * TR -> Prop)
        (tarjan' g u)
        (fun _ '(s, _) => step_aux (T s) (snd p) (fst (fst p)) (snd (fst p))).
Proof.
  eapply Hoare_toG. 2: {apply Tarjan_keep_step_aux_inv_prod; auto. }
  eapply Gequiv_tarjan. tauto.
Qed.

Lemma Tarjan_track_in_bridge_is_tree_edge' (u: V):
  Hoare (fun '(s, tr) => bridge_is_tree_edge root g s)
        (track (In u))
        (fun _ '(s, tr) => bridge_is_tree_edge root g s).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
Qed.

Lemma Tarjan_preloop_bridge_is_tree_edge' (u: V):
  Hoare ((fun '(s, tr) => bridge_is_tree_edge root g s): St * TR -> Prop)
        ((↑ (preloop u))%ghost)
        (fun _ '(s, tr) => bridge_is_tree_edge root g s).
Proof.
  eapply Hoare_toG. 2: {apply Tarjan_preloop_bridge_is_tree_edge; auto. }
  eapply Gequiv_preloop.
  tauto.
Qed.

Lemma Tarjan_set_tree_bridge_is_tree_edge' (u v: V) (e: E):
  Hoare ((fun '(s, tr) => bridge_is_tree_edge root g s /\ ~ v ∈ s.(visited)): St * TR -> Prop)
        ((↑ (set_tree u v e))%ghost)
        (fun _ '(s, tr) => bridge_is_tree_edge root g s /\ evalid (T s) e).
Proof.
  eapply Hoare_toG. 2: {apply Tarjan_set_tree_bridge_is_tree_edge; auto. }
  eapply Gequiv_set_tree.
  tauto.
Qed.

Lemma Tarjan_post_rec_bridge_is_tree_edge' (u v: V) (e: E):
  Hoare ((fun '(s, tr) => bridge_is_tree_edge root g s /\ evalid (T s) e): St * TR -> Prop)
        ((↑ (post_rec e u v))%ghost)
        (fun _ '(s, tr) => bridge_is_tree_edge root g s).
Proof.
  eapply Hoare_toG. 2: {apply Tarjan_post_rec_bridge_is_tree_edge; auto. }
  eapply Gequiv_post_rec.
  tauto.
Qed.

Lemma Tarjan_track_out_bridge_is_tree_edge' (u: V):
  Hoare (fun '(s, tr) => bridge_is_tree_edge root g s)
        (track (Out u))
        (fun _ '(s, tr) => bridge_is_tree_edge root g s).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
Qed.

Theorem Tarjan_bridge_is_tree_edge_inv' (u: V):
  Hoare (fun '(s, tr) => bridge_is_tree_edge root g s)
        (tarjan' g u)
        (fun _ '(s, tr) => bridge_is_tree_edge root g s).
Proof.
  eapply Hoare_toG. 2: {apply Tarjan_bridge_is_tree_edge_inv; auto. }
  eapply Gequiv_tarjan.
  tauto.
Qed.

Theorem Tarjan_keep_edge_inv' (u: V)(e: E):
  Hoare (fun '(s, tr) => evalid (state_to_rootedtree g root s) e)
        (tarjan' g u)
        (fun _ '(s, tr) => evalid (state_to_rootedtree g root s) e).
Proof.
  eapply Hoare_toG. 2: {apply Tarjan_keep_edge_inv; auto. }
  eapply Gequiv_tarjan. tauto.
Qed.





(*-------------------------------- mono, keep, ... properties --------------------------------*)

(*-------------------------------- about visited --------------------------------*)

Definition visited_in : St * TR -> Prop :=
  fun '(s, tr) => forall v, v ∈ s.(visited) -> tr |= have (t↑(In v)).

Definition visited_in_except_u (u: V): St * TR -> Prop :=
  fun '(s, tr) => forall v, v <> u -> v ∈ s.(visited) -> tr |= have (t↑(In v)).

Definition visited_persist: St * TR -> Prop :=
  fun '(s, tr) => forall v, tr |= have (t↑(In v)) -> v ∈ s.(visited).

Definition visited_persist_within (u: V): St * TR -> Prop :=
  fun '(s, tr) => (forall v, tr |= have (t↑(In v)) -> v ∈ s.(visited)) /\ (u ∈ s.(visited)).

Lemma Tarjan_track_in_visited_in (u: V): 
  Hoare (visited_in_except_u u)
        (track (In u))
        (fun _ => visited_in).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  destruct (classic (v = u)); subst.
  * apply app_have_atom; right; 
    apply singleton_have_atom; reflexivity.
  * apply app_have_atom; left; auto. 
Qed.

Lemma Tarjan_track_out_visited_in (u: V): 
  Hoare (visited_in)
        (track (Out u))
        (fun _ => visited_in).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  apply app_have_atom; left; auto.
Qed.

Lemma Tarjan_preloop_visited_in (u: V): 
  Hoare (visited_in)
        ((↑ (preloop u))%ghost)
        (fun _ => visited_in).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? []]; subst; auto.
Qed. 

Lemma Tarjan_set_tree_visited_in (u v: V) (e: E): 
  Hoare (visited_in)
        ((↑ (set_tree u v e))%ghost)
        (fun _ => visited_in_except_u v).
Proof.
  unfold set_tree, set_tree'.
  intro_state_pair.
  hoare_auto_G. 
  simpl; intros _ ? [?[]]; subst; simpl; intros.
  destruct H1; [|exfalso]; auto.
Qed.

Lemma Tarjan_post_rec_visited_in (u v: V) (e: E): 
  Hoare (visited_in)
        ((↑ (post_rec e u v))%ghost)
        (fun _ => visited_in).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ s0 [? [? [|[]]]]; subst; auto.
Qed. 

Theorem Tarjan_visited_in_inv (u: V):
  Hoare (visited_in_except_u u)
        (tarjan' g u)
        (fun _ => visited_in).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_auto V; intros W IH a.
  unfold trace_call_f, tarjan_f'.
  hoare_bind Tarjan_track_in_visited_in; simpl.
  hoare_bind'' Tarjan_track_out_visited_in.
  hoare_bind Tarjan_preloop_visited_in; simpl.
  clear a0 a1.
  unfold loop_body'; unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_visited_in.
    hoare_bind'' IH. 
    hoare_cons_pre Tarjan_set_tree_visited_in; intros; subst; auto.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ ? [?[? [|[]]]]; subst; auto.
Qed.

Theorem Tarjan_visited_in:
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => visited_in).
Proof.
  hoare_cons_pre Tarjan_visited_in_inv.
  intros (s, tr); intros []; subst; simpl.
  intros; congruence.
Qed.

Lemma Tarjan_track_in_visited_persist (u: V): 
  Hoare (visited_persist_within u)
        (track (In u))
        (fun _ => visited_persist).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  destruct (classic (v = u)); subst.
  * apply H. 
  * apply app_have_atom in Hv as []. 
    ** apply H; auto.
    ** rewrite singleton_have_atom in H1.
       inversion H1; subst; apply H. 
Qed.

Lemma Tarjan_track_out_visited_persist (u: V): 
  Hoare (visited_persist)
        (track (Out u))
        (fun _ => visited_persist).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  apply app_have_atom in Hv as []; auto. 
  rewrite singleton_have_atom in H0; inversion H0; auto.
Qed.

Lemma Tarjan_preloop_visited_persist (u: V): 
  Hoare (visited_persist)
        ((↑ (preloop u))%ghost)
        (fun _ => visited_persist).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? []]; subst; auto.
Qed. 

Lemma Tarjan_set_tree_visited_persist (u v: V) (e: E): 
  Hoare (visited_persist)
        ((↑ (set_tree u v e))%ghost)
        (fun _ => visited_persist_within v).
Proof.
  unfold set_tree, set_tree'.
  intro_state_pair.
  hoare_auto_G. 
  simpl; intros _ ? [?[]]; subst; simpl; intros; split.
  * intros; left; apply H; auto.
  * right; reflexivity.
Qed.

Lemma Tarjan_post_rec_visited_persist (u v: V) (e: E): 
  Hoare (visited_persist)
        ((↑ (post_rec e u v))%ghost)
        (fun _ => visited_persist).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ s0 [? [? [|[]]]]; subst; auto.
Qed. 

Theorem Tarjan_visited_persist_inv (u: V):
  Hoare (visited_persist_within u)
        (tarjan' g u)
        (fun _ => visited_persist).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_auto V; intros W IH a.
  unfold trace_call_f, tarjan_f'.
  hoare_bind Tarjan_track_in_visited_persist; simpl.
  hoare_bind'' Tarjan_track_out_visited_persist.
  hoare_bind Tarjan_preloop_visited_persist; simpl.
  clear a0 a1.
  unfold loop_body'; unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_visited_persist.
    hoare_bind'' IH.
    hoare_cons_pre Tarjan_set_tree_visited_persist; intros; subst; auto.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ ? [?[? [|[]]]]; subst; auto.
Qed.

Theorem Tarjan_visited_persist:
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => visited_persist).
Proof.
  hoare_cons_pre Tarjan_visited_persist_inv.
  intros (s, tr); intros []; subst; split; simpl.
  * intros; exfalso; eapply not_nil_have; eauto.
  * reflexivity.
Qed.

Definition visited_out_persist: St * TR -> Prop := 
  fun '(s, tr) => forall v, tr |= have (t↑(Out v)) -> v ∈ s.(visited).

Lemma Tarjan_track_in_visited_out_persist (u: V):
  Hoare (fun '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited))
        (track (In u))
        (fun _ '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited)).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  my_destruct H.
  intros; subst; split; try tauto; intros v Hv.
  apply app_have_atom in Hv; destruct Hv; auto. 
  rewrite singleton_have_atom in H1; inversion H1; subst; auto.
Qed.

Lemma Tarjan_track_out_visited_out_persist (u: V):
  Hoare (fun '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited))
        (track (Out u))
        (fun _ => visited_out_persist).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  apply app_have_atom in Hv; destruct Hv; auto.
  * apply H; auto.
  * rewrite singleton_have_atom in H0; inversion H0; subst; tauto.
Qed.

Lemma Tarjan_preloop_visited_out_persist (u: V):
  Hoare (fun '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited))
        ((↑ (preloop u))%ghost)
        (fun _ '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited)).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  intros _ s0 [? []]; subst; auto.
Qed.

Lemma Tarjan_set_tree_visited_out_persist (u v: V) (e: E):
  Hoare (fun '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited))
        ((↑ (set_tree u v e))%ghost)
        (fun _ '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited) /\ v ∈ s.(visited)).
Proof.
  unfold set_tree; intro_state_pair.
  hoare_auto_G; destruct H.
  simpl; intros _ ? [? []]; subst; split_r 2; auto.
  * intros; left; apply H; auto.
  * left; auto.
  * right; reflexivity.
Qed.

Lemma Tarjan_post_rec_visited_out_persist (u v: V) (e: E):
  Hoare (fun '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited))
        ((↑ (post_rec e u v))%ghost)
        (fun _ '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited)).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ ? [? [? [|[]]]]; subst; auto.
Qed.

Theorem Tarjan_visited_out_persist_inv (u: V):
  Hoare (fun '(s, tr) => visited_out_persist (s, tr) /\ u ∈ s.(visited))
        (tarjan' g u)
        (fun _ => visited_out_persist).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_fs_auto V.
  { forall_n 1. 
    hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv' V @tarjan'. }
  clear u; intros W IHa IH u _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  hoare_bind Tarjan_track_in_visited_out_persist; simpl.
  hoare_bind'' Tarjan_track_out_visited_out_persist.
  hoare_bind Tarjan_preloop_visited_out_persist; simpl.
  clear a a0.
  unfold loop_body'; unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - rename a0 into v; rename a into e.
    hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_visited_out_persist.
    eapply Hoare_bind. {
      hoare_conj_n 1.
      * hoare_cons_pre Tarjan_set_tree_visited_out_persist; intros; subst; tauto.
      * instantiate (1:= fun _ '(s, tr) => visited s u); unfold set_tree; hoare_auto_G; intros _ (s0, tr) [? []]; inversion H3; subst; left; tauto.
    } simpl; intros _.
    eapply Hoare_conseq_post. 2: {
      hoare_conj_n 1.
      * hoare_cons_pre IH; intros (s0, tr); tauto.
      * hoare_cons_pre (IHa0 _ u); intros (s0, tr); tauto.
    } simpl; intros _ (s0, tr); subst; split; try tauto.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ ? [?[? [|[]]]]; subst; auto.
Qed.
(* about offpsring *)

Definition offspring_persist : St * TR -> Prop :=
  fun '(s, tr) => forall x y, 
  tr |= have (s↑ (fun s => offspring (state_to_rootedtree g root s) x y) ) -> 
  offspring (state_to_rootedtree g root s) x y. 

Lemma Tarjan_track_in_offspring_persist (u: V):
  Hoare (offspring_persist)
        (track (In u))
        (fun _ => offspring_persist).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros x y Hxy.
  apply app_have_atom in Hxy; destruct Hxy; auto.
  rewrite singleton_have_atom in H0.
  simpl in H0; inversion H0; subst; auto.
Qed.

Lemma Tarjan_track_out_offspring_persist (u: V):
  Hoare (offspring_persist)
        (track (Out u))
        (fun _ => offspring_persist).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros x y Hxy.
  apply app_have_atom in Hxy; destruct Hxy; auto.
  rewrite singleton_have_atom in H0.
  simpl in H0; inversion H0; subst; auto.
Qed.

Lemma Tarjan_preloop_offspring_persist (u: V):
  Hoare (offspring_persist)
        ((↑ (preloop u))%ghost)
        (fun _ => offspring_persist).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? []]; subst; auto.
Qed.


Lemma Tarjan_set_tree_offspring_persist (u v: V) (e: E):
  Hoare (fun '(s, tr) => offspring_persist (s, tr) /\ ~ v ∈ s.(visited))
        ((↑ (set_tree u v e))%ghost)
        (fun _ => offspring_persist).
Proof.
  unfold set_tree.
  intro_state_pair.
  hoare_auto_G; destruct H.
  simpl; intros _ ? [s1 []]; subst.
  intros x y Hxy. 
  apply tree_keep_offspring; auto.
Qed.

Lemma Tarjan_post_rec_offspring_persist (u v: V) (e: E):
  Hoare (offspring_persist)
        ((↑ (post_rec e u v))%ghost)
        (fun _ => offspring_persist).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ ? [?[? [|[]]]]; subst; auto.
Qed.



Theorem Tarjan_offspring_persist_inv (u: V):
  Hoare (offspring_persist)
        (tarjan' g u)
        (fun _ => offspring_persist).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_auto V; intros W IH a.
  unfold trace_call_f, tarjan_f'.
  hoare_bind Tarjan_track_in_offspring_persist; simpl.
  hoare_bind'' Tarjan_track_out_offspring_persist.
  hoare_bind Tarjan_preloop_offspring_persist; simpl.
  clear a0 a1.
  unfold loop_body'; unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s.
    hoare_bind'' IH0. 
    unfold for_branch1'. 
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_offspring_persist.
    hoare_bind'' IH.
    hoare_cons_pre Tarjan_set_tree_offspring_persist; intros; subst; auto.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ ? [?[? [|[]]]]; subst; auto.
Qed.

Theorem Tarjan_offspring_persist': 
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => offspring_persist).
Proof.
  hoare_cons_pre Tarjan_offspring_persist_inv.
  intros (s, tr); intros []; subst; simpl.
  intros; exfalso; eapply not_nil_have; eauto.
Qed.

(* about tree_sub_conj *)

Definition tree_sub_conj_in : St * TR -> Prop :=
  fun '(s, tr) => forall v, v ∈ s.(visited) -> tr |= have (ts↑ (In (v)) (fun s => tree_sub_conj_P root g v s)). 

Definition tree_sub_conj_in_except (u: V): St * TR -> Prop :=
  fun '(s, tr) => forall v, v ∈ s.(visited) -> v <> u -> tr |= have (ts↑ (In (v)) (fun s => tree_sub_conj_P root g v s)).

Lemma Tarjan_track_in_tree_sub_conj_in (u: V):
  Hoare (fun '(s, tr) => tree_sub_conj_in_except u (s, tr) /\ tree_sub_conj_P root g u s)
        (track (In u))
        (fun _ => tree_sub_conj_in).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
  intros v Hv.
  destruct (classic (v = u)); subst.
  * rewrite app_have_atom; right.
    rewrite singleton_have_atom; split; tauto.
  * rewrite app_have_atom; left.
    apply H; auto.
Qed.

Lemma Tarjan_preloop_tree_sub_conj_in (u: V):
  Hoare (fun '(s, tr) => tree_sub_conj_in (s, tr))
        ((↑ (preloop u))%ghost)
        (fun _ => tree_sub_conj_in).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? []]; subst; auto. 
Qed.

Lemma Tarjan_set_tree_tree_sub_conj_in (u v: V) (e: E):
  Hoare (fun '(s, tr) => tree_sub_conj_in (s, tr))
        ((↑ (set_tree u v e))%ghost)
        (fun _ => tree_sub_conj_in_except v).
Proof.
  unfold set_tree; intro_state_pair.
  hoare_auto_G; my_destruct H.
  simpl; intros _ ? [? []]; subst; auto.
  intros w Hw Hneq.
  destruct Hw; [auto | sets_unfold in H0; subst]; congruence.
Qed.

Lemma Tarjan_post_rec_tree_sub_conj_in (u v: V) (e: E):
  Hoare (fun '(s, tr) => tree_sub_conj_in (s, tr))
        ((↑ (post_rec e u v))%ghost)
        (fun _ => tree_sub_conj_in).
Proof.
  intro_state_pair.
  unfold post_rec; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? [? [|[]]]]; subst; auto. 
Qed. 

Lemma Tarjan_track_out_tree_sub_conj_in (u: V):
  Hoare (fun '(s, tr) => tree_sub_conj_in (s, tr))
        (track (Out u))
        (fun _ => tree_sub_conj_in).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
  intros v Hv.
  apply app_have_atom; left; auto.
Qed.

Theorem Tarjan_tree_sub_conj_in_inv (u: V):
  Hoare (fun '(s, tr) => tree_sub_conj_in_except u (s, tr) /\ tree_sub_conj_P root g u s)
        (tarjan' g u)
        (fun _ => tree_sub_conj_in).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_fs_auto V. {
    forall_n 2.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv' V @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_sub_conj' unit @tarjan'. }
  clear u; intros W IHa IH u _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  eapply Hoare_bind. {
    hoare_conj_n 1.
    * hoare_cons_pre Tarjan_track_in_tree_sub_conj_in.
    * hoare_cons_pre Tarjan_track_in_keep_tree_sub_conj'; intros (s, tr); tauto. 
  }simpl; intros _.
  hoare_bind'' Tarjan_track_out_tree_sub_conj_in.
  eapply Hoare_bind. {
    hoare_conj_n 1.
    * hoare_cons_pre Tarjan_preloop_tree_sub_conj_in.
    * hoare_cons_pre Tarjan_preloop_keep_tree_sub_conj'; intros (s, tr); tauto. 
  }simpl; intros _.
  unfold loop_body', forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    eapply Hoare_bind. 2:{
      intros; hoare_conj2_n 1.
      * apply Tarjan_post_rec_tree_sub_conj_in.
      * apply Tarjan_post_rec_keep_tree_sub_conj'. }
    eapply Hoare_bind. {
      hoare_conj_n 1.
      * hoare_cons_pre Tarjan_set_tree_tree_sub_conj_in; intros; subst; tauto.
      * hoare_cons_pre Tarjan_set_tree_keep_tree_sub_conj'; intros; subst; split_r 2; tauto.
    } simpl; intros _.
    hoare_conj_n 1.
    * hoare_cons_pre IH; intros (s0, tr); intros; split; tauto.
    * eapply Hoare_conseq_post. 2: {
      apply Hoare_conj.
      * hoare_cons_pre (IHa0 _ u); intros (s0, tr); tauto.
      * hoare_cons_pre IHa1; intros (s0, tr); intros; tauto.
    } simpl; intros _ (s0, tr); intros; eapply tree_easy; apply H3.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ s1 [? [? [|[]]]]; subst; auto.
  - tauto.
Qed.

Theorem Tarjan_tree_sub_conj_in: 
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => tree_sub_conj_in).
Proof.
  hoare_cons_pre Tarjan_tree_sub_conj_in_inv.
  intros; destruct s; destruct H; subst; split; auto.
  * intros; congruence.
  * apply tree_subgraph_init_state; auto.
Qed.

Definition bridge_is_tree_edge_in : St * TR -> Prop :=
  fun '(s, tr) => forall v, v ∈ s.(visited) -> tr |= have (ts↑ (In (v)) (fun s => bridge_is_tree_edge root g s)).

Definition bridge_is_tree_edge_in_except (u: V): St * TR -> Prop :=
  fun '(s, tr) => forall v, v ∈ s.(visited) -> v <> u -> tr |= have (ts↑ (In (v)) (fun s => bridge_is_tree_edge root g s)).

Lemma Tarjan_track_in_bridge_is_tree_edge_in (u: V):
  Hoare (fun '(s, tr) => bridge_is_tree_edge_in_except u (s, tr) /\ bridge_is_tree_edge root g s)
        (track (In u))
        (fun _ => bridge_is_tree_edge_in).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
  intros v Hv.
  destruct (classic (v = u)); subst.
  * rewrite app_have_atom; right; apply singleton_have_atom; split; tauto.
  * rewrite app_have_atom; left; apply H; auto.
Qed.

Lemma Tarjan_preloop_bridge_is_tree_edge_in (u: V):
  Hoare (fun '(s, tr) => bridge_is_tree_edge_in (s, tr))
        ((↑ (preloop u))%ghost)
        (fun _ => bridge_is_tree_edge_in).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? []]; subst; auto.
Qed.

Lemma Tarjan_set_tree_bridge_is_tree_edge_in (u v: V) (e: E):
  Hoare (fun '(s, tr) => bridge_is_tree_edge_in (s, tr))
        ((↑ (set_tree u v e))%ghost)
        (fun _ => bridge_is_tree_edge_in_except v).
Proof.
  unfold set_tree; intro_state_pair.
  hoare_auto_G; my_destruct H.
  simpl; intros _ ? [? []]; subst; auto.
  intros w Hw Hneq.
  destruct Hw; auto; sets_unfold in H0; congruence.
Qed.

Lemma Tarjan_post_rec_bridge_is_tree_edge_in (u v: V) (e: E):
  Hoare (fun '(s, tr) => bridge_is_tree_edge_in (s, tr))
        ((↑ (post_rec e u v))%ghost)
        (fun _ => bridge_is_tree_edge_in).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ s0 [? [? [|[]]]]; subst; auto.
Qed.

Lemma Tarjan_track_out_bridge_is_tree_edge_in (u: V):
  Hoare (fun '(s, tr) => bridge_is_tree_edge_in (s, tr))
        (track (Out u))
        (fun _ => bridge_is_tree_edge_in).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
  intros v Hv.
  apply app_have_atom; left; auto.
Qed.

Theorem Tarjan_bridge_is_tree_edge_in_inv (u: V):
  Hoare (fun '(s, tr) => bridge_is_tree_edge_in_except u (s, tr) /\ bridge_is_tree_edge root g s)
        (tarjan' g u)
        (fun _ => bridge_is_tree_edge_in).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_fs_auto V. {
    forall_n 2.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_edge_inv' E @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_bridge_is_tree_edge_inv' unit @tarjan'. }
  clear u; intros W IHa IH u _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  eapply Hoare_bind. {
    hoare_conj_n 1.
    * hoare_cons_pre Tarjan_track_in_bridge_is_tree_edge_in.
    * hoare_cons_pre Tarjan_track_in_bridge_is_tree_edge'; intros (s, tr); tauto.
  }simpl; intros _.
  hoare_bind'' Tarjan_track_out_bridge_is_tree_edge_in.
  eapply Hoare_bind. {
    hoare_conj_n 1.
    * hoare_cons_pre Tarjan_preloop_bridge_is_tree_edge_in.
    * hoare_cons_pre Tarjan_preloop_bridge_is_tree_edge'; intros (s, tr); tauto.
  }simpl; intros _.
  unfold loop_body', forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    eapply Hoare_bind. 2:{
      intros; hoare_conj2_n 1.
      * apply Tarjan_post_rec_bridge_is_tree_edge_in.
      * apply Tarjan_post_rec_bridge_is_tree_edge'.
    }
    eapply Hoare_bind. {
      hoare_conj_n 1.
      * hoare_cons_pre Tarjan_set_tree_bridge_is_tree_edge_in; intros; subst; tauto.
      * hoare_cons_pre Tarjan_set_tree_bridge_is_tree_edge'; intros; subst; tauto. 
    } simpl; intros _.
    hoare_conj_n 1.
    * hoare_cons_pre IH; intros (s0, tr); intros; split; tauto.
    * eapply Hoare_conseq_post. 2: {
      hoare_conj_n 1.
      * hoare_cons_pre (IHa0 _ a); intros (s0, tr); tauto.
      * hoare_cons_pre IHa1; intros (s0, tr); intros; tauto.
      } simpl; intros _ (s0, tr); tauto.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ s1 [? [? [|[]]]]; subst; auto.
  - tauto.
Qed.

Theorem Tarjan_bridge_is_tree_edge_in: 
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => bridge_is_tree_edge_in).
Proof.
  hoare_cons_pre Tarjan_bridge_is_tree_edge_in_inv.
  intros; destruct s; destruct H; subst; split; auto.
  * intros; congruence.
  * apply bridge_is_tree_edge_init_state.
Qed.

(*-------------------------------- about visit order and interval --------------------------------*)

Definition before_visited : St * TR -> Prop :=
  fun '(_, tr) =>
  forall x y, (tr |= before_eq (t↑(In (x))) (t↑(In (y)))) ->
  (tr |= have (tsAtom (In(x)) (fun s => ~ y ∈ s.(visited) /\ x ∈ s.(visited)))). 
  
Lemma before_visited_stateless: 
  forall s1 s2 tr, 
    before_visited (s1, tr) -> before_visited (s2, tr).
Proof. auto. Qed.

Lemma Tarjan_track_in_before_visited (u: V): 
  Hoare (fun '(s, tr) => u ∈ s.(visited) /\ (~ (tr |= have (t↑(In u)))) /\ before_visited (s, tr) /\ visited_in_except_u u (s, tr) /\ visited_persist_within u (s, tr))
        (track (In u))
        (fun _ '(s, tr) => before_visited (s, tr) /\ visited_in (s, tr) /\ visited_persist (s, tr)).
Proof.
  eapply Hoare_conseq_post. 
  2: 
  {
    apply Hoare_conj.
    apply Hoare_conj.
    * hoare_cons_pre Tarjan_track_in_visited_in. 
      intros (s, tr); intros [_ [_ [_ [H _]]]].
      intros u0 Hu0; apply H; auto.
    * hoare_cons_pre Tarjan_track_in_visited_persist. 
      intros (s, tr); intros [_ [_ [_ [_ H]]]]; auto.
    * instantiate (1:= fun _ '(s, tr) => before_visited (s, tr)).
      intro_state_pair.
      hoare_cons_post Hoare_track_s.
      intros; subst; intros.
      my_destruct H.
      destruct (classic (u = x)); subst.
      {
        destruct (classic (l |= have (t↑ (In(y))))).
        * exfalso. 
          eapply latter_occur_not_before_eq; eauto.  
        * destruct (classic (y = x)). 
          ** subst; exfalso. 
             eapply not_before_eq_refl; eauto.
          ** apply app_last_have_atom. 
             repeat split; auto. 
      }
      {
        apply app_have_atom; left; auto.
        eapply before_eq_elim in H0; eauto.
        unfold not; intros Hin.
        rewrite singleton_have_atom in Hin.
        inversion Hin; subst; auto. 
      }
  }
  simpl; intros; auto.
  destruct s; split; apply H.
Qed.

Lemma Tarjan_track_out_before_visited (u: V): 
  Hoare (fun '(s, tr) => before_visited (s, tr) /\ visited_in (s, tr) /\ visited_persist (s, tr))
        (track (Out u))
        (fun _ '(s, tr) => before_visited (s, tr) /\ visited_in (s, tr) /\ visited_persist (s, tr)).
Proof.
  eapply Hoare_conseq_post. 
  2: 
  {
    apply Hoare_conj.
    apply Hoare_conj.
    * hoare_cons_pre Tarjan_track_out_visited_in. 
      intros (s, tr); intros [_ []]; auto.
    * hoare_cons_pre Tarjan_track_out_visited_persist. 
      intros (s, tr); intros [_ []]; auto.
    * instantiate (1:= fun _ '(s, tr) => before_visited (s, tr)).
      intro_state_pair.
      hoare_cons_post Hoare_track_s.
      intros; subst; intros.
      my_destruct H.
      apply app_have_atom; left.
      apply H.
      eapply before_eq_elim; eauto.
      unfold not; intros Hout. 
      rewrite singleton_have_atom in Hout. 
      inversion Hout.
      }
  simpl; intros; auto.
  destruct s; split; apply H.
Qed.

Lemma Tarjan_preloop_before_visited (u: V): 
  Hoare (fun '(s, tr) => before_visited (s, tr) /\ visited_in (s, tr) /\ visited_persist (s, tr))
        ((↑ (preloop u))%ghost)
        (fun _ '(s, tr) => before_visited (s, tr) /\ visited_in (s, tr) /\ visited_persist (s, tr)).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? []]; subst; auto.
Qed.

Lemma Tarjan_set_tree_before_visited (u v: V) (e: E): 
  Hoare (fun '(s, tr) => ~ (v ∈ s.(visited)) /\ before_visited (s, tr) /\ visited_in (s, tr) /\ visited_persist (s, tr))
        ((↑ (set_tree u v e))%ghost)
        (fun _ '(s, tr) => v ∈ s.(visited) /\ (~ (tr |= have (t↑(In v)))) /\ before_visited (s, tr) /\ visited_in_except_u v (s, tr) /\ visited_persist_within v (s, tr)).
Proof.
  eapply Hoare_conseq_post. 
  2: {
    do 2 apply Hoare_conj.
    apply Hoare_conj.
    * hoare_cons_pre Tarjan_set_tree_visited_in. 
      intros (s, tr); intros [_ [_ [H _]]]; auto.
    * hoare_cons_pre Tarjan_set_tree_visited_persist.
      intros (s, tr); intros [_ [_ [_ H]]]; auto.
    * instantiate (1:= fun _ '(s, tr) => before_visited (s, tr)).
      unfold set_tree, set_tree'.
      intro_state_pair.
      my_destruct H.
      hoare_auto_G.
      simpl; intros _ ? [? [? []]]; subst; auto.
    * instantiate (1:= fun _ '(s, tr) => ~ (tr |= have (t↑(In v)))).
      unfold set_tree, set_tree'.
      intro_state_pair.
      my_destruct H.
      hoare_auto_G.
      simpl; intros _ ? [? [? []]]; subst; auto.
    * instantiate (1:= fun _ '(s, tr) => v ∈ s.(visited)).
      unfold set_tree, set_tree'.
      intro_state_pair.
      my_destruct H.
      hoare_auto_G.
      simpl; intros _ ? [? []]; subst.
      right; reflexivity.
  }
  simpl; intros; auto.
  destruct s; repeat split; auto; apply H.
Qed.

Lemma Tarjan_before_visited_inv (u: V): 
  Hoare (fun '(s, tr) => u ∈ s.(visited) /\ (~ (tr |= have (t↑(In u)))) /\ before_visited (s, tr) /\ visited_in_except_u u (s, tr) /\ visited_persist_within u (s, tr))
        (tarjan' g u)
        (fun _ '(s, tr) => before_visited (s, tr) /\ visited_in (s, tr) /\ visited_persist (s, tr)).
Proof.  
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_auto V; intros W IH a. 
  unfold trace_call_f, tarjan_f'.
  hoare_bind Tarjan_track_in_before_visited.
  hoare_bind'' Tarjan_track_out_before_visited.
  hoare_bind Tarjan_preloop_before_visited.
  clear a0.
  unfold loop_body', forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s. hoare_bind'' IH0.
    my_destruct H.
    unfold for_branch1'. 
    eapply Hoare_bind; [|intros; eapply Hoare_bind].
    2: {apply IH. }
    {
      hoare_cons_pre Tarjan_set_tree_before_visited.
      intros; subst; repeat split; auto.
    }
    { 
      simpl; intros _.
      unfold post_rec; unfold_op. 
      intro_state_pair; hoare_auto_G. 
      simpl; intros _ TR [s2 [? [|[]]]]; subst; auto.
    } 
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ s1 [? [? [|[]]]]; subst; auto. 
Qed.

Theorem Tarjan_before_visited: 
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
  (tarjan' g root)
  (fun _ '(s, tr) => before_visited (s, tr) /\ visited_in (s, tr) /\ visited_persist (s, tr)).
Proof.
  hoare_cons_pre Tarjan_before_visited_inv.
  intros; destruct s; destruct H; subst; repeat split.
  * unfold not; intros; exfalso; eapply not_nil_have; eauto.
  * intros; exfalso. 
    eapply not_nil_before_eq; eauto.
  * intros; congruence.
  * intros; exfalso; eapply not_nil_have; eauto.
Qed.


Definition in_then_out : St * TR -> Prop :=
  fun '(s, tr) => forall v, tr |= before_weak (t↑ (In (v))) (t↑ (Out (v))).


Lemma Tarjan_tag_in_persist (u v: V):
  Hoare (fun '(s, tr) => tr |= have (t↑ (In (v))))
        (tarjan' g u)
        (fun _ '(s, tr) => tr |= have (t↑ (In (v)))).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_auto V; clear u; intros W IH u.
  unfold trace_call_f, tarjan_f'.
  eapply Hoare_bind with (Q := fun _ '(s, tr) => tr |= have (t↑ (In (v)))).
  { intro_state_pair; hoare_cons_post Hoare_track_s. 
    intros; subst; apply app_have_atom; left; auto. }
  simpl; intros _.
  eapply Hoare_bind with (Q := fun _ '(s, tr) => tr |= have (t↑ (In (v)))).
  2: { intros _; intro_state_pair; hoare_cons_post Hoare_track_s. 
    intros; subst; apply app_have_atom; left; auto. }
  eapply Hoare_bind with (Q := fun _ '(s, tr) => tr |= have (t↑ (In (v)))).
  { intro_state_pair; unfold preloop; unfold_op; hoare_auto_G.
    intros _ ? [? []]; subst; auto. }
  simpl; intros _.
  unfold loop_body'; unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    eapply Hoare_bind with (Q := fun _ '(s, tr) => tr |= have (t↑ (In (v)))).
    { intro_state_pair; unfold post_rec; unfold_op; hoare_auto_G.
      intros _ ? [? []]; inversion H3; subst; auto. }
    simpl; intros _.
    eapply Hoare_bind with (Q := fun _ '(s, tr) => tr |= have (t↑ (In (v)))).
    { apply IH. }
    { simpl; intros _; unfold post_rec; unfold_op; 
      intro_state_pair; hoare_auto_G; intros _ ? [? []]; inversion H3; subst; auto. }
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ ? [?[]]; subst; auto. 
Qed.


Lemma Tarjan_track_in_in_then_out (u: V): 
  Hoare (in_then_out)
        (track (In u))
        (fun _ '(s, tr) => in_then_out (s, tr) /\ (tr |= have (t↑ (In (u))))).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; split. 
  * intros v.
    pose proof H v.
    eapply before_weak_app; eauto.
    unfold not; intros; apply singleton_have_atom in H1; inversion H1. 
  * apply app_have_atom; right; 
    apply singleton_have_atom; reflexivity.
Qed.

Lemma Tarjan_preloop_in_then_out (u: V): 
  Hoare (fun '(s, tr) => in_then_out (s, tr) /\ (tr |= have (t↑ (In (u)))))
        ((↑ (preloop u))%ghost)
        (fun _ '(s, tr) => in_then_out (s, tr) /\ (tr |= have (t↑ (In (u))))).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? []]; subst; auto.
Qed.

Lemma Tarjan_set_tree_in_then_out (u v: V) (e: E): 
  Hoare (fun '(s, tr) => in_then_out (s, tr) /\ (tr |= have (t↑ (In (u)))))
        ((↑ (set_tree u v e))%ghost)
        (fun _ '(s, tr) => in_then_out (s, tr) /\ (tr |= have (t↑ (In (u))))).
Proof.
  unfold set_tree, set_tree'.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ ? [? []]; subst; auto.
Qed.

Lemma Tarjan_post_rec_in_then_out (u v: V) (e: E): 
  Hoare (fun '(s, tr) => in_then_out (s, tr) /\ (tr |= have (t↑ (In (u)))))
        ((↑ (post_rec e u v))%ghost)
        (fun _ '(s, tr) => in_then_out (s, tr) /\ (tr |= have (t↑ (In (u))))).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ ? [? []]; subst; auto.
Qed.

Lemma Tarjan_track_out_in_then_out (u: V): 
  Hoare (fun '(s, tr) => in_then_out (s, tr) /\ (tr |= have (t↑ (In (u)))))
        (track (Out u))
        (fun _ '(s, tr) => in_then_out (s, tr)).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v.
  destruct (classic (u = v)); subst.
  * destruct H. pose proof H v. destruct H1. 
    ** left; apply before_app; auto. 
    ** left; apply before_app.
       apply have_not_before; auto.
  * destruct H. 
    apply before_weak_app; auto. 
    unfold not; intros Hu; apply singleton_have_atom in Hu; inversion Hu; auto.
Qed.

Theorem Tarjan_in_then_out_inv (u: V): 
  Hoare (fun '(s, tr) => in_then_out (s, tr))
        (tarjan' g u)
        (fun _ '(s, tr) => in_then_out (s, tr)).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_fs_auto V.
  { forall_n 1. hoare_fix_nolv_ls_auto @Tarjan_tag_in_persist V @tarjan'. }
  clear u; intros W IHa IH u _.
  unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  hoare_bind Tarjan_track_in_in_then_out.
  hoare_bind'' Tarjan_track_out_in_then_out.
  hoare_bind Tarjan_preloop_in_then_out; simpl.
  clear a a0.
  unfold loop_body'; unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_in_then_out.
    eapply Hoare_bind.
    { hoare_cons_pre Tarjan_set_tree_in_then_out. intros; subst; auto. }
    simpl; intros _.
    (* eapply Hoare_conj'. *)
    eapply Hoare_conseq_post. 
    2: { apply Hoare_conj. 
    * hoare_cons_pre IH; intros (s0, tr); tauto.
    * hoare_cons_pre (IHa0 _ u); intros (s0, tr); tauto. }
    simpl; intros _ (s0, tr); tauto.
    (* hoare_conj有时会mismatch，因为只描述tr的函数类型不匹配 *)
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ ? [?[]]; subst; auto.
Qed.

Theorem Tarjan_in_then_out (u: V): 
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ '(s, tr) => in_then_out (s, tr)).
Proof.
  hoare_cons_pre Tarjan_in_then_out_inv.
  intros (s, tr); intros []; subst; simpl.
  intros; right; apply not_nil_have.
Qed.



Lemma Tarjan_track_in_in_out_interval (u v: V) (Hneq: u <> v):
  Hoare ((fun '(s, tr) => ~ (tr |= have (t↑ (Out (u)))) /\ u ∈ s.(visited)): St * TR -> Prop)
        (track (In v))
        (fun _ '(s, tr) => ~ (tr |= have (t↑ (Out (u)))) /\ u ∈ s.(visited)).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; unfold not; split; intros. 
  * apply app_have_atom in H0; destruct H0; try tauto.
  rewrite singleton_have_atom in H0; inversion H0; subst; tauto.
  * tauto.
Qed.

Lemma Tarjan_preloop_in_out_interval (u v: V):
  Hoare ((fun '(s, tr) => ~ (tr |= have (t↑ (Out (u)))) /\ u ∈ s.(visited)): St * TR -> Prop)
        ((↑ (@preloop V E _ _ v))%ghost)
        (fun _ '(s, tr) => ~ (tr |= have (t↑ (Out (u)))) /\ u ∈ s.(visited)).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  intros _ s0 [? []]; subst; split; tauto.
Qed. 

Lemma Tarjan_set_tree_in_out_interval (u v x y: V) (e: E):
  Hoare ((fun '(s, tr) => ~ (tr |= have (t↑ (Out (u)))) /\ u ∈ s.(visited)): St * TR -> Prop)
        ((↑ (set_tree x y e))%ghost)
        (fun _ '(s, tr) => ~ (tr |= have (t↑ (Out (u)))) /\ u ∈ s.(visited)).
Proof.
  unfold set_tree, set_tree'; intro_state_pair.
  hoare_auto_G.
  intros _ ? [?[]]; subst; split; try tauto.
  left; tauto.
Qed.

Lemma Tarjan_post_rec_in_out_interval (u v x y: V) (e: E):
  Hoare ((fun '(s, tr) => ~ (tr |= have (t↑ (Out (u)))) /\ u ∈ s.(visited)): St * TR -> Prop)
        ((↑ (post_rec e x y))%ghost)
        (fun _ '(s, tr) => ~ (tr |= have (t↑ (Out (u)))) /\ u ∈ s.(visited) ).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  intros _ s0 [? [? [|[]]]]; subst; split; tauto.
Qed.

Lemma Tarjan_track_out_in_out_interval (u v: V) (Hneq: u <> v):
  Hoare ((fun '(s, tr) => ~ (tr |= have (t↑ (Out (u))))): St * TR -> Prop)
        (track (Out v))
        (fun _ '(s, tr) => ~ (tr |= have (t↑ (Out (u))))).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; unfold not; intros. 
  apply app_have_atom in H0; destruct H0; try tauto.
  rewrite singleton_have_atom in H0; inversion H0; subst; tauto.
Qed.



Theorem Tarjan_in_out_interval_inv (v u: V):
  Hoare ((fun '(s, tr) => ~ (tr |= have (t↑ (Out (u)))) /\ u ∈ s.(visited) /\ u <> v): St * TR -> Prop)
        (tarjan' g v)
        (fun _ '(s, tr) => ~ (tr |= have (t↑ (Out (u))))).
Proof.
  unfold tarjan'. unfold trace_call. 
  hoare_fix_nolv_fs_auto V.
  { forall_n 1. hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv' V @tarjan'. }
  clear v; intros W IHa IH v _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'. 
  intro_state; destruct s0. 
  assert (u <> v) as Hneq by tauto.
  eapply Hoare_bind. { 
    hoare_cons_pre (Tarjan_track_in_in_out_interval u); intros; subst; tauto. }
  simpl; intros _.
  hoare_bind'' Tarjan_track_out_in_out_interval.
  hoare_bind Tarjan_preloop_in_out_interval.
  simpl; clear a.
  unfold loop_body', forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H2; subst.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    hoare_bind'' (Tarjan_post_rec_in_out_interval u v).
    eapply Hoare_bind. 2: {
      intros. eapply Hoare_conseq_post.
      2: { apply Hoare_conj. 
      apply (IH _ tt).
      hoare_cons_pre (IHa0 a0 u); intros (s2, tr); subst; tauto.
      }
      simpl; intros _ (s2, tr); subst; split; try tauto. }
    hoare_cons (Tarjan_set_tree_in_out_interval u v); intros; subst; try tauto.
    destruct s1; split_r 2; try tauto. 
    unfold not; intros; subst; tauto.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ ? [?[? [|[]]]]; subst; auto.
  - tauto.
  - tauto.
Qed.

Definition visited_in_once: St * TR -> Prop :=
  fun '(s, tr) => forall v, v ∈ s.(visited) -> tr |= have_once (t↑(In v)).

Definition visited_in_once_except_u (u: V): St * TR -> Prop :=
  fun '(s, tr) => forall v, v <> u -> v ∈ s.(visited) -> tr |= have_once (t↑(In v)).

Lemma Tarjan_track_in_visited_in_once (u: V):
  Hoare (fun '(s, tr) => visited_in_once_except_u u (s, tr) /\ ~ (tr |= have (t↑ (In u))))
        (track (In u))
        (fun _ => visited_in_once).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  destruct (classic (v = u)); subst.
  * apply have_once_app_r. 
    apply singleton_have_once; reflexivity.
    tauto.
  * apply have_once_app_l.
    apply H; auto.
    unfold not; intros con. rewrite singleton_have_atom in con.
    inversion con; congruence.
Qed.

Lemma Tarjan_preloop_visited_in_once (u: V):
  Hoare (fun '(s, tr) => visited_in_once (s, tr))
        ((↑ (preloop u))%ghost)
        (fun _ => visited_in_once).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  intros _ s0 [? []]; subst; auto.
Qed.

Lemma Tarjan_set_tree_visited_in_once (u v: V) (e: E):
  Hoare (fun '(s, tr) => visited_in_once (s, tr) /\ visited_persist (s, tr) /\ ~ v ∈ s.(visited))
        ((↑ (set_tree u v e))%ghost)
        (fun _ '(s, tr) => visited_in_once_except_u v (s, tr) /\ ~ (tr |= have (t↑ (In v)))).
Proof.
  unfold set_tree, set_tree'; intro_state_pair.
  hoare_auto_G; my_destruct H.
  intros _ ? [? []]; subst; split; auto. 
  intros w Hneq Hw; destruct Hw; auto.
  sets_unfold in H0; congruence.
Qed.

Lemma Tarjan_post_rec_visited_in_once (u v: V) (e: E):
  Hoare (fun '(s, tr) => visited_in_once (s, tr))
        ((↑ (post_rec e u v))%ghost)
        (fun _ => visited_in_once).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  intros _ s0 [? [? [|[]]]]; subst; auto.
Qed.

Lemma Tarjan_track_out_visited_in_once (u: V):
  Hoare (fun '(s, tr) => visited_in_once (s, tr))
        (track (Out u))
        (fun _ => visited_in_once).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  apply have_once_app_l.
  apply H; auto.
  unfold not; intros con. rewrite singleton_have_atom in con.
  inversion con; congruence.
Qed.

Theorem Tarjan_visited_in_once_inv (u: V):
  Hoare (fun '(s, tr) => visited_in_once_except_u u (s, tr) /\ ~ (tr |= have (t↑ (In u))) /\ visited_persist_within u (s, tr))
        (tarjan' g u)
        (fun _ => visited_in_once).
Proof.
  unfold tarjan', trace_call.
  hoare_fix_nolv_fs_auto V.
  { forall_n 1. hoare_fix_nolv_ls_auto @Tarjan_visited_persist_inv unit @tarjan'. }
  clear u; intros W IHa IH u _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  eapply Hoare_bind. {
    hoare_conj_n 1.
    * hoare_cons_pre (Tarjan_track_in_visited_in_once u); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_track_in_visited_persist u); intros (s, tr); intros HH; apply HH.
  } simpl; intros _.
  hoare_bind'' Tarjan_track_out_visited_in_once.
  eapply Hoare_bind. {
    hoare_conj_n 1.
    * hoare_cons_pre (Tarjan_preloop_visited_in_once u); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_preloop_visited_persist u); intros (s, tr); intros HH; apply HH.
  } simpl; intros _.
  unfold loop_body', forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    eapply Hoare_bind. 2:{
      intros. apply Hoare_conj2.
      * apply Tarjan_post_rec_visited_in_once.
      * apply Tarjan_post_rec_visited_persist.
    }
    eapply Hoare_bind. 2:{
      intros; hoare_conj_n 1.
      * apply (IH _ tt).
      * hoare_cons_pre (IHa0 _ tt); intros (s0, tr); intros HH; apply HH.
    }
    eapply Hoare_conseq_post. 2: {
      hoare_conj_n 1.
      * hoare_cons_pre Tarjan_set_tree_visited_in_once; intros; subst; tauto.
      * hoare_cons_pre Tarjan_set_tree_visited_persist; intros; subst; tauto.
    }
    simpl; intros _ (s0, tr); subst; split; try tauto.
    - hoare_auto_s.
      hoare_bind'' IH0.
      unfold for_branch2; unfold_op.
      hoare_auto_G.
      simpl; intros _ ? [?[? [|[]]]]; subst; auto.
    - tauto.
Qed.

Theorem Tarjan_visited_in_once: 
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => visited_in_once).
Proof.
  hoare_cons_pre Tarjan_visited_in_once_inv.
  intros (s, tr); intros []; subst; split_r 3; simpl; intros.
  * congruence.
  * apply not_nil_have.
  * exfalso; eapply not_nil_have; eauto.
  * reflexivity.
Qed.

Definition visited_out_once: St * TR -> Prop :=
  fun '(s, tr) => forall v, v ∈ s.(visited) -> tr |= have_once (t↑(Out v)). 

Theorem Tarjan_visited_out_once (u: V):
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g u)
        (fun _ => visited_out_once).
Admitted.

(*-------------------------------- about step_aux --------------------------------*) 


Definition step_aux_out: 
  V -> V -> V -> E -> (St * TR) -> Prop := 
  fun u x y e '(s, tr) =>
  step_aux (T s) e x y -> 
  tr |= have (ts↑ (Out (x)) (fun s => step_aux (T s) e x y)). 

Definition step_aux_out_except:
  V -> V -> V -> E -> (St * TR) -> Prop := 
  fun u x y e '(s, tr) =>
  u <> x ->
  step_aux (T s) e x y -> 
  tr |= have (ts↑ (Out (x)) (fun s => step_aux (T s) e x y)). 

Lemma step_aux_out_implies_except (u x y: V) (e: E) (s: (St * TR)): 
  step_aux_out u x y e s ->
  step_aux_out_except u x y e s.
Proof.
  intros. destruct s. simpl. 
  intros Hneq Hstep.
  apply H; auto.
Qed.

Lemma Tarjan_track_in_keep_step_aux_out_inv (u x y: V) (e: E):
  Hoare (step_aux_out u x y e)
        (track (In u))
        (fun _ => step_aux_out u x y e).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst.
  intros Hstep.
  rewrite app_have_atom; left; auto.
Qed.

Lemma Tarjan_preloop_keep_step_aux_out_inv (u x y: V) (e: E):
  Hoare (step_aux_out u x y e)
        ((↑ (preloop u))%ghost)
        (fun _ => step_aux_out_except u x y e).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  simpl; intros _ ? [s1 []].
  apply step_aux_out_implies_except; auto.
  same_tree_from_state_subst s1 s H1.
  subst s0; simpl; rewrite Hs; auto.
Qed.

Lemma Tarjan_set_tree_keep_step_aux_out_inv (u v: V) (x y: V) (e e': E):
  Hoare (fun '(s, tr) => step_aux_out_except u x y e (s, tr) /\ (tree_sub_conj_P root g u s /\ ~ v ∈ s.(visited)))
        (↑ (set_tree u v e'))%ghost
        (fun _ => step_aux_out_except u x y e).
Proof.
  unfold set_tree; intro_state_pair.
  hoare_auto_G; my_destruct H.
  simpl; intros _ ? [? []]; subst; auto.
  intros Hneq Hstep.
  assert (step_aux (T s) e x y) as Hstep'. {
    eapply tree_keep_step_aux'; try apply Hstep; auto; try apply H0.
    unfold not; intros; subst; auto. 
    destruct Hstep; simpl in *.
    unfold t_set in vp; equiv_dec_refl v; auto.
  }
  apply H; auto. 
Qed.

Lemma Tarjan_W_keep_step_aux_out_inv (u v x y: V) (e: E) (W: V -> program (St * list (Tag * St)) unit):
  (forall v, 
  Hoare (fun '(s, tr) => step_aux_out v x y e (s, tr) /\ tree_sub_conj_P root g v s)
        (W v)
        (fun _ => step_aux_out v x y e))
  ->
  Hoare (fun '(s, tr) => step_aux_out_except u x y e (s, tr) /\ tree_sub_conj_P root g v s)
        (W v)
        (fun _ => step_aux_out_except u x y e).
Proof.
  intros.
  unfold step_aux_out_except.
  intro_state_pair.
  eapply Hoare_conseq_post with (Q2:= fun _ s => u <> x -> step_aux (T (fst s)) e x y -> (snd s) |= have (ts↑ (Out (x)) (fun s => step_aux (T s) e x y))).
  { intros _ (s0, tr); intros; eauto. }
  apply hoare_bind_forall; intros Hxnu.
  hoare_cons (H v). { intros (s0, tr) Heq; inversion Heq; subst; eauto; tauto. }
  intros _ (s0, tr); simpl; intros; eauto.
Qed.

Lemma Tarjan_post_rec_keep_step_aux_out_inv (u v: V) (x y: V) (e e': E):
  Hoare (step_aux_out_except u x y e)
        (↑ (post_rec e' u v))%ghost
        (fun _ => step_aux_out_except u x y e).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ ? [s1 [? []]];
  [|destruct H1]; subst; auto.
Qed.

Lemma Tarjan_track_out_keep_step_aux_out_inv (u x y: V) (e: E):
  Hoare (step_aux_out_except u x y e)
        (track (Out u))
        (fun _ => step_aux_out u x y e).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst.
  intros Hstep.
  destruct (classic (u = x)); subst.
  * rewrite app_have_atom; right; 
    apply singleton_have_atom; split; auto.
  * rewrite app_have_atom; left; auto.
Qed.

Lemma Tarjan_keep_step_aux_out_inv (u x y: V) (e: E):
  Hoare (fun '(s, tr) => step_aux_out u x y e (s, tr) /\ tree_sub_conj_P root g u s)
        (tarjan' g u)
        (fun _ => step_aux_out u x y e).
Proof.
  unfold tarjan', trace_call.
  hoare_fix_nolv_fs_auto V.
  { forall_n 2. 
  * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_sub_conj' unit @tarjan'.
  * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv' V @tarjan'.
  }
  clear u; intros W IHa IH u _; unfold_Forall IHa.
  unfold tarjan_f', trace_call_f.
  eapply Hoare_bind. {
    hoare_conj_n 1.
    * hoare_cons_pre (Tarjan_track_in_keep_step_aux_out_inv u x y e); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_track_in_keep_tree_sub_conj'); intros (s, tr); tauto.
  } simpl; intros _.
  hoare_bind'' Tarjan_track_out_keep_step_aux_out_inv. 
  eapply Hoare_bind. {
    hoare_conj_n 1.
    * hoare_cons_pre (Tarjan_preloop_keep_step_aux_out_inv u x y e); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_preloop_keep_tree_sub_conj'); intros (s, tr); tauto.
  } simpl; intros _.
  unfold loop_body', forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s; rename a0 into v; rename a into e'.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    eapply Hoare_bind. 2:{ 
      intros. apply Hoare_conj2.
      * apply Tarjan_post_rec_keep_step_aux_out_inv.
      * apply Tarjan_post_rec_keep_tree_sub_conj'. }
    eapply Hoare_bind. {
      hoare_conj_n 1.
      * hoare_cons_pre (Tarjan_set_tree_keep_step_aux_out_inv u v x y e); intros; subst; tauto.
      * hoare_cons_pre (Tarjan_set_tree_keep_tree_sub_conj'); intros; subst; tauto. }
    simpl; intros _.
    apply Hoare_conj.
    * hoare_cons_pre Tarjan_W_keep_step_aux_out_inv. 
      intros (s0, tr); intros; split; try tauto; eapply tree_easy; apply H3.
      intros; apply (IH _ tt).
    * eapply Hoare_conseq_post. 2: {
      hoare_conj_n 1.
      * hoare_cons_pre IHa0; intros (s0, tr); intros; tauto.
      * hoare_cons_pre (IHa1 _ u); intros (s0, tr); intros; tauto.
      }
      { simpl; intros _ (s0, tr) ?; eapply tree_easy; apply H3. }
  - hoare_auto_s; rename a0 into v; rename a into e'.
    hoare_bind'' IH0.
    unfold for_branch2.
    unfold_op; hoare_auto_G.
    simpl; intros _ ? [? [? [|[]]]]; subst; auto.
  - tauto.
Qed.
  

Theorem Tarjan_step_aux_out (x y: V) (e: E): 
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => step_aux_out root x y e).
Proof.
  hoare_cons_pre Tarjan_keep_step_aux_out_inv.
  intros (s, tr); intros []; subst; simpl; split.
  * intros; exfalso; destruct H; simpl in *; inversion ve.
  * apply tree_subgraph_init_state; auto.
Qed.

(* Theorem Tarjan_step_aux_out'': 
 Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ s' => forall x y e, step_aux_out root x y e s').
Proof.
  apply hoare_bind_forall; intros x.
  apply hoare_bind_forall; intros y.
  apply hoare_bind_forall; intros e.
  apply Tarjan_step_aux_out.
Qed. *)


(*-------------------------------- about bridge --------------------------------*)

Definition bridge_out: V -> V -> E -> St * TR -> Prop :=
  fun x y e '(s, tr) => 
  step_aux (T s) e x y ->
  List.In e s.(bridges) ->
  tr |= have (ts↑ (Out (x)) (fun s => List.In e s.(bridges))).

Definition bridge_out_except (u: V): V -> V -> E -> St * TR -> Prop :=
  fun x y e '(s, tr) => 
  x <> u ->
  step_aux (T s) e x y ->
  List.In e s.(bridges) ->
  tr |= have (ts↑ (Out (x)) (fun s => List.In e s.(bridges))).

Definition bridge_persist: St * TR -> Prop :=
  fun '(s, tr) => forall e, 
  tr |= have (s↑ (fun s => List.In e s.(bridges))) -> 
  List.In e s.(bridges).


Lemma Tarjan_track_in_bridge_out (u: V) (x y: V) (e: E):
  Hoare (fun '(s, tr) => bridge_out x y e (s, tr))
        (track (In u))
        (fun _ '(s, tr) => bridge_out x y e (s, tr)).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s; my_destruct H.
  intros; subst; auto; intros Hstep Hbridge.
  rewrite app_have_atom; left; eapply H; eauto.
Qed.

Lemma Tarjan_preloop_bridge_out (u: V) (x y: V) (e: E):
  Hoare (fun '(s, tr) => bridge_out x y e (s, tr))
        ((↑ (preloop u))%ghost)
        (fun _ '(s, tr) => bridge_out_except u x y e (s, tr)).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G; my_destruct H.
  simpl; intros _ s0 [? []]; subst; simpl; auto.
Qed.

Lemma Tarjan_set_tree_bridge_out (u v: V)(x y: V)(e e': E):
  Hoare (fun '(s, tr) => bridge_out_except u x y e (s, tr) /\ tree_sub_conj_P root g u s)
        ((↑ (set_tree u v e'))%ghost)
        (fun _ => bridge_out_except u x y e).
Proof.
  unfold set_tree; intro_state_pair.
  hoare_auto_G; my_destruct H.
  simpl; intros _ ? [? []]; subst; auto.
  intros Hxnu Hstep Hbridge.
  apply H; auto.
  eapply tree_keep_step_aux'; eauto.
  apply H0. 
  unfold not; intros; subst v.
  destruct Hstep; simpl in *.
  unfold t_set in vp; equiv_dec_refl y; auto.
Qed.

Lemma Tarjan_W_bridge_out (u v: V) (x y: V) (e: E) (W: V -> program (St * list (Tag * St)) unit): 
  (forall v, 
  Hoare (fun '(s, tr) => bridge_out x y e (s, tr) /\ tree_sub_conj_P root g v s)
        (W v)
        (fun _ => bridge_out x y e))
  ->
  Hoare (fun '(s, tr) => bridge_out_except u x y e (s, tr) /\ tree_sub_conj_P root g v s)
        (W v)
        (fun _ => bridge_out_except u x y e).
Proof.
  intros.
  unfold bridge_out in H.
  unfold bridge_out_except. 
  intro_state_pair.
  eapply Hoare_conseq_post with (Q2:= fun _ s => 
  x <> u -> step_aux (T (fst s)) e x y -> List.In e (fst s).(bridges) -> (snd s) |= have (ts↑ (Out (x)) (fun s => List.In e s.(bridges)))).
  { intros _ (s0, tr); intros; eapply H1; eauto. }
  apply hoare_bind_forall; intros Hxnu. 
  hoare_cons (H v).
  { intros (s0, tr) Heq; inversion Heq; subst; split; eapply H0; eauto. }
  intros _ (s0, tr); simpl; intros; tauto.
Qed.

Lemma Tarjan_post_rec_bridge_out (u v: V) (x y: V) (e a: E):
  Hoare (fun s' => bridge_out_except u x y e s' /\ (let '(s, _) := s' in tree_sub_conj_P root g u s) /\ (let '(s, _) := s' in step_aux (T s) a u v))
        ((↑ (post_rec a u v))%ghost)
        (fun _ s' => bridge_out_except u x y e s').
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G; my_destruct H.
  simpl; intros _ s0 [s1 [? [|[]]]]; simpl; auto.
  2: {subst; auto. }
  same_tree_from_state_subst s s1 H3.
  rewrite H2; simpl; intros; apply H; auto. 
  rewrite Hs; auto.
  rewrite H3 in H6; simpl in H6.
  destruct H6; [subst a|]; auto.
  exfalso. rewrite <- Hs in H5.
  eapply step_aux_unique in H1; eauto.
  destruct H1; subst; auto.
  destruct H0; auto.
Qed.


Lemma Tarjan_track_out_bridge_out (u: V) (x y: V) (e: E):
  Hoare (bridge_out_except u x y e)
        (track (Out u))
        (fun _ => bridge_out x y e).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros Hstep' Hbridge.
  destruct (classic (x = u)); subst.
  2: rewrite app_have_atom; left; eapply H; eauto. 
  rewrite app_have_atom; right; apply singleton_have_atom; split; auto.
Qed.

Lemma Tarjan_bridge_out_inv (u: V) (x y: V) (e: E):
  Hoare (fun '(s, tr) => bridge_out x y e (s, tr) /\ tree_sub_conj_P root g u s)
        (tarjan' g u)
        (fun _ => bridge_out x y e).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_fs_auto V. {
    forall_n 3.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_sub_conj' unit @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv' V @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_step_aux_outv'_prod (V * V * E)%type @tarjan'.
  }
  clear u; simpl; intros W IHa IH u _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  eapply Hoare_bind.
  { apply Hoare_conj.
  * hoare_cons_pre (Tarjan_track_in_bridge_out _ x y e); intros (s0, tr); intros; subst; simpl; tauto.
  * hoare_cons_pre Tarjan_track_in_keep_tree_sub_conj'; intros (s0, tr); intros; subst; simpl; tauto. }
  simpl; intros _.
  hoare_bind'' Tarjan_track_out_bridge_out.
  eapply Hoare_bind.
  {apply Hoare_conj. 
  * hoare_cons_pre (Tarjan_preloop_bridge_out _ x y e). 
  * hoare_cons_pre (Tarjan_preloop_keep_tree_sub_conj' _). }
  simpl; intros _.
  unfold loop_body', forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s; rename a0 into v; rename a into e'.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    eapply Hoare_bind. 2:{ 
      intros; apply Hoare_conj.
      * hoare_cons_post (Tarjan_post_rec_bridge_out _ _ x y e).
      * hoare_cons_pre Tarjan_post_rec_keep_tree_sub_conj'; intros (s0, tr); tauto. }
    eapply Hoare_bind. {
      hoare_conj_n 3.
      * hoare_cons_pre (Tarjan_set_tree_bridge_out u v x y e); intros; subst; tauto.
      * hoare_cons_pre (Tarjan_set_tree_keep_tree_sub_conj'); intros; subst; tauto.
      * instantiate (1:= fun _ '(s, tr) => step_aux (T s) e' u v). 
        unfold set_tree; hoare_auto_G; intros _ ? [? []]; subst.
        eapply step_easy; apply H.
      * instantiate (1:= fun _ '(s, tr) => v ∈ s.(visited)).
        unfold set_tree; hoare_auto_G; intros _ ? [? []]; subst; right; reflexivity.
    }
    simpl; intros _.
    hoare_conj_n 2. { 
      hoare_cons_pre Tarjan_W_bridge_out.
      * intros (s0, tr); intros; split; try tauto.
      * intros; hoare_cons_pre IH; intros (s0, tr); intros; split; try tauto. 
    }
    { eapply Hoare_conseq_post. 2: {
      hoare_conj_n 1.
      * hoare_cons_pre IHa0; intros (s0, tr); intros; tauto.
      * hoare_cons_pre (IHa1 _ u); intros (s0, tr); intros; tauto.
      }
      { simpl; intros _ (s0, tr); intros; eapply tree_easy; apply H3. }
    }
    { hoare_cons_pre (IHa2 _ (u, v, e')). }
  - hoare_auto_s; rename a0 into v; rename a into e'.
    hoare_bind'' IH0.
    unfold for_branch2.
    unfold_op; hoare_auto_G.
    simpl; intros _ ? [? [? [|[]]]]; subst; auto.
  - tauto.
Qed.

Theorem Tarjan_bridge_out (x y: V) (e: E):
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => bridge_out x y e).
Proof.
  hoare_cons_pre Tarjan_bridge_out_inv.
  intros (s, tr); intros []; subst; split; simpl.
  * intros; exfalso; auto.
  * apply tree_subgraph_init_state; auto.
Qed.


Lemma Tarjan_track_in_bridge_persist (u: V):
  Hoare (fun '(s, tr) => bridge_persist (s, tr))
        (track (In u))
        (fun _ '(s, tr) => bridge_persist (s, tr)).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto; intros.
  rewrite app_have_atom in H0; destruct H0 as [|Hu]; auto.
  rewrite singleton_have_atom in Hu; auto.
Qed.

Lemma Tarjan_preloop_bridge_persist (u: V):
  Hoare (fun '(s, tr) => bridge_persist (s, tr))
        ((↑ (preloop u))%ghost)
        (fun _ '(s, tr) => bridge_persist (s, tr)).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  intros _ s0 [? []]; subst; auto.
Qed.

Lemma Tarjan_set_tree_bridge_persist (u v: V) (e: E):
  Hoare (fun '(s, tr) => bridge_persist (s, tr))
        ((↑ (set_tree u v e))%ghost)
        (fun _ => bridge_persist).
Proof.
  unfold set_tree; intro_state_pair.
  hoare_auto_G.
  intros _ ? [? []]; subst; auto.
Qed.

Lemma Tarjan_post_rec_bridge_persist (u v: V) (e: E):
  Hoare (fun '(s, tr) => bridge_persist (s, tr))
        ((↑ (post_rec e u v))%ghost)
        (fun _ => bridge_persist).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  intros _ s0 [? [? [|[]]]]; subst; simpl; auto.
Qed.

Lemma Tarjan_track_out_bridge_persist (u: V):
  Hoare (bridge_persist)
        (track (Out u))
        (fun _ => bridge_persist).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto; intros e ?.
  rewrite app_have_atom in H0; destruct H0 as [|Hu]; auto.
  rewrite singleton_have_atom in Hu; auto.
Qed.

Lemma Tarjan_bridge_persist_inv (u: V):
  Hoare (fun '(s, tr) => bridge_persist (s, tr))
        (tarjan' g u)
        (fun _ => bridge_persist).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_auto V.
  clear u; intros W IH u; simpl.
  unfold trace_call_f, tarjan_f'.
  hoare_bind Tarjan_track_in_bridge_persist.
  hoare_bind'' Tarjan_track_out_bridge_persist.
  hoare_bind Tarjan_preloop_bridge_persist.
  simpl; clear a a0.
  unfold loop_body', forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    hoare_bind'' Tarjan_post_rec_bridge_persist. 
    hoare_bind'' IH.
    hoare_cons_pre Tarjan_set_tree_bridge_persist.
    intros; subst; tauto.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2.
    unfold_op; hoare_auto_G.
    simpl; intros _ ? [? [? [|[]]]]; subst; auto.
Qed.
    
Theorem Tarjan_bridge_persist (u: V):
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => bridge_persist).
Proof.
  hoare_cons_pre Tarjan_bridge_persist_inv.
  intros (s, tr); intros []; subst; simpl.
  intros; eapply not_nil_have; eauto.
Qed.

Definition bridge_in: St * TR -> Prop :=
  fun '(s, tr) =>
  forall x y e, step_aux (T s) e x y ->
  tr |= have (ts↑ (In (x)) (fun s => ~ List.In e s.(bridges))).


Lemma Tarjan_track_in_bridge_in (u: V):
  Hoare (fun '(s, tr) => bridge_in (s, tr))
        (track (In u))
        (fun _ '(s, tr) => bridge_in (s, tr) /\ (tr |= have (t↑ (In (u))))).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s; my_destruct H.
  intros _ (s0, tr) Heq; inversion Heq; subst; split; intros.
  * rewrite app_have_atom; left; eapply H; eauto.
  * rewrite app_have_atom; right; apply singleton_have_atom; split; auto.
Qed.

Lemma Tarjan_preloop_bridge_in (u: V):
  Hoare (fun '(s, tr) => bridge_in (s, tr) /\ (tr |= have (t↑ (In (u)))))
        ((↑ (preloop u))%ghost)
        (fun _ '(s, tr) => bridge_in (s, tr) /\ (tr |= have (t↑ (In (u))))).
Proof. 
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G; my_destruct H.
  simpl; intros _ s0 [? []]; subst; auto.
Qed.


Lemma Tarjan_set_tree_bridge_in (u v: V) (e : E) (Hstep': step_aux g e u v):
  Hoare (fun '(s, tr) => bridge_in (s, tr) /\ (tr |= have (t↑ (In (u)))) /\ (bridge_persist (s, tr)) /\ (tree_sub_conj_P root g u s /\ ~ v ∈ s.(visited)) /\ bridge_is_tree_edge root g s)
        ((↑ (set_tree u v e))%ghost)
        (fun _ '(s, tr) => bridge_in (s, tr) /\ (tr |= have (t↑ (In (u))))).
Proof.
  unfold set_tree; intro_state_pair.
  hoare_auto_G; my_destruct H.
  intros _ ? [? []]; subst; split;auto.
  intros x y e' Hstep.
  destruct (classic (y = v)); [subst y|]; auto.
  * assert (x = u) by (destruct Hstep; simpl in *; unfold t_set in vp; equiv_dec_refl v; auto); subst x. 
    assert (e' = e) by (destruct Hstep; simpl in *; unfold t_set in ve; equiv_dec_refl v; inversion ve; subst; auto); subst e'.
    eapply have_tsatom_exclude_middle in H0; destruct H0; [exfalso|apply H0].
    apply have_tsatom_satom in H0.
    apply H1 in H0; apply H3 in H0.
    eapply sub_reverse with (g2:=g) in H0; eauto; try apply H2.
    2: apply Rootedtree_noemptyedge.
    2: apply OriginalGraph_stepuniqueundirected.
    destruct H0 as [[]|[]]; auto.
  * apply (H x y). eapply tree_keep_step_aux'; eauto; apply H2.
Qed.

Lemma Tarjan_post_rec_bridge_in (u v: V) (e : E):
  Hoare (fun '(s, tr) => bridge_in (s, tr) /\ (tr |= have (t↑ (In (u)))))
        (↑ (post_rec e u v))%ghost
        (fun _ '(s, tr) => bridge_in (s, tr) /\ (tr |= have (t↑ (In (u))))).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ ? [? [? [|[]]]]; subst; auto.
Qed.


Lemma Tarjan_track_out_bridge_in (u: V):
  Hoare (fun '(s, tr) => bridge_in (s, tr))
        (track (Out u))
        (fun _ '(s, tr) => bridge_in (s, tr)).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros _ (s0, tr) Heq; inversion Heq; subst; auto.
  intros x y e Hstep.
  rewrite app_have_atom; left; eapply H; eauto.
Qed. 

(* 标准的conjuction证明格式 *)
Lemma Tarjan_bridge_in_inv (u: V):
  Hoare (fun '(s, tr) => bridge_in (s, tr) /\ bridge_persist (s, tr) /\ tree_sub_conj_P root g u s /\ bridge_is_tree_edge root g s)
        (tarjan' g u)
        (fun _ '(s, tr) => bridge_in (s, tr)).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_fs_auto V. {
    forall_n 6.
    * hoare_fix_nolv_ls_auto @Tarjan_bridge_persist_inv unit @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_sub_conj' unit @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_bridge_is_tree_edge_inv' unit @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_tag_in_persist V @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv' V @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_edge_inv' E @tarjan'.
  }
  clear u; intros W IHa IH u _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  eapply Hoare_bind. {
    hoare_conj_n 3.
    * hoare_cons_pre (Tarjan_track_in_bridge_in u); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_track_in_bridge_persist u); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_track_in_keep_tree_sub_conj' u); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_track_in_bridge_is_tree_edge' u); intros (s, tr); tauto.
  } simpl; intros _. 
  hoare_bind'' Tarjan_track_out_bridge_in.
  eapply Hoare_bind. {
    hoare_conj_n 3.
    * hoare_cons_pre (Tarjan_preloop_bridge_in u); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_preloop_bridge_persist u); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_preloop_keep_tree_sub_conj' u); intros (s, tr); tauto.
    * hoare_cons_pre (Tarjan_preloop_bridge_is_tree_edge' u); intros (s, tr); tauto.
  } simpl; intros _. 
  unfold loop_body', forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; auto].
  hoare_auto_G; destruct H1; subst.
  - rename a0 into v; rename a into e.
    hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    rewrite <- bind_assoc.
    eapply Hoare_bind. 2: {
      intros; hoare_conj2_n 3.
      * apply (Tarjan_post_rec_bridge_in).
      * apply (Tarjan_post_rec_bridge_persist).
      * apply (Tarjan_post_rec_keep_tree_sub_conj').
      * apply (Tarjan_post_rec_bridge_is_tree_edge').
    } 
    eapply Hoare_bind. {
      my_destruct H.
      hoare_conj_n 3.
      * hoare_cons_pre Tarjan_set_tree_bridge_in; intros (s0, tr) Heq; 
        inversion Heq; subst; split_r 4; auto.
      * hoare_cons_pre Tarjan_set_tree_bridge_persist; intros (s0, tr) Heq; 
        inversion Heq; subst; auto.
      * hoare_cons_pre Tarjan_set_tree_keep_tree_sub_conj'; intros (s0, tr) Heq; 
        inversion Heq; subst; auto.
      * hoare_cons_pre Tarjan_set_tree_bridge_is_tree_edge'; intros (s0, tr) Heq; 
        inversion Heq; subst; auto.
    } { simpl; intros _. 
      hoare_conj_n 3.
      * eapply Hoare_conseq_post. 2: { 
          hoare_conj_n 1.
          * hoare_cons_pre IH; intros (s0, tr); tauto.
          * hoare_cons_pre (IHa3 _ u); intros (s0, tr); tauto.
        } intros _ (s0, tr); tauto.
      * hoare_cons_pre (IHa0 _ tt).
      * eapply Hoare_conseq_post. 2: { 
          hoare_conj_n 1.
          * hoare_cons_pre (IHa1 _ tt); intros (s0, tr); tauto.
          * hoare_cons_pre (IHa4 _ u); intros (s0, tr); tauto.
          } intros _ (s0, tr); intros []; eapply tree_easy; eauto.
      * eapply Hoare_conseq_post. 2: { hoare_conj_n 1.
          * hoare_cons_pre (IHa2 _ tt); intros (s0, tr); tauto.
          * hoare_cons_pre (IHa5 _ e); intros (s0, tr); tauto.
          } simpl; intros _ (s0, tr); tauto.
        }
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ ? [? [? [|[]]]]; subst; auto.
  - tauto.
Qed.

Theorem Tarjan_bridge_in (u: V):
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => bridge_in).
Proof.
  hoare_cons_pre Tarjan_bridge_in_inv.
  intros (s, tr); intros []; subst; simpl; split_r 3.
  * intros; destruct H; simpl in *; inversion ve.
  * intros; exfalso; eapply not_nil_have; eauto.
  * intros; apply tree_subgraph_init_state; auto.
  * intros e Hein; inversion Hein.
Qed.


(*-------------------------------- about dfn --------------------------------*)

Definition dfn_persist : St * TR -> Prop :=
  fun '(s, tr) => forall u sn, 
  tr |= have (ts↑ (Out u)(fun s => s = sn)) -> 
  s.(dfn) u = sn.(dfn) u. 

Lemma Tarjan_track_in_dfn_persist (u: V): 
  Hoare (fun '(s, tr) => (dfn_persist (s, tr) /\ ~ (tr |= have (t↑ (In (u))))))
        (track (In u))
        (fun _ '(s, tr) => dfn_persist (s, tr) /\ (tr |= have_once (t↑ (In (u)))) /\ (tr |= (t↑ (In (u))))).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  my_destruct H.
  intros; subst; split_r 2. 
  * intros v sn Hdfnu.
    apply app_have_atom in Hdfnu; destruct Hdfnu as [|Hu]; auto.
    rewrite singleton_have_atom in Hu; inversion Hu; subst; auto.
  * apply have_once_app_r; auto.
    apply singleton_have_once; reflexivity.
  * apply app_last_atom; reflexivity.
Qed.

Lemma Tarjan_preloop_dfn_persist (u: V): 
  Hoare (fun '(s, tr) => dfn_persist (s, tr) /\ (tr |= have_once(t↑ (In (u)))) /\ (tr |= (t↑ (In (u)))) /\ in_then_out (s, tr))
        ((↑ (preloop u))%ghost)
        (fun _ => dfn_persist).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  my_destruct H.
  simpl; intros _ s0 [? []]; subst; auto. 
  intros v sn ?; simpl. 
  destruct (classic (u = v)); [subst v|].
  * exfalso. apply have_tsatom_tatom in H3. 
    eapply have_once_before_have_implies_have_both in H3; eauto.
    eapply trace_in_out_inversion; eauto.
  * equiv_dec_simpl u v; apply H; auto.
Qed.

Lemma Tarjan_set_tree_dfn_persist (u v: V) (e: E): 
  Hoare (dfn_persist)
        ((↑ (set_tree u v e))%ghost)
        (fun _ => dfn_persist).
Proof.
  unfold set_tree, set_tree'.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ ? [?[]]; subst; simpl; intros; auto.
Qed.

Lemma Tarjan_post_rec_dfn_persist (u v: V) (e: E): 
  Hoare (dfn_persist)
        ((↑ (post_rec e u v))%ghost)
        (fun _ => dfn_persist).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ s0 [? [? [|[]]]]; subst; auto.
Qed.

Lemma Tarjan_track_out_dfn_persist (u: V): 
  Hoare (dfn_persist)
        (track (Out u))
        (fun _ => dfn_persist).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v dfnu Hdfnu.
  apply app_have_atom in Hdfnu; destruct Hdfnu; auto.
  rewrite singleton_have_atom in H0; inversion H0; subst; auto.
Qed.

(* 标准的conjuction证明格式 *)
Lemma Tarjan_dfn_persist_inv (u: V): 
  Hoare (fun '(s, tr) => dfn_persist (s, tr) /\ ~ (tr |= have (t↑ (In (u)))) /\ in_then_out (s, tr) /\ visited_persist_within u (s, tr))
        (tarjan' g u)
        (fun _ => dfn_persist).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_fs_auto V.
  { forall_n 3. 
    * hoare_fix_nolv_ls_auto @Tarjan_in_then_out_inv unit @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_tag_in_persist V @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_visited_persist_inv unit @tarjan'.
  }
  clear u; intros W IHa IH u _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  eapply Hoare_bind. {
    hoare_conj_n 2.
    * hoare_cons_pre Tarjan_track_in_dfn_persist; intros (s0, tr); subst; tauto.
    * hoare_cons_pre Tarjan_track_in_in_then_out; intros (s0, tr); subst; tauto.
    * hoare_cons_pre Tarjan_track_in_visited_persist; 
      intros (s0, tr); intros [_ [_ [_ H]]]; apply H.
  }
  simpl; intros _.
  eapply Hoare_bind. 2: { intros. hoare_cons_post Tarjan_track_out_dfn_persist. }
  eapply Hoare_bind. {
    hoare_conj_n 2.
    * hoare_cons_pre Tarjan_preloop_dfn_persist; intros (s0, tr); subst; tauto.
    * hoare_cons_pre Tarjan_preloop_in_then_out; intros (s0, tr); subst; tauto.
    * hoare_cons_pre Tarjan_preloop_visited_persist; 
      intros (s0, tr); intros [_ [_ [_ H]]]; apply H.
  }
  intros; simpl; clear a.
  unfold loop_body'; unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; tauto]; rename a into e.
  hoare_auto_G; destruct H1; subst; rename a into v.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    eapply Hoare_bind. {
      hoare_conj_n 3.
      * hoare_cons_pre Tarjan_set_tree_dfn_persist; intros; subst; tauto.
      * hoare_cons_pre Tarjan_set_tree_in_then_out; intros; subst; tauto.
      * hoare_cons_pre Tarjan_set_tree_visited_persist; intros; subst; tauto.
      * instantiate (1:= fun _ '(s, tr) => ~ (tr |= have (t↑ (In (v))))).
        eapply Hoare_conseq_pre with (P2:= fun '(s, tr) => ~ (tr |= have (t↑ (In (v))))).
        ** intros; subst; unfold not; intros; apply H1; apply H; auto.
        ** unfold set_tree, set_tree'; intro_state_pair; hoare_auto_G; 
           intros _ ? [?[]]; subst; tauto.
    }
    intros; simpl; clear a.
    eapply Hoare_bind. 2: {
      intros. apply Hoare_conj2; [|apply Hoare_conj2].
      * apply Tarjan_post_rec_dfn_persist.
      * apply Tarjan_post_rec_in_then_out.
      * apply Tarjan_post_rec_visited_persist.
    }
    hoare_conj_n 2.
    * hoare_cons_pre IH; intros (s0, tr); tauto.
    * eapply Hoare_conseq_post. 2: { apply Hoare_conj.  
      * hoare_cons_pre (IHa0 v tt); intros (s0, tr); tauto.
      * hoare_cons_pre (IHa1 v u); intros (s0, tr); tauto. }
      simpl; intros _ (s0, tr); tauto.
    * hoare_cons_pre IHa2.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ ? [?[? [|[]]]]; subst; auto.
Qed.

Theorem Tarjan_dfn_persist (u: V):
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => dfn_persist).
Proof.
  hoare_cons_pre Tarjan_dfn_persist_inv.
  intros; destruct s; destruct H; subst; simpl; split_r 4.
  * intros; exfalso; eapply not_nil_have; eauto.
  * eapply not_nil_have; eauto.
  * intros; right; apply not_nil_have; eauto. 
  * intros; exfalso; eapply not_nil_have; eauto.
  * reflexivity.
Qed.



(*-------------------------------- about low --------------------------------*)




Definition low_persist : St * TR -> Prop :=
  fun '(s, tr) => forall u sn, 
  tr |= have (ts↑ (Out u)(fun s => s = sn)) -> 
  s.(low) u = sn.(low) u. 

Lemma Tarjan_track_in_low_persist (u: V): 
  Hoare (fun '(s, tr) => (low_persist (s, tr) /\ ~ (tr |= have (t↑ (In (u))))))
        (track (In u))
        (fun _ '(s, tr) => low_persist (s, tr) /\ (tr |= have_once (t↑ (In (u)))) /\ (tr |= (t↑ (In (u))))).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  my_destruct H.
  intros; subst; split_r 2. 
  * intros v sn Hdfnu.
    apply app_have_atom in Hdfnu; destruct Hdfnu as [|Hu]; auto.
    rewrite singleton_have_atom in Hu; inversion Hu; subst; auto.
  * apply have_once_app_r; auto.
    apply singleton_have_once; reflexivity.
  * apply app_last_atom; reflexivity.
Qed.

Lemma Tarjan_preloop_low_persist (u: V): 
  Hoare (fun '(s, tr) => low_persist (s, tr) /\ (tr |= have_once(t↑ (In (u)))) /\ (tr |= (t↑ (In (u)))) /\ in_then_out (s, tr))
        ((↑ (preloop u))%ghost)
        (fun _ '(s, tr) => low_persist (s, tr) /\ ~ (tr |= have (t↑ (Out (u))))).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  my_destruct H.
  simpl; intros _ s0 [? []]; subst; split; auto. 
  * intros v sn ?; simpl. 
    destruct (classic (u = v)); [subst v|].
    ** exfalso. apply have_tsatom_tatom in H3. 
       eapply have_once_before_have_implies_have_both in H3; eauto.
       eapply trace_in_out_inversion; eauto.
    ** equiv_dec_simpl u v; apply H; auto.
  * unfold not; intros. 
    eapply have_once_before_have_implies_have_both in H3; eauto.
    eapply trace_in_out_inversion; eauto.
Qed.

Lemma Tarjan_set_tree_low_persist (u v: V) (e: E): 
  Hoare (fun '(s, tr) => low_persist (s, tr) /\ ~ (tr |= have (t↑ (Out (u)))))
        ((↑ (set_tree u v e))%ghost)
        (fun _ '(s, tr) => low_persist (s, tr) /\ ~ (tr |= have (t↑ (Out (u))))).
Proof.
  unfold set_tree, set_tree'.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ ? [?[]]; subst; simpl; intros; auto.
Qed.

Lemma Tarjan_post_rec_low_persist (u v: V) (e: E): 
  Hoare (fun '(s, tr) => low_persist (s, tr) /\ ~ (tr |= have (t↑ (Out (u)))))
        ((↑ (post_rec e u v))%ghost)
        (fun _ '(s, tr) => low_persist (s, tr) /\ ~ (tr |= have (t↑ (Out (u))))).
Proof.
  unfold post_rec; unfold_op.
  intro_state_pair.
  hoare_auto_G.
  simpl; intros _ s0 [? [? [|[]]]]; subst; auto.
  * split; try tauto. 
    intros w; intros; simpl. 
    destruct (classic (u = w)); [subst w|].
    ** exfalso. apply have_tsatom_tatom in H0; tauto.
    ** equiv_dec_simpl u w; apply H; auto. 
  * split; try tauto. 
    intros w; intros; simpl.
    destruct (classic (u = w)); [subst w|].
    ** exfalso. apply have_tsatom_tatom in H0; tauto.
    ** equiv_dec_simpl u w; apply H; auto. 
Qed.

Lemma Tarjan_track_out_low_persist (u: V): 
  Hoare (low_persist)
        (track (Out u))
        (fun _ => low_persist).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v dfnu Hdfnu.
  apply app_have_atom in Hdfnu; destruct Hdfnu; auto.
  rewrite singleton_have_atom in H0; inversion H0; subst; auto.
Qed.

(* 标准的conjuction证明格式 *)
Lemma Tarjan_low_persist_inv (u: V): 
  Hoare (fun '(s, tr) => low_persist (s, tr) /\ ~ (tr |= have (t↑ (In (u)))) /\ in_then_out (s, tr) /\ visited_persist_within u (s, tr) /\ u ∈ s.(visited))
        (tarjan' g u)
        (fun _ => low_persist).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_fs_auto V.
  { forall_n 5. 
    * hoare_fix_nolv_ls_auto @Tarjan_in_then_out_inv unit @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_tag_in_persist V @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_visited_persist_inv unit @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_in_out_interval_inv V @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv' V @tarjan'.
  }
  clear u; intros W IHa IH u _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  eapply Hoare_bind. {
    hoare_conj_n 3.
    * hoare_cons_pre Tarjan_track_in_low_persist; intros (s0, tr); subst; tauto.
    * hoare_cons_pre Tarjan_track_in_in_then_out; intros (s0, tr); subst; tauto.
    * hoare_cons_pre Tarjan_track_in_visited_persist; 
      intros (s0, tr); intros [_ [_ [_ H]]]; apply H.
    * instantiate (1:= fun _ '(s, tr) => u ∈ s.(visited)).
      intro_state_pair; hoare_cons_post Hoare_track_s.
      intros _ (s0, tr) ?; inversion H0; subst; tauto.
  }
  simpl; intros _.
  eapply Hoare_bind. 2: { intros. hoare_cons_post Tarjan_track_out_low_persist. }
  eapply Hoare_bind. {
    hoare_conj_n 3.
    * hoare_cons_pre Tarjan_preloop_low_persist; intros (s0, tr); subst; tauto.
    * hoare_cons_pre Tarjan_preloop_in_then_out; intros (s0, tr); subst; tauto.
    * hoare_cons_pre Tarjan_preloop_visited_persist; 
      intros (s0, tr); intros [_ [_ [_ H]]]; apply H.
    * instantiate (1:= fun _ '(s, tr) => u ∈ s.(visited)).
      intro_state_pair; unfold preloop; unfold_op; hoare_auto_G. 
      intros _ s0 [? []]; subst; tauto.
  }
  intros; simpl; clear a.
  unfold loop_body'; unfold forset.
  hoare_fix_nolv_auto (E -> Prop).
  intros W0 IH0 eset; simpl.
  unfold forset_f, forset_body.
  intro_state_pair.
  hoare_auto_G; hoare_auto_s; [|subst; tauto]; rename a into e.
  hoare_auto_G; destruct H1; subst; rename a into v.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch1'.
    assert (u <> v) as Hneq by (unfold not; intros; subst; tauto).
    eapply Hoare_bind. {
      hoare_conj_n 5.
      * hoare_cons_pre Tarjan_set_tree_low_persist; intros; subst; tauto.
      * hoare_cons_pre Tarjan_set_tree_in_then_out; intros; subst; tauto.
      * hoare_cons_pre Tarjan_set_tree_visited_persist; intros; subst; tauto.
      * instantiate (1:= fun _ '(s, tr) => ~ (tr |= have (t↑ (In (v))))).
        eapply Hoare_conseq_pre with (P2:= fun '(s, tr) => ~ (tr |= have (t↑ (In (v))))).
        ** intros; subst; unfold not; intros; apply H1; apply H; auto.
        ** unfold set_tree, set_tree'; intro_state_pair; hoare_auto_G; 
           intros _ ? [?[]]; subst; tauto.
      * instantiate (1:= fun _ '(s, tr) => u ∈ s.(visited)). 
        unfold set_tree, set_tree'; intro_state_pair; hoare_auto_G; 
        intros _ ? [?[]]; subst; left; inversion H3; subst; tauto. 
      * instantiate (1:= fun _ '(s, tr) => v ∈ s.(visited)). 
        intro_state_pair; unfold preloop; unfold_op; hoare_auto_G. 
        intros _ ? [?[]]; subst; right; inversion H3; subst; reflexivity. 
    }
    intros; simpl; clear a.
    eapply Hoare_bind. 
    { hoare_conj_n 3.
    * apply Hoare_conj. 
      ** hoare_cons_pre IH; intros (s0, tr); tauto.
      ** hoare_cons_pre (IHa3 v u); intros (s0, tr); subst; split_r 2; try tauto.
    * apply Hoare_conj.  
      ** hoare_cons_pre (IHa0 v tt); intros (s0, tr); tauto.
      ** hoare_cons_pre (IHa1 v u); intros (s0, tr); tauto.
    * hoare_cons_pre IHa2.
    * hoare_cons_pre (IHa4 _ u).
    }
    * intros. apply Hoare_conj; [|apply Hoare_conj].
      ** eapply Hoare_conseq_post. 2: {
        apply Hoare_conj. 
        hoare_cons_pre Tarjan_post_rec_low_persist; intros (s0, tr); subst; tauto. 
        instantiate (1:= fun _ '(s, tr) => ~ (tr |= have (t↑ (Out (u))))).
        intro_state_pair; unfold post_rec; unfold_op; hoare_auto_G.
        intros _ s1 [? [? [|[]]]]; subst; simpl; tauto.
        } intros _ (s0, tr); subst; tauto.
      ** hoare_cons_pre Tarjan_post_rec_in_then_out; intros (s0, tr); subst; tauto.
      ** apply Hoare_conj. 
         hoare_cons_pre Tarjan_post_rec_visited_persist.
         intro_state_pair. unfold post_rec; unfold_op; hoare_auto_G.
         intros _ s1 [? [? [|[]]]]; subst; simpl; tauto.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros ? (s0, tr) [? [Hxl [|[]]]]; inversion Hxl; subst; simpl; auto.
    split_r 3; try tauto.
    split; try tauto.
    intros. 
    equiv_dec_simpl u u0.
    * exfalso. apply have_tsatom_tatom in H3; tauto.
    * apply H; auto.
Qed.

Theorem Tarjan_low_persist (u: V):
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => low_persist).
Proof.
  hoare_cons_pre Tarjan_low_persist_inv.
  intros; destruct s; destruct H; subst; simpl; split_r 4.
  * intros; exfalso; eapply not_nil_have; eauto.
  * eapply not_nil_have; eauto.
  * intros; right; apply not_nil_have; eauto. 
  * split; [|reflexivity]; intros; exfalso; eapply not_nil_have; eauto.
  * reflexivity.
Qed.







End BASICS'.
