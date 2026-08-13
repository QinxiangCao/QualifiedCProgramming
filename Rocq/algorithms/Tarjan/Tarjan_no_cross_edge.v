

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From TraceLib Require Import TraceBasic TraceLogic TraceRecur CommonTactics MapLib.
From GraphLib Require Import GraphLib tarjan.
From Algorithms Require Import Tarjan Tarjan_tactics Tarjan_set_tree Tarjan_basics Tarjan_basics_ex.


Import SetsNotation.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope sets.
Local Open Scope map_scope.

Section NOCROSSEDGE.

Context {V E: Type}
        (root: V)
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V E)
        {origin_gvalid: OriginalGraph_gvalid g}
        (g_vvalid_root: vvalid g root).

Notation T := (state_to_rootedtree g root).

Lemma Tarjan_set_tree_basic (u v: V) (e: E):
  Hoare (fun s => u ∈ s.(visited))
        (set_tree u v e)
        (fun _ s => step_aux (T s) e u v).
Proof.
  unfold set_tree; unfold_op.
  intro_state; hoare_auto_s; subst.
  apply step_easy; auto.
Qed.

Lemma Tarjan_set_tree_unvisited (u v w: V) (e: E):
  Hoare (fun s => ~ w ∈ s.(visited) /\ w <> v)
        (set_tree u v e)
        (fun _ s => ~ w ∈ s.(visited)).
Proof.
  unfold set_tree; unfold_op.
  intro_state; hoare_auto_s; subst; simpl. 
  unfold not; intros; destruct H.
  destruct H0; auto.
Qed.

Lemma Tarjan_set_tree_visit_is_offspring (u v: V) (e: E):
  Hoare (fun s => u ∈ s.(visited))
        (set_tree u v e)
        (fun _ s => v ∈ s.(visited) /\ offspring (T s) u v).
Proof.
  hoare_cons_post Tarjan_set_tree_basic.
  intros; split.
  * destruct H; auto.
  * apply step_rt; eexists; eauto.
Qed.

Lemma Tarjan_post_rec_visit_is_offspring (u v w: V) (e: E):
  Hoare (fun s => ((v ∈ s.(visited) /\ ~ w ∈ s.(visited) \/ w ∈ s.(visited) /\ offspring (T s) v w) /\ u ∈ s.(visited)) /\ offspring (T s) u v)
        (post_rec e u v)
        ((fun _ s => (offspring (T s) u v /\ u ∈ s.(visited) /\ ~ w ∈ s.(visited) \/
        offspring (T s) u v /\ w ∈ visited s /\ offspring (T s) v w))).
Proof.
  unfold post_rec; unfold_op.
  intro_state; hoare_auto_s; 
  [|destruct H0]; subst; auto;
  (repeat destruct H; [left|right]; 
  repeat split; auto).
Qed.

Lemma Tarjan_visit_is_offspring (u v: V):
  Hoare (fun s => u ∈ s.(visited) /\ ~ v ∈ s.(visited))
        (tarjan g u)
        (fun _ s => ( u ∈ s.(visited) /\ ~ v ∈ s.(visited)) 
        \/ 
        (v ∈ s.(visited) /\ offspring (state_to_rootedtree g root s) u v)).
Proof.
  unfold tarjan.
  (* first induction *)
  hoare_fix_nolv_fs_auto V.
  { 
    forall_n 2.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv V @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_offspring_inv_prod (V * V)%type @tarjan.
  } 
  intros W IH0 IH1 v0 _; simpl.
  unfold_Forall IH0.
  clear u; rename v0 into u.
  unfold tarjan_f.
  unfold_preloop.
  apply Hoare_conseq_pre with 
    (P2:= fun s => u ∈ s.(visited) /\ ~ v ∈ s.(visited)).
  { intros; subst; auto. }
  unfold loop_body. unfold forset.
  (* second induction *)
  hoare_fix_nolv_fs_auto (E -> Prop).
  { 
    forall_n 2.
    * hoare_fix_nolv_ls_auto @Tarjan_loop_body_keep_visit V @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_loop_body_keep_offspring_prod (V * V)%type @tarjan.
      intros; apply (IHa0 u0 (x, y)).
  }
  intros W0 IH' IH eset _.
  unfold_Forall IH'.
  intro_state.
  unfold forset_f, forset_body.
  hoare_auto_s.
  - unfold for_branch1.
    destruct (classic (v = a0)).
    * subst a0. rewrite bind_assoc.
      eapply Hoare_bind.
      { hoare_cons_pre Tarjan_set_tree_visit_is_offspring; intros; subst; tauto. }
      simpl; intros _.
      rewrite bind_assoc.
      eapply Hoare_bind.
      { apply Hoare_conj2.
        * apply IHa.
        * apply (IHa0 v (u, v)). }
      simpl; intros _. 
      eapply Hoare_bind.
      { apply Hoare_conj.
        * hoare_cons_pre (Tarjan_post_rec_keep_visited _ _ v).
        * hoare_cons_pre (Tarjan_post_rec_keep_offspring root g _ _ u v). }
      simpl; intros _.
      apply Hoare_disj_r.
      apply Hoare_conj.
      { hoare_cons_pre IHa1. }
      { hoare_cons_pre (IHa2 _ (u, v)). }
    * rewrite bind_assoc. 
      eapply Hoare_bind.
      { apply Hoare_conj.
        * hoare_cons_pre Tarjan_set_tree_basic; intros; subst; tauto.
        * hoare_cons_pre (Tarjan_set_tree_unvisited _ _ v); intros; subst; tauto. }
      simpl; intros _. rewrite bind_assoc. 
      eapply Hoare_bind.
      {
        apply Hoare_conj; [apply Hoare_conj|].
        * hoare_cons_pre IH1; intros s [Hstep]; split; [destruct Hstep|]; auto.
        * hoare_cons_pre (IHa _ u); intros s [Hstep]; destruct Hstep; auto. 
        * hoare_cons_pre (IHa0 a0 (u, a0)); intros s [Hstep]; apply step_rt; eexists; eauto. 
      }
      simpl; intros _.
      intro_state.
      eapply Hoare_bind.
      hoare_cons_pre Tarjan_post_rec_visit_is_offspring. 
      { intros; subst; eauto. }
      simpl; intros _.
      apply Hoare_disj.
      { hoare_cons_pre IH. }
      {
        apply Hoare_disj_r. 
        apply Hoare_conj.
        hoare_cons_pre IHa1.
        hoare_cons_pre (IHa2 _ (u, v)).
        intros s [? []].
        etransitivity; eauto.
      }  (*W0*)
  - unfold for_branch2.
    hoare_bind'' IH.
    unfold_op.
    hoare_auto_s.
    subst; auto.
    exact tt.
  - hoare_cons_pre IH. 
    intros; subst; auto.
  - subst. left; apply H0. 
Qed.

Lemma Tarjan_neighbor_is_offspring (u v: V) (Huv: step g u v):
  Hoare (fun s : St => u ∈ s.(visited) /\ ~ v ∈ s.(visited)) 
        (tarjan g u)
        (fun (_ : unit) (s : St) => offspring (state_to_rootedtree g root s) u v).
Proof.
  eapply Hoare_conseq_post.
  2:
  {
    apply Hoare_conj.
    * hoare_cons_pre Tarjan_visit_neighbor.
      intros; exact I.
    * apply Tarjan_visit_is_offspring.
  }
  simpl; intros.
  destruct H as [H []].
  * destruct H0; exfalso; auto.
  * destruct H0; auto.
Qed.

Lemma Tarjan_neighbor''_is_offspring (u v: V):
  Hoare (fun s : St => u ∈ s.(visited) /\ ~ v ∈ s.(visited) /\ step g u v) 
        (tarjan g u)
        (fun (_ : unit) (s : St) => offspring (state_to_rootedtree g root s) u v).
Proof.
  intro_state. hoare_cons_pre Tarjan_neighbor_is_offspring.
  my_destruct H.
  intros; subst; split; auto.
Qed.

Local Open Scope trace_scope.

Lemma Tarjan_neighbor_is_offspring' (x y: V):
  Hoare (fun '(s, tr) => tr = nil)
        (tarjan' g root)
        (fun _ '(s, tr) => trace_in_implies 
        (fun u s => (~ y ∈ s.(visited) /\ u ∈ s.(visited)) /\ step g u y) 
        (fun u s => offspring (state_to_rootedtree g root s) u y) 
        x tr).
Proof.
  intros.
  eapply Hoare_trace_in_implies.
  simpl. intros. 
  hoare_cons_pre Tarjan_neighbor''_is_offspring. 
Qed.

Lemma Tarjan_neighbor_is_offspring'_prod (p: V * V):
  Hoare (fun '(s, tr) => tr = nil)
        (tarjan' g root)
        (fun _ '(s, tr) => trace_in_implies 
        (fun u s => (~ (snd p) ∈ s.(visited) /\ u ∈ s.(visited)) /\ step g u (snd p)) 
        (fun u s => offspring (state_to_rootedtree g root s) u (snd p)) 
        (fst p) tr).
Proof. intros; destruct p; simpl; apply Tarjan_neighbor_is_offspring'. Qed.

Lemma Tarjan_neighbor_is_offspring''_prod:
  Hoare (fun '(s, tr) => tr = nil)
        (tarjan' g root)
        (fun _ '(s, tr) => 
        forall p, trace_in_implies 
        (fun u s => (~ (snd p) ∈ s.(visited) /\ u ∈ s.(visited)) /\ step g u (snd p)) 
        (fun u s => offspring (state_to_rootedtree g root s) u (snd p)) 
        (fst p) tr).
Proof.
  pose proof Tarjan_neighbor_is_offspring'_prod.
  apply hoare_bind_forall in H.
  hoare_cons_post H; intros; destruct s; subst; auto. 
Qed.

Theorem Tarjan_no_cross_edge':
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ '(s, tr) => no_cross_edge g (state_to_rootedtree g root s)).
Proof.
  eapply Hoare_conseq_post.
  2: { 
    do 2 apply Hoare_conj.
    apply Tarjan_before_visited.
    apply Tarjan_visited_reachable'; auto.
    hoare_cons_pre Tarjan_neighbor_is_offspring''_prod; intros (s, tr); tauto.
    apply Tarjan_offspring_persist'; auto. 
  }
  simpl; intros _ (s, tr); intros.
  my_destruct H.
  intros x y Hx Hy Hstep; simpl in Hx, Hy.
  apply H1 in Hx, Hy.
  apply H2 in Hx, Hy.
  eapply before_eq_exclude_middle in Hx as [|[]]; eauto.
  * eapply step_sym' in Hstep. 
    apply H in H5.
    eapply have_global_prop_ts in H5; [|apply Hstep].
    specialize (H0 (y, x)); unfold trace_in_implies in H0; simpl in H0.
    apply H0 in H5.
    apply have_tsatom_satom in H5.
    apply H4 in H5.
    right; auto.
  * apply H in H5.
    eapply have_global_prop_ts in H5; [|apply Hstep].
    specialize (H0 (x, y)); unfold trace_in_implies in H0; simpl in H0.
    apply H0 in H5.
    apply have_tsatom_satom in H5.
    apply H4 in H5.
    left; auto.
  * apply trace_in_inversion in H5; subst.
    left; reflexivity.
Qed.



Theorem Tarjan_no_cross_edge:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => no_cross_edge g (state_to_rootedtree g root s)).
Proof.
  eapply Hoare_fromG.
  apply Gequiv_tarjan.
  apply Tarjan_no_cross_edge'.
  intros; exists nil; auto.
Qed.
    

End NOCROSSEDGE.

