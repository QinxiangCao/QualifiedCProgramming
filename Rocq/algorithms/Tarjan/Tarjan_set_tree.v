
Require Import Coq.Logic.Classical_Prop.
Require Import SetsClass.SetsClass.
From TraceLib Require Import CommonTactics MapLib.
From GraphLib Require Import GraphLib subgraph rootedtree tarjan.
From Algorithms Require Import Tarjan Tarjan_tactics.

Import SetsNotation.
Local Open Scope sets.
Local Open Scope map_scope.

Section SETTREE.


Context {V E: Type}
        (root: V)
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V E)
        {origin_gvalid: OriginalGraph_gvalid g}
        (g_vvalid_root: vvalid g root).

Lemma tree_property_keep (s: St) (u v: V) (e: E): 
  v <> root -> 
  visited s u -> 
  ~ visited s v -> 
  vvalid g v ->
  ~ (exists x, visited s x /\ tedge s x = Some e) ->
  is_rooted_tree (state_to_rootedtree g root s) -> 
  is_rooted_tree (state_to_rootedtree g root (set_tree' u v e s)).
Proof.
  intros Hr Hu Hv Hvg He H.
  destruct H as [].
  Opaque clos_refl_trans. 
  split; auto; unfold set_tree'; simpl in *.
  - equiv_dec_simpl v root.
  - intros v0 [H|H] H0.
    * equiv_dec_simpl v v0. 
    * sets_unfold in H; subst v0.
      exists e. 
      equiv_dec_refl v.
  - intros; unfold t_set in H1.
    equiv_dec_simpl v v1;
    equiv_dec_simpl v v2.
    * exfalso; firstorder.
    * exfalso; firstorder.
    * apply edge_unique; auto.
      ** destruct H; auto.
         exfalso; auto.
      ** destruct H0; auto.
         exfalso; auto.
  - left; auto.
  - intros v0 [H|H].
    * equiv_dec_simpl v v0.
      firstorder.
    * sets_unfold in H; subst v0.
      equiv_dec_refl v.
      left; auto.
  - intros v0 [H|H].
    * specialize (path_exist v0 H).
      induction_n1 path_exist. 
      reflexivity.
      transitivity_n1 root0.
      ** apply IHrt; auto. 
         rewrite <- H0; auto.
      ** clear IHrt.
         equiv_dec_simpl v v0. 
    * sets_unfold in H; subst v0.
      transitivity_n1 u; [|equiv_dec_refl v].
      specialize (path_exist u Hu).
      assert (forall w, clos_refl_trans (fun x y : V => (v !-> w; fa s) y = x) root u); [|auto]. 
      induction_n1 path_exist. 
      reflexivity.
      transitivity_n1 root0.
      ** apply IHrt; auto.
         rewrite <- H; auto.
      ** equiv_dec_simpl v u.
  - intros. 
    specialize (finite_vertices v0).
    destruct H; auto.
    sets_unfold in H; subst v0.
    apply original_finite_vertices; auto.
Qed.

Lemma tree_subgraph_keep (s: St) (u v: V) (e: E) 
  (is_rt: is_rooted_tree (state_to_rootedtree g root s)): 
  step_aux g e u v ->
  subgraph (state_to_rootedtree g root s) g ->
  subgraph (state_to_rootedtree g root (set_tree' u v e s)) g.
Proof.
  intros Hge Hsub.
  unfold subgraph in *.
  intros x y e0 He0.
  destruct He0; simpl in *.
  destruct (classic ( y = v )).
  - subst y.
    unfold t_set in vp, ve;
    equiv_dec_refl v.
    inversion ve.
    subst x e0; auto.
  - destruct vy; [| exfalso; auto].
    assert (visited s x). { destruct vx; auto. 
    sets_unfold in H1; subst x. 
    unfold t_set in vp. equiv_dec_simpl v y.
    rewrite <- vp. destruct is_rt.  
    eapply parent_valid; eauto. } clear vx.
    unfold t_set in vp, ve; destruct (equiv_dec v y).
    ** exfalso; auto.
    ** apply Hsub; split; auto. 
Qed.

Lemma tree_add_edge_keep (s: St) (u v: V) (e e0: E): 
  ~ visited s v ->
  rt_evalid (state_to_rootedtree g root s) e ->
  rt_evalid (state_to_rootedtree g root (set_tree' u v e0 s)) e.
Proof.
  intros H [x []].
  exists x; split; simpl in *.
  * left; auto.
  * equiv_dec_simpl v x.
Qed.

Lemma tree_keep_step (s: St) (x y u v: V) (e: E): 
  ~ visited s v ->
  step (state_to_rootedtree g root s) x y ->
  step (state_to_rootedtree g root (set_tree' u v e s)) x y.
Proof.
  intros Hv Hstep.
  destruct Hstep as [e0 []].
  exists e0; split; simpl in *.
  - left; auto.
  - left; auto.
  - equiv_dec_simpl v y.
  - equiv_dec_simpl v y.
Qed.

Lemma tree_keep_step' (s: St) (x y u v: V) (e: E)
  (is_rt: is_rooted_tree (state_to_rootedtree g root s)): 
  y <> v ->
  step (state_to_rootedtree g root (set_tree' u v e s)) x y ->
  step (state_to_rootedtree g root s) x y.
Proof.
  intros.
  destruct H0 as [e0 []].
  exists e0; split; simpl in *;
  unfold t_set in *; equiv_dec_simpl v y.
  * destruct vx; auto; subst. 
    sets_unfold in H1; subst. 
    destruct vy; try congruence.
    destruct is_rt; simpl in *.
    eapply parent_valid; eauto. 
  * destruct vy; try congruence.
Qed.

Lemma tree_keep_step_aux (s: St) (x y u v: V) (e: E):
  ~ visited s v ->
  step_aux (state_to_rootedtree g root s) e x y ->
  step_aux (state_to_rootedtree g root (set_tree' u v e s)) e x y.
Proof.
  intros Hv Hstep.
  destruct Hstep; split; simpl in *.
  - left; auto.
  - left; auto.
  - equiv_dec_simpl v y.
  - equiv_dec_simpl v y.
Qed.

Lemma tree_keep_step_aux' (s: St) (x y u v: V) (e e0: E)
  (is_rt: is_rooted_tree (state_to_rootedtree g root s)):
  y <> v ->
  step_aux (state_to_rootedtree g root (set_tree' u v e0 s)) e x y -> 
  step_aux (state_to_rootedtree g root s) e x y.
Proof.
  intros.
  destruct H0; split; simpl in *;
  unfold t_set in *; equiv_dec_simpl v y.
  * destruct vx; auto; subst. 
    sets_unfold in H1; subst. 
    destruct vy; try congruence.
    destruct is_rt; simpl in *.
    eapply parent_valid; eauto. 
  * destruct vy; try congruence.
Qed.

Lemma tree_keep_offspring (s: St) (x y u v: V) (e: E): 
  ~ visited s v ->
  offspring (state_to_rootedtree g root s) x y ->
  offspring (state_to_rootedtree g root (set_tree' u v e s)) x y.
Proof.
  intros.
  unfold offspring, reachable in *.
  induction_1n H0.
  reflexivity.
  transitivity_1n x0; auto.
  apply tree_keep_step; auto.
Qed.

Lemma tree_add_edge_trivial (s: St) (u v: V) (e: E): 
  evalid (state_to_rootedtree g root (set_tree' u v e s)) e.
Proof.
  exists v; split; simpl in *.
  - right; reflexivity.
  - unfold t_set; equiv_dec_refl v.
Qed.

Lemma tree_add_vertex_is_leaf (s: St) (u v: V) (e: E)
  (is_rt: is_rooted_tree (state_to_rootedtree g root s)):
  visited s u -> 
  ~ visited s v ->
  isleaf (state_to_rootedtree g root (set_tree' u v e s)) v.
Proof.
  intros Hu Hv.
  unfold isleaf; unfold not; intros.
  destruct H as [e0 []]; simpl in *.
  destruct (classic (v = y)).
  * subst y; unfold t_set in *; equiv_dec_refl v; subst; auto.
  * unfold t_set in *. equiv_dec_simpl v y. 
    destruct vy; auto.
    destruct is_rt; simpl in *.
    apply parent_valid in H1; rewrite vp in H1; auto.
Qed.

Lemma tree_keep_offspring' (s: St) (x y u v: V) (e: E)
  (is_rt: is_rooted_tree (state_to_rootedtree g root s)):
  y <> v ->
  visited s u ->
  ~ visited s v ->
  offspring (state_to_rootedtree g root (set_tree' u v e s)) x y ->
  offspring (state_to_rootedtree g root s) x y.
Proof.
  intros.
  unfold offspring, reachable in *.
  induction_n1 H2.
  reflexivity.
  transitivity_n1 x0; auto.
  * apply IHrt; auto.
    unfold not; intros; subst.
    eapply tree_add_vertex_is_leaf with (e:=e) in is_rt; eauto. 
    eapply is_rt; eauto.
  * eapply tree_keep_step'; eauto.
Qed.

Lemma step_easy (u v: V) (e: E) (s: St):
  u ∈ s.(visited) ->
  step_aux (state_to_rootedtree g root (set_tree' u v e s)) e u v.
Proof.
  intros; split; simpl.
  - left; auto.
  - right; reflexivity.
  - equiv_dec_refl v.
  - equiv_dec_refl v.
Qed.

End SETTREE.
