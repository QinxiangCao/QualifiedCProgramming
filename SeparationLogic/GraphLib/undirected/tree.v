Require Import SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From MaxMinLib Require Import MaxMin Interface. 
From ListLib Require Import Base.Inductive General.NoDup General.Length.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.path_basic.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.Syntax.
Require Import GraphLib.reachable.Zweight.
Local Open Scope list.

Import ListNotations.
Import SetsNotation.
Local Open Scope sets.

(* 树的基本定义：包含树的性质和树的判定 *)

Class Tree 
    (G V E: Type) 
    {pg: Graph G V E} 
    {gv: GValid G} 
    (P: Type) 
    {path: Path G V E P}:=
{
  tree: G -> Prop;
  tree_connected: forall g, tree g -> connected g;
  tree_no_curcuit: forall g, tree g -> 
  ~ exists u p, ( p <> nil /\ is_simple_epath g u p u); 
  tree_decide: forall g, connected g -> (~ exists x p, p <> nil /\ is_simple_epath g x p x) -> tree g;
}.

(* 关于AddEdge前后都是树的证明和顶点边列表关系 *)
Section ADDLEAFISTREE.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}. (*存在一个tree的谓词 *)

Context (g1 g2: G)
        {g_valid1: gvalid g1}
        {g_valid2: gvalid g2}.

(* 在该前提下进行的加边操作的基本性质 *)
Context {u v: V}
        {e: E}
        {Hu: vvalid g1 u}
        {Hv: ~ vvalid g1 v}
        {He: ~ evalid g1 e}
        (Hadd: addEdge g1 g2 u v e). 

Lemma addEdge_tree_connected:
  tree g1 -> 
  connected g2.
Proof.
  intros tr1 x y Hx Hy.
  pose proof Hadd as Hadd'.
  destruct Hadd' as [ Hvx _ Hstep_add].
  apply Hvx in Hx as [|[|]]; apply Hvx in Hy as [|[|]]; subst.
  * eapply (sub_reachable g1 g2);
    [eapply addEdge_subgraph; eauto|eapply tree_connected; eauto].
  * eapply (sub_reachable g1 g2); 
    [eapply addEdge_subgraph; eauto|eapply tree_connected; eauto].
  * transitivity u.
    + eapply (sub_reachable g1 g2); 
      [eapply addEdge_subgraph; eauto|eapply tree_connected; eauto].
    + apply step_rt; exists e; apply Hadd; right; auto. 
  * eapply (sub_reachable g1 g2); 
    [eapply addEdge_subgraph; eauto|eapply tree_connected; eauto]. 
  * reflexivity. 
  * transitivity u.
    + eapply (sub_reachable g1 g2); 
      [eapply addEdge_subgraph; eauto|eapply tree_connected; eauto].
    + apply step_rt; exists e; apply Hadd; right; auto. 
  * transitivity u.
    + apply step_rt; exists e; apply Hadd; right; auto. 
    + eapply (sub_reachable g1 g2); 
      [eapply addEdge_subgraph; eauto|eapply tree_connected; eauto].
  * apply step_rt; exists e; apply Hadd; right; auto. 
  * reflexivity. 
  Unshelve. all: auto.
Qed.

Lemma addEdge_tree_no_curcuit:
  tree g1 -> 
  (~ exists x p, p <> nil /\ is_simple_epath g2 x p x).
Proof.
  intros tr1 [x [p [Hpne Hsimple]]].
  destruct (classic (In e p)) as [Hin | Hnotin].
  * eapply addEdge_simple_cycle_not_in_new_edge; eauto.
  * eapply tree_no_curcuit; eauto.
    exists x, p; split; auto.
    destruct Hsimple as [Hpath Hnodup].
    split; auto.
    eapply addEdge_valid_epath_new_to_old; eauto.
Qed. 

Theorem addEdge_tree: 
  tree g1 -> tree g2. 
Proof.
  intros tr1.
  apply tree_decide; auto.
  apply addEdge_tree_connected; auto.
  apply addEdge_tree_no_curcuit; auto.
Qed.

Lemma deleteLeaf_tree_connected:
  tree g2 -> 
  connected g1.
Proof.
  intros tr2 x y Hx Hy.
  assert (Hxv: x <> v) by (intros Heq; subst; contradiction).
  assert (Hyv: y <> v) by (intros Heq; subst; contradiction).
  pose proof Hadd as Hadd'.
  destruct Hadd' as [ Hvertex _ Hstep_add].
  assert (Hx2: vvalid g2 x) by (apply Hvertex; left; auto).
  assert (Hy2: vvalid g2 y) by (apply Hvertex; left; auto).
  destruct (reachable_valid_epath g2 x y (tree_connected g2 tr2 x y Hx2 Hy2))
    as [p Hpath].
  eapply valid_epath_simple_directed in Hpath as [q Hsimple]; eauto.
  assert (Hnotin: ~ In e q) by (eapply addEdge_simple_epath_old_endpoints_not_in_new_edge; try eapply Hsimple; eauto).
  eapply valid_epath_reachable.
  eapply addEdge_valid_epath_new_to_old; eauto.
  apply Hsimple.
Qed.

Lemma deleteLeaf_tree_no_curcuit:
  tree g2 -> 
  (~ exists x p, p <> nil /\ is_simple_epath g1 x p x).
Proof.
  intros tr2 [x [p [Hpne [Hpath Hnodup]]]].
  eapply tree_no_curcuit; eauto.
  exists x, p; split; auto.
  split; auto.
  eapply addEdge_valid_epath_old_to_new; eauto.
Qed.

Theorem deleteLeaf_tree:
  tree g2 -> tree g1.
Proof.
  intros tr2.
  apply tree_decide; auto.
  apply deleteLeaf_tree_connected; auto.
  apply deleteLeaf_tree_no_curcuit; auto.
Qed.

End ADDLEAFISTREE.

(* 树本身的一些性质。可能需要用到树操作来进行证明 *)

Section TREE.
Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {simplegraph: SimpleGraph G V E}. (*这里要求原图是simple graph是一个很明显的疑惑点*)

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}.

Context (g: G)
        {g_valid: gvalid g}
        {g_tree: tree g}.

Lemma no_self_loop: forall u e,
  ~ step_aux g e u u.
Proof.
  intros. intros Hstep. 
  eapply tree_no_curcuit; eauto. 
  exists u, (e :: nil); split; [unfold not; intros; inversion H|split]. 
  * apply valid_epath_single; auto.
  * repeat constructor; auto.
Qed.

Lemma no_multiple_edge: forall u v e1 e2,
  step_aux g e1 u v -> step_aux g e2 u v -> e1 = e2.
Proof.
  intros.
  destruct (classic (e1 = e2)); auto.
  exfalso. 
  eapply tree_no_curcuit; eauto. 
  exists u, (e1 :: e2 :: nil); split; [symmetry; apply nil_cons|split]. 
  * eapply valid_epath_cons; eauto. 
    apply valid_epath_single; auto. 
    apply step_sym; auto. 
  * repeat constructor; auto. 
    simpl; unfold not; intros [|]; auto. 
Qed.


Lemma tree_edge_is_bridge: forall u v e,
  step_aux g e u v ->
  ~ reachable_without g e u v.
Proof.
  intros u v e Hstep Hrw.
  apply reachable_without_valid_epath in Hrw as [p [Hvalid_epath Hnot_in]].
  assert (Hfor : Forall (fun x => x <> e) p) by (rewrite Forall_forall; intros ? ? ?; subst; auto). 
  pose proof Hvalid_epath as Hp. 
  eapply valid_epath_simple_Forall in Hvalid_epath as [q [[Hqvalid Hqnodup] Hqfor]]; eauto.
  2:{ intros; eapply step_aux_unique_undirected; eauto. }
  eapply tree_no_curcuit; eauto.
  exists u, (e :: rev q); split; [symmetry; apply nil_cons|split].
  * eapply valid_epath_cons; eauto.
    eapply valid_epath_rev; eauto. 
  * constructor.
    + rewrite <- in_rev.
      rewrite Forall_forall in Hqfor.
      intros Hin.
      pose proof (Hqfor e Hin) as Hneq.
      contradiction.
    + apply NoDup_rev; auto.
Qed.

Theorem tree_one_simple_epath: 
  forall u v p1 p2,
  is_simple_epath g u p1 v ->
  is_simple_epath g u p2 v ->
  p1 = p2.
Proof.
  intros u v p1; revert u v. 
  induction p1 as [|e1 q1 IHp1]; intros u v p2 Hp1 Hp2.
  - unfold is_simple_epath in *.
    destruct Hp1 as [Hp1 _], Hp2 as [Hp2 Hnodup2].
    apply valid_epath_nil_inv in Hp1; subst u.
    destruct p2 as [|e2 q2].
    + reflexivity.
    + exfalso.
      eapply tree_no_curcuit; eauto.
      exists v, (e2 :: q2); split; [symmetry; apply nil_cons|split; auto].
  - unfold is_simple_epath in *.
    destruct Hp1 as [Hpath1 Hnodup1], Hp2 as [Hpath2 Hnodup2].
    apply valid_epath_cons_inv in Hpath1 as [w1 [Hstep1 Htail1]].
    inversion Hnodup1 as [|? ? Hnotin1 Hnodup_tail1]; subst.
    assert (Hin_e1_p2 : In e1 p2).
    {
      destruct (classic (In e1 p2)); auto.
      exfalso.
      eapply tree_edge_is_bridge; eauto.
      eapply valid_epath_reachable_without.
      + eapply valid_epath_app; [apply Hpath2|apply valid_epath_rev; eauto].
      + rewrite in_app_iff.
        intros [|]; [contradiction|apply Hnotin1; apply in_rev; auto].
    }
    destruct (in_split _ _ Hin_e1_p2) as [l1 [l2 Hp2eq]].
    subst p2.
    apply valid_epath_app_inv in Hpath2 as [x [Hpre Hsuf]].
    apply valid_epath_cons_inv in Hsuf as [y [Hstep2 Htail2]]. 
    eapply step_aux_unique_undirected in Hstep1 as [[]|[]]; eauto; subst.
    + destruct l1 as [|a l1'].
      * simpl. f_equal.
        eapply IHp1; eauto. 
        split; auto.
        inversion Hnodup2; auto.
      * exfalso.
        eapply tree_no_curcuit; eauto.
        exists u, (a :: l1'); split; [symmetry; apply nil_cons|split; auto].
        apply NoDup_app_remove_r in Hnodup2; auto.
    + destruct l1 as [|a l1'].
      * apply valid_epath_nil_inv in Hpre; subst; exfalso.
        eapply no_self_loop; eauto.
      * exfalso. 
        eapply tree_no_curcuit; eauto. 
        exists w1, (e1 :: a :: l1'); split; [symmetry; apply nil_cons|split]. 
        eapply valid_epath_cons; eauto.
        constructor; [|apply NoDup_app_remove_r in Hnodup2; auto]. 
        apply NoDup_remove in Hnodup2 as []. 
        unfold not; intros; apply H0. 
        apply in_or_app; left; auto.
Qed.

(* 树中任意两点间有且仅有一个 simple_epath *)
Lemma tree_unique_simple_epath: forall u v,
  vvalid g u -> vvalid g v ->
  exists! p, is_simple_epath g u p v.
Proof.
  intros.
  pose proof (reachable_valid_epath g u v (tree_connected g g_tree u v H H0)) as [p Hpath].
  eapply valid_epath_simple in Hpath as [q Hsimple]; eauto.
  exists q. split; auto.
  intros q' Hsimple'.
  eapply tree_one_simple_epath; eauto. 
  intros; eapply step_aux_unique_undirected; eauto.
Qed.

Section FINITE.

Context {fg: FiniteGraph G V E}. 


Definition is_leaf (v: V): Prop := 
  exists ! u, (exists e, step_aux g e u v). 

Lemma in_epath_evalid: 
  forall u v p e,
    valid_epath g u p v ->
    In e p ->
    evalid g e.
Proof.
  intros. 
  revert u H. 
  induction p; intros. 
  + contradiction. 
  + inversion H0; subst. 
    * apply valid_epath_cons_inv in H as [w [Hstep Hrest]]. 
      eapply step_evalid; eauto. 
    * apply valid_epath_cons_inv in H as [w [Hstep Hrest]]. 
      eapply IHp; eauto. 
Qed.

Lemma simple_epath_length_bounded : forall u v p,
  is_simple_epath g u p v ->
  (Zlength p <= edge_num g)%Z.
Proof.
  intros; unfold edge_num.
  destruct H as [Hvalid Hnodup].
  assert (incl p (bijective_listE g)) by 
  (intros e Hin; apply bijective_edges; auto; eapply in_epath_evalid; eauto).
  rewrite ! Zlength_correct. 
  apply inj_le.
  apply NoDup_incl_length; auto. 
Qed.


Theorem longest_simple_epath_exists :
  (exists v, vvalid g v) -> 
  exists p, max_object_of_subset Z.le (fun x => exists u v, is_simple_epath g u x v) (@Zlength E) p.
Proof.
  intros [v0 Hv0].
  set (Q := fun n => exists u v p, is_simple_epath g u p v /\ Zlength p = n).
  set (K := Zlength (bijective_listE g)).

  assert (Hexists: exists n, (0 <= n <= K)%Z /\ Q n).
  { exists 0%Z. split. 
    + split; [lia | apply Zlength_nonneg]. 
    + exists v0, v0, nil. split.
      * split; [apply valid_epath_empty | constructor].
      * apply Zlength_nil. }

  destruct (max_n_in_range Q K) as [max_n [HPmax [[Hlow Hhigh] Hmax]]];
  [apply Zlength_nonneg|auto|].

  destruct HPmax as [u_max [v_max [p_max [Hsimple_max Hlen_max]]]].
  exists p_max. split.
  + exists u_max, v_max; auto.
  + intros p [u [v Hsimple']]. 
    rewrite Hlen_max.
    apply Hmax.
    * split; [apply Zlength_nonneg|eapply simple_epath_length_bounded; eauto].
    * exists u, v, p; split; auto.
Qed.

Theorem at_least_one_leaf: 
  (exists e, evalid g e) -> (* 至少有一条边 *)
  exists v, is_leaf v.
Proof.
  intros [a Ha].

  assert (Hexists_v: exists v, vvalid g v).
  { destruct (no_empty_edge g a g_valid Ha) as [x [y Hstep]].
    exists x. eapply step_vvalid1; eauto. }
  pose proof (longest_simple_epath_exists Hexists_v) as [p [Hpsimple Hmax]].
  destruct Hpsimple as [u [v Hpsimple]].

  assert (Hp_not_nil: p <> nil).
  { intros Heq; subst p.
    destruct (no_empty_edge g a g_valid Ha) as [x [y Hstep]].
    assert (is_simple_epath g x (a :: nil) y).
    { split.
      - apply valid_epath_single; auto.
      - constructor; [simpl; auto | constructor]. }
    pose proof (Hmax (a :: nil) (ex_intro _ x (ex_intro _ y H))) as Hlen_le.
    rewrite Zlength_nil in Hlen_le.
    rewrite Zlength_cons, Zlength_nil in Hlen_le.
    lia. } 
  destruct (list_snoc_destruct p) as [|[e [q Hpq]]]; [contradiction|subst].  
  destruct Hpsimple as [Hpvalid Hpnodup]. 
  pose proof Hpvalid as Hp. 
  apply valid_epath_snoc_inv in Hpvalid as [w [Hpre Hstep]].
  exists v, w. split.
  - exists e; auto. 
  - intros x [e' Hstep']. 
    destruct (classic (e' = e)) as [|Hneq1]; [subst|exfalso].
    { eapply step_aux_unique_undirected in Hstep as [[]|]; subst; eauto. 
      destruct H; subst; auto. } 
    destruct (classic (In e' q)). 
    { apply in_split in H as [l1 [l2 H]]. 
      rewrite H in Hpre. 
      apply valid_epath_app_inv in Hpre as [y [Hl1 Hel2]]. 
      apply valid_epath_cons_inv in Hel2 as [z [He' Hl2]]. 
      eapply step_aux_unique_undirected in He' as [[]|[]]; eauto; subst y z. 
      * eapply tree_no_curcuit; eauto. 
        exists v, (l2 ++ e :: nil); split; [symmetry; apply app_cons_not_nil|split]. 
        + eapply valid_epath_snoc; eauto. 
        + subst. 
          rewrite <- app_assoc in Hpnodup.
          apply NoDup_app_remove_l in Hpnodup. 
          rewrite <- app_comm_cons in Hpnodup. 
          inversion Hpnodup; auto. 
      * eapply tree_no_curcuit; eauto. 
        exists v, (e' :: l2 ++ e :: nil); split; [symmetry; apply nil_cons|split]. 
        + eapply valid_epath_cons with (v:=x); eauto;
          [eapply step_sym; eauto|].
          eapply valid_epath_snoc; eauto.
        + subst. 
          rewrite <- app_assoc in Hpnodup.
          apply NoDup_app_remove_l in Hpnodup. 
          auto. 
    }
    assert (is_simple_epath g u ((q ++ [e]) ++ [e']) x). {
      split.
      - eapply valid_epath_snoc; eauto. 
        eapply step_sym; eauto.
      - apply Nodup_app_comm. 
        constructor; auto. 
        rewrite in_app_iff in *.
        intros [Hin | Hin]; auto; inversion Hin; auto.
    }
    pose proof Hmax ((q ++ [e]) ++ [e']) ltac:(exists u, x; auto). 
    rewrite Zlength_app, Zlength_cons, Zlength_nil in H1.  
    lia.
Qed.

(* 最长的路径的两个端点都是叶子 *)

Definition parent_edge_rel (r x: V) (e: E) : Prop :=
  exists p w, is_simple_epath g r (p ++ e :: nil) x /\ step_aux g e w x.

Lemma path_to_endpoint_uses_incident_edge_last :
  forall r x y p e,
    is_simple_epath g r p x ->
    In e p ->
    step_aux g e y x ->
    exists p', p = p' ++ e :: nil.
Proof.
  intros r x y p e [Hpath Hnodup] Hin Hstep_yx.
  destruct (in_split _ _ Hin) as [l1 [l2 Hp]].
  subst p.
  destruct l2 as [|a l2'].
  - exists l1; reflexivity.
  - apply valid_epath_app_inv in Hpath as [m [Hpre Hsuf]].
    apply valid_epath_cons_inv in Hsuf as [z [Hstep1 Hrest]].
    eapply step_aux_unique_undirected in Hstep1 as [[Hz1 Hz2]|[Hz1 Hz2]]; eauto.
    + subst z y.
      exfalso.
      eapply tree_no_curcuit; eauto.
      exists x, (a :: l2'); split; [discriminate|].
      split.
      * exact Hrest.
      * apply NoDup_app_remove_l in Hnodup.
        inversion Hnodup; subst; auto.
    + subst z m.
      exfalso.
      eapply tree_no_curcuit; eauto.
      exists x, (e :: a :: l2'); split; [discriminate|].
      split.
      * eapply valid_epath_cons; eauto.
        eapply step_sym; eauto.
      * apply NoDup_app_remove_l in Hnodup.
        exact Hnodup.
Qed.

Lemma edge_of_vertex_exists :
  forall r x,
    vvalid g r ->
    vvalid g x ->
    x <> r ->
    exists e, parent_edge_rel r x e.
Proof.
  intros r x Hr Hx Hneq.
  destruct (tree_unique_simple_epath r x Hr Hx) as [q [Hsimple _]].
  destruct (valid_epath_inv_n1 g r q x (proj1 Hsimple))
    as [[Heq Hnil]|[p [w [e [Hq [Hpre Hstep]]]]]].
  - subst. contradiction.
  - exists e. exists p, w. split.
    + subst q. destruct Hsimple; split; auto.
    + exact Hstep.
Qed.

Lemma parent_edge_rel_right_unique :
  forall r x e1 e2,
    parent_edge_rel r x e1 ->
    parent_edge_rel r x e2 ->
    e1 = e2.
Proof.
  intros r x e1 e2 [p1 [w1 [H1 Hstep1]]] [p2 [w2 [H2 Hstep2]]].
  assert (Hp : p1 ++ e1 :: nil = p2 ++ e2 :: nil).
  { eapply tree_one_simple_epath; eauto. }
  apply app_inj_tail_iff in Hp; tauto.
Qed.

Lemma parent_edge_prefix_simple :
  forall r x y p e,
    is_simple_epath g r (p ++ e :: nil) y ->
    step_aux g e x y ->
    is_simple_epath g r p x.
Proof.
  intros r x y p e [Hvalid Hnodup] Hstep.
  apply valid_epath_snoc_inv in Hvalid as [z [Hpre Hlast]].
  assert (Hzx: z = x).
  {
    eapply step_aux_unique_undirected in Hlast as [[]|]; eauto; subst.
    destruct H; subst; auto.
  }
  subst z.
  split; auto.
  apply NoDup_app_remove_r in Hnodup; auto.
Qed.

Lemma parent_edge_rel_left_unique :
  forall r x y e,
    parent_edge_rel r x e ->
    parent_edge_rel r y e ->
    x = y.
Proof.
  intros r x y e [px [wx [Hsx Hstepx]]] [py [wy [Hsy Hstepy]]].
  eapply step_aux_unique_undirected in Hstepx as [[Hwx Hxy]|]; eauto.
  destruct H; subst.
  assert (Hpyx : is_simple_epath g r py x).
  { eapply parent_edge_prefix_simple; eauto. }
  assert (Heq : px ++ e :: nil = py).
  { eapply tree_one_simple_epath; eauto. }
  subst py.
  destruct Hsy as [_ Hnodup].
  apply NoDup_remove_2 in Hnodup.
  rewrite in_app_iff in Hnodup.
  exfalso; apply Hnodup; left.
  rewrite in_app_iff; right; left; reflexivity.
Qed.

Lemma parent_edge_rel_of_vertex_in_list :
  forall r xs es x e,
    Forall2 (parent_edge_rel r) xs es ->
    In x xs ->
    parent_edge_rel r x e ->
    In e es.
Proof.
  intros r xs es x e Hfor.
  induction Hfor; intros Hin Hrel.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [Hx|Hin].
    + subst x. simpl.
      left. eapply parent_edge_rel_right_unique; eauto.
    + simpl. right. eapply IHHfor; eauto.
Qed.

Lemma parent_edge_rel_of_edge_in_list :
  forall r xs es e,
    Forall2 (parent_edge_rel r) xs es ->
    In e es ->
    exists x, In x xs /\ parent_edge_rel r x e.
Proof.
  intros r xs es e Hfor.
  induction Hfor; intros Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [He|Hin].
    + exists x. split; [left; reflexivity|].
      subst e. exact H.
    + destruct (IHHfor Hin) as [z [Hyin Hyrel]].
      exists z. split; [right; exact Hyin|exact Hyrel].
Qed.

Lemma edge_has_parent_vertex :
  forall r e,
    vvalid g r ->
    evalid g e ->
    exists x, x <> r /\ vvalid g x /\ parent_edge_rel r x e.
Proof.
  intros r e Hr He.
  destruct (no_empty_edge g e g_valid He) as [u [v Hstep]].
  pose proof (step_vvalid1 _ _ _ _ Hstep) as Hu.
  pose proof (step_vvalid2 _ _ _ _ Hstep) as Hv.
  destruct (tree_unique_simple_epath r u Hr Hu) as [pu [Hpu _]].
  destruct (tree_unique_simple_epath r v Hr Hv) as [pv [Hpv _]].
  destruct (classic (In e pu)) as [Hin_u|Hnin_u].
  - destruct (path_to_endpoint_uses_incident_edge_last r u v pu e Hpu Hin_u (step_sym _ _ _ _ Hstep)) as [p' Hp'].
    exists u; repeat split.
    + intro Heq; subst u.
      eapply tree_no_curcuit; eauto.
      exists r, (p' ++ e :: nil); split.
      * destruct p'; discriminate.
      * subst; auto.
    + auto.
    + exists p', v; split; [subst|apply step_sym]; auto.
  - destruct (classic (In e pv)) as [Hin_v|Hnin_v].
    { 
      destruct (path_to_endpoint_uses_incident_edge_last r v u pv e Hpv Hin_v Hstep) as [p' Hp'].
      exists v; repeat split.
      + intro Heq; subst v.
        eapply tree_no_curcuit; eauto.
        exists r, (p' ++ e :: nil); split.
        * destruct p'; discriminate.
        * subst; auto.
      + auto.
      + exists p', u; split; [subst|]; auto. 
    }
    { 
      exfalso.
      eapply tree_edge_is_bridge; eauto.
      eapply valid_epath_reachable_without.
      + eapply valid_epath_app.
        * eapply valid_epath_rev; apply Hpu.
        * apply Hpv.
      + rewrite in_app_iff.
        intros [Hin|]; [apply in_rev in Hin|]; auto. 
    }
Qed.

(* 每个顶点列表都存在对应的父亲边列表 *)
Lemma parent_edges_for_vertices :
  forall r xs,
    vvalid g r ->
    NoDup (r :: xs) ->
    (forall x, In x xs -> vvalid g x) ->
    exists es, Forall2 (parent_edge_rel r) xs es /\ NoDup es /\ Zlength es = Zlength xs.
Proof.
  intros r xs Hr Hnodup Hvalids.
  inversion Hnodup as [|? ? Hnotin_r Hnodup_xs]; subst.
  induction xs as [|x xs IH]; intros.
  - exists nil; repeat split; constructor.
  - inversion Hnodup_xs as [|? ? Hnotin_x Hnodup_tail]; subst.
    assert (Hx : vvalid g x) by (apply Hvalids; left; reflexivity).
    assert (Hxr : x <> r) by (intro Heq; subst; apply Hnotin_r; simpl; auto).
    destruct (edge_of_vertex_exists r x Hr Hx Hxr) as [e Hrel].
    assert (Htail_valid : forall y, In y xs -> vvalid g y) by (intros y Hy; apply Hvalids; right; exact Hy).
    assert (Htail_nodup : NoDup (r :: xs)) by (constructor; auto; intro Hin; apply Hnotin_r; simpl; auto). 
    inversion Htail_nodup; subst.
    destruct (IH Htail_nodup Htail_valid H1 H2) as [es [Hfor [Hesnodup Hlen]]].
    exists (e :: es). repeat split.
    + constructor; auto.
    + constructor; auto.
      intro Hin.
      destruct (parent_edge_rel_of_edge_in_list r xs es e Hfor Hin)
      as [y [Hyin Hyrel]].
      assert (x = y) by (eapply parent_edge_rel_left_unique; eauto).
      subst y. contradiction.
    + simpl. rewrite ! Zlength_cons; now rewrite Hlen.
Qed.

Theorem tree_size_formula0: 
  (vertex_num g > 0)%Z ->
  (vertex_num g - 1 = edge_num g)%Z.
Proof.
  unfold vertex_num, edge_num.
  intros Hpos. 
  destruct (bijective_listV g) as [|r vs] eqn:Hvlist.
  - rewrite Zlength_nil in Hpos; lia.
  - assert (Hr : vvalid g r) by (apply bijective_vertices; auto; rewrite Hvlist; simpl; eauto).
    assert (Hvs_valid : forall x, In x vs -> vvalid g x) by (intros x Hin; apply bijective_vertices; auto; rewrite Hvlist; simpl; auto). 
    pose proof (bijective_listV_NoDup g g_valid) as vlist_nodup. 
    pose proof (bijective_vertices g g_valid) as vlist_iff. 
    pose proof (bijective_listE_NoDup g g_valid) as elist_nodup.
    pose proof (bijective_edges g g_valid) as elist_iff.
    
    pose proof parent_edges_for_vertices r vs Hr ltac:(rewrite <- Hvlist; auto) Hvs_valid 
    as [es [Hfor [Hesnodup Hlen]]]; subst. 

    rewrite Hvlist in vlist_nodup, vlist_iff.

    assert (Hall1 : forall e, In e es -> In e (bijective_listE g)).
    {
      intros e Hin; apply bijective_edges; auto.
      destruct (parent_edge_rel_of_edge_in_list r vs es e Hfor Hin)
      as [x [_ [p [w [_ Hstep]]]]].
      eapply step_evalid; eauto.
    }
    assert (Hall2 : forall e, In e (bijective_listE g) -> In e es).
    {
      intros e Hin; apply elist_iff in Hin as He; auto.
      destruct (edge_has_parent_vertex r e Hr He) as [x [Hxneq [Hxvalid Hrel]]].
      assert (Hinx : In x vs) by (apply vlist_iff in Hxvalid as [|]; [subst; contradiction|auto]).
      eapply parent_edge_rel_of_vertex_in_list; eauto.
    }
    assert (Hperm : Permutation es (bijective_listE g)) by (apply NoDup_Permutation; auto; intros; split; auto).
    rewrite Zlength_cons; simpl.
    rewrite <- Hlen. 
    rewrite ! Zlength_correct.
    rewrite (Permutation_length Hperm).
    lia.
Qed. 

End FINITE.


End TREE.



Section MST.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {elistbijective: EListBijective G V E}.
Context {P: Type}
        {path: Path G V E P}
        {tr: Tree G V E P}.
Context (r: G)
        {r_valid: gvalid r}
        {ew: EdgeWeight G E}.

Definition total_weight : G -> option Z :=
  fun g => fold_right Z_op_plus (Some 0%Z)
    (map (@weight G E ew r) (@bijective_listE G V E pg gv _ g)).

Definition is_mst : G -> Prop := 
  fun g => min_object_of_subset Z_op_le 
          (fun g => gvalid g /\ tree g /\ subgraph_vertex_eq g r)          
          (total_weight) g. 

Lemma is_mst_legal:
  forall y, is_mst y -> gvalid y /\ tree y /\ subgraph_vertex_eq y r.
Proof.
  intros y Hmst.
  unfold is_mst, min_object_of_subset in Hmst.
  tauto.
Qed.

Lemma mst_edge_step:
  forall y u v e,
    is_mst y ->
    evalid y e ->
    step_aux r e u v ->
    step_aux y e u v.
Proof.
  intros y u v e Hmst Hevalid Hstep_r.
  pose proof (is_mst_legal y Hmst) as [Hyvalid [_ Hsub]].
  destruct (no_empty_edge y e Hyvalid Hevalid) as [x [z Hstep_y]].
  destruct Hsub as [_ Hsub_step].
  pose proof (Hsub_step x z e Hstep_y) as Hstep_r'.
  eapply step_aux_unique_undirected in Hstep_r as [[] | []]; eauto; subst.
  - subst; exact Hstep_y.
  - subst; apply step_sym; exact Hstep_y.
Qed.

End MST.



Section TREE_OPERATION.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {simplegraph: SimpleGraph G V E}
        {addLeafExist: addLeafExist G V E}. (*要求原图的加边存在性*)
Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}.
Context (g: G)
        {g_valid: gvalid g}
        {g_tree: tree g}.

Context {fg: FiniteGraph G V E}. 

Theorem tree_size_formula: 
  (vertex_num g > 0)%Z ->
  (vertex_num g - 1 = edge_num g)%Z.
Proof.
  unfold vertex_num, edge_num.
  intros. 
  assert (forall n, Zlength (bijective_listE g) = Z.of_nat n + 1 -> Zlength (bijective_listV g) - 1 = Zlength (bijective_listE g))%Z.  
  {
    clear H. intros n.
    revert g g_valid g_tree.
    induction n. 
    * intros. 
      simpl in H. 
  
      pose proof (bijective_vertices g g_valid) as vlist_iff.
      pose proof (bijective_listV_NoDup g g_valid) as vlist_nodup.
      pose proof (bijective_edges g g_valid) as elist_iff.
      pose proof (bijective_listE_NoDup g g_valid) as elist_nodup.

      destruct (bijective_listE g); [discriminate|rewrite Zlength_cons in H]. 
      destruct l; [|rewrite Zlength_cons in H; pose proof Zlength_nonneg l; lia]. 
      clear H. 
      assert (In e [e]) by (left; auto). 
      eapply elist_iff in H; eauto. 
      apply no_empty_edge in H as [u [v Hstep]]; auto. 

      assert (Huneqv: u <> v) by (intros ?; subst; eapply no_self_loop; eauto).
      (* assert (Huneqv: u <> v) by (exfalso; apply test_point). *)

      assert (Hu: In u (bijective_listV g)) by (apply vlist_iff; eapply step_vvalid1; eauto).
      assert (Hv: In v (bijective_listV g)) by (apply vlist_iff; eapply step_vvalid2; eauto).
      assert (Hw: ~ exists w, w <> u /\ w <> v /\ In w (bijective_listV g)). 
      {
        unfold not; intros [w [Hwnequ [Hwneqv Hw]]]. 
        apply vlist_iff in Hw. 
        pose proof (tree_connected g g_tree v w ltac:(eapply step_vvalid2; eauto) Hw) as Hreachable.
        destruct (reachable_valid_epath g v w Hreachable) as [p Hpath].
        eapply valid_epath_simple_directed in Hpath as [q [Hqpath Hqnodup]]; eauto.
        destruct q as [|a q].
        - apply valid_epath_nil_inv in Hqpath; auto. 
        - assert (Ha_valid : evalid g a).
          { apply valid_epath_cons_inv in Hqpath as [y [Ha_step _]].
            eapply step_evalid; eauto. }
          assert (Ha_eq : a = e).
          { apply elist_iff in Ha_valid as [Ha_eq | []]; auto. }
          subst a.
          destruct q as [|a q].
          + apply valid_epath_single_inv in Hqpath.
            eapply step_aux_unique_undirected in Hqpath as [[]|]; eauto.
            destruct H; subst; auto.
          + inversion Hqnodup as [|? ? Hnotin _]; subst. 
            assert (He_valid : evalid g a).
            { apply valid_epath_cons_inv in Hqpath as [y [He_step Hrest]].
              apply valid_epath_cons_inv in Hrest as [z [Ha_step _]].
              eapply step_evalid; eauto. }
            assert (Ha_eq : a = e).
            { apply elist_iff in He_valid as [Ha_eq | []]; auto. }
            subst a. apply Hnotin; simpl; auto.
      }
      assert (Hperm : Permutation (bijective_listV g) [u; v]).
      {
        apply NoDup_Permutation; auto.
        - constructor.
          + simpl. intros [Hu_eq | []]. subst. contradiction.
          + constructor; auto; apply NoDup_nil.
        - intros x; split; intros Hin.
          + destruct (classic (x = u)) as [Hx|Hx]; [subst; simpl; auto|].
            destruct (classic (x = v)) as [Hxv|Hxv]; [subst; simpl; auto|].
            exfalso. apply Hw. exists x; repeat split; auto.
          + simpl in Hin. destruct Hin as [Hin|[Hin|[]]]; subst; auto.
      }
      rewrite !Zlength_correct.
      rewrite (Permutation_length Hperm).
      simpl. lia.
    * intros. 
      assert (Hleaf: exists v, is_leaf g v). 
      { 
        apply at_least_one_leaf; auto. 
        destruct (bijective_listE g) eqn: Hel; [rewrite Zlength_nil in H; lia|].
        exists e; apply bijective_edges; auto; subst; rewrite Hel; left; auto.
      } destruct Hleaf as [v [u [[e Hstep] Hleaf]]]. 
      eapply addLeaf_valid in Hstep as [h [Hvalid [[Hu [Hv He]] Hadd]]]; eauto. 

      assert (tree h) by (eapply deleteLeaf_tree with (g2:=g); eauto). 
      assert (HpermV : Permutation (bijective_listV g) (v :: bijective_listV h)).
      {
        eapply addEdge_vlist_permutation; eauto.
        + apply bijective_listV_NoDup; auto. 
        + apply bijective_vertices; auto.
        + apply bijective_listV_NoDup; auto.
        + apply bijective_vertices; auto.
      }
      assert (HpermE : Permutation (bijective_listE g) (e :: bijective_listE h)).
      {
        eapply addEdge_elist_permutation; eauto.
        + apply bijective_listE_NoDup; auto.
        + apply bijective_edges; auto.
        + apply bijective_listE_NoDup; auto.
        + apply bijective_edges; auto.
      }
      apply Permutation_length in HpermV, HpermE. 
      simpl in HpermV, HpermE. 
      pose proof IHn h Hvalid H0. 
      rewrite ! Zlength_correct in *.
      lia.  
  }
  destruct (bijective_listE g) eqn: Hel. 
  {
    rewrite Zlength_nil.
    assert (Zlength (bijective_listV g) = 1)%Z.
    { 
      pose proof (bijective_vertices g g_valid) as vlist_iff.
      pose proof (bijective_listV_NoDup g g_valid) as vlist_nodup.
      pose proof (bijective_edges g g_valid) as elist_iff.
      destruct (bijective_listV g) as [|r [|x xs]].
      - rewrite Zlength_nil in H; lia.
      - rewrite Zlength_cons, Zlength_nil; lia.
      - assert (Hr : vvalid g r) by (apply vlist_iff; simpl; auto).
        assert (Hx : vvalid g x) by (apply vlist_iff; simpl; auto).
        assert (Hrx : r <> x).
        { intro Heq; subst.
          simpl in vlist_nodup.
          inversion vlist_nodup; subst.
          apply H3; simpl; auto. }
        destruct (reachable_valid_epath g r x (tree_connected g g_tree r x Hr Hx))
          as [p Hpath].
        destruct p as [|a p].
        + apply valid_epath_nil_inv in Hpath; contradiction.
        + apply valid_epath_cons_inv in Hpath as [y [Hstep _]].
          assert (Ha_valid : evalid g a) by (eapply step_evalid; eauto).
          apply elist_iff in Ha_valid. 
          rewrite Hel in Ha_valid; contradiction.
    }
    lia.
  } 
  apply H0 with (n := Z.to_nat (Zlength l)). 
  rewrite ! Zlength_cons; simpl. 
  rewrite Zlength_correct; lia.
Qed.


End TREE_OPERATION.

Section SPANNING_TREE.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {elistbijective: EListBijective G V E}.
Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}.
Context (g: G)
        {g_valid: gvalid g}
        {g_connected: connected g}.

Context {fg: FiniteGraph G V E}
        {addEdgeExist: addEdgeExist G V E}.  

Definition connected_subgraph_eq (h: G) : Prop := 
  gvalid h /\ connected h /\ subgraph_vertex_eq h g. 

Lemma connected_subgraph_eq_refl: 
  connected_subgraph_eq g. 
Proof. 
  repeat split; auto. 
Qed. 

Lemma connected_subgraph_eq_edge_num_lt_bounded: 
  forall h, connected_subgraph_eq h ->  
  (edge_num h <= edge_num g)%Z. 
Proof. 
  intros h [Hvalid [Hconnected Hsub]]. 
  unfold edge_num. 
  pose proof (bijective_listE_NoDup g g_valid) as elist_nodup_g.
  pose proof (bijective_edges g g_valid) as elist_iff_g.
  pose proof (bijective_listE_NoDup h Hvalid) as elist_nodup_h.
  pose proof (bijective_edges h Hvalid) as elist_iff_h.

  assert (forall e, In e (bijective_listE h) -> In e (bijective_listE g)). {
    intros e Heh. 
    rewrite elist_iff_h in Heh. 
    apply no_empty_edge in Heh as [x [y Hstep]]; auto. 
    rewrite elist_iff_g. 
    eapply step_evalid; eauto. 
    apply Hsub; eauto. 
  }
  rewrite ! Zlength_correct.
  apply NoDup_incl_length in H; auto. 
  lia.
Qed. 

Lemma connected_subgraph_eq_edge_num_gt_bounded: 
  forall h, connected_subgraph_eq h ->  
  (edge_num h >= 0)%Z. 
Proof. 
  intros. 
  unfold edge_num. 
  rewrite ! Zlength_correct.
  lia.
Qed. 

Lemma connected_subgraph_eq_exist: 
  exists h, 
    min_object_of_subset Z.le connected_subgraph_eq edge_num h.
Proof.
  set (Q := fun n => exists h, connected_subgraph_eq h /\ edge_num h = n).
  assert (Hexists: exists n, (0 <= n <= edge_num g)%Z /\ Q n).
  { exists (edge_num g)%Z. split.
    + split; unfold edge_num; 
      rewrite ! Zlength_correct; lia. 
    + exists g; repeat split; auto. 
  }
  destruct (min_n_in_range Q (edge_num g)) as [m [Hm [Hlow Hhigh]]]; auto. 
  { unfold edge_num; rewrite ! Zlength_correct; lia. }
  destruct Hm as [h [Hconnected_subgraph_eq Hedge_num]].
  exists h; split; auto. 
  intros; rewrite Hedge_num; apply Hhigh; auto. 
  split; [unfold edge_num; rewrite ! Zlength_correct; lia|
  apply connected_subgraph_eq_edge_num_lt_bounded; auto]. 
  exists b; split; auto. 
Qed.

Lemma spanningtree_exist: 
  exists h, 
    gvalid h /\ tree h /\ subgraph_vertex_eq h g.
Proof.
  destruct connected_subgraph_eq_exist as [h [[Hvalid [Hconnected Hsub]] Hmin]].
  exists h; split; [|split]; auto. 
  apply tree_decide; auto. 
  intros [u [p [Hpne Hsimple]]]. 
  destruct p; [auto|clear Hpne]. 
  pose proof Hsimple as [Hpath Hnodup]. 
  apply valid_epath_cons_inv in Hpath as [v [Hstep Hrest]]. 
  pose proof Hvalid as Hh.
  eapply addEdge_valid_inv in Hvalid as [i [Hvalidi [Hadd [Hvx [Hvy Hnotinea]]]]]; 
  [|eapply step_vvalid1; eauto|eapply step_vvalid2; eauto|eapply step_evalid; eauto|exact Hstep]. 
  assert (connected_subgraph_eq i). {
    split; [|split]; auto. 
    + intros x y Hx Hy. 
      assert (Hhx:vvalid h x) by (eapply Hadd; auto). 
      assert (Hhy:vvalid h y) by (eapply Hadd; auto). 
      pose proof Hconnected x y Hhx Hhy. 
      apply reachable_valid_epath in H as [q Hqpath]. 
      apply valid_epath_simple in Hqpath as [q' [Hqpath Hqnodup]].
      2:{ intros; eapply step_aux_unique_undirected with (g:=h); try apply Hh; eauto. } 
      clear q; rename q' into q. 
      destruct (classic (In e q)) as [Hin | Hnotin]; [|].
      * apply in_split in Hin as [q1 [q2 Hp]]; subst.
        apply valid_epath_app_inv in Hqpath as [a [Hqpre Hqrest]].
        apply valid_epath_cons_inv in Hqrest as [b [Hqstep Hqpost]].
        eapply step_aux_unique_undirected in Hstep as [[]|[]]; eauto; subst a b.
        - eapply valid_epath_reachable. 
          instantiate (1:= q1 ++ (rev p) ++ q2).
          eapply addEdge2_valid_epath_new_to_old; eauto. 
          { 
            eapply valid_epath_app; eauto. 
            eapply valid_epath_app; eauto. 
            apply valid_epath_rev; auto. 
          }
          {
            rewrite ! in_app_iff; intros ?. 
            apply NoDup_remove_2 in Hqnodup; rewrite in_app_iff in Hqnodup.
            inversion Hnodup; subst. 
            rewrite <- in_rev in H. 
            tauto. 
          } 
        - eapply valid_epath_reachable.
          instantiate (1:= q1 ++ p ++ q2).
          eapply addEdge2_valid_epath_new_to_old; eauto. 
          { 
            eapply valid_epath_app; eauto. 
            eapply valid_epath_app; eauto. 
          }
          {
            rewrite ! in_app_iff; intros ?. 
            apply NoDup_remove_2 in Hqnodup; rewrite in_app_iff in Hqnodup.
            inversion Hnodup; subst. 
            tauto. 
          } 
      * eapply valid_epath_reachable.
        eapply addEdge2_valid_epath_new_to_old; eauto. 
    + split. 
      * intros; split; intros. 
        - apply Hsub. 
          apply Hadd. 
          left; auto. 
        - apply Hsub in H.  
          apply Hadd in H as [|[|]]; auto; subst; auto. 
      * intros. 
        apply Hsub. 
        apply Hadd; left; auto. 
  }
  assert (Hadd_perm: Permutation (bijective_listE h) (e :: bijective_listE i)).
  {
    eapply addEdge_elist_permutation with
      (g1 := i) (g2 := h) (u := u) (v := v) (e := e); eauto.
    - apply bijective_listE_NoDup. exact Hvalidi.
    - apply bijective_edges. exact Hvalidi.
    - apply bijective_listE_NoDup. exact Hh.
    - apply bijective_edges. exact Hh.
  }
  apply Permutation_length in Hadd_perm. 
  apply Hmin in H; unfold edge_num in H. 
  rewrite ! Zlength_correct in H. 
  simpl in Hadd_perm. 
  lia. 
Qed. 

Context {ew: EdgeWeight G E}.

Theorem connected_have_mst: 
  exists h, is_mst g h. 
Proof. 
  set (edge_weight_sum := fun l => fold_right Z_op_plus (Some 0%Z) (map (weight g) l)).
  set (legal := fun h => gvalid h /\ tree h /\ subgraph_vertex_eq h g).
  assert (edge_weight_sum_perm:
    forall l1 l2, Permutation l1 l2 -> edge_weight_sum l1 = edge_weight_sum l2).
  {
    intros l1 l2 Hperm. 
    induction Hperm; unfold edge_weight_sum in *; simpl; auto.
    - rewrite IHHperm; auto.
    - destruct (weight g x), (weight g y), (fold_right Z_op_plus (Some 0%Z) (map (weight g) l)); simpl; auto; f_equal; lia.
    - congruence.
  }
  destruct (Nodup_all_sublists (bijective_listE g) (bijective_listE_NoDup g g_valid))
    as [edge_sets [Hedge_sets_sound Hedge_sets_complete]].
  set (represented := fun l =>
    In l edge_sets /\ exists h, legal h /\ Permutation l (bijective_listE h)).

  assert (legal_edges_in_g:
    forall h, legal h -> incl (bijective_listE h) (bijective_listE g)).
  {
    intros h [Hvalid [_ Hsub]] e Hin.
    apply bijective_edges in Hin; auto.
    apply no_empty_edge in Hin as [u [v Hstep]]; auto.
    apply bijective_edges; auto.
    eapply step_evalid; eauto. 
    apply Hsub; eauto.
  }
  destruct spanningtree_exist as [h0 Hh0].
  assert (represented_exists : exists l, In l edge_sets /\ represented l).
  {
    destruct (Hedge_sets_complete (bijective_listE h0)) as [l0 [Hl0 Hperm0]].
    - apply bijective_listE_NoDup; tauto.
    - apply legal_edges_in_g; auto.
    - exists l0; split; auto.
      split; auto; exists h0; split; auto.
  }
  destruct represented_exists as [l0 [Hl0 Hrepr0]].
  destruct (Z_op_finite_min edge_weight_sum represented edge_sets l0 Hl0 Hrepr0
    ltac:(intros y Hy; exact (proj1 Hy))) as [lm [Hreprm Hminm]].
  destruct Hreprm as [_ [hm [Hlegalm Hpermm]]].
  exists hm.
  split; auto.
  intros h Hlegalh.
  destruct (Hedge_sets_complete (bijective_listE h)) as [lh [Hlh Hpermh]].
  - apply bijective_listE_NoDup; try tauto. 
    apply Hlegalh.
  - apply legal_edges_in_g; auto.
  - assert (Hreprh : represented lh) by (split; auto; exists h; split; auto).
    specialize (Hminm lh Hreprh).
    pose proof (edge_weight_sum_perm lm (bijective_listE hm) Hpermm).
    unfold edge_weight_sum in H. 
    unfold total_weight.
    rewrite <- H.
    rewrite (edge_weight_sum_perm lh (bijective_listE h) Hpermh) in Hminm.
    exact Hminm.
Qed. 

End SPANNING_TREE.
