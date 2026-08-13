Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.directed.rootedtree.
Require Import GraphLib.directed.dfstree.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.undirected.undirected_basic.
Require Import GraphLib.Syntax.
Require Import MaxMinLib.MaxMin MaxMinLib.Interface.
Require Import SetsClass.SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Arith.Arith.

Local Open Scope sets_scope.

Record OriginalGraphType {V E: Type} := {
  original_vvalid : V -> Prop;
  original_step: E -> Prop;
  original_step_fst: E -> V;
  original_step_snd: E -> V;
  original_listV: list V;
}.

Arguments OriginalGraphType _ _ : clear implicits.

Record OriginalGraphProp {V E: Type} (origin: OriginalGraphType V E): Prop := {
  original_step_fst_valid: forall e, origin.(original_step) e -> origin.(original_vvalid) (origin.(original_step_fst) e);
  original_step_snd_valid: forall e, origin.(original_step) e -> origin.(original_vvalid) (origin.(original_step_snd) e);
  original_finite_vertices: forall v, origin.(original_vvalid) v -> In v origin.(original_listV) ;
}.

Arguments OriginalGraphProp _ _ : clear implicits.

Record original_step_aux {V E: Type} (g: OriginalGraphType V E) (e: E) (x y: V): Prop:=
{ 
  original_vx : original_vvalid g x; 
  original_vy : original_vvalid g y;
  original_ve : original_step g e; 
  original_vH : (original_step_fst g e = x /\ original_step_snd g e = y) \/ 
  (original_step_fst g e = y /\ original_step_snd g e = x);
}.

#[export]Instance OriginalGraph_graph {V E: Type} : 
  Graph (OriginalGraphType V E) V E := {|
  graph_basic.vvalid := original_vvalid;
  graph_basic.evalid := original_step;
  graph_basic.step_aux := original_step_aux;
|}.

#[export]Instance OriginalGraph_gvalid {V E: Type} : 
  GValid (OriginalGraphType V E) :=
  @OriginalGraphProp V E.

#[export]Instance OriginalGraph_stepvalid {V E: Type}: 
  StepValid (OriginalGraphType V E) V E.
Proof.
  split; intros;
  destruct H; 
  destruct original_vH0; 
  destruct H as [? ?]; auto;
  repeat split; auto.
Qed.

#[export]Instance OriginalGraph_noemptyedge {V E: Type}: 
  NoEmptyEdge (OriginalGraphType V E) V E.
Proof.
  split; intros.
  exists (g.(original_step_fst V E) e), (g.(original_step_snd V E) e).
  repeat split; auto.
  apply original_step_fst_valid; auto.
  apply original_step_snd_valid; auto.
Qed.

#[export]Instance OriginalGraph_stepuniqueundirected {V E: Type}: 
  StepUniqueUndirected (OriginalGraphType V E) V E.
Proof.
  split; intros.
  destruct H0.
  destruct H1.
  destruct original_vH0; destruct original_vH1;
  destruct H; destruct H0; subst; firstorder. 
Qed.

#[export]Instance OriginalGraph_undirected {V E: Type}: 
  UndirectedGraph (OriginalGraphType V E) V E.
Proof.
  split; intros; auto.
  destruct H.
  destruct original_vH0; auto; 
  split; tauto. 
Qed.

#[export]Instance Original_finitegraph {V E: Type}:
  FiniteGraph (OriginalGraphType V E) V E. 
Proof.
  refine {|graph_basic.listV := original_listV; |}.
  intros.
  apply original_finite_vertices; auto.
Defined.


Record RootedTreeType {V E: Type}:=
{
  vset: V -> Prop;
  theroot: V;
  parent: V -> V;
  edge: V -> option E;
  listV: list V;
}.

Arguments RootedTreeType _ _ : clear implicits.

Notation "tree '.(vset)'" := (vset tree) (at level 1).
Notation "tree '.(root)'" := (theroot tree) (at level 1).
Notation "tree '.(parent)'" := (parent tree) (at level 1).
Notation "tree '.(edge)'" := (edge tree) (at level 1).

Record RootedTreeProp {V E: Type} (rt: RootedTreeType V E):=
{
  root_no_edge: rt.(edge) (rt.(root)) = None;
  edge_some: forall v, rt.(vset) v -> v <> rt.(root) -> exists e, rt.(edge) v = Some e;
  edge_unique: forall v1 v2, rt.(vset) v1 -> rt.(vset) v2 -> rt.(edge) v1 = rt.(edge) v2 -> v1 = v2;
  root_valid: rt.(vset) rt.(theroot);
  parent_valid: forall v, rt.(vset) v -> rt.(vset) (rt.(parent) v);
  path_exist: forall v, rt.(vset) v -> clos_refl_trans (fun x y => rt.(parent) y = x) rt.(theroot) v;
  finite_vertices: forall v, rt.(vset) v -> In v rt.(listV) ;
}.

Arguments RootedTreeProp _ _ : clear implicits.

Definition rt_vvalid {V E: Type} (g: RootedTreeType V E) (v: V): Prop :=
  g.(vset) v.

Definition rt_evalid {V E: Type} (g: RootedTreeType V E) (e: E): Prop :=
  exists v, g.(vset) v /\ g.(edge) v = Some e.

Record rt_step_aux {V E: Type} (g: RootedTreeType V E) (e: E) (x y: V): Prop := 
{ 
  vx : g.(vset) x;
  vy : g.(vset) y;
  ve : g.(edge) y = Some e;
  vp : g.(parent) y = x
}.

#[export]Program Instance Rootedtree_graph {V E: Type}:
  graph_basic.Graph (RootedTreeType V E) V E := {
  vvalid := rt_vvalid ;
  evalid := rt_evalid ;
  step_aux := rt_step_aux;
}.

#[export]Instance Rootedtree_gvalid {V E: Type}:
  graph_basic.GValid (RootedTreeType V E) :=
  @RootedTreeProp V E.

#[export]Instance Rootedtree_stepvalid {V E: Type}: 
  StepValid (RootedTreeType V E) V E.
Proof.
  split; intros; destruct H; auto.
  exists y; auto.
Qed. 

#[export]Instance Rootedtree_noemptyedge {V E: Type} : 
  graph_basic.NoEmptyEdge (RootedTreeType V E) V E.
Proof.
  split; intros.
  destruct H0 as [v [? ?]].
  exists (parent g v), v; repeat split; auto.
  apply parent_valid; auto.
Qed.

#[export]Instance Rootedtree_directedgragh {V E: Type}: 
  graph_basic.StepUniqueDirected (RootedTreeType V E) V E .
Proof.
  split; intros ? ? ? ? ? ? HH ? ?.
  destruct H.
  destruct H0.
  rewrite <- ve0 in ve1.
  eapply edge_unique in ve1; eauto. 
  subst y2.
  rewrite <- vp1; subst x2.
  split; auto.
Qed.

#[export]Instance RootedTree_finitegraph {V E: Type}:
  graph_basic.FiniteGraph (RootedTreeType V E) V E. 
Proof.
  refine {|graph_basic.listV:= listV;|}.
  intros; apply finite_vertices; auto.
Defined.

#[export]Instance Rootedtree_forest {V E: Type}:
  Forest (RootedTreeType V E) V E.
Proof.
  split.
  - intros g x1 x2 e1 e2 y HH H1 H2.
    destruct H1 as [_ _ H1 _].
    destruct H2 as [_ _ H2 _].
    rewrite H1 in H2. 
    inversion H2; auto. 
  - intros g x y HH Hxy Hyx.
    assert (Hfather_vunique: forall x1 x2 y,
      step g x1 y -> step g x2 y -> x1 = x2).
    {
      intros x1 x2 y0 H1 H2.
      destruct H1 as [e1 H1].
      destruct H2 as [e2 H2].
      destruct H1 as [_ _ _ Hparent1].
      destruct H2 as [_ _ _ Hparent2].
      rewrite <- Hparent1, <- Hparent2; auto.
    }
    assert (Hroot_is_root: forall x0,
      vvalid g x0 -> reachable g (g.(root)) x0).
    {
      intros x0 Hvalid.
      apply path_exist in Hvalid as H0; auto.
      revert Hvalid; rename H0 into Hpath.
      remember g.(root) as r.
      induction_n1 Hpath.
      - reflexivity.
      - destruct (classic (x0 = r)).
        + subst x0; reflexivity.
        + eapply parent_valid in Hvalid as Hparent_valid; eauto.
          rewrite H in Hparent_valid.
          apply IHrt in Hparent_valid as Hreach; auto.
          etransitivity; eauto.
          unfold reachable.
          apply step_rt.
          apply edge_some in Hvalid as Hedge; auto.
          destruct Hedge as [e Hedge].
          exists e; repeat split; auto.
          subst r; auto.
    }
    assert (Hroot_no_father: forall x0, ~ step g x0 g.(root)).
    {
      intros x0 Hstep.
      destruct Hstep as [e Hstep].
      destruct Hstep as [_ _ Hedge _].
      erewrite root_no_edge in Hedge; eauto.
      inversion Hedge.
    }
    assert (Hone_reachable_down_up: forall x0 y0 z,
      reachable g x0 z -> step g y0 z -> x0 <> z -> reachable g x0 y0).
    {
      intros x0 y0 z Hreach Hstep Hneq.
      unfold reachable in Hreach.
      induction_n1 Hreach.
      - exfalso; apply Hneq; trivial.
      - match goal with
        | Hlast : step g ?p z |- _ =>
            assert (p = y0) as Heq
              by (eapply Hfather_vunique; [exact Hlast | exact Hstep]);
            subst p;
            unfold reachable; exact Hreach
        end.
    }
    assert (Hpartial_order: forall x0 y0,
      reachable g x0 y0 -> reachable g y0 x0 -> x0 = y0).
    {
      intros x0 y0 Hxy0 Hyx0.
      destruct (classic (x0 = y0)); auto.
      pose proof Hxy0 as Hxy0_valid.
      eapply reachable_vvalid in Hxy0_valid as [Hxvalid _]; eauto.
      apply Hroot_is_root in Hxvalid as Hroot_path; auto.
      clear Hxvalid H.
      revert y0 Hxy0 Hyx0.
      unfold reachable in Hroot_path.
      remember g.(root) as r.
      induction_n1 Hroot_path; intros; auto.
      - unfold reachable in Hyx0.
        induction_n1 Hyx0; subst; auto.
        exfalso.
        eapply Hroot_no_father; eauto.
      - destruct (classic (x0 = y0)).
        + subst; auto.
        + eapply Hone_reachable_down_up in Hyx0 as Hup; eauto.
          eapply step_reachable_reachable in H as Hdown; eauto.
          eapply IHrt in Hup; eauto.
          subst r0. symmetry.
          eapply IHrt; eauto.
    }
    assert (Hno_edge_refl: forall x0 y0,
      step g x0 y0 -> ~ step g y0 x0).
    {
      intros x0 y0 Hstep Hback.
      pose proof Hstep as Hstep_valid.
      destruct Hstep_valid as [e Hstep_aux].
      eapply step_vvalid1 in Hstep_aux as Hxvalid; eauto.
      apply Hroot_is_root in Hxvalid as Hroot_path; auto.
      clear e Hstep_aux Hxvalid.
      revert y0 Hstep Hback.
      unfold reachable in Hroot_path.
      remember g.(root) as r.
      induction_n1 Hroot_path; intros.
      - eapply Hroot_no_father; eauto.
      - eapply Hfather_vunique in H; eauto.
        subst y0.
        eapply IHrt; eauto.
    }
    destruct (classic (x = y)).
    + subst y.
      eapply Hno_edge_refl; eauto.
    + apply H.
      eapply Hpartial_order; eauto.
      apply step_rt; auto.
Qed.
  
#[export]Instance Rootedtree_prop {V E: Type} :
  RootedTree (RootedTreeType V E) V E.
Proof.
  refine {|root := theroot;|}.
  - intros; apply root_valid; auto.
  - intros g x HH H.
  apply path_exist in H as H0; auto. 
  revert H; rename H0 into H.
  remember g.(root) as r. 
  induction_n1 H. 
  reflexivity.
  destruct (classic (x = r)).
  subst x; reflexivity.
  eapply parent_valid in H0 as Hy.
  rewrite H1 in Hy.
  apply IHrt in Hy as ?; auto.
  etransitivity; eauto.
  unfold reachable.
  apply step_rt.
  apply edge_some in H0 as H4; auto.
  destruct H4 as [e H4].
  exists e; repeat split; auto.
  subst r; auto.
  auto. 
Defined.


#[export]Instance simple_graph{V E: Type}: 
  graph_basic.SimpleGraph (RootedTreeType V E) V E.
Proof.
  split; intros.
  - eapply father_eunique; eauto.
  - unfold not; intros H0.
    apply step_trivial in H0.
    eapply no_edge_refl; eauto.
    Unshelve. auto.
Qed.

Section TARJAN.
Context {V E: Type}
        (g: OriginalGraphType V E)
        (origin_gvalid: OriginalGraph_gvalid g)
        (dfstree: RootedTreeType V E)
        (tree_valid: Rootedtree_gvalid dfstree)
        (RootedTree_finitegraph: FiniteGraph (RootedTreeType V E) V E) (*hope to derived from sub*)
        (sub: subgraph dfstree g)
        (dfn: V -> nat)
        (dfnv: dfn_valid dfstree dfn)
        (low: V -> nat).

Notation theroot := dfstree.(root).
Notation subtree := (offspring dfstree).
Notation son := (step dfstree).

(* 这个定义看起来怪怪的 *)
Definition no_cross_edge := 
  forall x y, reachable g theroot x -> reachable g theroot y -> step g x y -> reachable dfstree x y \/ reachable dfstree y x.

Definition reachable_visited: Prop :=
  forall u, reachable g theroot u -> vvalid dfstree u.

Context {nocross: no_cross_edge}
        {reacheable_is_visited: reachable_visited}.


Section LOW. 

Definition step_without_tree (x y: V): Prop := 
  exists e, step_aux g e x y /\ ~ evalid dfstree e.

Definition subtree_step (y: V): (V -> Prop) := 
  fun w => exists z, 
    subtree y z /\ step_without_tree z w. 

Definition low_tree (y: V) : V -> Prop := subtree y ∪ subtree_step y.

(* v的low值满足定义 *)
Definition is_low_v (v: V): nat -> Prop :=
  fun lowv => 
    min_value_of_subset Nat.le (low_tree v) dfn lowv.

Definition is_low (fun_low: V -> nat): Prop :=
  forall v, vvalid dfstree v -> is_low_v v (fun_low v). 

(* 函数fun_low在v上满足local性质 *)
Definition low_valid_v (v: V) (fun_low: V -> nat): Prop :=
  min_value_of_subset Nat.le
  (min_value_of_subset Nat.le (son v) fun_low ∪ 
  min_value_of_subset Nat.le (step_without_tree v ∪ [v]) dfn)
  (fun x => x) (fun_low v).


Definition low_valid (fun_low: V -> nat): Prop := 
  forall v, vvalid dfstree v -> low_valid_v v fun_low.

Lemma low_valid1: is_low low -> 
  forall y z, vvalid dfstree y -> 
  subtree y z -> 
  low y <= dfn z.
Proof.
  intros H y z Hvy H0.
  specialize (H y Hvy). 
  eapply min_exists_union_l; eauto. 
Qed.

Lemma low_valid2: is_low low -> 
  forall y z w, vvalid dfstree y -> 
  subtree y z -> 
  step_without_tree z w -> 
  low y <= dfn w.
Proof.
  intros H y z w Hvy H0 H1. 
  specialize (H y Hvy). 
  unfold is_low_v in H; unfold low_tree in H. 
  eapply min_exists_union_r in H; eauto. 
  exists w; split; auto. 
  exists z; split; auto. 
Qed.

Lemma low_intros: is_low low -> 
  forall y, 
  vvalid dfstree y ->
  (exists z, subtree y z /\ low y = dfn z) \/ 
  (exists z w, subtree y z /\ step_without_tree z w /\ low y = dfn w).
Proof.
  intros H y Hvy. 
  specialize (H y Hvy). 
  destruct H as [a []]. 
  unfold low_tree in H. 
  destruct H as [[| [z []]] _]. 
  - left; exists a; auto.
  - right; exists z, a; auto. 
Qed. 


Lemma low_witness (w: V) (n: nat):
  is_low_v w n -> 
  exists x, low_tree w x /\ dfn x = n.
Proof.
  unfold is_low_v.
  intros [x [[Hx _] Heq]].
  exists x; auto.
Qed.

Lemma low_bound (w: V) (n: nat) (x: V):
  is_low_v w n -> 
  low_tree w x -> 
  n <= dfn x.
Proof.
  unfold is_low_v.
  intros [y [[_ Hmin] Heq]] Hx.
  subst. apply Hmin. auto.
Qed.

Lemma subtree_decompose (u: V): 
  subtree u ==  
  [u] ∪ 
  (fun w => exists z, son u z /\ subtree z w).
Proof. 
  split; intros. 
  - destruct (classic (u = a)). 
    * subst; left; reflexivity. 
    * eapply real_offspring in H0 as [? []]; eauto . 
      right; exists x; auto. 
  - destruct H as [|[? []]].
    * sets_unfold in H; subst; reflexivity. 
    * eapply step_reachable_reachable; eauto. 
  Unshelve. auto.  
Qed.

Lemma subtree_step_decompose (y : V) (Hvy: vvalid dfstree y): 
  subtree_step y  == 
  step_without_tree y ∪
  (fun w => exists z, son y z /\ subtree_step z w).
Proof.
  split; intros.
  - destruct H as [z [? ?]].
    destruct (classic (y = z)); [subst; left; auto|right]. 
    eapply real_offspring in H1 as [w [? ?]]; eauto. 
    exists w; split; auto. 
    exists z; split; auto. 
  - destruct H as [|[w [? [z []]]]]. 
    + exists y; split; auto. 
      reflexivity. 
    + exists z; split; auto. 
      eapply step_reachable_reachable; eauto. 
  Unshelve. auto.
Qed. 

Theorem low_tree_decompose (y: V) (Hvy: vvalid dfstree y):
  low_tree y == 
  [y] ∪ step_without_tree y ∪ 
  (fun w => exists z, son y z /\ low_tree z w).
Proof.
  unfold low_tree. 
  rewrite subtree_decompose. 
  rewrite !Sets_union_assoc. 
  apply Sets_union_congr; [reflexivity|].
  rewrite subtree_step_decompose; auto.
  rewrite <- Sets_union_assoc.
  rewrite Sets_union_comm.
  rewrite <- Sets_union_assoc. 
  rewrite Sets_union_comm. 
  apply Sets_union_congr; [reflexivity|]. 
  split; [intros [[z []]|[z []]]|intros [z [? [|]]]]. 
  * exists z; split; [|right]; auto. 
  * exists z; split; [|left]; auto. 
  * right; exists z; split; auto. 
  * left; exists z; split; auto. 
Qed.


Lemma low_valid_induction (v: V) (fun_low: V -> nat)
  (IHv: forall w, son v w -> is_low_v w (fun_low w)): 
  min_value_of_subset Nat.le (son v) fun_low == 
  min_value_of_subset Nat.le ((fun w => exists z, son v z /\ low_tree z w)) dfn.
Proof. 
  split; intros.
  - apply min_eq_forward with (f1 := fun_low) (P1 := son v); auto.
    + apply NatLe_TotalOrder.
    + intros z Hson.
      pose proof IHv z Hson as Hlow.
      apply low_witness in Hlow as [w [Hw Heq]].
      exists w. split.
      * exists z; split; auto.
      * rewrite Heq. apply Nat.le_refl.
    + intros w [z [Hson Hlow]].
      exists z. split; auto.
      pose proof IHv z Hson as Hlowz.
      apply low_bound with (x := w) in Hlowz; auto.
  - apply min_eq_forward with 
      (f1 := dfn) 
      (P1 := (fun w => exists z, son v z /\ low_tree z w)); auto.
    + apply NatLe_TotalOrder.
    + intros w [z [Hson Hlow]].
      exists z. split; auto.
      pose proof IHv z Hson as Hlowz.
      apply low_bound with (x := w) in Hlowz; auto.
    + intros z Hson.
      pose proof IHv z Hson as Hlow.
      apply low_witness in Hlow as [w [Hw Heq]].
      exists w. split.
      * exists z; split; auto.
      * rewrite Heq. apply Nat.le_refl.
Qed. 

Lemma low_valid_induction_is_low 
  (v: V) 
  (fun_low: V -> nat) 
  (Hv: vvalid dfstree v)
  (IHv: forall w, son v w -> is_low_v w (fun_low w)):
  low_valid_v v fun_low ->
  is_low_v v (fun_low v).
Proof.
  intros.
  unfold low_valid_v in H. 
  rewrite low_valid_induction in H; auto.
  apply min_union_iff in H.
  unfold is_low_v.
  rewrite low_tree_decompose; auto. 
  rewrite (Sets_union_comm [v] (step_without_tree v)).
  rewrite Sets_union_comm. 
  auto.
Qed.

Lemma low_valid_implies_is_low 
  (fun_low: V -> nat): 
  low_valid fun_low ->
  is_low fun_low.
Proof.
  intros low_valid.
  unfold is_low.
  pose proof @rooted_tree_induction_bottom_up 
  (RootedTreeType V E) V E _ _ _ _ _ dfstree tree_valid _ _
  (fun v => vvalid dfstree v -> is_low_v v (fun_low v)).
  apply H.
  intros.
  apply low_valid_induction_is_low; auto.
  intros; apply H0; auto. 
  destruct H2; eapply step_vvalid2; eauto.
Qed.

End LOW.

Context {low_valid: is_low low}.


Lemma closed_offspring: forall x y z e,
  dfn x < low y ->
  step_aux dfstree e x y ->
  reachable_without g e y z -> 
  subtree y z.
Proof.
  intros.
  unfold reachable_without in H1.
  induction_n1 H1; [reflexivity|].
  rename z into w; rename y0 into z. 
  (* 
     归纳假设 (IH): y 到 z 的路径已经在 y 的子树内。
     目标: 证明下一步走到 w，w 依然在 y 的子树内。
     
          x
          | e (blocked)
          v
          y
         / \
       ... z ... (已知 z 在 y 的子树内)
            \?
             w (下一步)
  *)
  assert (Hyz: subtree y z) by (apply IHrt; auto); clear IHrt. 
  
  (* 利用 DFS 性质：无横叉边 (No Cross Edge)。
     所以 w 要么是 z 的后代，要么是 z 的祖先。*)
  assert (Hcases: subtree z w \/ subtree w z). {
      assert (reachable g theroot z). { 
        apply step_vvalid2 in H0 as Hvy.
        eapply root_is_root in Hvy; eauto. 
        simpl in Hvy. 
        eapply sub_reachable; eauto.
        transitivity y; auto. }  
      destruct H2 as [ezw []].  
      assert (step g z w) by (exists ezw; auto).
      apply nocross; auto. 
      transitivity z; auto. 
      apply step_rt; auto. } 
  
  destruct Hcases as [Hzw|Hwz]. 
  
  (* Case 1: w 是 z 的后代。
     这种情况很简单，由传递性可知 w 也在 y 的子树内。
     
          y
          :
          z
          : (subtree)
          v
          w
  *)
  1: { transitivity z; auto. }

  (* Case 2: w 是 z 的祖先。
     因为z同时为y和w的后代，所以y与w存在后代关系。
     如果w是y的后代，那么已经得证。
  *)
    eapply offspring_one_reachable in Hwz; [|apply Hyz];
    destruct Hwz as [?|Hwy]; auto.
    destruct (classic (w = y)); [subst; reflexivity|]. 
    (*  y是w的后代时：
            w -------.               
            ^        |                 
            |        |                 
            x        |                
            | e      |(是否是树边？)         
            v        |                 
            y        |                 
            :        |                 
            v        |                 
            z - - - -'             *)
    assert (Hwx: subtree w x). {
      eapply one_reachable_down_up; eauto. 
      exists e; auto. } 
    destruct H2 as [ezw [Hzw Hneq]].
    destruct (classic (evalid dfstree ezw)). 
    (* w -> z是树边时，与树的性质矛盾 *)
    + apply no_empty_edge in H2 as [z' [w' ]]; auto.
      apply sub in H2 as Hg. 
      eapply step_aux_unique_undirected in Hg as [[]|[]]; 
      [| | |apply Hzw]; eauto; subst z' w'. 
      * transitivity z; auto. 
        apply step_rt. 
        exists ezw; auto. 
      * exfalso. 
        assert (Hsonxy: son x y) by (exists e; auto).
        assert (Hsonwz: son w z) by (exists ezw; auto).
        eapply step_subtree_pair in Hsonxy; eauto. 
        destruct Hsonxy; subst.
        eapply father_eunique in H2; eauto.
    (* z -> w不是树边时，与low的取值矛盾 *)
    + eapply step_vvalid2 in H0 as Hvy. 
      assert (low y <= dfn w). {
        eapply low_valid2; eauto. 
        exists ezw; auto. } 
      apply @dfn_valid_offspring with (dfn:=dfn) in Hwx; auto. 
      lia. 
  Unshelve. auto. auto. auto.
Qed.


Lemma father_unreachable: forall x y e,
  dfn x < low y ->
  step_aux dfstree e x y ->
  ~ reachable_without g e y x.
Proof.
  unfold not; intros.
  eapply closed_offspring in H0 as H2; eauto.
  eapply step_trivial in H0 as H3; eauto.
  apply step_rt in H3.
  eapply offspring_partial_order in H3; eauto.
  subst y.
  eapply no_self_loop; eauto.
  Unshelve. auto. auto.
Qed. 

(* ================================================================= *)
(* 主定理：树边是否是桥等价于桥两端点的low值与dfn值关系                 *)
(* ================================================================= *)
Lemma tarjan: forall x y e, 
  step_aux dfstree e x y -> 
  (is_bridge g e <-> dfn x < low y).
Proof.
  intros x y e H0.
  assert (vvalid dfstree y) as Hvy by (apply H0).
  pose proof H0 as He.
  apply step_trivial in H0.
  split.
  - intros Hb; apply NNPP. 
    unfold not at 1; intros. 
    eapply Compare_dec.not_lt in H. 
    (* 
       分析 low y 的定义。low y 是 y 能通过其子树中的点 z 
       以及一条非树边 (z, w) 所能到达的最小 dfn 值的点 w。
    *)
    eapply low_intros with (y := y) in low_valid as 
    [[z [Hyz Hlowy]]|[z [w [Hyz [Hzw Hlowy]]]]]; eauto. 
    
    (* Case 1: 简单情况：y的low值来自其subtree内部，没有跳出子树 *)
    1: { apply dfnv in H0. 
      eapply @dfn_valid_offspring in Hyz; eauto. lia. } 
    
    (* Case 2: 一般情况：存在回边/非树边。
       y 的后代 z 有一条边指向 w (step_without_tree z w)。
       图示如下：
             x
             | e (待测边)
             v
             y
             : (subtree)
             v
             z - - -> w (非树边)
    *)
    destruct Hzw as [ezw [Hzw Hout]]. 
    (* 利用 DFS 树性质：无横叉边 (No Cross Edge)，
       所以 w 要么是 z 的祖先，要么是 z 的后代。 *)
      assert (Hcases: subtree z w \/ subtree w z). {
        assert (reachable g theroot z). {
          eapply root_is_root in Hvy; eauto. 
          simpl in Hvy. 
          eapply sub_reachable; eauto.
          transitivity y; auto. }  
        assert (step g z w) by (exists ezw; auto).
        apply nocross; auto. 
        transitivity z; auto. 
        apply step_rt; auto. } 
    
    destruct Hcases as [Himposible|Hwz]. 

    (* 不可能情况：w是z的后代。这与 w 的 dfn 更小矛盾 *)
    + eapply @dfn_valid_offspring in Himposible; eauto. 
      eapply @dfn_valid_offspring in Hyz; eauto. 
      apply dfnv in H0. lia. 
    
    (* 可能情况：z 是 w 的后代 (即 w 是 z 的祖先)。
       此时我们需要判断 w 相对于 x 的位置。
    *)
    + assert (Hxw: subtree x z) by (eapply step_reachable_reachable; eauto). 
      eapply offspring_one_reachable in Hxw; [|apply Hwz]; destruct Hxw as [Hxw|Hwx]; auto.
      (* w和x的子树都包含z，所以它们也有子树关系 *)

      (* 情况 2.1: w = x
         即回边直接指回了 x。
         
         图示：
             x <----------. (w=x)
             | e          |
             v            |
             y            | (ezw)
             :            |
             v            |
             z - - - - - -'
         
         存在环 x->y->...->z->x，去掉 e (x->y) 后，y 仍可通过 z 回到 x。
         所以 e 不是桥。
      *)
      * destruct (classic (x = w)); [subst w|].
        (* w <> x时，逻辑上的矛盾排除 *)
        2: { eapply real_offspring in H1 as [t [Hxt Htw]]; eauto. 
          eapply @dfn_valid_offspring in Htw; eauto. 
          apply dfnv in Hxt. lia. } 
        
        (* w = x时，构造旁路证明非桥 *)
        eapply Hb; [apply sub; eauto|]. 
        apply reachable_without_sym. 
        eapply reachable_without_step_offspring1 in Hyz; eauto. 
        transitivity z; [eapply sub_reachable_without; eauto|]. 
        apply step_without_rt. 
        exists ezw; split; auto. 
        unfold not; intros; subst. 
        eapply step_evalid in He; eauto.

      (* 情况 2.2: x 是 w 的后代 (w 是 x 的真祖先)
         回边指到了 x 的上方。
         
         图示：
             w < - - - -.
             :          |
             v          |
             x          |
             | e        | (ezw)
             v          |
             y          |
             :          |
             v          |
             z - - - - -'
         
         存在路径 y->...->z->w->...->x，不经过 e。
         所以 e 不是桥。
      *)
      * eapply Hb; [apply sub; eauto|]. 
        apply reachable_without_sym. 
        
        eapply reachable_without_step_offspring1 in Hyz; eauto. 
        eapply reachable_without_step_offspring2 in Hwx; eauto. 
        transitivity z; [eapply sub_reachable_without; eauto|]. 
        transitivity w; [|eapply sub_reachable_without; eauto]. 
        apply step_without_rt. 
        exists ezw; split; auto. 
        unfold not; intros; subst. 
        eapply step_evalid in He; eauto.
  
  - intros lowy. 
    unfold is_bridge; intros x' y' He'. 
    pose proof H0 as [exy Hxy]. 
    eapply no_multiple_edge in He; eauto; subst. 
    apply sub in Hxy as Hg. 
    eapply step_aux_unique_undirected in He' as [[]|[]]; eauto; subst x' y'. 
    * apply father_unreachable in Hxy; auto. 
      unfold not; intros; apply Hxy. 
      eapply reachable_without_sym; auto. 
    * apply father_unreachable; auto. 
  Unshelve. auto. auto. auto. auto. auto. auto.
Qed.


Lemma tree_path_safe: forall u v e,
  reachable dfstree u v ->  
  ~ evalid dfstree e ->      
  reachable_without g e u v. 
Proof.
  intros u v e H_tree H_not_tree. 
  unfold reachable in H_tree.
  induction_n1 H_tree; [reflexivity|].
  transitivity u0; auto.
  apply step_without_rt.
  destruct H as [e0 H_step_tree].
  exists e0; split; auto.
  unfold not; intros H_eq; subst e0.
  apply H_not_tree.
  eapply step_evalid; eauto.
Qed.

Definition reachable_edge (u: V) (e: E): Prop :=
  exists x y, step_aux g e x y /\ reachable g u x.


(* ================================================================= *)
(* 副定理：非树边一定不是桥 *)
(* ================================================================= *)
Lemma tarjan_trivial: forall e, 
  reachable_edge theroot e -> 
  reachable_visited ->
  ~ evalid dfstree e -> 
  ~ is_bridge g e.
Proof.
  intros e H_reach H_visited H_not_tree.
  (* 
            root
           /    \
          :      : (tree paths)
          v      v
          x ---- y
             e (non-tree edge)
  *)
  destruct H_reach as [x [y [H_step_e H_root_x]]].
  
  assert (H_valid_x: vvalid dfstree x).
  { apply H_visited; auto. }
  assert (H_valid_y: vvalid dfstree y). { 
    apply H_visited.
    eapply reachable_step_reachable; eauto.
    exists e; apply H_step_e. }

  unfold is_bridge; unfold not; intros H_bridge.
  eapply H_bridge; eauto; clear H_bridge.

  apply step_sym in H_step_e. 
  transitivity (root dfstree).
  * apply reachable_without_sym.
    eapply tree_path_safe; eauto.
    apply root_is_root; auto.
  * apply tree_path_safe; auto.
    apply root_is_root; auto.
Qed.


End TARJAN.
