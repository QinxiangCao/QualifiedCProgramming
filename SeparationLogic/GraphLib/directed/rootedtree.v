
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Lia.

Class Forest (G V E : Type)
  {pg : Graph G V E} {gv : GValid G}
  {stepvalid : StepValid G V E}
  {step_aux_unique : StepUniqueDirected G V E} := {
  father_eunique : forall g x1 x2 e1 e2 y,
    gvalid g ->
    step_aux g e1 x1 y ->
    step_aux g e2 x2 y ->
    e1 = e2;

  no_reachable_back_edge :
    forall g x y,
      gvalid g ->
      reachable g x y ->
      ~ step g y x;
}.

Class RootedTree (G V E : Type)
  {pg : Graph G V E} {gv : GValid G}
  {stepvalid : StepValid G V E}
  {step_aux_unique : StepUniqueDirected G V E}
  {forest : Forest G V E} := {
  root : G -> V;
  root_is_valid : forall g, gvalid g -> vvalid g (root g);
  root_is_root : forall g x, gvalid g -> vvalid g x -> reachable g (root g) x;
}.

Section ROOTEDTREE.
Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {step_aux_unique: StepUniqueDirected G V E}
        {forest: Forest G V E}
        (* {rootedtree: RootedTree G V E} *)
        {g: G}
        {gvalid: gvalid g}.

Definition offspring (g: G) := (reachable g).

Definition nearest_common_ancester (x y z: V) :=
  offspring g x y /\ offspring g x z /\
  (forall w, offspring g x w -> w <> x -> ~ (offspring g w y /\ offspring g w z)). 

Definition brothers (x y z: V) :=
  y <> z /\ step g x y /\ step g x z.

Definition isleaf (g: G) (x: V) :=
  forall y, ~ step g x y.

Lemma father_vunique: forall x1 x2 y, 
  step g x1 y -> step g x2 y -> x1 = x2.
Proof.
  intros.
  destruct H as [e1 ?].
  destruct H0 as [e2 ?].
  eapply father_eunique in H as H2; eauto.
  subst e2.
  eapply step_aux_unique in H; eauto.
  destruct H; auto.
Qed.

Lemma real_offspring: forall y w: V,
  offspring g y w -> y <> w -> exists z, step g y z /\ offspring g z w.
Proof.
  intros y w H. unfold offspring in H; unfold reachable in H.
  induction_1n H.
  - exfalso; auto.
  - destruct (classic (y0 = w)).
  * subst. exists w; auto.
  * exists y0; auto.
Qed.

Lemma one_reachable_down_up: forall x y z: V,
  offspring g x z -> 
  step g y z -> 
  x <> z -> 
  offspring g x y.
Proof.
  intros.
  unfold offspring in H. 
  unfold reachable in H.
  induction_n1 H.
  - exfalso; apply H1; trivial.
  - assert(x0 = y).
    eapply father_vunique; eauto.
    subst; auto.
Qed.

Lemma offspring_one_reachable: forall x y z: V, 
  offspring g x z -> 
  offspring g y z -> 
  offspring g y x \/ offspring g x y.
Proof.
  intros. 
  destruct_equality_impl x z.
  unfold offspring, reachable in *.
  induction_n1 H0; subst.
  - right; auto.
  - destruct_equality_impl x y0. 
    eapply IHrt; eauto.
    eapply one_reachable_down_up; eauto.
Qed.

Lemma offspring_partial_order: forall x y, 
  offspring g x y -> 
  offspring g y x -> 
  x = y.
Proof.
  intros. 
  destruct (classic (x = y)); [auto|]. 
  apply real_offspring in H1 as [z [Hstep Hoff]]; auto. 
  exfalso; eapply (no_reachable_back_edge _ z x); eauto. 
  transitivity y; auto.
Qed.

Lemma no_edge_refl : forall x y, 
  step g x y -> ~ step g y x.
Proof.
  intros.
  eapply no_reachable_back_edge; eauto. 
  apply step_rt; auto.
Qed.


Lemma no_multiple_edge: forall x y e1 e2,
  step_aux g e1 x y -> step_aux g e2 x y -> e1 = e2.
Proof.
  intros.
  eapply father_eunique; eauto.
Qed.

Lemma no_self_loop: forall x e,
  ~ step_aux g e x x.
Proof.
  intros; unfold not; intros.
  apply step_trivial in H.
  eapply no_edge_refl; eauto. 
Qed.

Lemma offspring_not_father: forall x y,
  offspring g x y -> 
  ~ step g y x.
Proof.
  intros.
  unfold not; intros.
  pose proof H0 as H2.
  unfold step in H0. 
  destruct H0 as [e ?].
  destruct (classic (x = y)).
  - subst y.
    eapply no_self_loop; eauto. 
  - apply H1. 
    eapply offspring_partial_order; eauto.
    apply step_rt; auto.
Qed.

Lemma reachable_without_step_offspring1: forall e x y z,
  step_aux g e x y -> 
  offspring g y z -> 
  reachable_without g e y z.
Proof.
  intros.
  unfold offspring in H0.
  unfold reachable in H0.
  induction_n1 H0.
  reflexivity.
  etransitivity.
  eapply IHrt; eauto.
  unfold step in H1.
  destruct H1 as [e0 ?].
  unfold reachable_without.
  apply step_without_rt.
  exists e0; split; auto.
  unfold not; intros.
  subst e0.
  eapply step_aux_unique in H1; eauto.
  destruct H1 as [? ?].
  subst y0 z.
  eapply offspring_not_father; eauto.
  exists e; auto.
Qed.

Lemma reachable_without_step_offspring2: forall e x y z,
  step_aux g e x y -> 
  offspring g z x -> 
  reachable_without g e z x.
Proof.
  intros.
  unfold offspring in H0.
  unfold reachable in H0.
  induction_1n H0.
  unfold reachable_without; reflexivity.
  etransitivity; eauto.
  unfold step in H1.
  destruct H1 as [e0 ?].
  unfold reachable_without.
  transitivity_1n z0; try reflexivity.
  exists e0; split; auto.
  unfold not; intros.
  subst e0.
  eapply step_aux_unique in H1; eauto.
  destruct H1 as [? ?].
  subst z0 z.
  eapply offspring_not_father; eauto.
  exists e; auto.
Qed.

Lemma step_minimal: forall x y z,
  step g x y -> offspring g x z -> offspring g z y -> z = x \/ z = y.
Proof.  
  intros.
  revert y H H1.
  unfold offspring, reachable in H0.
  induction_n1 H0; auto.
  destruct_equality_impl z y.
  eapply one_reachable_down_up in H1; eauto. 
  exfalso.
  eapply offspring_not_father with (x:=z)(y:=x0); eauto.
  etransitivity; eauto.
Qed.

Lemma one_reachable_up_down: forall x y z w,
  step g x y -> offspring g x z -> x <> z -> offspring g z w -> 
  offspring g y w -> offspring g y z.
Proof.
  intros.
  eapply offspring_one_reachable in H2; eauto.
  destruct H2; auto.
  eapply step_minimal in H2; eauto. 
  destruct H2; subst.
  - exfalso; apply H1; auto.
  - reflexivity.
Qed. 

Lemma step_subtree_pair: 
  forall w x y z,
    step g z w ->
    offspring g x w ->
    step g y x ->
    offspring g z y ->
    w = x /\ y = z.
Proof.
  intros w x y z H_son_wz H_sub_wx H_son_xy H_sub_yz.
  assert (H_off_zx: offspring g z x). { etransitivity.
    - apply H_sub_yz.
    - apply step_rt; auto. }
  pose proof (step_minimal z w x H_son_wz H_off_zx H_sub_wx) as [H_eq | H_eq].
  - subst x.
    exfalso.
    eapply offspring_not_father.
    + apply H_sub_yz.
    + apply H_son_xy.

  - subst x.
    split; auto.
    symmetry.
    eapply father_vunique.
    + apply H_son_wz.
    + apply H_son_xy.
Qed.

Lemma nearest_coancester_exist': forall x y z,
  offspring g x y -> offspring g x z ->
  (exists w, nearest_common_ancester w y z).
Proof.
  intros.
  revert z H0.
  unfold offspring, reachable in H.
  induction_1n H.
  - exists y; repeat split; auto.
    reflexivity.
    intros; unfold not; intros.
    destruct H2.
    eapply offspring_partial_order in H2; eauto.
  - assert(offspring g x0 z \/ ~ offspring g x0 z);
    [apply classic;auto|].
    destruct H2.
    + eapply IHrt; eauto.
    + exists x. repeat split; auto.
      * unfold offspring, reachable in *.
        transitivity_1n x0; auto.
      * intros. unfold not;intros.
        destruct H5.
        eapply offspring_one_reachable in H as H7; eauto.
        destruct H7.
        ** apply H2; etransitivity; eauto.
        ** eapply one_reachable_down_up in H7; eauto.
           eapply offspring_partial_order in H7; eauto.
           unfold not; intros; subst w; auto.
Qed.

Lemma nearest_coancester_symmetric: forall x y z,
  nearest_common_ancester x y z -> nearest_common_ancester x z y.
Proof.
  intros.
  destruct H as [H1 [H2 H3]].
  repeat split; auto.
  intros. 
  eapply H3 in H0; eauto.
  unfold not; intros.
  destruct H4.
  unfold not in H0.
  apply H0; auto. 
Qed.

Lemma nearest_common_ancester_unique: forall x1 x2 y z,
  nearest_common_ancester x1 y z -> 
  nearest_common_ancester x2 y z ->
  x1 = x2.
Proof.
  intros.
  destruct H as [H1 [H2 H3]].
  destruct H0 as [H4 [H5 H6]].
  eapply offspring_one_reachable in H1 as H; eauto.
  destruct H.
  - destruct_equality_impl x1 x2.
    eapply H3 in H; eauto.
    exfalso; auto.
  - destruct_equality_impl x1 x2.
    eapply H6 in H; eauto.
    exfalso; auto.
Qed.

Lemma brothers_sym: forall x y z,
  brothers x y z -> brothers x z y.
Proof.
  intros.
  destruct H as [H1 [H2 H3]].
  repeat split; auto.
Qed.

Lemma brothers_not_offspring: forall x y z, 
  brothers z x y -> ~ offspring g x y.
Proof.
  intros.
  destruct H as [? [? ?]].
  unfold not; intros.
  revert z H H0 H1.
  unfold offspring, reachable in H2.
  induction_n1 H2; auto.
  eapply father_vunique in H3 as H4; eauto. 
  subst z.
  eapply offspring_not_father; eauto.
Qed.

Lemma brother_ancester_relation: forall x y z, 
  brothers x y z -> nearest_common_ancester x y z.
Proof.
  intros.
  destruct H as [H1 [H2 H3]].
  repeat split; auto.
  - unfold offspring, reachable.
    transitivity_n1 x; auto. 
    reflexivity.
  - unfold offspring, reachable.
    transitivity_n1 x; auto. 
    reflexivity.
  - intros. unfold not; intros.
    destruct H4 as [H4 H5].
    eapply step_minimal in H4; eauto.
    eapply step_minimal in H5; eauto.
    destruct H4; auto.
    destruct H5; auto.
    subst y z; auto.
Qed.

Section TREEINDUCTION.

Context {fg: FiniteGraph G V E}
        {rootedtree: RootedTree G V E}.

Notation thelistV := (graph_basic.listV g).

Lemma listV_not_empty: thelistV <> nil.
Proof.
  assert (In (root g) thelistV).
  apply graph_basic.finite_vertices; auto. 
  apply root_is_valid; auto.
  unfold not; intros. 
  rewrite H0 in H.
  eapply in_nil; eauto.
Qed.

Inductive num_of_offspring : V -> list V -> nat -> Prop :=
  | num_of_offspring_nil: forall u, num_of_offspring u nil 0
  | num_of_offspring_cons_reacheable: forall u a l n,
    reachable g u a ->
    num_of_offspring u l n ->
    num_of_offspring u (a :: l) (S n)
  | num_of_offspring_cons_no_reachable: forall u a l n,
    ~ reachable g u a ->
    num_of_offspring u l n ->
    num_of_offspring u (a :: l) n.

Lemma num_of_offspring_le_on_step : forall x y l n m,
  step g x y ->
  num_of_offspring y l n ->
  num_of_offspring x l m ->
  n <= m.
Proof.
  induction l; 
  intros; 
  inversion H0; subst; 
  inversion H1 ; subst; 
  try lia; 
  pose proof (IHl _ _ H H7 H9); 
  try lia.
  exfalso; apply H6; unfold reachable. 
  transitivity_1n y; auto. 
Qed. 

Lemma num_of_offspring_lt_on_step : forall x y l n m, 
  step g x y -> 
  In x l ->   
  num_of_offspring y l n ->
  num_of_offspring x l m ->
  n < m.
Proof.
  intros.
  destruct l; simpl in * ; try lia.
  generalize dependent y; generalize dependent x; revert n m v.
  induction l.
  - intros. destruct H0; [subst |exfalso; apply H0].
    inversion H2; subst. 
    + inversion H1 ; subst.
      * exfalso; eapply offspring_not_father; eauto.
      * inversion H7; subst; inversion H9; subst; try lia. 
    + exfalso; apply H5; reflexivity.
  - intros; destruct H0.
    + subst. inversion H2; subst; 
      [inversion H1; subst | exfalso; apply H5; reflexivity].
      * exfalso; eapply offspring_not_father; eauto.
      * apply Arith_base.le_lt_n_Sm_stt.
        eapply num_of_offspring_le_on_step; eauto.
    + inversion H2; subst; inversion H1; subst; 
      specialize (IHl _ _ _ _ H0 H8 _ H H10); try lia. 
      exfalso; apply H6; unfold reachable. 
      transitivity_1n y; auto. 
Qed.

    
Lemma num_of_offspring_lt_for_graph: forall x y n m, 
  step g x y -> 
  num_of_offspring y thelistV n -> 
  num_of_offspring x thelistV m -> 
  n < m. 
Proof.
  intros.
  eapply num_of_offspring_lt_on_step; eauto.
  apply graph_basic.finite_vertices; auto.
  destruct H.
  eapply step_vvalid1; eauto.
Qed.


Lemma non_leaf_has_positive_offspring_num: forall x y l, 
  step g x y -> 
  In y l -> 
  ~ num_of_offspring x l 0. 
Proof.
  intros.
  revert x y H H0.
  induction l. 
  - intros. inversion H0.
  - unfold not; intros.
  inversion H1; subst.
  eapply IHl; eauto.
  inversion H0; subst;
  [exfalso; apply H5; apply step_rt|]; auto.
Qed.

Lemma num_of_offspring_is_bounded: forall l, exists bound, forall x n, 
  num_of_offspring x l n -> 
  n <= bound.
Proof.
  intros.
  induction l.
  - exists 0; intros; inversion H; lia. 
  - destruct IHl as [bound Hbound].
    exists (S bound); intros.
    inversion H; subst.
    * pose proof Hbound x n0 H5 as Hn. lia.
    * pose proof Hbound x n H5 as Hn. lia.
Qed. 

Lemma num_of_offspring_exists : forall x l, exists n, num_of_offspring x l n.
Proof.
  intros. induction l. 
  - exists 0. apply num_of_offspring_nil.
  - destruct IHl as [n Hn].
    destruct (classic (reachable g x a)).
    + exists (S n). apply num_of_offspring_cons_reacheable; auto.
    + exists n. apply num_of_offspring_cons_no_reachable; auto.
Qed.

Lemma parent_relation_is_well_founded:
  well_founded (fun (x y: V) => step g y x).
Proof.
  unfold well_founded.
  pose proof listV_not_empty as listV_not_empty.
  assert (forall a n bound, num_of_offspring a thelistV n -> n <= bound -> 
  Acc (fun x y: V => step g y x) a). {
  - intros a n bound; revert a n. 
    induction bound as [|m].
    + intros. 
      assert (n = 0) by lia; subst; clear H0. 
      inversion H ; subst.
      * congruence.  
      * apply Acc_intro; intros.
        assert (In y thelistV). {
        apply graph_basic.finite_vertices; auto.
        destruct H2.
        eapply step_vvalid2; eauto. }
        exfalso. 
        eapply non_leaf_has_positive_offspring_num; eauto.
    + intros. apply Acc_intro; intros y Hstep.
      pose proof (num_of_offspring_exists y thelistV) as [m' H1].
      eapply IHm; eauto.
      eapply num_of_offspring_lt_for_graph in Hstep; eauto. 
      lia. }
  intros.
  pose proof num_of_offspring_is_bounded thelistV as [bound].
  pose proof num_of_offspring_exists a thelistV as [n].
  eapply H; eauto. 
Qed.

Theorem rooted_tree_induction_bottom_up (P: V -> Prop):
  (forall v, (forall u, step g v u -> P u) -> P v) ->
  (forall v,  P v).
Proof.
  eapply well_founded_induction.
  apply parent_relation_is_well_founded.
Qed.

Theorem rooted_tree_induction_top_down (P: V -> Prop):
  P (root g) ->
  (forall x, P x -> (forall y, step g x y -> P y)) ->
  (forall v, vvalid g v -> P v).
Proof.
  intros.
  apply root_is_root in H1; auto.
  unfold reachable in H1.
  remember (root g) as r.
  induction_n1 H1.
  - auto.
  - eapply H0; auto.
Qed.

End TREEINDUCTION.
    
End ROOTEDTREE.
