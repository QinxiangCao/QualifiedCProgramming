
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import SetsClass.SetsClass.
Require Import Coq.Arith.Arith.
From MaxMinLib Require Import MaxMin Interface.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From RecordUpdate Require Import RecordUpdate.
From TraceLib Require Import TraceBasic TraceLogic TraceRecur CommonTactics MapLib.
From GraphLib Require Import GraphLib tarjan.
From Algorithms Require Import Tarjan Tarjan_tactics Tarjan_set_tree Tarjan_basics Tarjan_basics_ex Tarjan_no_cross_edge Tarjan_is_dfn.

Import SetsNotation.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope sets.
Local Open Scope map_scope.
Local Open Scope trace_scope.

Section ISLOW.
    
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

Definition Sets_minus {A: Type} (S1 S2: A -> Prop): A -> Prop := 
  fun s => S1 s /\ ~ S2 s.

Notation " A '∖' B " := (Sets_minus A B) (at level 20). 

Lemma Sets_minus_union_singleton_cancel {A: Type} (S: A -> Prop) (a: A):
  ~ a ∈ S -> 
  (S ∪ [a]) ∖ [a] == S.
Proof.
  intros.
  split; intros.
  * destruct H0; destruct H0; auto.
  exfalso; auto.
  * split; auto.
  left; auto.
  sets_unfold; unfold not; intros; subst; auto.
Qed.

Lemma Sets_minus_included {A: Type} (S: A -> Prop) (a: A):
  S ∖ [a] ⊆ S.
Proof. firstorder. Qed.

Lemma Sets_minus_not_included {A: Type} (S: A -> Prop) (a: A):
  ~ a ∈ S ∖ [a].
Proof. firstorder. Qed.


Definition low_eq_dfn: V -> (@St V E) -> Prop := fun u s => s.(low) u = s.(dfn) u.

Definition low_le_dfn (s: @St V E): Prop :=
  forall v, v ∈ s.(visited) -> s.(low) v <= s.(dfn) v.

Lemma min_value_of_subset_equiv_nat {A: Type}:
  forall (P Q: A -> Prop) (f: A -> nat),
    P == Q ->
    min_value_of_subset Nat.le P f == min_value_of_subset Nat.le Q f.
Proof.
  intros P Q f HPQ.
  sets_unfold in HPQ.
  split; intros Hmin.
  - destruct Hmin as [x [[Hx Hleast] Heq]].
    exists x; split; [split|]; auto.
    + apply HPQ; auto.
    + intros b Hb.
      apply Hleast.
      apply HPQ; auto.
  - destruct Hmin as [x [[Hx Hleast] Heq]].
    exists x; split; [split|]; auto.
    + apply HPQ; auto.
    + intros b Hb.
      apply Hleast.
      apply HPQ; auto.
Qed.

Lemma le_min_nat_min:
  forall x y, le_min Nat.le x y = Nat.min x y.
Proof.
  intros x y.
  unfold le_min.
  destruct (@le_total nat Nat.le NatLe_TotalOrder x y).
  - rewrite Nat.min_l; lia.
  - rewrite Nat.min_r; lia.
Qed.

Lemma min_value_union_singleton_id:
  forall (P: nat -> Prop) n m,
    min_value_of_subset Nat.le P id n ->
    min_value_of_subset Nat.le (P ∪ [m]) id (Nat.min n m).
Proof.
  intros P n m Hmin.
  pose proof (min_union_1_right' Nat.le n m id P Hmin) as H.
  rewrite le_min_nat_min in H.
  exact H.
Qed.

Lemma min_value_of_subset_func_ext_nat {A: Type}:
  forall (P: A -> Prop) (f h: A -> nat) n,
    (forall x, x ∈ P -> f x = h x) ->
    min_value_of_subset Nat.le P f n ->
    min_value_of_subset Nat.le P h n.
Proof.
  intros P f h n Hext [x [[Hx Hleast] Heq]].
  exists x; split; [split|].
  - exact Hx.
  - intros y Hy.
    rewrite <- (Hext x Hx), <- (Hext y Hy).
    apply Hleast; auto.
  - rewrite <- Hext; auto.
Qed.

Lemma min_value_of_subset_func_ext_nat_iff {A: Type}:
  forall (P: A -> Prop) (f h: A -> nat),
    (forall x, x ∈ P -> f x = h x) ->
    min_value_of_subset Nat.le P f == min_value_of_subset Nat.le P h.
Proof.
  intros P f h Hext.
  split; intros Hmin.
  - eapply min_value_of_subset_func_ext_nat; eauto.
  - apply (min_value_of_subset_func_ext_nat P h f).
    + intros x Hx; symmetry; auto.
    + exact Hmin.
Qed.

Lemma min_value_of_subset_union_id:
  forall (P Q: nat -> Prop) n m,
    min_value_of_subset Nat.le P id n ->
    min_value_of_subset Nat.le Q id m ->
    min_value_of_subset Nat.le (P ∪ Q) id (Nat.min n m).
Proof.
  intros P Q n m Hn Hm.
  pose proof (min_union' Nat.le n m id P Q Hn Hm) as H.
  rewrite le_min_nat_min in H.
  exact H.
Qed.

Lemma min_value_nested_union_add_right:
  forall (T Q: nat -> Prop) l m,
    min_value_of_subset Nat.le
      (T ∪ min_value_of_subset Nat.le Q id) id l ->
    min_value_of_subset Nat.le
      (T ∪ min_value_of_subset Nat.le (Q ∪ [m]) id) id
      (Nat.min l m).
Proof.
  intros T Q l m [x [[Hx Hleast] Heq]].
  unfold id in Heq; subst x.
  destruct (le_dec l m) as [Hlm|Hml].
  - rewrite Nat.min_l by lia.
    exists l; split; [split|reflexivity].
    + destruct Hx as [HT|HQ].
      * left; auto.
      * right.
        pose proof (min_value_union_singleton_id Q l m HQ) as Hnew.
        rewrite Nat.min_l in Hnew by lia.
        exact Hnew.
    + intros b Hb.
      destruct Hb as [HT|HQnew].
      * apply Hleast; left; auto.
      * destruct HQnew as [y [[Hy Hqleast] Hyb]].
        unfold id in Hyb; subst b.
        destruct Hy as [HyQ|HyM].
        -- apply Hleast.
           right.
           exists y; split; [split|reflexivity].
           ++ exact HyQ.
           ++ intros z Hz; apply Hqleast; left; auto.
        -- unfold Sets.singleton in HyM; rewrite <- HyM; unfold id in *; lia.
  - rewrite Nat.min_r by lia.
    exists m; split; [split|reflexivity].
    + right.
      exists m; split; [split|reflexivity].
      * right; reflexivity.
      * intros y Hy.
        destruct Hy as [HyQ|HyM].
        -- pose proof (min_nonempty_exists id Q (ex_intro _ y HyQ)) as [q Hq].
           assert (Hlq: l <= q).
           { apply Hleast; right; exact Hq. }
           destruct Hq as [q0 [[Hq0 Hqleast] Hqeq]].
           unfold id in Hqeq; subst q.
           unfold id in Hqleast.
           specialize (Hqleast y HyQ).
           assert (Hml' : m <= l) by lia.
           eapply Nat.le_trans; [exact Hml'|].
           eapply Nat.le_trans; [exact Hlq|exact Hqleast].
        -- unfold Sets.singleton in HyM; rewrite <- HyM; unfold id in *; lia.
    + intros b Hb.
      destruct Hb as [HT|HQnew].
      * assert (Hlb: l <= b) by (apply Hleast; left; auto).
        assert (Hml': m <= l) by lia.
        eapply Nat.le_trans; eauto.
      * destruct HQnew as [y [[Hy Hqleast] Hyb]].
        unfold id in Hyb; subst b.
        destruct Hy as [HyQ|HyM].
        -- pose proof (min_nonempty_exists id Q (ex_intro _ y HyQ)) as [q Hq].
           assert (Hlq: l <= q).
           { apply Hleast; right; exact Hq. }
           destruct Hq as [q0 [[Hq0 Hqleast0] Hqeq]].
           unfold id in Hqeq; subst q.
           unfold id in Hqleast0.
           specialize (Hqleast0 y HyQ).
           assert (Hml' : m <= l) by lia.
           eapply Nat.le_trans; [exact Hml'|].
           eapply Nat.le_trans; [exact Hlq|exact Hqleast0].
        -- unfold Sets.singleton in HyM; rewrite <- HyM; unfold id in *; lia.
Qed.

Lemma min_value_nested_union_add_right_func {A: Type}:
  forall (T: nat -> Prop) (Q: A -> Prop) (f: A -> nat) l w,
    min_value_of_subset Nat.le
      (T ∪ min_value_of_subset Nat.le Q f) id l ->
    min_value_of_subset Nat.le
      (T ∪ min_value_of_subset Nat.le (Q ∪ [w]) f) id
      (Nat.min l (f w)).
Proof.
  intros T Q f l w [x [[Hx Hleast] Heq]].
  unfold id in Heq; subst x.
  destruct (le_dec l (f w)) as [Hlw|Hwl].
  - rewrite Nat.min_l by lia.
    exists l; split; [split|reflexivity].
    + destruct Hx as [HT|HQ].
      * left; auto.
      * right.
        pose proof (min_union_1_right' Nat.le l w f Q HQ) as Hnew.
        rewrite le_min_nat_min in Hnew.
        rewrite Nat.min_l in Hnew by lia.
        exact Hnew.
    + intros b Hb.
      destruct Hb as [HT|HQnew].
      * apply Hleast; left; auto.
      * destruct HQnew as [y [[Hy Hqleast] Hyb]].
        unfold id in Hyb; subst b.
        destruct Hy as [HyQ|HyW].
        -- apply Hleast.
           right.
           exists y; split; [split|reflexivity].
           ++ exact HyQ.
           ++ intros z Hz; apply Hqleast; left; auto.
        -- unfold Sets.singleton in HyW; rewrite <- HyW; unfold id in *; lia.
  - rewrite Nat.min_r by lia.
    exists (f w); split; [split|reflexivity].
    + right.
      exists w; split; [split|reflexivity].
      * right; reflexivity.
      * intros y Hy.
        destruct Hy as [HyQ|HyW].
        -- pose proof (min_nonempty_exists f Q (ex_intro _ y HyQ)) as [q Hq].
           assert (Hlq: l <= q).
           { apply Hleast; right; exact Hq. }
           destruct Hq as [q0 [[Hq0 Hqleast] Hqeq]].
           specialize (Hqleast y HyQ).
           lia.
        -- unfold Sets.singleton in HyW; rewrite <- HyW; lia.
    + intros b Hb.
      destruct Hb as [HT|HQnew].
      * assert (Hlb: l <= b) by (apply Hleast; left; auto).
        assert (Hwl': f w <= l) by lia.
        eapply Nat.le_trans; eauto.
      * destruct HQnew as [y [[Hy Hqleast] Hyb]].
        unfold id in Hyb; subst b.
        destruct Hy as [HyQ|HyW].
        -- pose proof (min_nonempty_exists f Q (ex_intro _ y HyQ)) as [q Hq].
           assert (Hlq: l <= q).
           { apply Hleast; right; exact Hq. }
           destruct Hq as [q0 [[Hq0 Hqleast0] Hqeq]].
           subst q.
           specialize (Hqleast0 y HyQ).
           assert (Hwl' : f w <= l) by lia.
           eapply Nat.le_trans; [exact Hwl'|].
           eapply Nat.le_trans; [exact Hlq|exact Hqleast0].
        -- unfold Sets.singleton in HyW; rewrite <- HyW; unfold id in *; lia.
Qed.

Lemma min_value_nested_union_add_left_func {A: Type}:
  forall (P: A -> Prop) (f: A -> nat) (Q: nat -> Prop) l w,
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le P f ∪ Q) id l ->
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (P ∪ [w]) f ∪ Q) id
      (Nat.min l (f w)).
Proof.
  intros P f Q l w H.
  rewrite Sets_union_comm.
  eapply min_value_nested_union_add_right_func.
  rewrite Sets_union_comm.
  exact H.
Qed.

Definition step_in_eset {G V E: Type} {pg: Graph G V E} (g: G) (eset: E -> Prop) (x y: V) : Prop :=
  exists e, step_aux g e x y /\ e ∈ eset.

Definition step_without_tree_in_set
  {G V E: Type}
  {pg: Graph G V E}
  (g: G) (dfstree: RootedTreeType V E)
  (eset: E -> Prop) (x y: V) :=
  exists e, step_aux g e x y /\ e ∈ eset /\ ~ evalid dfstree e.

Definition low_valid_candidate_set (u: V) (eset: E -> Prop) (s: St) : nat -> Prop :=
  min_value_of_subset Nat.le
    (step_in_eset (state_to_rootedtree g root s) eset u) s.(low)
  ∪ min_value_of_subset Nat.le
    (step_without_tree_in_set g (state_to_rootedtree g root s) eset u ∪ [u])
    s.(dfn).

Definition low_valid_v_inv_with_eset (u: V) (eset: E -> Prop) (s: St) :=
  vvalid (state_to_rootedtree g root s) u ->
  min_value_of_subset Nat.le (low_valid_candidate_set u eset s) id (s.(low) u).

Definition tree_edge_in_eset (u: V) (eset: E -> Prop) (s: St) :=
  forall e w, step_aux (state_to_rootedtree g root s) e u w -> e ∈ eset.

Definition low_valid_loop_inv (u: V) (eset: E -> Prop) (s: St) :=
  low_valid_v_inv_with_eset u eset s /\
  tree_sub_conj_P root g u s /\
  eset_in_visited g u eset s /\
  tree_edge_in_eset u eset s.

#[export] Instance low_valid_v_inv_with_eset_proper (v: V):
  Proper (Sets.equiv ==> eq ==> iff) (low_valid_v_inv_with_eset v).
Proof.
  intros eset1 eset2 Heq_eset st1 st2 Heq_st.
  subst st2.
  assert (step_in_eset (state_to_rootedtree g root st1) eset1 v ==
          step_in_eset (state_to_rootedtree g root st1) eset2 v) as Hstep.
  { firstorder. }
  assert (step_without_tree_in_set g (state_to_rootedtree g root st1) eset1 v ==
          step_without_tree_in_set g (state_to_rootedtree g root st1) eset2 v) as Hback.
  { firstorder. }
  assert
    (min_value_of_subset Nat.le
       (step_in_eset (state_to_rootedtree g root st1) eset1 v) (low st1)
     ∪ min_value_of_subset Nat.le
       (step_without_tree_in_set g (state_to_rootedtree g root st1) eset1 v ∪ [v])
       (dfn st1) ==
     min_value_of_subset Nat.le
       (step_in_eset (state_to_rootedtree g root st1) eset2 v) (low st1)
     ∪ min_value_of_subset Nat.le
       (step_without_tree_in_set g (state_to_rootedtree g root st1) eset2 v ∪ [v])
       (dfn st1)) as Hcand.
  {
    apply Sets_union_congr.
    - apply min_value_of_subset_equiv_nat; auto.
    - apply min_value_of_subset_equiv_nat.
      rewrite Hback.
      reflexivity.
  }
  split; intros H Hv; specialize (H Hv);
  unfold low_valid_v_inv_with_eset in *.
  - rewrite <- Hcand; auto.
  - rewrite Hcand; auto.
Qed.

#[export] Instance tree_edge_in_eset_proper (v: V):
  Proper (Sets.equiv ==> eq ==> iff) (tree_edge_in_eset v).
Proof.
  intros eset1 eset2 Heq_eset st1 st2 Heq_st.
  subst st2.
  sets_unfold in Heq_eset.
  split; intros H e w Hstep.
  - apply Heq_eset.
    eapply H; eauto.
  - apply Heq_eset.
    eapply H; eauto.
Qed.

#[export] Instance low_valid_loop_inv_proper (v: V):
  Proper (Sets.equiv ==> eq ==> iff) (low_valid_loop_inv v).
Proof.
  intros eset1 eset2 Heq_eset st1 st2 Heq_st.
  subst st2.
  unfold low_valid_loop_inv.
  split.
  - intros [Hlow [Htree [Hvisit Hedge]]].
    split; [|split; [|split]].
    + rewrite <- Heq_eset; exact Hlow.
    + exact Htree.
    + rewrite <- Heq_eset; exact Hvisit.
    + rewrite <- Heq_eset; exact Hedge.
  - intros [Hlow [Htree [Hvisit Hedge]]].
    split; [|split; [|split]].
    + rewrite Heq_eset; exact Hlow.
    + exact Htree.
    + rewrite Heq_eset; exact Hvisit.
    + rewrite Heq_eset; exact Hedge.
Qed.

Lemma tree_edge_in_eset_empty:
  forall u s,
    isleaf (state_to_rootedtree g root s) u ->
    tree_edge_in_eset u ∅ s.
Proof.
  unfold tree_edge_in_eset, isleaf.
  intros u s Hleaf e w Hstep.
  exfalso.
  apply (Hleaf w).
  exists e; auto.
Qed.

Lemma Tarjan_preloop_keep_isleaf (u v: V):
  Hoare (fun s : St => isleaf (state_to_rootedtree g root s) v)
        (preloop u)
        (fun _ s => isleaf (state_to_rootedtree g root s) v).
Proof.
  intro_state.
  unfold_preloop.
  subst; auto.
Qed.

Lemma tree_edge_in_eset_add_tree:
  forall s u v e done,
    is_rooted_tree (state_to_rootedtree g root s) ->
    u ∈ visited s ->
    ~ v ∈ visited s ->
    tree_edge_in_eset u done s ->
    tree_edge_in_eset u (done ∪ [e]) (set_tree' u v e s).
Proof.
  intros s u v e done Htree Hu Hv Hdone e0 w Hstep.
  destruct (classic (w = v)) as [Hwv|Hwv].
  - subst w.
    destruct Hstep; simpl in *.
    unfold t_set in ve.
    destruct (equiv_dec v v) as [_|Hneq]; [|exfalso; apply Hneq; reflexivity].
    inversion ve; subst e0.
    right; reflexivity.
  - left.
    apply Hdone with (w:=w).
    eapply tree_keep_step_aux'; eauto.
Qed.

Lemma tree_edge_in_eset_same_tree:
  forall u done s1 s2,
    state_to_rootedtree g root s1 = state_to_rootedtree g root s2 ->
    tree_edge_in_eset u done s1 ->
    tree_edge_in_eset u done s2.
Proof.
  intros u done s1 s2 HT H e w Hstep.
  apply H with (w:=w).
  rewrite HT; auto.
Qed.

Lemma tree_edge_in_eset_mono:
  forall u done done' s,
    done ⊆ done' ->
    tree_edge_in_eset u done s ->
    tree_edge_in_eset u done' s.
Proof.
  intros u done done' s Hsub H e w Hstep.
  apply Hsub.
  eapply H; eauto.
Qed.

Lemma eset_in_visited_empty:
  forall u s,
    eset_in_visited g u ∅ s.
Proof.
  intros u s x [e [_ He]].
  sets_unfold in He; tauto.
Qed.

Lemma eset_in_visited_add_visited_edge:
  forall u done s e w,
    u ∈ visited s ->
    w ∈ visited s ->
    step_aux g e u w ->
    eset_in_visited g u done s ->
    eset_in_visited g u (done ∪ [e]) s.
Proof.
  intros u done s e w Hu Hw Hstep Hdone x [e0 [Hstepx He0]].
  destruct He0 as [He0|He0].
  - apply Hdone.
    exists e0; split; auto.
  - sets_unfold in He0.
    assert (e0 = e) by (symmetry; exact He0); subst e0.
    pose proof (step_aux_unique_undirected g e u w u x
                  origin_gvalid Hstep Hstepx) as Huniq.
    destruct Huniq as [[_ Hxw]|[Hxu _]]; subst; auto.
Qed.

Lemma tree_edge_in_eset_update_low:
  forall u done s f,
    tree_edge_in_eset u done s ->
    tree_edge_in_eset u done (s <| low ::= f |>).
Proof.
  intros u done s f H.
  eapply tree_edge_in_eset_same_tree; [|exact H].
  unfold state_to_rootedtree; simpl; reflexivity.
Qed.

Lemma tree_edge_in_eset_update_bridges:
  forall u done s f,
    tree_edge_in_eset u done s ->
    tree_edge_in_eset u done (s <| bridges ::= f |>).
Proof.
  intros u done s f H.
  eapply tree_edge_in_eset_same_tree; [|exact H].
  unfold state_to_rootedtree; simpl; reflexivity.
Qed.

Lemma tree_edge_in_eset_excludes_back_branch_tree_edge:
  forall s e u w done,
    is_rooted_tree (state_to_rootedtree g root s) ->
    subgraph (state_to_rootedtree g root s) g ->
    step_aux g e u w ->
    tree_edge_in_eset u done s ->
    ~ e ∈ done ->
    s.(tedge) u <> Some e ->
    ~ evalid (state_to_rootedtree g root s) e.
Proof.
  intros s e u w done Htree Hsub Hstep Hdone Hnotdone Hparent Hevalid.
  pose proof Hevalid as Hrev.
  eapply sub_reverse with (g2:=g) in Hrev; eauto.
  2: apply Rootedtree_noemptyedge.
  2: apply OriginalGraph_stepuniqueundirected.
  destruct Hrev as [Htree_step|Htree_step].
  - apply Hnotdone.
    eapply Hdone; eauto.
  - destruct Htree_step.
    simpl in ve.
    apply Hparent; auto.
Qed.

Lemma Tarjan_keep_tree_edge_in_eset:
  forall u w parent_e done,
    Hoare
      (fun s =>
         u <> w /\
         tree_sub_conj_P root g u s /\
         tree_sub_conj_P root g w s /\
         step_aux (state_to_rootedtree g root s) parent_e u w /\
         tree_edge_in_eset u done s)
      (tarjan g w)
      (fun _ s => tree_edge_in_eset u done s).
Proof.
  intros u w parent_e done s0 ret s1 Hpre Hrun.
  destruct Hpre as
    [Huw [[Htreeu0 [Hsubu0 Hu0]]
    [[Htreew0 [Hsubw0 Hw0]] [Huwstep0 Hdone0]]]].
  assert (Htreew1: tree_sub_conj_P root g w s1).
  {
    pose proof (@Tarjan_keep_tree_subgraph_inv V E root _ eq_dec g
                  origin_gvalid g_vvalid_root w) as Hkeep.
    unfold Hoare in Hkeep.
    eapply Hkeep.
    - split; [exact Htreew0|split; [exact Hsubw0|exact Hw0]].
    - exact Hrun.
  }
  destruct Htreew1 as [Htree1 [Hsub1 Hw1]].
  assert (Huwstep1: step_aux (state_to_rootedtree g root s1) parent_e u w).
  {
    pose proof (@Tarjan_keep_step_aux_inv V E root _ eq_dec g
                  w u w parent_e) as Hkeep.
    unfold Hoare in Hkeep.
    eapply Hkeep; eauto.
  }
  unfold tree_edge_in_eset.
  intros e0 x Hstep1.
  destruct (classic (x ∈ visited s0)) as [Hx0|Hnx0].
  - destruct (classic (step_aux (state_to_rootedtree g root s0) e0 u x)) as [Hstep0|Hnostep0].
    + eapply Hdone0; eauto.
    + pose proof (@Tarjan_keep_nostep_aux_inv V E root _ eq_dec g
                    w u x e0) as Hkeep.
      unfold Hoare in Hkeep.
      specialize (Hkeep s0 ret s1).
      destruct (Hkeep (conj Hu0 (conj Hx0 Hnostep0)) Hrun) as [_ [_ Hnostep1]].
      contradiction.
  - pose proof (@Tarjan_visit_is_offspring V E root _ eq_dec g
                  origin_gvalid g_vvalid_root w x) as Hvisit.
    unfold Hoare in Hvisit.
    specialize (Hvisit s0 ret s1 (conj Hw0 Hnx0) Hrun).
    destruct Hvisit as [[_ Hnotx1]|[Hx1 Hoff]].
    + destruct Hstep1; contradiction.
    + destruct (classic (x = w)) as [Hxw|Hxw].
      * subst x.
        destruct Huwstep1 as [_ _ Hedge_parent _].
        destruct Hstep1 as [_ _ Hedge_x _].
        rewrite Hedge_parent in Hedge_x.
        inversion Hedge_x; subst e0.
        eapply Hdone0; eauto.
      * exfalso.
        assert (Hwu: offspring (state_to_rootedtree g root s1) w u).
        {
          eapply one_reachable_down_up; eauto.
          exists e0; exact Hstep1.
        }
        eapply offspring_not_father in Hwu.
        apply Hwu.
        exists parent_e; exact Huwstep1.
        Unshelve.
        all: eauto.
Qed.

Lemma Tarjan_keep_tree_edge_in_eset_prod
  (w: V) (p: (V * E) * (E -> Prop)):
  Hoare
    (fun s =>
       fst (fst p) <> w /\
       tree_sub_conj_P root g (fst (fst p)) s /\
       tree_sub_conj_P root g w s /\
       step_aux (state_to_rootedtree g root s) (snd (fst p)) (fst (fst p)) w /\
       tree_edge_in_eset (fst (fst p)) (snd p) s)
    (tarjan g w)
    (fun _ s => tree_edge_in_eset (fst (fst p)) (snd p) s).
Proof.
  destruct p as [[u e] done]; simpl.
  apply Tarjan_keep_tree_edge_in_eset.
Qed.

Lemma Tarjan_low_valid_keep_in_father_branch:
  forall a v done s,
    ~ a ∈ done ->
    s.(tedge) v = Some a ->
    is_rooted_tree (state_to_rootedtree g root s) ->
    low_valid_v_inv_with_eset v done s ->
    low_valid_v_inv_with_eset v (done ∪ [a]) s.
Proof.
  intros a v done s Hdone Hparent Htree Hlow Hv.
  specialize (Hlow Hv).
  assert (step_in_eset (state_to_rootedtree g root s) done v ==
          step_in_eset (state_to_rootedtree g root s) (done ∪ [a]) v) as Hstep.
  {
    split; intros Hx.
    - destruct Hx as [e [Hstep He]].
      exists e; split; auto. left; auto.
    - destruct Hx as [e [Hstep He]].
      destruct He as [He|He].
      + exists e; split; auto.
      + 
      sets_unfold in He.
      assert (e = a) by (symmetry; exact He); subst e.
      exfalso.
      destruct Hstep; simpl in *.
      assert ((state_to_rootedtree g root s).(edge) v =
              (state_to_rootedtree g root s).(edge) a0) as Hedge_eq.
      { simpl; rewrite Hparent, ve; reflexivity. }
      pose proof (@edge_unique V E (state_to_rootedtree g root s)
                    Htree v a0 vx vy Hedge_eq) as Hv_eq.
      subst a0.
      assert (Hself_step: step (state_to_rootedtree g root s) v v).
      { exists a; split; simpl; auto. }
      pose proof Hself_step as Hself_step'.
      eapply no_edge_refl in Hself_step; eauto.
  }
  assert (step_without_tree_in_set g (state_to_rootedtree g root s) done v ==
          step_without_tree_in_set g (state_to_rootedtree g root s) (done ∪ [a]) v) as Hnontree.
  {
    split; intros Hx.
    - destruct Hx as [e [Hst [He Hne]]].
      exists e; split; [exact Hst|].
      split; [left; exact He|exact Hne].
    - destruct Hx as [e [Hst [He Hne]]].
      destruct He as [He|He].
      + exists e; split; [exact Hst|].
        split; [exact He|exact Hne].
      + sets_unfold in He.
        assert (e = a) by (symmetry; exact He); subst e.
        exfalso; apply Hne.
        exists v; simpl; split; auto.
  }
  assert (low_valid_candidate_set v done s ==
          low_valid_candidate_set v (done ∪ [a]) s) as Hcand.
  {
    unfold low_valid_candidate_set.
    apply Sets_union_congr.
    - apply min_value_of_subset_equiv_nat; auto.
    - apply min_value_of_subset_equiv_nat.
      rewrite Hnontree; reflexivity.
  }
  rewrite <- Hcand; auto.
  Unshelve.
  all: eauto.
Qed.

Lemma Tarjan_low_loop_keep_in_father_branch:
  forall a w v done s,
    ~ a ∈ done ->
    s.(tedge) v = Some a ->
    step_aux g a v w ->
    w ∈ visited s ->
    low_valid_loop_inv v done s ->
    low_valid_loop_inv v (done ∪ [a]) s.
Proof.
  intros a w v done s Hnotdone Hparent Hstep Hw
    [Hlow [[Htree [Hsub Hv]] [Hvisit Hedge]]].
  split; [|split; [|split]].
  - eapply Tarjan_low_valid_keep_in_father_branch; eauto.
  - split; [exact Htree|split; [exact Hsub|exact Hv]].
  - eapply (eset_in_visited_add_visited_edge v done s a w); eauto.
  - eapply tree_edge_in_eset_mono; [|exact Hedge].
    intros x Hx; left; auto.
Qed.

Lemma step_in_eset_add_tree:
  forall s e v w done,
    is_rooted_tree (state_to_rootedtree g root s) ->
    step_aux (state_to_rootedtree g root s) e v w ->
    step_in_eset (state_to_rootedtree g root s) done v ∪ [w] ==
    step_in_eset (state_to_rootedtree g root s) (done ∪ [e]) v.
Proof.
  intros s e v w done Htree Hstep.
  sets_unfold; intros x; split; intros Hx.
  - destruct Hx as [Hx|Hx].
    + destruct Hx as [e0 [Hst He0]].
      exists e0; split; [exact Hst|left; exact He0].
    + unfold Sets.singleton in Hx.
      assert (x = w) by (symmetry; exact Hx); subst x.
      exists e; split; [exact Hstep|right; reflexivity].
  - destruct Hx as [e0 [Hst He0]].
    destruct He0 as [He0|He0].
    + left. exists e0; split; auto.
    + unfold Sets.singleton in He0.
      assert (e0 = e) by (symmetry; exact He0); subst e0.
      right.
      pose proof (step_aux_unique (state_to_rootedtree g root s)
                    e v w v x Htree Hstep Hst) as [_ Hwx].
      exact Hwx.
Qed.

Lemma step_without_tree_in_set_add_tree:
  forall s e v w done,
    step_aux (state_to_rootedtree g root s) e v w ->
    step_without_tree_in_set g (state_to_rootedtree g root s) done v ==
    step_without_tree_in_set g (state_to_rootedtree g root s) (done ∪ [e]) v.
Proof.
  intros s e v w done HstepT.
  sets_unfold; intros x; split; intros Hx.
  - destruct Hx as [e0 [Hst [He0 Hne0]]].
    exists e0; split; [exact Hst|split; [left; exact He0|exact Hne0]].
  - destruct Hx as [e0 [Hst [He0 Hne0]]].
    destruct He0 as [He0|He0].
    + exists e0; split; [exact Hst|split; auto].
    + unfold Sets.singleton in He0.
      assert (e0 = e) by (symmetry; exact He0); subst e0.
      exfalso; apply Hne0.
      destruct HstepT; exists w; split; auto.
Qed.

Lemma step_without_tree_in_set_add_back:
  forall s e v w done,
    step_aux g e v w ->
    ~ evalid (state_to_rootedtree g root s) e ->
    (step_without_tree_in_set g (state_to_rootedtree g root s) done v ∪ [v] ∪ [w]) ==
    (step_without_tree_in_set g (state_to_rootedtree g root s) (done ∪ [e]) v ∪ [v]).
Proof.
  intros s e v w done Hstep Hne.
  sets_unfold; intros x; split; intros Hx.
  - destruct Hx as [[Hx|Hx]|Hx].
    + destruct Hx as [e0 [Hst [He0 Hne0]]].
      left. exists e0; split; [exact Hst|split; auto].
      left; auto.
    + right; auto.
    + unfold Sets.singleton in Hx; subst x.
      left. exists e; split; [exact Hstep|split; auto].
      right; reflexivity.
  - destruct Hx as [Hx|Hx].
    + destruct Hx as [e0 [Hst [He0 Hne0]]].
      destruct He0 as [He0|He0].
      * left; left. exists e0; split; [exact Hst|split; auto].
      * unfold Sets.singleton in He0.
        assert (e0 = e) by (symmetry; exact He0); subst e0.
        pose proof (step_aux_unique_undirected g e v w v x
                      origin_gvalid Hstep Hst) as Huniq.
        destruct Huniq as [[_ Hwx]|[Hvx _]].
        -- right; exact Hwx.
        -- left; right; exact Hvx.
    + left; right; auto.
Qed.

Lemma Tarjan_low_valid_keep_in_back_branch:
  forall s0 s e w v done,
    is_rooted_tree (state_to_rootedtree g root s0) ->
    step_aux g e v w ->
    ~ evalid (state_to_rootedtree g root s0) e ->
    s = s0 <| low ::= (fun low0 => v !-> Nat.min (low0 v) (dfn s0 w); low0) |>
    ->
    low_valid_v_inv_with_eset v done s0 ->
    low_valid_v_inv_with_eset v (done ∪ [e]) s.
Proof.
  intros s0 s e w v done Htree Hstep Hne Hs Hinv Hv.
  assert (HT: state_to_rootedtree g root s = state_to_rootedtree g root s0).
  { subst s; unfold state_to_rootedtree; simpl; reflexivity. }
  rewrite HT in Hv.
  specialize (Hinv Hv).
  subst s; simpl.
  unfold t_set.
  destruct (equiv_dec v v) as [_|Hneq]; [|exfalso; apply Hneq; reflexivity].
  assert (step_in_eset (state_to_rootedtree g root s0) (done ∪ [e]) v ==
          step_in_eset (state_to_rootedtree g root s0) done v) as Hstepdone.
  {
    sets_unfold; intros x; split; unfold step_in_eset; intros Hx.
    - destruct Hx as [e0 [Hst He0]].
      destruct He0 as [He0|He0].
      + exists e0; split; auto.
      + unfold Sets.singleton in He0.
        assert (e0 = e) by (symmetry; exact He0); subst e0.
        exfalso; apply Hne.
        destruct Hst; exists x; split; auto.
    - destruct Hx as [e0 [Hst He0]].
      exists e0; split; auto. left; auto.
  }
  assert
    (min_value_of_subset Nat.le
       (step_in_eset (state_to_rootedtree g root s0) (done ∪ [e]) v)
       (v !-> Nat.min (low s0 v) (dfn s0 w); low s0) ==
     min_value_of_subset Nat.le
       (step_in_eset (state_to_rootedtree g root s0) done v)
       (low s0)) as Htreevals.
  {
    pose proof (min_value_of_subset_equiv_nat
                  (step_in_eset (state_to_rootedtree g root s0) (done ∪ [e]) v)
                  (step_in_eset (state_to_rootedtree g root s0) done v)
                  (v !-> Nat.min (low s0 v) (dfn s0 w); low s0)
                  Hstepdone) as Hmv.
    sets_unfold in Hmv.
    split; intros Hmin.
    - eapply min_value_of_subset_func_ext_nat.
      2: { apply Hmv; exact Hmin. }
      intros x Hx.
      destruct Hx as [e0 [Hst _]].
      destruct Hst.
      unfold t_set.
      destruct (equiv_dec v x) as [Heqvx|Hneqvx]; auto.
      exfalso.
      assert (Heq' : v = x) by apply Heqvx; subst x.
      assert (Hself_step: step (state_to_rootedtree g root s0) v v).
      { exists e0; split; simpl; auto. }
      pose proof Hself_step as Hself_step'.
      eapply no_edge_refl in Hself_step; eauto.
    - apply Hmv.
      eapply min_value_of_subset_func_ext_nat.
      2: exact Hmin.
      intros x Hx.
      destruct Hx as [e0 [Hst _]].
      destruct Hst.
      unfold t_set.
      destruct (equiv_dec v x) as [Heqvx|Hneqvx]; auto.
      exfalso.
      assert (Heq' : v = x) by apply Heqvx; subst x.
      assert (Hself_step: step (state_to_rootedtree g root s0) v v).
      { exists e0; split; simpl; auto. }
      pose proof Hself_step as Hself_step'.
      eapply no_edge_refl in Hself_step; eauto.
  }
  assert
    (min_value_of_subset Nat.le
       (step_without_tree_in_set g (state_to_rootedtree g root s0) (done ∪ [e]) v ∪ [v])
       (dfn s0) ==
     min_value_of_subset Nat.le
       ((step_without_tree_in_set g (state_to_rootedtree g root s0) done v ∪ [v]) ∪ [w])
       (dfn s0)) as Hnontreevals.
  {
    apply min_value_of_subset_equiv_nat.
    symmetry.
    apply step_without_tree_in_set_add_back; auto.
  }
  unfold low_valid_candidate_set in *.
  rewrite Htreevals.
  rewrite Hnontreevals.
  replace (Nat.min (low s0 v) (dfn s0 w)) with
    (Nat.min (low s0 v) (dfn s0 w)) by reflexivity.
  eapply min_value_nested_union_add_right_func.
  exact Hinv.
  Unshelve.
  all: eauto.
Qed.

Lemma Tarjan_low_loop_keep_in_back_branch:
  forall s0 s e w v done,
    step_aux g e v w ->
    w ∈ visited s0 ->
    ~ evalid (state_to_rootedtree g root s0) e ->
    s = s0 <| low ::= (fun low0 => v !-> Nat.min (low0 v) (dfn s0 w); low0) |>
    ->
    low_valid_loop_inv v done s0 ->
    low_valid_loop_inv v (done ∪ [e]) s.
Proof.
  intros s0 s e w v done Hstep Hw Hne Hs
    [Hlow [[Htree [Hsub Hv]] [Hvisit Hedge]]].
  split; [|split; [|split]].
  - eapply Tarjan_low_valid_keep_in_back_branch; eauto.
  - subst s; simpl.
    split; [exact Htree|split; [exact Hsub|exact Hv]].
  - subst s; simpl.
    eapply (eset_in_visited_add_visited_edge v done s0 e w); eauto.
  - subst s.
    apply tree_edge_in_eset_update_low.
    eapply tree_edge_in_eset_mono; [|exact Hedge].
    intros x Hx; left; auto.
Qed.

Lemma Tarjan_low_valid_keep_in_son_branch:
  forall s0 s e w v done,
    is_rooted_tree (state_to_rootedtree g root s0) ->
    step_aux (state_to_rootedtree g root s0) e v w ->
    s = s0 <| low ::= (fun low0 => v !-> Nat.min (low0 v) (low s0 w); low0) |>
    ->
    low_valid_v_inv_with_eset v done s0 ->
    low_valid_v_inv_with_eset v (done ∪ [e]) s.
Proof.
  intros s0 s e w v done Htree HstepT Hs Hinv Hv.
  assert (HT: state_to_rootedtree g root s = state_to_rootedtree g root s0).
  { subst s; unfold state_to_rootedtree; simpl; reflexivity. }
  rewrite HT in Hv.
  specialize (Hinv Hv).
  subst s; simpl.
  unfold t_set.
  destruct (equiv_dec v v) as [_|Hneq]; [|exfalso; apply Hneq; reflexivity].
  assert (Hvw: v <> w).
  {
    intro Hvw; subst w.
    assert (Hself_step: step (state_to_rootedtree g root s0) v v).
    { exists e; exact HstepT. }
    pose proof Hself_step as Hself_step'.
    eapply no_edge_refl in Hself_step; eauto.
  }
  assert
    (min_value_of_subset Nat.le
       (step_in_eset (state_to_rootedtree g root s0) (done ∪ [e]) v)
       (v !-> Nat.min (low s0 v) (low s0 w); low s0) ==
     min_value_of_subset Nat.le
       (step_in_eset (state_to_rootedtree g root s0) done v ∪ [w])
       (low s0)) as Htreevals.
  {
    pose proof (min_value_of_subset_equiv_nat
                  (step_in_eset (state_to_rootedtree g root s0) (done ∪ [e]) v)
                  (step_in_eset (state_to_rootedtree g root s0) done v ∪ [w])
                  (v !-> Nat.min (low s0 v) (low s0 w); low s0)) as Hmv.
    assert (Hstepdone:
      step_in_eset (state_to_rootedtree g root s0) (done ∪ [e]) v ==
      step_in_eset (state_to_rootedtree g root s0) done v ∪ [w]).
    {
      symmetry.
      apply step_in_eset_add_tree; auto.
    }
    specialize (Hmv Hstepdone).
    sets_unfold in Hmv.
    split; intros Hmin.
    - eapply min_value_of_subset_func_ext_nat.
      2: { apply Hmv; exact Hmin. }
      intros x Hx.
      destruct Hx as [Hx|Hx].
      + destruct Hx as [e0 [Hst _]].
        destruct Hst.
        unfold t_set.
        destruct (equiv_dec v x) as [Heqvx|Hneqvx].
        * exfalso.
          assert (Heq' : v = x) by apply Heqvx; subst x.
          assert (Hself_step: step (state_to_rootedtree g root s0) v v).
          { exists e0; split; simpl; auto. }
          pose proof Hself_step as Hself_step'.
          eapply no_edge_refl in Hself_step; eauto.
        * reflexivity.
      + unfold Sets.singleton in Hx.
        assert (x = w) by (symmetry; exact Hx); subst x.
        unfold t_set.
        destruct (equiv_dec v w) as [Heqvw|Hneqvw].
        * exfalso; apply Hvw; apply Heqvw.
        * reflexivity.
    - apply Hmv.
      eapply min_value_of_subset_func_ext_nat.
      2: exact Hmin.
      intros x Hx.
      destruct Hx as [Hx|Hx].
      + destruct Hx as [e0 [Hst _]].
        destruct Hst.
        unfold t_set.
        destruct (equiv_dec v x) as [Heqvx|Hneqvx].
        * exfalso.
          assert (Heq' : v = x) by apply Heqvx; subst x.
          assert (Hself_step: step (state_to_rootedtree g root s0) v v).
          { exists e0; split; simpl; auto. }
          pose proof Hself_step as Hself_step'.
          eapply no_edge_refl in Hself_step; eauto.
        * reflexivity.
      + unfold Sets.singleton in Hx.
        assert (x = w) by (symmetry; exact Hx); subst x.
        unfold t_set.
        destruct (equiv_dec v w) as [Heqvw|Hneqvw].
        * exfalso; apply Hvw; apply Heqvw.
        * reflexivity.
  }
  assert
    (min_value_of_subset Nat.le
       (step_without_tree_in_set g (state_to_rootedtree g root s0) (done ∪ [e]) v ∪ [v])
       (dfn s0) ==
     min_value_of_subset Nat.le
       (step_without_tree_in_set g (state_to_rootedtree g root s0) done v ∪ [v])
       (dfn s0)) as Hnontreevals.
  {
    apply min_value_of_subset_equiv_nat.
    rewrite <- (step_without_tree_in_set_add_tree s0 e v w done HstepT).
    reflexivity.
  }
  unfold low_valid_candidate_set in *.
  rewrite Htreevals.
  rewrite Hnontreevals.
  eapply min_value_nested_union_add_left_func.
  exact Hinv.
  Unshelve.
  all: eauto.
Qed.

Lemma Tarjan_post_rec_low_loop_son_branch:
  forall u w e done,
    Hoare
      (fun s =>
         low_valid_v_inv_with_eset u done s /\
         tree_sub_conj_P root g u s /\
         eset_in_visited g u done s /\
         tree_edge_in_eset u (done ∪ [e]) s /\
         step_aux (state_to_rootedtree g root s) e u w /\
         step_aux g e u w /\
         w ∈ visited s)
      (post_rec e u w)
      (fun _ s => low_valid_loop_inv u (done ∪ [e]) s).
Proof.
  intros u w e done.
  intro_state.
  destruct H as
    [Hlow [[Htree [Hsub Hu]]
    [Hvisit [Hedge_union [HstepT [Hstepg Hw]]]]]].
  unfold post_rec; unfold_op.
  hoare_auto_s;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end;
  subst; simpl.
  - assert (Hlow_loop:
      low_valid_loop_inv u (done ∪ [e])
        (s0 <| low ::= (fun low0 : V -> nat => u !-> Nat.min (low0 u) (low s0 w); low0) |>)).
    {
      split; [|split; [|split]].
      - eapply Tarjan_low_valid_keep_in_son_branch; eauto.
      - split; [exact Htree|split; [exact Hsub|exact Hu]].
      - eapply (eset_in_visited_add_visited_edge u done s0 e w); eauto.
      - apply tree_edge_in_eset_update_low.
        exact Hedge_union.
    }
    exact Hlow_loop.
  - assert (Hlow_loop:
      low_valid_loop_inv u (done ∪ [e])
        (s0 <| low ::= (fun low0 : V -> nat => u !-> Nat.min (low0 u) (low s0 w); low0) |>)).
    {
      split; [|split; [|split]].
      - eapply Tarjan_low_valid_keep_in_son_branch; eauto.
      - split; [exact Htree|split; [exact Hsub|exact Hu]].
      - eapply (eset_in_visited_add_visited_edge u done s0 e w); eauto.
      - apply tree_edge_in_eset_update_low.
        exact Hedge_union.
    }
    destruct Hlow_loop as [Hlow_loop [Htree_loop [Hvisit_loop Hedge_loop]]].
    split; [|split; [|split]].
    + unfold low_valid_v_inv_with_eset, low_valid_candidate_set in *; simpl.
      exact Hlow_loop.
    + destruct Htree_loop as [Htree' [Hsub' Hu']].
      simpl; split; [exact Htree'|split; [exact Hsub'|exact Hu']].
    + unfold eset_in_visited in *; simpl; exact Hvisit_loop.
    + eapply tree_edge_in_eset_update_bridges.
      exact Hedge_loop.
  Unshelve.
  all: eauto.
Qed.

Lemma Tarjan_keep_low_valid_v_inv_with_eset_set_tree:
  forall s u w e done,
    tree_sub_conj_P root g u s ->
    low_valid_v_inv_with_eset u done s ->
    eset_in_visited g u done s ->
    ~ w ∈ visited s ->
    step_aux g e u w ->
    ~ e ∈ done ->
    low_valid_v_inv_with_eset u done (set_tree' u w e s).
Proof.
  intros s u w e done [Htree [Hsub Hu]] Hinv Hdonevis Hwv Hstepg Hnotdone Hv.
  specialize (Hinv Hu).
  assert (Hstep_set:
    step_in_eset (state_to_rootedtree g root (set_tree' u w e s)) done u ==
    step_in_eset (state_to_rootedtree g root s) done u).
  {
    sets_unfold; intros x; split; intros Hx.
    - destruct Hx as [e0 [Hst He0]].
      destruct (classic (x = w)) as [Hxw|Hxw].
      + subst x.
        destruct Hst; simpl in *.
        unfold t_set in ve.
        destruct (equiv_dec w w) as [Heq|Hneq]; [|exfalso; apply Hneq; reflexivity].
        inversion ve; subst e0.
        contradiction.
      + exists e0; split; [|exact He0].
        eapply tree_keep_step_aux'; eauto.
    - destruct Hx as [e0 [Hst He0]].
      exists e0; split; [|exact He0].
      destruct Hst; split; simpl in *.
      + left; auto.
      + left; auto.
      + unfold t_set.
        destruct (equiv_dec w x) as [Hwx|Hnwx].
        * assert (w = x) by apply Hwx; subst x.
          exfalso; apply Hwv; exact vy.
        * exact ve.
      + unfold t_set.
        destruct (equiv_dec w x) as [Hwx|Hnwx].
        * assert (w = x) by apply Hwx; subst x.
          exfalso; apply Hwv; exact vy.
        * exact vp.
  }
  assert (Htreevals:
    min_value_of_subset Nat.le
      (step_in_eset (state_to_rootedtree g root (set_tree' u w e s)) done u)
      (low (set_tree' u w e s)) ==
    min_value_of_subset Nat.le
      (step_in_eset (state_to_rootedtree g root s) done u)
      (low s)).
  {
    simpl.
    apply min_value_of_subset_equiv_nat; auto.
  }
  assert (Hnontree_set:
    step_without_tree_in_set g (state_to_rootedtree g root (set_tree' u w e s)) done u ==
    step_without_tree_in_set g (state_to_rootedtree g root s) done u).
  {
    sets_unfold; intros x; split; intros Hx.
    - destruct Hx as [e0 [Horig [He0 Hne]]].
      exists e0; split; [exact Horig|split; [exact He0|]].
      intro Hevalid.
      apply Hne.
      apply tree_add_edge_keep; auto.
    - destruct Hx as [e0 [Horig [He0 Hne]]].
      exists e0; split; [exact Horig|split; [exact He0|]].
      intro Hevalid.
      destruct Hevalid as [z [Hzv Hze]]; simpl in *.
      unfold t_set in Hze.
      destruct (equiv_dec w z) as [Hwz|Hnwz].
      + assert (w = z) by apply Hwz; subst z.
        inversion Hze; subst e0.
        contradiction.
      + apply Hne.
        exists z; split; auto.
        destruct Hzv as [Hzv|Hzv]; auto.
        unfold Sets.singleton in Hzv.
        assert (z = w) by (symmetry; exact Hzv); contradiction.
  }
  assert (Hnontreevals:
    min_value_of_subset Nat.le
      (step_without_tree_in_set g
         (state_to_rootedtree g root (set_tree' u w e s)) done u ∪ [u])
      (dfn (set_tree' u w e s)) ==
    min_value_of_subset Nat.le
      (step_without_tree_in_set g (state_to_rootedtree g root s) done u ∪ [u])
      (dfn s)).
  {
    simpl.
    apply min_value_of_subset_equiv_nat.
    rewrite Hnontree_set; reflexivity.
  }
  unfold low_valid_v_inv_with_eset, low_valid_candidate_set in *.
  simpl.
  rewrite Htreevals.
  rewrite Hnontreevals.
  exact Hinv.
Qed.

Lemma low_valid_v_inv_with_eset_update_bridges:
  forall u done s f,
    low_valid_v_inv_with_eset u done s ->
    low_valid_v_inv_with_eset u done (s <| bridges ::= f |>).
Proof.
  intros u done s f Hlow.
  unfold low_valid_v_inv_with_eset, low_valid_candidate_set in *.
  simpl.
  exact Hlow.
Qed.

Lemma Tarjan_keep_low_valid_v_inv_with_eset:
  forall u w done,
    Hoare
      (fun s =>
         u <> w /\
         tree_sub_conj_P root g u s /\
         tree_sub_conj_P root g w s /\
         low_valid_v_inv_with_eset u done s /\
         eset_in_visited g u done s /\
         (forall e, e ∈ done -> ~ step_aux g e u w))
      (tarjan g w)
      (fun _ s => low_valid_v_inv_with_eset u done s).
Proof.
  intros u w done s0 ret s1 Hpre Hrun.
  destruct Hpre as
    [Huw [[Htreeu0 [Hsubu0 Hu0]]
    [Htreew0 [Hinv0 [Hdonevis Hnotdonew]]]]].
  assert (Htreew1: tree_sub_conj_P root g w s1).
  {
    pose proof (@Tarjan_keep_tree_subgraph_inv V E root _ eq_dec g
                  origin_gvalid g_vvalid_root w) as Hkeep.
    unfold Hoare in Hkeep.
    eapply Hkeep; eauto.
  }
  destruct Htreew1 as [Htree1 [Hsub1 Hw1]].
  assert (Hlowu: low s1 u = low s0 u).
  {
    pose proof (@Tarjan_keep_low_inv V E _ eq_dec g w u (low s0 u)) as Hkeep.
    unfold Hoare in Hkeep.
    specialize (Hkeep s0 ret s1).
    destruct (Hkeep) as [_ Hlow]; eauto.
  }
  assert (Hstep_set:
    step_in_eset (state_to_rootedtree g root s1) done u ==
    step_in_eset (state_to_rootedtree g root s0) done u).
  {
    sets_unfold; intros x; split; intros Hx.
    - destruct Hx as [e0 [Hst1 He0]].
      assert (Horig: step_aux g e0 u x) by (apply Hsub1; exact Hst1).
      assert (Hxvis0: x ∈ visited s0).
      { apply Hdonevis. exists e0; split; auto. }
      destruct (classic (step_aux (state_to_rootedtree g root s0) e0 u x)) as [Hst0|Hnost0].
      + exists e0; split; auto.
      + exfalso.
        pose proof (@Tarjan_keep_nostep_aux_inv V E root _ eq_dec g w u x e0) as Hkeep.
        unfold Hoare in Hkeep.
        specialize (Hkeep s0 ret s1).
        destruct (Hkeep) as [_ [_ Hnost1]]; eauto.
    - destruct Hx as [e0 [Hst0 He0]].
      pose proof (@Tarjan_keep_step_aux_inv V E root _ eq_dec g w u x e0) as Hkeep.
      unfold Hoare in Hkeep.
      exists e0; split; [eapply Hkeep; eauto|auto].
  }
  assert (Htreevals:
    min_value_of_subset Nat.le
      (step_in_eset (state_to_rootedtree g root s1) done u) (low s1) ==
    min_value_of_subset Nat.le
      (step_in_eset (state_to_rootedtree g root s0) done u) (low s0)).
  {
    pose proof (min_value_of_subset_equiv_nat
                  (step_in_eset (state_to_rootedtree g root s1) done u)
                  (step_in_eset (state_to_rootedtree g root s0) done u)
                  (low s1) Hstep_set) as Hmv.
    sets_unfold in Hmv.
    assert (Hlow_ext:
      forall x,
        x ∈ step_in_eset (state_to_rootedtree g root s0) done u ->
        low s1 x = low s0 x).
    {
      intros x [e0 [Hst0 He0]].
      assert (Horig: step_aux g e0 u x) by (apply Hsubu0; exact Hst0).
      assert (Hxvis0: x ∈ visited s0).
      { apply Hdonevis. exists e0; split; auto. }
      assert (Hxw: x <> w).
      {
        intro Hxw; subst x.
        specialize (Hnotdonew e0 He0).
        contradiction.
      }
      pose proof (@Tarjan_keep_low_inv V E _ eq_dec g w x (low s0 x)) as Hkeep.
      unfold Hoare in Hkeep.
      specialize (Hkeep s0 ret s1).
      destruct (Hkeep) as [_ Hlow]; eauto.
    }
    split; intros Hmin.
    - eapply min_value_of_subset_func_ext_nat.
      2: { apply Hmv; exact Hmin. }
      exact Hlow_ext.
    - apply Hmv.
      eapply min_value_of_subset_func_ext_nat.
      2: exact Hmin.
      intros x Hx; symmetry; apply Hlow_ext; auto.
  }
  assert (Hnontree_set:
    step_without_tree_in_set g (state_to_rootedtree g root s1) done u ==
    step_without_tree_in_set g (state_to_rootedtree g root s0) done u).
  {
    sets_unfold; intros x; split; intros Hx.
    - destruct Hx as [e0 [Horig [He0 Hne1]]].
      exists e0; split; [exact Horig|split; [exact He0|]].
      intro Hevalid0; apply Hne1.
      pose proof (@Tarjan_keep_edge_inv V E root _ eq_dec g w e0) as Hkeep.
      unfold Hoare in Hkeep.
      eapply Hkeep; eauto.
    - destruct Hx as [e0 [Horig [He0 Hne0]]].
      exists e0; split; [exact Horig|split; [exact He0|]].
      intro Hevalid1.
      assert (Hxvis0: x ∈ visited s0).
      { apply Hdonevis. exists e0; split; auto. }
      assert (Hxw: x <> w).
      {
        intro Hxw; subst x.
        specialize (Hnotdonew e0 He0).
        contradiction.
      }
      pose proof Hevalid1 as Hrev.
      eapply sub_reverse with (g2:=g) in Hrev; eauto.
      2: apply Rootedtree_noemptyedge.
      2: apply OriginalGraph_stepuniqueundirected.
      destruct Hrev as [Hst1|Hst1].
      + assert (~ step_aux (state_to_rootedtree g root s1) e0 u x) as Hnost1.
        {
          assert (Hnost0: ~ step_aux (state_to_rootedtree g root s0) e0 u x).
          {
            intro Hst0; apply Hne0.
            destruct Hst0; exists x; split; auto.
          }
          pose proof (@Tarjan_keep_nostep_aux_inv V E root _ eq_dec g w u x e0) as Hkeep.
          unfold Hoare in Hkeep.
          specialize (Hkeep s0 ret s1).
          destruct (Hkeep (conj Hu0 (conj Hxvis0 Hnost0)) Hrun) as [_ [_ Hnost1]].
          exact Hnost1.
        }
        contradiction.
      + assert (~ step_aux (state_to_rootedtree g root s1) e0 x u) as Hnost1.
        {
          assert (Hnost0: ~ step_aux (state_to_rootedtree g root s0) e0 x u).
          {
            intro Hst0; apply Hne0.
            destruct Hst0; exists u; split; auto.
          }
          pose proof (@Tarjan_keep_nostep_aux_inv V E root _ eq_dec g w x u e0) as Hkeep.
          unfold Hoare in Hkeep.
          specialize (Hkeep s0 ret s1).
          destruct (Hkeep (conj Hxvis0 (conj Hu0 Hnost0)) Hrun) as [_ [_ Hnost1]].
          exact Hnost1.
        }
        contradiction.
  }
  assert (Hnontreevals:
    min_value_of_subset Nat.le
      (step_without_tree_in_set g (state_to_rootedtree g root s1) done u ∪ [u])
      (dfn s1) ==
    min_value_of_subset Nat.le
      (step_without_tree_in_set g (state_to_rootedtree g root s0) done u ∪ [u])
      (dfn s0)).
  {
    pose proof (min_value_of_subset_equiv_nat
                  (step_without_tree_in_set g (state_to_rootedtree g root s1) done u ∪ [u])
                  (step_without_tree_in_set g (state_to_rootedtree g root s0) done u ∪ [u])
                  (dfn s1)) as Hmv.
    assert (Hset:
      step_without_tree_in_set g (state_to_rootedtree g root s1) done u ∪ [u] ==
      step_without_tree_in_set g (state_to_rootedtree g root s0) done u ∪ [u]).
    { rewrite Hnontree_set; reflexivity. }
    specialize (Hmv Hset).
    sets_unfold in Hmv.
    assert (Hdfn_ext:
      forall x,
        x ∈ step_without_tree_in_set g (state_to_rootedtree g root s0) done u ∪ [u] ->
        dfn s1 x = dfn s0 x).
    {
      intros x Hx.
      destruct Hx as [Hx|Hx].
      - destruct Hx as [e0 [Horig [He0 _]]].
        assert (Hxvis0: x ∈ visited s0).
        { apply Hdonevis. exists e0; split; auto. }
        assert (Hxw: x <> w).
        {
          intro Hxw; subst x.
          specialize (Hnotdonew e0 He0).
          contradiction.
        }
        pose proof (@Tarjan_keep_dfn_inv V E _ eq_dec g w x (dfn s0 x)) as Hkeep.
        unfold Hoare in Hkeep.
        specialize (Hkeep s0 ret s1).
        destruct (Hkeep) as [_ Hdfn]; eauto.
      - unfold Sets.singleton in Hx.
        assert (x = u) by (symmetry; exact Hx); subst x.
        pose proof (@Tarjan_keep_dfn_inv V E _ eq_dec g w u (dfn s0 u)) as Hkeep.
        unfold Hoare in Hkeep.
        specialize (Hkeep s0 ret s1).
        destruct (Hkeep) as [_ Hdfn]; eauto.
    }
    split; intros Hmin.
    - eapply min_value_of_subset_func_ext_nat.
      2: { apply Hmv; exact Hmin. }
      exact Hdfn_ext.
    - apply Hmv.
      eapply min_value_of_subset_func_ext_nat.
      2: exact Hmin.
      intros x Hx; symmetry; apply Hdfn_ext; auto.
  }
  unfold low_valid_v_inv_with_eset in *.
  intros _.
  rewrite Hlowu.
  specialize (Hinv0 Hu0).
  unfold low_valid_candidate_set in *.
  rewrite Htreevals.
  rewrite Hnontreevals.
  exact Hinv0.
Qed.

Lemma Tarjan_keep_low_valid_v_inv_with_eset_prod
  (w: V) (p: V * (E -> Prop)):
  Hoare
    (fun s =>
       fst p <> w /\
       tree_sub_conj_P root g (fst p) s /\
       tree_sub_conj_P root g w s /\
       low_valid_v_inv_with_eset (fst p) (snd p) s /\
       eset_in_visited g (fst p) (snd p) s /\
       (forall e, e ∈ snd p -> ~ step_aux g e (fst p) w))
    (tarjan g w)
    (fun _ s => low_valid_v_inv_with_eset (fst p) (snd p) s).
Proof.
  destruct p as [u done]; simpl.
  apply Tarjan_keep_low_valid_v_inv_with_eset.
Qed.

Lemma Tarjan_low_valid_init_state:
  forall v s,
  low_eq_dfn v s ->
  low_valid_v_inv_with_eset v ∅ s.
Proof.
  intros v s Hs Hv.
  rewrite Hs.
  exists (dfn s v); split; [split|reflexivity].
  - right.
    exists v; split; [split|reflexivity].
    + right; reflexivity.
    + intros x Hx.
      destruct Hx as [Hempty|Hx].
      * destruct Hempty as [e [_ He]]; sets_unfold in He; tauto.
      * sets_unfold in Hx; subst; lia.
  - intros n Hn.
    destruct Hn as [Hn|Hn].
    + destruct Hn as [x [[Hx _] Heq]].
      destruct Hx as [e [_ He]]; sets_unfold in He; tauto.
    + destruct Hn as [x [[Hx _] Heq]].
      destruct Hx as [Hempty|Hx].
      * destruct Hempty as [e [_ He]]; sets_unfold in He; tauto.
      * sets_unfold in Hx; rewrite <- Heq; subst; lia.
Qed.

Lemma Tarjan_low_valid_final_state:
  forall v s,
  subgraph (state_to_rootedtree g root s) g ->
  low_valid_v_inv_with_eset v (fun e0: E => exists v0, original_step_aux g e0 v v0) s ->
  vvalid (state_to_rootedtree g root s) v ->
  low_valid_v g (state_to_rootedtree g root s) s.(dfn) v s.(low).
Proof.
  intros v s Hsub Hinv Hv.
  apply Hinv in Hv; clear Hinv.
  assert (step_in_eset (state_to_rootedtree g root s)
            (fun e0 : E => exists v0 : V, original_step_aux g e0 v v0) v ==
          step (state_to_rootedtree g root s) v) as Htree.
  {
    split; unfold step_in_eset; intros.
    - destruct H as [e0 []].
      eapply step_trivial; eauto.
    - destruct H as [e0 Hstep].
      exists e0; split; auto.
      exists a.
      apply Hsub; auto.
  }
  assert (step_without_tree_in_set g (state_to_rootedtree g root s)
            (fun e0 : E => exists v0 : V, original_step_aux g e0 v v0) v ==
          step_without_tree g (state_to_rootedtree g root s) v) as Hnontree.
  {
    split; intros H.
    - unfold step_without_tree_in_set in H.
      unfold step_without_tree.
      destruct H as [e0 [? [_ ?]]].
      exists e0; split; auto.
    - unfold step_without_tree in H.
      unfold step_without_tree_in_set.
      destruct H as [e0 [? ?]].
      exists e0; split; [auto|split; auto].
      exists a; auto.
  }
  unfold low_valid_v.
  assert
    (min_value_of_subset Nat.le
       (step_in_eset (state_to_rootedtree g root s)
          (fun e0 : E => exists v0 : V, original_step_aux g e0 v v0) v)
       (low s)
     ∪ min_value_of_subset Nat.le
       (step_without_tree_in_set g (state_to_rootedtree g root s)
          (fun e0 : E => exists v0 : V, original_step_aux g e0 v v0) v ∪ [v])
       (dfn s) ==
     min_value_of_subset Nat.le (step (state_to_rootedtree g root s) v)
       (low s)
     ∪ min_value_of_subset Nat.le
       (step_without_tree g (state_to_rootedtree g root s) v ∪ [v])
       (dfn s)) as Hcand.
  {
    apply Sets_union_congr.
    - apply min_value_of_subset_equiv_nat; auto.
    - apply min_value_of_subset_equiv_nat.
      rewrite Hnontree.
      reflexivity.
  }
  pose proof (min_value_of_subset_equiv_nat _ _ id Hcand) as Houter.
  sets_unfold in Houter.
  apply Houter; auto.
Qed.

Lemma Tarjan_preloop_low_eq_dfn (u: V):
  Hoare (fun _ : St => True)
        (preloop u)
        (fun _ s => low_eq_dfn u s).
Proof.
  unfold_preloop;
  subst; unfold low_eq_dfn; simpl;
  unfold t_set; equiv_dec_refl u; auto.
Qed.

Lemma Tarjan_low_valid_single_inv (u: V):
  Hoare
    (fun s => tree_sub_conj_P root g u s /\
              isleaf (state_to_rootedtree g root s) u)
    (tarjan g u)
    (fun _ s =>
       low_valid_v_inv_with_eset u
         (fun e0 : E => exists v0, step_aux g e0 u v0) s).
Proof.
  unfold tarjan.
  hoare_fix_nolv_fs_auto V.
  {
    forall_n 6.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_low_valid_v_inv_with_eset_prod (V * (E -> Prop))%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv V @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_subgraph_inv unit @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_step_aux_inv_prod (V * V * E)%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_eset_in_visited_inv' (V * (E -> Prop))%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_edge_in_eset_prod ((V * E) * (E -> Prop))%type @tarjan.
  }
  intros W IHa IH u0 _.
  unfold_Forall IHa.
  clear u; rename u0 into u.
  unfold tarjan_f.
  eapply Hoare_bind.
  {
    hoare_conj_n 2.
    * hoare_cons_pre Tarjan_preloop_low_eq_dfn.
    * hoare_cons_pre Tarjan_preloop_keep_tree_sub_conj.
      intros; apply H.
    * hoare_cons_pre Tarjan_preloop_keep_isleaf.
      intros; apply H.
  }
  simpl; intros _.
  eapply Hoare_conseq.
  3: {
    unfold loop_body, forset.
    eapply Hoare_forset with
      (P := fun done s => low_valid_loop_inv u done s).
    - apply low_valid_loop_inv_proper.
    - intros done a Hdone_sub Ha_univ Ha_not_done.
      intro_state.
      unfold forset_body.
      hoare_auto_s.
      + unfold for_branch1.
        eapply Hoare_bind with
          (Q := fun _ s =>
            low_valid_v_inv_with_eset u done s /\
            tree_sub_conj_P root g u s /\
            eset_in_visited g u done s /\
            tree_sub_conj_P root g a0 s /\
            isleaf (state_to_rootedtree g root s) a0 /\
            step_aux (state_to_rootedtree g root s) a u a0 /\
            tree_edge_in_eset u (done ∪ [a]) s).
        {
          unfold set_tree.
          intro_state.
          match goal with
          | Hpre : low_valid_loop_inv u done _ |- _ =>
              destruct Hpre as [Hlow [[Htree [Hsub Hu]] [Hvisit Hedge]]]
          end.
          hoare_auto_s.
          subst.
          split; [|split; [|split; [|split; [|split; [|split]]]]].
          - eapply Tarjan_keep_low_valid_v_inv_with_eset_set_tree.
            + split; [exact Htree|split; [exact Hsub|exact Hu]].
            + exact Hlow.
            + exact Hvisit.
            + exact H1.
            + exact H0.
            + exact Ha_not_done.
          - split; [|split].
            + apply tree_property_keep; auto.
              * unfold not; intros; subst a0; auto.
                destruct Htree; simpl in *.
                exfalso; apply H1; apply root_valid.
              * eapply step_vvalid2; eauto.
              * unfold not; intros Hex.
                destruct Hex as [x [Hx Heq]].
                assert (evalid (state_to_rootedtree g root s0) a) as Hevalid.
                { exists x; split; auto. }
                eapply sub_reverse with (g2:=g) in Hevalid; eauto.
                2: apply Rootedtree_noemptyedge.
                2: apply OriginalGraph_stepuniqueundirected.
                destruct Hevalid as [Hst|Hst];
                destruct Hst as [Hvx Hvy _ _].
                -- apply H1; exact Hvy.
                -- apply H1; exact Hvx.
            + apply tree_subgraph_keep; auto.
            + left; auto.
          - unfold eset_in_visited in *; simpl.
            intros x Hex; left; apply Hvisit; exact Hex.
          - split; [|split].
            + apply tree_property_keep; auto.
              * unfold not; intros; subst a0; auto.
                destruct Htree; simpl in *.
                exfalso; apply H1; apply root_valid.
              * eapply step_vvalid2; eauto.
              * unfold not; intros Hex.
                destruct Hex as [x [Hx Heq]].
                assert (evalid (state_to_rootedtree g root s0) a) as Hevalid.
                { exists x; split; auto. }
                eapply sub_reverse with (g2:=g) in Hevalid; eauto.
                2: apply Rootedtree_noemptyedge.
                2: apply OriginalGraph_stepuniqueundirected.
                destruct Hevalid as [Hst|Hst];
                destruct Hst as [Hvx Hvy _ _].
                -- apply H1; exact Hvy.
                -- apply H1; exact Hvx.
            + apply tree_subgraph_keep; auto.
            + right; reflexivity.
          - apply tree_add_vertex_is_leaf; auto.
          - apply step_easy; auto.
          - eapply tree_edge_in_eset_add_tree; eauto.
        }
        simpl; intros _.
        eapply Hoare_bind with
          (Q := fun _ s =>
            low_valid_v_inv_with_eset u done s /\
            tree_sub_conj_P root g a0 s /\
            u ∈ visited s /\
            step_aux (state_to_rootedtree g root s) a u a0 /\
            eset_in_visited g u done s /\
            tree_edge_in_eset u (done ∪ [a]) s).
        {
          hoare_conj_n 5.
          * hoare_cons_pre (IHa0 _ (u, done)).
            intros s [Hlowu [Htreeu [Hvisitu [Htree_w [Hleaf_w [HstepT Hedge_union]]]]]].
            split; [|split; [|split; [|split; [|split]]]].
            -- intro Huw; subst a0.
               destruct Htreeu as [Hrtu _].
               assert (Hself: step (state_to_rootedtree g root s) u u).
               { exists a; exact HstepT. }
               assert (~ step (state_to_rootedtree g root s) u u) as Hno.
               { eapply no_edge_refl; eauto. }
               contradiction.
            -- exact Htreeu.
            -- exact Htree_w.
            -- exact Hlowu.
            -- exact Hvisitu.
            -- intros e0 He0 Hstepuw.
               destruct H as [_ [_ [Hvisit0 _]]].
               apply H1.
               apply Hvisit0.
               exists e0; split; auto.
          * hoare_cons_pre (IHa2 _ tt).
          * hoare_cons_pre (IHa1 _ u).
            intros s [Hlowu [Htreeu [Hvisitu [Htree_w [Hleaf_w [HstepT Hedge_union]]]]]].
            destruct Htreeu as [_ [_ Hu]]; exact Hu.
          * hoare_cons_pre (IHa3 _ (u, a0, a)).
          * hoare_cons_pre (IHa4 _ (u, done)).
          * hoare_cons_pre (IHa5 _ ((u, a), done ∪ [a])).
            intros s [Hlowu [Htreeu [Hvisitu [Htree_w [Hleaf_w [HstepT Hedge_union]]]]]].
            split; [|split; [|split; [|split]]].
            -- intro Huw; subst a0.
               destruct Htreeu as [Hrtu _].
               assert (Hself: step (state_to_rootedtree g root s) u u).
               { exists a; exact HstepT. }
               assert (~ step (state_to_rootedtree g root s) u u) as Hno.
               { eapply no_edge_refl; eauto. }
               contradiction.
            -- exact Htreeu.
            -- exact Htree_w.
            -- exact HstepT.
            -- exact Hedge_union.
        }
        simpl; intros _.
        intro_state.
        match goal with
        | Hpre : low_valid_v_inv_with_eset u done _ /\ _ |- _ =>
            destruct Hpre as [Hlowu [Htree_w [Hu_vis [HstepT [Hvisitu Hedge_union]]]]]
        end.
        assert (Htreeu: tree_sub_conj_P root g u s1).
        { eapply tree_easy; [exact Htree_w|exact Hu_vis]. }
        destruct Htreeu as [Htreeu_rt [Hsubu Hu_u]].
        destruct Htree_w as [_ [_ Hw]].
        unfold post_rec; unfold_op.
        hoare_auto_s;
        repeat match goal with
        | Hc : _ /\ _ |- _ => destruct Hc
        end;
        subst; simpl.
        * assert (Hloop:
            low_valid_loop_inv u (done ∪ [a])
              (s1 <| low ::= (fun low0 : V -> nat => u !-> Nat.min (low0 u) (low s1 a0); low0) |>)).
          {
            split; [|split; [|split]].
            - eapply Tarjan_low_valid_keep_in_son_branch.
              + exact Htreeu_rt.
              + exact HstepT.
              + reflexivity.
              + exact Hlowu.
            - split; [exact Htreeu_rt|split; [exact Hsubu|exact Hu_u]].
            - eapply (eset_in_visited_add_visited_edge u done s1 a a0); eauto.
            - apply tree_edge_in_eset_update_low.
              exact Hedge_union.
          }
          destruct Hloop as [Hlow_loop [Htree_loop [Hvisit_loop Hedge_loop]]].
          split; [|split; [|split]].
          -- unfold low_valid_v_inv_with_eset, low_valid_candidate_set in *; simpl.
             exact Hlow_loop.
          -- destruct Htree_loop as [Htree' [Hsub' Hu']].
             simpl; split; [exact Htree'|split; [exact Hsub'|exact Hu']].
          -- unfold eset_in_visited in *; simpl; exact Hvisit_loop.
          -- eapply tree_edge_in_eset_update_bridges.
             exact Hedge_loop.
          Unshelve.
          all: eauto.
        * split; [|split; [|split]].
          -- eapply Tarjan_low_valid_keep_in_son_branch.
             ++ exact Htreeu_rt.
             ++ exact HstepT.
             ++ reflexivity.
             ++ exact Hlowu.
          -- split; [exact Htreeu_rt|split; [exact Hsubu|exact Hu_u]].
          -- eapply (eset_in_visited_add_visited_edge u done s1 a a0); eauto.
          -- apply tree_edge_in_eset_update_low.
             exact Hedge_union.
      + unfold for_branch2.
        unfold_op.
        hoare_auto_s.
        repeat match goal with
        | Hc : _ /\ _ |- _ => destruct Hc
        end.
        subst.
        repeat match goal with
        | Hnn : ~ ~ _ |- _ => apply NNPP in Hnn
        end.
        match goal with
        | Hpre : low_valid_loop_inv u done _ |- _ =>
            destruct Hpre as [Hlow [[Htree [Hsub Hu]] [Hvisit Hedge]]]
        end.
        match goal with
        | Hrt : is_rooted_tree (state_to_rootedtree g root ?st) |- _ =>
            assert (Hne: ~ evalid (state_to_rootedtree g root st) a)
            by (eapply tree_edge_in_eset_excludes_back_branch_tree_edge; eauto)
        end.
        match goal with
        | Hstep : step_aux g a u ?w,
          Hvisited : ?w ∈ visited ?st |- _ =>
            eapply (Tarjan_low_loop_keep_in_back_branch st _ a w u done);
            [exact Hstep|exact Hvisited|eassumption|reflexivity|]
        end;
        split; [exact Hlow|split; [split; [exact Htree|split; [exact Hsub|exact Hu]]|split; [exact Hvisit|exact Hedge]]].
      + repeat match goal with
        | Hc : _ /\ _ |- _ => destruct Hc
        end;
        subst.
        repeat match goal with
        | Hnn : ~ ~ _ |- _ => apply NNPP in Hnn
        end.
        match goal with
        | Hpre : low_valid_loop_inv u done ?st,
          Hstep : step_aux g a u ?w,
          Hvisited : ?w ∈ visited ?st,
          Hparent : tedge ?st u = Some a |- _ =>
            eapply (Tarjan_low_loop_keep_in_father_branch a w u done st);
            [exact Ha_not_done|exact Hparent|exact Hstep|exact Hvisited|exact Hpre]
        end.
  }
  - intros s [Hloweq [Htree Hleaf]].
    split; [|split; [|split]].
    + apply Tarjan_low_valid_init_state; auto.
    + exact Htree.
    + apply eset_in_visited_empty.
    + apply tree_edge_in_eset_empty; auto.
  - intros.
    destruct H as [Hlow _].
    exact Hlow.
Qed.

Notation T := (state_to_rootedtree g root).
Notation St := (@St V E).
Notation Tag := (@Tag V).
Notation TR := (@TR Tag St).

Definition tree_sub_leaf_in : St * TR -> Prop :=
  fun '(s, tr) =>
    forall v, v ∈ s.(visited) ->
      tr |= have
        (ts↑ (In v)
          (fun s => tree_sub_conj_P root g v s /\
                    isleaf (state_to_rootedtree g root s) v)).

Definition tree_sub_leaf_in_except (u: V): St * TR -> Prop :=
  fun '(s, tr) =>
    forall v, v ∈ s.(visited) -> v <> u ->
      tr |= have
        (ts↑ (In v)
          (fun s => tree_sub_conj_P root g v s /\
                    isleaf (state_to_rootedtree g root s) v)).

Lemma Tarjan_track_in_tree_sub_leaf_in (u: V):
  Hoare
    (fun '(s, tr) =>
       tree_sub_leaf_in_except u (s, tr) /\
       tree_sub_conj_P root g u s /\
       isleaf (state_to_rootedtree g root s) u)
    (track (In u))
    (fun _ => tree_sub_leaf_in).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
  intros v Hv.
  destruct (classic (v = u)); subst.
  - rewrite app_have_atom; right.
    rewrite singleton_have_atom; split; tauto.
  - rewrite app_have_atom; left.
    apply H; auto.
Qed.

Lemma Tarjan_preloop_tree_sub_leaf_in (u: V):
  Hoare (fun '(s, tr) => tree_sub_leaf_in (s, tr))
        ((↑ (preloop u))%ghost)
        (fun _ => tree_sub_leaf_in).
Proof.
  intro_state_pair.
  unfold preloop; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? []]; subst; auto.
Qed.

Lemma Tarjan_set_tree_tree_sub_leaf_in (u v: V) (e: E):
  Hoare (fun '(s, tr) => tree_sub_leaf_in (s, tr))
        ((↑ (set_tree u v e))%ghost)
        (fun _ => tree_sub_leaf_in_except v).
Proof.
  unfold set_tree; intro_state_pair.
  hoare_auto_G; my_destruct H.
  simpl; intros _ ? [? []]; subst; auto.
  intros w Hw Hneq.
  destruct Hw; [auto | sets_unfold in H0; subst]; congruence.
Qed.

Lemma Tarjan_post_rec_tree_sub_leaf_in (u v: V) (e: E):
  Hoare (fun '(s, tr) => tree_sub_leaf_in (s, tr))
        ((↑ (post_rec e u v))%ghost)
        (fun _ => tree_sub_leaf_in).
Proof.
  intro_state_pair.
  unfold post_rec; unfold_op.
  hoare_auto_G.
  simpl; intros _ s0 [? [? [|[]]]]; subst; auto.
Qed.

Lemma Tarjan_track_out_tree_sub_leaf_in (u: V):
  Hoare (fun '(s, tr) => tree_sub_leaf_in (s, tr))
        (track (Out u))
        (fun _ => tree_sub_leaf_in).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; auto.
  intros v Hv.
  apply app_have_atom; left; auto.
Qed.

Lemma Tarjan_set_tree_isleaf' (u v: V) (e: E):
  Hoare
    ((fun '(s, _) =>
        tree_sub_conj_P root g u s /\ ~ v ∈ s.(visited)): St * TR -> Prop)
    ((↑ (set_tree u v e))%ghost)
    (fun _ '(s, _) => isleaf (state_to_rootedtree g root s) v).
Proof.
  eapply Hoare_toG
    with (P := fun s => tree_sub_conj_P root g u s /\ ~ v ∈ s.(visited))
         (Q := fun _ s => isleaf (state_to_rootedtree g root s) v).
  - eapply Gequiv_set_tree.
  - unfold set_tree, set_tree'.
    intro_state.
    hoare_cons_post Hoare_update'.
    intros _ s1 Hs1.
    subst s1.
    destruct H as [[Htree [Hsub Hu]] Hnot].
    apply tree_add_vertex_is_leaf; auto.
  - tauto.
Qed.

Lemma Tarjan_root_isleaf_init_state:
  isleaf (state_to_rootedtree g root (initSt root)) root.
Proof.
  unfold isleaf; unfold not; intros x Hstep.
  destruct Hstep as [e Hstep].
  destruct Hstep; simpl in *.
  unfold t_empty in ve.
  inversion ve.
Qed.

Theorem Tarjan_tree_sub_leaf_in_inv (u: V):
  Hoare
    (fun '(s, tr) =>
       tree_sub_leaf_in_except u (s, tr) /\
       tree_sub_conj_P root g u s /\
       isleaf (state_to_rootedtree g root s) u)
    (tarjan' g u)
    (fun _ => tree_sub_leaf_in).
Proof.
  unfold tarjan'. unfold trace_call.
  hoare_fix_nolv_fs_auto V.
  {
    forall_n 2.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv' V @tarjan'.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_sub_conj' unit @tarjan'.
  }
  clear u; intros W IHa IH u _; unfold_Forall IHa.
  unfold trace_call_f, tarjan_f'.
  eapply Hoare_bind.
  {
    hoare_conj_n 1.
    * hoare_cons_pre Tarjan_track_in_tree_sub_leaf_in.
    * hoare_cons_pre Tarjan_track_in_keep_tree_sub_conj';
      intros (s, tr) [_ [Htree _]]; exact Htree.
  }
  simpl; intros _.
  hoare_bind'' Tarjan_track_out_tree_sub_leaf_in.
  eapply Hoare_bind.
  {
    hoare_conj_n 1.
    * hoare_cons_pre Tarjan_preloop_tree_sub_leaf_in.
    * hoare_cons_pre Tarjan_preloop_keep_tree_sub_conj';
      intros (s, tr) [Hleafin Htree]; exact Htree.
  }
  simpl; intros _.
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
      * apply Tarjan_post_rec_tree_sub_leaf_in.
      * apply Tarjan_post_rec_keep_tree_sub_conj'. }
    eapply Hoare_bind.
    {
      hoare_conj_n 2.
      * hoare_cons_pre Tarjan_set_tree_tree_sub_leaf_in; intros; subst; tauto.
      * hoare_cons_pre Tarjan_set_tree_keep_tree_sub_conj';
        intros; subst; destruct H as [Hleafin Htree];
        first
          [ refine (conj Htree (conj _ _)); eauto
          | exact Htree
          | eauto ].
      * hoare_cons_pre Tarjan_set_tree_isleaf';
        intros; subst; destruct H as [Hleafin Htree];
        first
          [ refine (conj Htree _); eauto
          | exact Htree
          | eauto ].
    }
    simpl; intros _.
    hoare_conj_n 1.
    * hoare_cons_pre IH; intros (s0, tr); intros; split; tauto.
    * eapply Hoare_conseq_post. 2: {
        apply Hoare_conj.
        - hoare_cons_pre (IHa0 _ u); intros (s0, tr); tauto.
        - hoare_cons_pre IHa1; intros (s0, tr); intros; tauto.
      }
      simpl; intros _ (s0, tr); intros; eapply tree_easy; apply H3.
  - hoare_auto_s.
    hoare_bind'' IH0.
    unfold for_branch2; unfold_op.
    hoare_auto_G.
    simpl; intros _ s1 [? [? [|[]]]]; subst; auto.
  - tauto.
Qed.

Theorem Tarjan_tree_sub_leaf_in:
  Hoare (fun '(s, tr) => s = initSt root /\ tr = nil)
        (tarjan' g root)
        (fun _ => tree_sub_leaf_in).
Proof.
  hoare_cons_pre Tarjan_tree_sub_leaf_in_inv.
  intros; destruct s; destruct H; subst; split_r 2; auto.
  - intros; congruence.
  - apply tree_subgraph_init_state; auto.
  - apply Tarjan_root_isleaf_init_state.
Qed.

Lemma Tarjan_low_valid_trace_in_implies (v: V):
  Hoare (fun '(s, tr) => tr = nil)
        (tarjan' g root)
        (fun _ '(_, tr) =>
           trace_in_implies
             (fun u s =>
                tree_sub_conj_P root g u s /\
                isleaf (state_to_rootedtree g root s) u)
             (fun u s =>
                low_valid_v_inv_with_eset u
                  (fun e0 : E => exists v0, step_aux g e0 u v0) s)
             v tr).
Proof.
  eapply Hoare_trace_in_implies.
  simpl. intros.
  hoare_cons_pre Tarjan_low_valid_single_inv.
Qed.

Definition full_eset (v: V): E -> Prop :=
  fun e => exists w, step_aux g e v w.

Definition closed_low_valid (v: V) (s: St): Prop :=
  tree_sub_conj_P root g v s /\
  neighbor_visit g v s /\
  low_valid_v_inv_with_eset v (full_eset v) s.

Definition processed_low_valid (u: V) (s: St): Prop :=
  forall v, v <> u -> offspring (state_to_rootedtree g root s) u v ->
    closed_low_valid v s.

Definition processed_low_valid_except_noedge (u w: V) (s: St): Prop :=
  forall v, v <> u -> v <> w ->
    offspring (state_to_rootedtree g root s) u v ->
    closed_low_valid v s /\
    (forall e, e ∈ full_eset v -> ~ step_aux g e v w).

Definition low_valid_top_down (u: V) (s: St): Prop :=
  forall v, offspring (state_to_rootedtree g root s) u v ->
    closed_low_valid v s.

Lemma eset_in_visited_full_neighbor:
  forall u s,
    eset_in_visited g u (full_eset u) s ->
    neighbor_visit g u s.
Proof.
  intros u s H x [e Hstep].
  apply H.
  exists e; split; [exact Hstep|].
  exists x; exact Hstep.
Qed.

Lemma closed_low_valid_to_final:
  forall v s,
    subgraph (state_to_rootedtree g root s) g ->
    closed_low_valid v s ->
    vvalid (state_to_rootedtree g root s) v ->
    low_valid_v g (state_to_rootedtree g root s) s.(dfn) v s.(low).
Proof.
  intros v s Hsub [_ [_ Hlow]] Hv.
  eapply Tarjan_low_valid_final_state; eauto.
Qed.

Lemma closed_low_valid_from_loop_full:
  forall u s,
    low_valid_loop_inv u (full_eset u) s ->
    closed_low_valid u s.
Proof.
  intros u s [Hlow [Htree [Hvisit _]]].
  split; [exact Htree|split; [|exact Hlow]].
  apply eset_in_visited_full_neighbor; auto.
Qed.

Lemma low_valid_v_inv_update_low_not_child:
  forall v u n s,
    v <> u ->
    is_rooted_tree (state_to_rootedtree g root s) ->
    (forall e, ~ step_aux (state_to_rootedtree g root s) e v u) ->
    low_valid_v_inv_with_eset v (full_eset v) s ->
    low_valid_v_inv_with_eset v (full_eset v)
      (s <| low ::= (fun low0 => u !-> Nat.min (low0 u) n; low0) |>).
Proof.
  intros v u n s Hvu Htree Hnochild Hlow Hv.
  assert (HT:
    state_to_rootedtree g root
      (s <| low ::= (fun low0 : V -> nat => u !-> Nat.min (low0 u) n; low0) |>) =
    state_to_rootedtree g root s).
  { unfold state_to_rootedtree; simpl; reflexivity. }
  rewrite HT in Hv.
  specialize (Hlow Hv).
  simpl.
  unfold t_set.
  destruct (equiv_dec u v) as [Heq|Hneq].
  - exfalso; apply Hvu.
    symmetry; apply Heq.
  - assert (Htreevals:
      min_value_of_subset Nat.le
        (step_in_eset (state_to_rootedtree g root s) (full_eset v) v)
        (u !-> Nat.min (low s u) n; low s) ==
      min_value_of_subset Nat.le
        (step_in_eset (state_to_rootedtree g root s) (full_eset v) v)
        (low s)).
    {
      apply min_value_of_subset_func_ext_nat_iff.
      intros x [e [Hstep _]].
      unfold t_set.
      destruct (equiv_dec u x) as [Hux|Hux]; auto.
      assert (u = x) by apply Hux; subst x.
      exfalso; eapply Hnochild; eauto.
    }
    unfold low_valid_v_inv_with_eset, low_valid_candidate_set in *.
    simpl.
    rewrite Htreevals.
    exact Hlow.
Qed.

Lemma closed_low_valid_update_low_not_child:
  forall v u n s,
    v <> u ->
    is_rooted_tree (state_to_rootedtree g root s) ->
    (forall e, ~ step_aux (state_to_rootedtree g root s) e v u) ->
    closed_low_valid v s ->
    closed_low_valid v
      (s <| low ::= (fun low0 => u !-> Nat.min (low0 u) n; low0) |>).
Proof.
  intros v u n s Hvu Htree Hnochild [Htreev [Hvisit Hlow]].
  split; [|split].
  - destruct Htreev as [Hrt [Hsub Hv]].
    simpl; split; [exact Hrt|split; [exact Hsub|exact Hv]].
  - intros x Hstep.
    simpl; apply Hvisit; auto.
  - eapply low_valid_v_inv_update_low_not_child; eauto.
Qed.

Lemma closed_low_valid_update_low_offspring:
  forall v u n s,
    v <> u ->
    offspring (state_to_rootedtree g root s) u v ->
    is_rooted_tree (state_to_rootedtree g root s) ->
    closed_low_valid v s ->
    closed_low_valid v
      (s <| low ::= (fun low0 => u !-> Nat.min (low0 u) n; low0) |>).
Proof.
  intros v u n s Hvu Hoff Htree Hclosed.
  eapply closed_low_valid_update_low_not_child; eauto.
  intros e Hstep.
  assert (Hnot: ~ step (state_to_rootedtree g root s) v u).
  { eapply offspring_not_father; eauto. }
  apply Hnot.
  exists e; exact Hstep.
  Unshelve.
  all: eauto.
Qed.

Lemma closed_low_valid_update_bridges:
  forall v s f,
    closed_low_valid v s ->
    closed_low_valid v (s <| bridges ::= f |>).
Proof.
  intros v s f [Htreev [Hvisit Hlow]].
  split; [|split].
  - destruct Htreev as [Hrt [Hsub Hv]].
    simpl; split; [exact Hrt|split; [exact Hsub|exact Hv]].
  - intros x Hstep.
    simpl; apply Hvisit; auto.
  - apply low_valid_v_inv_with_eset_update_bridges.
    exact Hlow.
Qed.

Lemma processed_low_valid_leaf:
  forall u s,
    isleaf (state_to_rootedtree g root s) u ->
    processed_low_valid u s.
Proof.
  unfold processed_low_valid.
  intros u s Hleaf v Hvu Hoff.
  unfold offspring in Hoff.
  apply reachable_1n in Hoff as [[w [Hstep _]]|Huv].
  - exfalso.
    apply (Hleaf w).
    exact Hstep.
  - exfalso.
    apply Hvu.
    symmetry; exact Huv.
Qed.

Lemma processed_low_valid_update_low:
  forall u n s,
    is_rooted_tree (state_to_rootedtree g root s) ->
    processed_low_valid u s ->
    processed_low_valid u
      (s <| low ::= (fun low0 => u !-> Nat.min (low0 u) n; low0) |>).
Proof.
  unfold processed_low_valid.
  intros u n s Htree Hproc v Hvu Hoff.
  simpl in Hoff.
  eapply closed_low_valid_update_low_offspring; eauto.
Qed.

Lemma processed_low_valid_update_bridges:
  forall u s f,
    processed_low_valid u s ->
    processed_low_valid u (s <| bridges ::= f |>).
Proof.
  unfold processed_low_valid.
  intros u s f Hproc v Hvu Hoff.
  simpl in Hoff.
  apply closed_low_valid_update_bridges.
  eapply Hproc; eauto.
Qed.

Lemma Tarjan_post_rec_keep_processed_low_valid:
  forall u w e,
    Hoare
      (fun s =>
         processed_low_valid u s /\
         tree_sub_conj_P root g u s)
      (post_rec e u w)
      (fun _ s => processed_low_valid u s).
Proof.
  intros u w e.
  intro_state.
  destruct H as [Hproc [Htree [Hsub Hu]]].
  unfold post_rec; unfold_op.
  hoare_auto_s;
  repeat match goal with
  | Hc : _ /\ _ |- _ => destruct Hc
  end;
  subst; simpl.
  - unfold processed_low_valid in *.
    intros v Hvu Hoff; simpl in Hoff.
    change (closed_low_valid v
      ((s0 <| low ::= (fun low0 : V -> nat =>
              u !-> Nat.min (low0 u) (low s0 w); low0) |>)
       <| bridges ::= (fun bridges0 : list E => e :: bridges0) |>)).
    apply closed_low_valid_update_bridges.
    eapply closed_low_valid_update_low_offspring; eauto.
  - unfold processed_low_valid in *.
    intros v Hvu Hoff; simpl in Hoff.
    change (closed_low_valid v
      (s0 <| low ::= (fun low0 : V -> nat =>
              u !-> Nat.min (low0 u) (low s0 w); low0) |>)).
    eapply closed_low_valid_update_low_offspring; eauto.
Qed.

Lemma low_valid_v_inv_set_tree_irrelevant:
  forall s parent child e v,
    tree_sub_conj_P root g parent s ->
    closed_low_valid v s ->
    ~ child ∈ visited s ->
    step_aux g e parent child ->
    low_valid_v_inv_with_eset v (full_eset v) (set_tree' parent child e s).
Proof.
  intros s parent child e v [Hrt [Hsub Hparent]]
    [[Hrtv [Hsubv Hvold]] [Hneigh Hlow]] Hchild Hstep Hvnew.
  assert (Hno_v_child: forall e0, ~ step_aux g e0 v child).
  {
    intros e0 Hvc.
    apply Hchild.
    apply Hneigh.
    exists e0; exact Hvc.
  }
  assert (Hvchild: v <> child).
  { intro Hvc; subst child; contradiction. }
  specialize (Hlow Hvold).
  assert (Hstep_set:
    step_in_eset (state_to_rootedtree g root (set_tree' parent child e s))
      (full_eset v) v ==
    step_in_eset (state_to_rootedtree g root s) (full_eset v) v).
  {
    sets_unfold; intros x; split; intros Hx.
    - destruct Hx as [e0 [Hst Hfull]].
      destruct (classic (x = child)) as [Hxc|Hxc].
      + subst x.
        destruct Hst; simpl in *.
        unfold t_set in ve, vp.
        destruct (equiv_dec child child) as [_|Hneq];
          [|exfalso; apply Hneq; reflexivity].
        inversion ve; subst e0.
        assert (parent = v).
        {
          destruct (equiv_dec child child) as [Heq|Hneq'];
            [|exfalso; apply Hneq'; reflexivity].
          exact vp.
        }
        subst parent.
        exfalso; eapply Hno_v_child; eauto.
      + exists e0; split; [|exact Hfull].
        eapply tree_keep_step_aux'; eauto.
    - destruct Hx as [e0 [Hst Hfull]].
      exists e0; split; [|exact Hfull].
      destruct Hst; split; simpl in *; try (left; auto);
      unfold t_set;
      destruct (equiv_dec child x) as [Hcx|Hcx].
      + assert (child = x) by apply Hcx; subst x.
        exfalso; apply Hchild; exact vy.
      + exact ve.
      + assert (child = x) by apply Hcx; subst x.
        exfalso; apply Hchild; exact vy.
      + exact vp.
  }
  assert (Htreevals:
    min_value_of_subset Nat.le
      (step_in_eset (state_to_rootedtree g root (set_tree' parent child e s))
        (full_eset v) v)
      (low (set_tree' parent child e s)) ==
    min_value_of_subset Nat.le
      (step_in_eset (state_to_rootedtree g root s) (full_eset v) v)
      (low s)).
  {
    simpl.
    apply min_value_of_subset_equiv_nat; auto.
  }
  assert (Hnontree_set:
    step_without_tree_in_set g
      (state_to_rootedtree g root (set_tree' parent child e s))
      (full_eset v) v ==
    step_without_tree_in_set g
      (state_to_rootedtree g root s) (full_eset v) v).
  {
    sets_unfold; intros x; split; intros Hx.
    - destruct Hx as [e0 [Horig [Hfull Hne]]].
      exists e0; split; [exact Horig|split; [exact Hfull|]].
      intro Heold.
      apply Hne.
      apply tree_add_edge_keep; auto.
    - destruct Hx as [e0 [Horig [Hfull Hne]]].
      exists e0; split; [exact Horig|split; [exact Hfull|]].
      intro Henew.
      destruct Henew as [z [Hzv Hze]].
      simpl in *.
      unfold t_set in Hze.
      destruct (equiv_dec child z) as [Hcz|Hcz].
      + assert (child = z) by apply Hcz; subst z.
        inversion Hze; subst e0.
        destruct Hfull as [w Hvw].
        pose proof (step_aux_unique_undirected g e parent child v w
                      origin_gvalid Hstep Hvw) as Huniq.
        destruct Huniq as [[Hpv Hcw]|[Hpw Hcv]].
        * subst parent w.
          eapply Hno_v_child; eauto.
        * subst child.
          contradiction.
      + apply Hne.
        exists z; split; auto.
        destruct Hzv as [Hzv|Hzv]; auto.
        unfold Sets.singleton in Hzv.
        assert (z = child) by (symmetry; exact Hzv); subst z.
        exfalso; apply Hcz; reflexivity.
  }
  assert (Hnontreevals:
    min_value_of_subset Nat.le
      (step_without_tree_in_set g
         (state_to_rootedtree g root (set_tree' parent child e s))
         (full_eset v) v ∪ [v])
      (dfn (set_tree' parent child e s)) ==
    min_value_of_subset Nat.le
      (step_without_tree_in_set g
         (state_to_rootedtree g root s) (full_eset v) v ∪ [v])
      (dfn s)).
  {
    simpl.
    apply min_value_of_subset_equiv_nat.
    rewrite Hnontree_set; reflexivity.
  }
  unfold low_valid_v_inv_with_eset, low_valid_candidate_set in *.
  simpl.
  rewrite Htreevals.
  rewrite Hnontreevals.
  exact Hlow.
Qed.

Lemma closed_low_valid_set_tree_irrelevant:
  forall s parent child e v,
    tree_sub_conj_P root g parent s ->
    closed_low_valid v s ->
    ~ child ∈ visited s ->
    step_aux g e parent child ->
    closed_low_valid v (set_tree' parent child e s).
Proof.
  intros s parent child e v Hparent Hclosed Hchild Hstep.
  destruct Hclosed as [[Hrtv [Hsubv Hv]] [Hneigh Hlow]].
  split; [|split].
  - destruct Hparent as [Hrt [Hsub Hpar]].
    simpl; split; [|split].
    + apply tree_property_keep; auto.
      * intro Hcr; subst child.
        apply Hchild.
        destruct Hrt; simpl in *; apply root_valid.
      * eapply step_vvalid2; eauto.
      * unfold not; intros Hex.
        destruct Hex as [x [Hx Heq]].
        assert (evalid (state_to_rootedtree g root s) e) as Hevalid.
        { exists x; split; auto. }
        eapply sub_reverse with (g2:=g) in Hevalid; eauto.
        2: apply Rootedtree_noemptyedge.
        2: apply OriginalGraph_stepuniqueundirected.
        destruct Hevalid as [Hst|Hst];
        destruct Hst as [Hvx Hvy _ _].
        -- apply Hchild; exact Hvy.
        -- apply Hchild; exact Hvx.
    + apply tree_subgraph_keep; auto.
    + left; exact Hv.
  - intros x Hx.
    simpl; left.
    apply Hneigh; exact Hx.
  - eapply low_valid_v_inv_set_tree_irrelevant.
    + exact Hparent.
    + split; [split; [exact Hrtv|split; [exact Hsubv|exact Hv]]|].
      split; [exact Hneigh|exact Hlow].
    + exact Hchild.
    + exact Hstep.
Qed.

Lemma processed_low_valid_except_noedge_set_tree:
  forall s u w e,
    tree_sub_conj_P root g u s ->
    processed_low_valid u s ->
    ~ w ∈ s.(visited) ->
    step_aux g e u w ->
    processed_low_valid_except_noedge u w (set_tree' u w e s).
Proof.
  unfold processed_low_valid, processed_low_valid_except_noedge.
  intros s u w e [Htree [Hsub Hu]] Hproc Hnotw Hstep v Hvu Hvw Hoff.
  assert (Hoff_old: offspring (state_to_rootedtree g root s) u v).
  {
    exact (@tree_keep_offspring' V E root _ eq_dec g origin_gvalid
             g_vvalid_root s u v u w e Htree Hvw Hu Hnotw Hoff).
  }
  pose proof (Hproc v Hvu Hoff_old) as Hclosed_old.
  split.
  - eapply closed_low_valid_set_tree_irrelevant; eauto.
    split; [exact Htree|split; [exact Hsub|exact Hu]].
  - intros e0 Hfull Hstep_v_w.
    destruct Hclosed_old as [_ [Hneigh _]].
    apply Hnotw.
    apply Hneigh.
    exists e0; exact Hstep_v_w.
Qed.

Lemma Tarjan_keep_closed_low_valid:
  forall v w,
    Hoare
      (fun s =>
         v <> w /\
         closed_low_valid v s /\
         tree_sub_conj_P root g w s /\
         (forall e, e ∈ full_eset v -> ~ step_aux g e v w))
      (tarjan g w)
      (fun _ s => closed_low_valid v s).
Proof.
  intros v w s0 ret s1 Hpre Hrun.
  destruct Hpre as [Hvw [Hclosed [Htreew Hnoedge]]].
  destruct Hclosed as [Htreev [Hvisitv Hlowv]].
  split; [|split].
  - destruct Htreev as [Hrt0 [Hsub0 Hv0]].
    assert (Htreew1: tree_sub_conj_P root g w s1).
    {
      pose proof (@Tarjan_keep_tree_subgraph_inv V E root _ eq_dec g
                    origin_gvalid g_vvalid_root w) as Hkeep_tree.
      unfold Hoare in Hkeep_tree.
      eapply Hkeep_tree; eauto.
    }
    destruct Htreew1 as [Hrt1 [Hsub1 _]].
    assert (Hv1: v ∈ visited s1).
    {
      pose proof (Tarjan_keep_visited_inv g w v) as Hkeep_visit.
      unfold Hoare in Hkeep_visit.
      eapply Hkeep_visit; eauto.
    }
    split; [exact Hrt1|split; [exact Hsub1|exact Hv1]].
  - intros x Hstepvx.
    pose proof (Tarjan_keep_visited_inv g w x) as Hkeep.
    unfold Hoare in Hkeep.
    eapply Hkeep; eauto.
  - pose proof (Tarjan_keep_low_valid_v_inv_with_eset v w (full_eset v)) as Hkeep.
    unfold Hoare in Hkeep.
    eapply Hkeep; eauto.
    split; [exact Hvw|split; [exact Htreev|split; [exact Htreew|split; [exact Hlowv|split]]]].
    + intros x [e [Hstep Hfull]].
      apply Hvisitv.
      exists e; exact Hstep.
    + exact Hnoedge.
Qed.

Lemma Tarjan_keep_closed_low_valid_prod
  (w: V) (v: V):
  Hoare
    (fun s =>
       v <> w /\
       closed_low_valid v s /\
       tree_sub_conj_P root g w s /\
       (forall e, e ∈ full_eset v -> ~ step_aux g e v w))
    (tarjan g w)
    (fun _ s => closed_low_valid v s).
Proof.
  apply Tarjan_keep_closed_low_valid.
Qed.

Lemma Tarjan_low_valid_single_inv_prod
  (u: V) (_: unit):
  Hoare
    (fun s => tree_sub_conj_P root g u s /\
              isleaf (state_to_rootedtree g root s) u)
    (tarjan g u)
    (fun _ s =>
       low_valid_v_inv_with_eset u
         (fun e0 : E => exists v0, step_aux g e0 u v0) s).
Proof.
  apply Tarjan_low_valid_single_inv.
Qed.

Lemma Tarjan_visit_neighbor_prod
  (u: V) (_: unit):
  Hoare ATrue
    (tarjan g u)
    (fun _ s => neighbor_visit g u s).
Proof.
  exact (@Tarjan_visit_neighbor V E _ eq_dec g origin_gvalid u).
Qed.

Lemma Tarjan_processed_low_valid_inv (u: V):
  Hoare
    (fun s => tree_sub_conj_P root g u s /\
              isleaf (state_to_rootedtree g root s) u)
    (tarjan g u)
    (fun _ s => processed_low_valid u s).
Proof.
  unfold tarjan.
  hoare_fix_nolv_fs_auto V.
  {
    forall_n 7.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_closed_low_valid_prod V @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_visited_inv V @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_tree_subgraph_inv unit @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_keep_nooffspring_inv_prod (V * V)%type @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_visit_is_offspring V @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_low_valid_single_inv_prod unit @tarjan.
    * hoare_fix_nolv_ls_auto @Tarjan_visit_neighbor_prod unit @tarjan.
  }
  intros W IHa IH u0 _.
  unfold_Forall IHa.
  clear u; rename u0 into u.
  unfold tarjan_f.
  eapply Hoare_bind.
  {
    hoare_conj_n 1.
    * hoare_cons_pre Tarjan_preloop_keep_tree_sub_conj.
      intros; apply H.
    * hoare_cons_pre Tarjan_preloop_keep_isleaf.
      intros; apply H.
  }
  simpl; intros _.
  eapply Hoare_conseq.
  3: {
    unfold loop_body, forset.
    eapply Hoare_forset with
      (P := fun _ s => processed_low_valid u s /\
                       tree_sub_conj_P root g u s).
    - intros done1 done2 _ s1 s2 Hs; subst; reflexivity.
    - intros done a Hdone_sub Ha_univ Ha_not_done.
      intro_state.
      unfold forset_body.
      hoare_auto_s.
      + unfold for_branch1.
        eapply Hoare_bind with
          (Q := fun _ s =>
            processed_low_valid_except_noedge u a0 s /\
            tree_sub_conj_P root g a0 s /\
            isleaf (state_to_rootedtree g root s) a0 /\
            tree_sub_conj_P root g u s /\
            step_aux (state_to_rootedtree g root s) a u a0 /\
            a0 ∈ visited s).
        {
          unfold set_tree.
          intro_state.
          destruct H as [Hproc [Htree [Hsub Hu]]].
          hoare_auto_s.
          subst.
          split; [|split; [|split; [|split; [|split]]]].
          - eapply processed_low_valid_except_noedge_set_tree; eauto.
            split; [exact Htree|split; [exact Hsub|exact Hu]].
          - split; [|split].
            + apply tree_property_keep; auto.
              * unfold not; intros; subst a0; auto.
                destruct Htree; simpl in *.
                exfalso; apply H1; apply root_valid.
              * eapply step_vvalid2; eauto.
              * unfold not; intros Hex.
                destruct Hex as [x [Hx Heq]].
                assert (evalid (state_to_rootedtree g root s0) a) as Hevalid.
                { exists x; split; auto. }
                eapply sub_reverse with (g2:=g) in Hevalid; eauto.
                2: apply Rootedtree_noemptyedge.
                2: apply OriginalGraph_stepuniqueundirected.
                destruct Hevalid as [Hst|Hst];
                destruct Hst as [Hvx Hvy _ _].
                -- apply H1; exact Hvy.
                -- apply H1; exact Hvx.
            + apply tree_subgraph_keep; auto.
            + right; reflexivity.
          - apply tree_add_vertex_is_leaf; auto.
          - split; [|split].
            + apply tree_property_keep; auto.
              * unfold not; intros; subst a0; auto.
                destruct Htree; simpl in *.
                exfalso; apply H1; apply root_valid.
              * eapply step_vvalid2; eauto.
              * unfold not; intros Hex.
                destruct Hex as [x [Hx Heq]].
                assert (evalid (state_to_rootedtree g root s0) a) as Hevalid.
                { exists x; split; auto. }
                eapply sub_reverse with (g2:=g) in Hevalid; eauto.
                2: apply Rootedtree_noemptyedge.
                2: apply OriginalGraph_stepuniqueundirected.
                destruct Hevalid as [Hst|Hst];
                destruct Hst as [Hvx Hvy _ _].
                -- apply H1; exact Hvy.
                -- apply H1; exact Hvx.
            + apply tree_subgraph_keep; auto.
            + left; exact Hu.
          - apply step_easy; auto.
          - right; reflexivity.
        }
        simpl; intros _.
        eapply Hoare_bind with
          (Q := fun _ s =>
            processed_low_valid u s /\
            tree_sub_conj_P root g u s).
        {
          intros s_pre ret s_post Hpre Hrun.
          destruct Hpre as
            [Hexcept [Htree_child [Hleaf_child [Htree_u [Hstep_parent Hchild_vis]]]]].
          assert (Hproc_child: processed_low_valid a0 s_post).
          {
            pose proof (IH a0) as Hproc_child_Hoare.
            unfold Hoare in Hproc_child_Hoare.
            eapply Hproc_child_Hoare; eauto.
          }
          assert (Hlow_child:
            low_valid_v_inv_with_eset a0
              (fun e0 : E => exists v0, step_aux g e0 a0 v0) s_post).
          {
            unfold Hoare in IHa5.
            eapply (IHa5 a0 tt); eauto.
          }
          assert (Hvisit_child: neighbor_visit g a0 s_post).
          {
            pose proof (IHa6 a0 tt) as Hvisit_Hoare.
            unfold Hoare in Hvisit_Hoare.
            eapply Hvisit_Hoare.
            - exact I.
            - exact Hrun.
          }
          assert (Htree_child_post: tree_sub_conj_P root g a0 s_post).
          {
            unfold Hoare in IHa2.
            eapply (IHa2 a0 tt); eauto.
          }
          assert (Hu_post: u ∈ visited s_post).
          {
            destruct Htree_u as [_ [_ Hu_pre]].
            unfold Hoare in IHa1.
            eapply (IHa1 a0 u); eauto.
          }
          assert (Htree_u_post: tree_sub_conj_P root g u s_post).
          {
            eapply tree_easy; eauto.
          }
          assert (Hclosed_child: closed_low_valid a0 s_post).
          {
            split; [exact Htree_child_post|split; [exact Hvisit_child|]].
            exact Hlow_child.
          }
          split; [|exact Htree_u_post].
          unfold processed_low_valid.
          intros v Hvu Hoff_uv.
          destruct (classic (v = a0)) as [Hvchild|Hvchild].
          { subst v; exact Hclosed_child. }
          destruct (classic (v ∈ visited s_pre)) as [Hv_pre|Hv_pre].
          - assert (Hoff_pre: offspring (state_to_rootedtree g root s_pre) u v).
            {
              apply NNPP.
              intro Hno_pre.
              assert (Hno_post: ~ offspring (state_to_rootedtree g root s_post) u v).
              {
                unfold Hoare in IHa3.
                eapply (IHa3 a0 (u, v)); eauto.
                split; [|split; [|split]].
                - destruct Htree_u as [_ [_ Hu_pre]]; exact Hu_pre.
                - exact Hv_pre.
                - exact Hno_pre.
                - exact Htree_child.
              }
              contradiction.
            }
            destruct (Hexcept v Hvu Hvchild Hoff_pre) as [Hclosed_pre Hnoedge].
            unfold Hoare in IHa0.
            eapply (IHa0 a0 v).
            + split; [exact Hvchild|split; [exact Hclosed_pre|split; [exact Htree_child|exact Hnoedge]]].
            + exact Hrun.
          - assert (Hvisit_case:
              (a0 ∈ visited s_post /\ ~ v ∈ visited s_post) \/
              (v ∈ visited s_post /\
               offspring (state_to_rootedtree g root s_post) a0 v)).
            {
              unfold Hoare in IHa4.
              eapply (IHa4 a0 v).
              - split; [exact Hchild_vis|exact Hv_pre].
              - exact Hrun.
            }
            destruct Hvisit_case as [[_ Hnot_v_post]|[_ Hoff_child]].
            + exfalso.
              apply Hnot_v_post.
              assert (Huv: u <> v) by (intro Huv; apply Hvu; symmetry; exact Huv).
              pose proof (reachable_vvalid u v Huv Hoff_uv) as [_ Hvvalid].
              simpl in Hvvalid; exact Hvvalid.
            + apply Hproc_child; auto.
        }
        simpl; intros _.
        apply Hoare_conj.
        * hoare_cons_pre Tarjan_post_rec_keep_processed_low_valid.
        * hoare_cons_pre Tarjan_post_rec_keep_tree_sub_conj.
      + unfold for_branch2.
        unfold_op.
        hoare_auto_s.
        repeat match goal with
        | Hc : _ /\ _ |- _ => destruct Hc
        end.
        subst.
        split.
        * unfold processed_low_valid.
          intros v0 Hv0u Hoff; simpl in Hoff.
          change (offspring (T s0) u v0) in Hoff.
          destruct H4 as [Htree0 [Hsub0 Hu0]].
          eapply closed_low_valid_update_low_offspring; eauto.
        * destruct H4 as [Htree0 [Hsub0 Hu0]].
          simpl; split; [exact Htree0|split; [exact Hsub0|exact Hu0]].
      + repeat match goal with
        | Hc : _ /\ _ |- _ => destruct Hc
        end;
        subst; split; auto.
  }
  - intros s [Htree Hleaf].
    split.
    + apply processed_low_valid_leaf; auto.
    + exact Htree.
  - intros.
    destruct H as [Hproc _].
    exact Hproc.
Qed.

Theorem Tarjan_low_valid:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => low_valid g (state_to_rootedtree g root s) s.(dfn) s.(low)).
Proof.
  eapply Hoare_conseq_post.
  2: {
    hoare_conj_n 4.
    * apply Tarjan_rooted_tree; auto.
    * apply Tarjan_subgraph; auto.
    * hoare_cons_pre (Tarjan_low_valid_single_inv root).
      intros s Hs; subst; split.
      -- apply tree_subgraph_init_state; auto.
      -- apply Tarjan_root_isleaf_init_state.
    * hoare_cons_pre (Tarjan_visit_neighbor_prod root tt).
      intros; exact I.
    * hoare_cons_pre (Tarjan_processed_low_valid_inv root).
      intros s Hs; subst; split.
      -- apply tree_subgraph_init_state; auto.
      -- apply Tarjan_root_isleaf_init_state.
  }
  intros _ s [Hrt [Hsub [Hlowroot [Hvisitroot Hproc]]]].
  unfold low_valid.
  intros v Hv.
  assert (Hclosed: closed_low_valid v s).
  {
    destruct (classic (v = root)) as [Hvr|Hvr].
    - subst v.
      split; [|split].
      + split; [exact Hrt|split; [exact Hsub|]].
        destruct Hrt; simpl in *; apply root_valid.
      + exact Hvisitroot.
      + exact Hlowroot.
    - apply Hproc; auto.
      change (offspring (T s) (GraphLib.directed.rootedtree.root (T s)) v).
      eapply root_is_root; eauto.
  }
  eapply closed_low_valid_to_final; eauto.
Qed.


Theorem Tarjan_is_low:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => is_low g (state_to_rootedtree g root s) s.(dfn) s.(low)).
Proof.
  eapply Hoare_conseq_post.
  2: { hoare_conj_n 5.
  * apply Tarjan_rooted_tree; auto.
  * apply Tarjan_subgraph; auto.
  * apply Tarjan_low_valid.
  * apply Tarjan_reachable_visited; auto.
  * apply Tarjan_dfn_valid; auto.
  * apply Tarjan_no_cross_edge; auto. }
  intros.
  destruct H as [Htree [Hsub [Hlow [Hreach [Hdfn Hnocross]]]]].
  apply low_valid_implies_is_low; auto.
  apply RootedTree_finitegraph.
Qed.

End ISLOW.
