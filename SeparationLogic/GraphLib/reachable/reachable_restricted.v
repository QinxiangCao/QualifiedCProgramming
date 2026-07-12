Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Lia.

Section reachableWITHOUT.

Context {G: Type}
        {V: Type}
        {E: Type}
        {g: G}
        {graph: Graph G V E}.

Definition step_without (g0: G) (e: E) (x y: V) : Prop :=
  exists e0, step_aux g0 e0 x y /\ e <> e0.

Definition reachable_without (g0: G) (e: E) (x y: V) : Prop :=
  clos_refl_trans (step_without g0 e) x y.

Definition is_bridge (g0: G) (e: E) : Prop :=
  forall x y, step_aux g0 e x y -> 
  ~ ( reachable_without g0 e x y).

Lemma step_without_rt : 
  forall e x y, 
  step_without g e x y -> reachable_without g e x y.
Proof.
  intros.
  unfold reachable_without in *.
  transitivity_1n y; auto.
  reflexivity.
Qed.

End reachableWITHOUT.

Section reachableTL.

Context {G: Type}
        {V: Type}
        {E: Type}
        {g: G}
        {graph: Graph G V E}.

Definition step_tl (P: V -> Prop) (g: G) (x y: V) : Prop :=
  step g x y /\ P y.
  
Definition reachable_tl (P: V -> Prop) (g: G) (x y: V) : Prop :=
  clos_refl_trans (step_tl P g) x y.

Lemma step_tl_rt: 
  forall P x y, 
  step_tl P g x y -> reachable_tl P g x y.
Proof.
  intros P x y H.
  unfold reachable_tl in *.
  transitivity_1n y; auto.
  reflexivity.
Qed.

Lemma reachable_gt_reachable (g0: G) (P: V -> Prop): forall x y, 
  reachable_tl P g0 x y -> reachable g0 x y.
Proof.
  intros x y H.
  unfold reachable_tl in H.
  induction_1n H.
  unfold reachable; reflexivity.
  unfold reachable in *.
  transitivity_1n x0; auto.
  destruct H0; auto.
Qed.

End reachableTL.

Section reachableGT.

Context {G: Type}
        {V: Type}
        {E: Type}
        {g: G}
        {graph: Graph G V E}
        {dfn: V -> nat}.
    
Definition reachable_dfn_gt (P: V -> nat) (z: nat) (g: G) (x y: V) : Prop :=
  reachable_tl (fun t => P t >= z) g x y.

Lemma reachable_gt_mono (g0: G): forall n1 n2 x y,
  n1 >= n2 ->
  reachable_dfn_gt dfn n1 g0 x y -> reachable_dfn_gt dfn n2 g0 x y.
Proof.
  intros n1 n2 x y H0 H1.
  unfold reachable_dfn_gt in *.
  unfold reachable_tl in *.
  induction_1n H1.
  reflexivity.
  transitivity_1n x0; auto.
  destruct H; split; auto.
  lia.
Qed.

End reachableGT.

Section reachableWITHIN.

Local Open Scope sets.

Context {G: Type}
        {V: Type}
        {E: Type}
        {g: G}
        {graph: Graph G V E}.

Definition step_in_eset (g: G) (eset: E -> Prop) (x y: V) : Prop :=
  exists e, step_aux g e x y /\ e ∈ eset.

Definition reachable_in_eset (g: G) (eset: E -> Prop) (x y: V): Prop:=
  clos_refl_trans (step_in_eset g eset) x y.

Lemma step_in_eset_emptyset: 
  forall x y, ~ step_in_eset g ∅ x y.
Proof.
  intros.
  unfold not; intros; 
  destruct H as [? []].
  apply H0.
Qed.

Lemma reachable_in_eset_emptyset:
  forall x y, reachable_in_eset g ∅ x y -> x = y.
Proof.
  intros.
  unfold reachable_in_eset in H.
  induction_1n H; auto.
  exfalso; eapply step_in_eset_emptyset; eauto.
Qed.

Lemma step_in_eset_rt :
  forall eset x y,
    step_in_eset g eset x y ->
    reachable_in_eset g eset x y.
Proof.
  intros eset x y H.
  unfold reachable_in_eset.
  transitivity_1n y; auto.
  reflexivity.
Qed.

Lemma reachable_in_eset_weaken :
  forall eset1 eset2 x y,
    eset1 ⊆ eset2 ->
    reachable_in_eset g eset1 x y ->
    reachable_in_eset g eset2 x y.
Proof.
  intros eset1 eset2 x y Hsub Hreach.
  unfold reachable_in_eset in *.
  induction_1n Hreach.
  - reflexivity.
  - transitivity_1n x0; auto.
    match goal with
    | Hstep0 : step_in_eset g eset1 _ _ |- _ =>
        destruct Hstep0 as [e [Hstep Heset]]
    end.
    exists e.
    split.
    + exact Hstep.
    + apply Hsub; exact Heset.
Qed.

Lemma step_in_eset_sym 
  {gv: GValid G}
  {undirected: UndirectedGraph G V E}:
  forall eset x y,
    step_in_eset g eset x y ->
    step_in_eset g eset y x.
Proof.
  intros eset x y [e [Hstep Heset]].
  exists e.
  split; auto.
  eapply step_sym; eauto. 
Qed.


Lemma reachable_in_eset_sym
  {gv: GValid G}
  {undirected: UndirectedGraph G V E}:
  forall eset x y,
    reachable_in_eset g eset x y ->
    reachable_in_eset g eset y x.
Proof.
  intros eset x y Hreach.
  unfold reachable_in_eset in *.
  induction_1n Hreach.
  - reflexivity.
  - transitivity_n1 x0; auto.
    eapply step_in_eset_sym; eauto.
Qed.

Lemma reachable_in_eset_trans :
  forall eset x y z,
    reachable_in_eset g eset x y ->
    reachable_in_eset g eset y z ->
    reachable_in_eset g eset x z.
Proof.
  intros eset x y z Hxy Hyz.
  unfold reachable_in_eset in *.
  induction_1n Hxy.
  - exact Hyz.
  - transitivity_1n x0; auto.
Qed.

End reachableWITHIN.
