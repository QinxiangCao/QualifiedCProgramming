Require Import GraphLib.graph_basic.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.

Section reachable.
  
Context {G: Type}
        {V: Type}
        {E: Type}
        {g: G}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}.

Definition step (g: G) (x y: V): Prop :=
  exists e, step_aux g e x y.

Definition reachable (g: G) (x y: V): Prop :=
  clos_refl_trans (step g) x y.

Definition connected (g: G): Prop := forall x y, vvalid g x -> vvalid g y -> reachable g x y.

Lemma step_trivial: forall x y e, 
  step_aux g e x y ->
  step g x y.
Proof.
  intros.
  exists e; auto.
Qed.

Lemma step_rt : forall (g: G) x y, 
  step g x y -> 
  reachable g x y.
Proof.
  intros.
  unfold reachable in *.
  transitivity_1n y; auto.
  reflexivity.
Qed.

Lemma step_vvalid: forall x y, 
  step g x y -> 
  vvalid g x /\ vvalid g y.
Proof.
  intros.
  destruct H as [e H].
  split.
  - apply step_vvalid1 in H; auto.
  - apply step_vvalid2 in H; auto.
Qed.  

Lemma reachable_vvalid: forall x y: V, 
  x <> y -> 
  reachable g x y -> 
  vvalid g x /\ vvalid g y.
Proof.
  intros.
  split.
  - revert H.
  unfold reachable in H0.
  induction_1n H0.
  * exfalso; auto.
  * eapply step_vvalid with (y:=x0); eauto.
  - revert H.
  rename H0 into H.
  intros.
  unfold reachable in H.
  induction_n1 H.
  * exfalso; auto.
  * eapply step_vvalid with (x:=x0); eauto.
Qed.


Lemma step_reachable_reachable: forall x y z,
  step g x y -> 
  reachable g y z ->
  reachable g x z. 
Proof.
  intros.
  unfold reachable in *.
  transitivity_1n y; auto.
Qed.

Lemma reachable_step_reachable: forall x y z,
  reachable g x y -> 
  step g y z ->
  reachable g x z. 
Proof.
  intros.
  unfold reachable in *.
  transitivity_n1 y; auto.
Qed.

Lemma reachable_trans: forall x y z,
  reachable g x y ->
  reachable g y z ->
  reachable g x z.
Proof.
  intros x y z Hxy Hyz.
  unfold reachable in *.
  transitivity y; auto.
Qed.

Lemma reachable_step_not_reachable:
  forall s x y,
    reachable g s x ->
    ~ reachable g s y ->
    ~ step g x y.
Proof.
  intros s x y Hsx Hnot Hstep.
  apply Hnot.
  eapply reachable_step_reachable; eauto.
Qed.

Lemma reachable_1n: forall x y,
  reachable g x y ->
  (exists z, step g x z /\ reachable g z y) \/ x = y.
Proof.
  intros.
  unfold reachable in H.
  induction_1n H. 
  - right; reflexivity.
  - destruct IHrt as [[z []]| ]; auto. 
    * left; exists x0; auto. 
    * subst; left; exists y; auto.
Qed.

End reachable.
