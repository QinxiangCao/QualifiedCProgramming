
Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Lemma list_snoc_destruct: forall {A: Type} (l: list A),
  l = nil \/
  exists a l', l = l' ++ [a].
Proof.
  intros.
  revert l; apply rev_ind.
  + left; reflexivity.
  + intros.
    right.
    eauto.
Qed.

Lemma app_eq_app {A : Type}: forall (l1 l2 l3 l4 : list A),
  l1 ++ l2 = l3 ++ l4 ->
  (exists m, l1 = l3 ++ m /\ l4 = m ++ l2) \/
  (exists m, l3 = l1 ++ m /\ l2 = m ++ l4).
Proof.
  induction l1; intros.
  - simpl in H. right. exists l3. auto.
  - destruct l3.
    + simpl in H. left. exists (a :: l1). auto.
    + simpl in H. injection H as Heq Hrem.
      apply IHl1 in Hrem as [|].
      * left. destruct H as [m [? ?]]. subst.
        exists m. split; auto.
      * right. destruct H as [m [? ?]]. subst.
        exists m. split; auto.
Qed.