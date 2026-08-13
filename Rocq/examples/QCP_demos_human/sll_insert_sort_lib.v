Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Fixpoint insert (x: Z) (l: list Z): list Z :=
  match l with
  | nil => [x]
  | y :: l' => if x >? y then y :: insert x l' else x :: l
  end.

Lemma upperbound_insert_nil:
  forall x l,
    strict_upperbound x l ->
    insert x l = l ++ [x].
Proof.
  intros. 
  induction l; simpl; try easy.
  simpl in H. destruct H.
  destruct (x >? a) eqn:b; simpl; try lia.
  apply IHl in H0. rewrite H0. reflexivity.
Qed.

Lemma upperbound_insert_cons:
  forall x l1 l2 y,
    strict_upperbound x l1 ->
    x <= y ->
    insert x (l1 ++ y :: l2) = l1 ++ x :: y :: l2.
Proof.
  intros. 
  induction l1; simpl; try easy; simpl in H.
  - destruct (x >? y) eqn:b; simpl; [lia | easy].
  - destruct H. destruct (x >? a) eqn:b; simpl; try lia.
    apply IHl1 in H1. rewrite H1. reflexivity.
Qed.

Lemma increasing_aux_insert:
  forall x l a,
    increasing_aux l a ->
    a <= x ->
    increasing_aux (insert x l) a.
Proof.
  intros. revert a H H0.  
  induction l; intros; simpl; try easy.
  simpl in H. 
  destruct (x >? a) eqn:b; simpl.
  - split; try easy.
    apply IHl; [easy | lia].
  - repeat split; try easy. lia.
Qed.

Lemma increasing_insert:
  forall x l,
    increasing l ->
    increasing (insert x l).
Proof.
  intros. destruct l; simpl; try easy.
  simpl in H.
  destruct (x >? z) eqn:b; simpl.
  - apply increasing_aux_insert; [easy | lia]. 
  - split; [lia | easy]. 
Qed.

Lemma perm_insert:
  forall x l,
    Permutation (l ++ [x]) (insert x l).
Proof.
  intros. induction l; simpl; try easy.
  destruct (x >? a).
  - rewrite IHl. reflexivity.
  - rewrite <- Permutation_cons_append. apply perm_swap.
Qed.  
