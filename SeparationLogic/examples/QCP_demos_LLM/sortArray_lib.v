Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Require Import String.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Import naive_C_Rules.
Local Open Scope sac.

Fixpoint insert (x: Z) (l: list Z): list Z :=
  match l with
  | nil => [x]
  | y :: l' => if x >? y then y :: insert x l' else x :: l
  end.

Lemma upperbound_insert_nil:
  forall x l,
    strict_lowerbound x l ->
    insert x l = x :: l.
Proof.
  intros.
  induction l; simpl; try easy.
  simpl in H. destruct H.
  destruct (x >? a) eqn:b; simpl.
  - lia.
  - reflexivity.
Qed.

Lemma upperbound_insert_cons:
  forall x y l,
    y <= x ->
    strict_lowerbound x l ->
    insert x (y :: l) = y :: x :: l.
Proof.
  intros.
  simpl.
  destruct (x >? y) eqn:b; simpl.
  - rewrite upperbound_insert_nil; auto.
  - assert (x = y) by lia. subst. reflexivity.
Qed.

Lemma increasing_aux_insert:
  forall x l start,
    increasing_aux l start ->
    start <= x ->
    increasing_aux (insert x l) start.
Proof.
  intros. revert start H H0.
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

Lemma increasing_aux_middle:
  forall l y x l2 start,
    increasing_aux (l ++ y :: l2) start ->
    y <= x ->
    strict_lowerbound x l2 ->
    increasing_aux (l ++ y :: x :: l2) start.
Proof.
  induction l; intros; simpl in *.
  - destruct l2 eqn:E2; simpl in *.
    + lia.
    + destruct H as [Hsy Hrest].
      destruct H1 as [Hxz Hup].
      split.
      * exact Hsy.
      * split.
        -- lia.
        -- destruct Hrest as [_ Htail].
           split.
           ++ lia.
           ++ exact Htail.
  - destruct H as [Hsa Hrest].
    split.
    + exact Hsa.
    + eapply IHl; eauto.
Qed.

Lemma increasing_middle:
  forall l1 y x l2,
    increasing (l1 ++ y :: l2) ->
    y <= x ->
    strict_lowerbound x l2 ->
    increasing (l1 ++ y :: x :: l2).
Proof.
  destruct l1; intros; simpl in *.
  - destruct l2 eqn:E2; simpl in *.
    + lia.
    + destruct H as [Hyz Hrest].
      destruct H1 as [Hxz Hup].
      split.
      * lia.
      * split.
        -- lia.
        -- exact Hrest.
  - eapply increasing_aux_middle; eauto.
Qed.

Fixpoint last_val_local (default: Z) (l: list Z) : Z :=
  match l with
  | nil => default
  | y :: l' => last_val_local y l'
  end.

Lemma last_val_local_in :
  forall x l,
    In (last_val_local x l) (x :: l).
Proof.
  intros x l.
  induction l as [ | y l IH ] in x |- *; simpl.
  - left. reflexivity.
  - right. apply IH.
Qed.

Lemma increasing_aux_snoc_local :
  forall l start x,
    increasing_aux l start ->
    last_val_local start l <= x ->
    increasing_aux (l ++ [x]) start.
Proof.
  induction l as [ | y l IH ]; intros start x Hinc Hlast; simpl in *.
  - split; [lia | easy].
  - destruct Hinc as [Hle Hinc].
    split.
    + exact Hle.
    + apply IH; assumption.
Qed.

Lemma increasing_snoc_local :
  forall l x,
    increasing l ->
    match l with
    | nil => True
    | y :: l' => last_val_local y l' <= x
    end ->
    increasing (l ++ [x]).
Proof.
  intros l x Hinc Hlast.
  destruct l as [ | y l ].
  - simpl. auto.
  - simpl in *. apply increasing_aux_snoc_local; assumption.
Qed.

Lemma increasing_cons_local :
  forall x l,
    lowerbound x l ->
    increasing l ->
    increasing (x :: l).
Proof.
  intros x l Hlb Hinc.
  destruct l; simpl; auto.
  destruct Hlb as [Hxy _].
  split; [exact Hxy | exact Hinc].
Qed.

Lemma prefix_suffix_sorted_perm_local :
  forall l1 l2 l3,
    prefix_suffix_sorted l1 l2 ->
    Permutation l2 l3 ->
    prefix_suffix_sorted l1 l3.
Proof.
  intros l1 l2 l3 Hsorted Hperm.
  unfold prefix_suffix_sorted in *.
  intros x Hinx.
  apply (lowerbound_perm x l2 l3 Hperm).
  apply Hsorted.
  exact Hinx.
Qed.

Lemma prefix_suffix_sorted_prefix_perm_local :
  forall l1 l2 l3,
    Permutation l1 l2 ->
    prefix_suffix_sorted l1 l3 ->
    prefix_suffix_sorted l2 l3.
Proof.
  intros l1 l2 l3 Hperm Hsorted.
  unfold prefix_suffix_sorted in *.
  intros x Hinx.
  apply Hsorted.
  eapply Permutation_in.
  - apply Permutation_sym. exact Hperm.
  - exact Hinx.
Qed.

Lemma prefix_suffix_sorted_singleton_le_local :
  forall l x y,
    prefix_suffix_sorted l [x] ->
    x <= y ->
    prefix_suffix_sorted l [y].
Proof.
  intros l x y Hsorted Hxy.
  unfold prefix_suffix_sorted in *.
  intros z Hz.
  specialize (Hsorted z Hz).
  simpl in Hsorted.
  simpl.
  destruct Hsorted as [Hzx _].
  split; [lia | easy].
Qed.

Lemma prefix_suffix_sorted_snoc_singleton_local :
  forall l x y,
    prefix_suffix_sorted l [y] ->
    x <= y ->
    prefix_suffix_sorted (l ++ [x]) [y].
Proof.
  intros l x y Hsorted Hxy.
  unfold prefix_suffix_sorted in *.
  intros z Hz.
  apply in_app_or in Hz.
  destruct Hz as [Hz | Hz].
  - apply Hsorted. exact Hz.
  - simpl in Hz.
    destruct Hz as [Hz | Hz].
    + subst z. simpl. split; [lia | easy].
    + contradiction.
Qed.

Lemma prefix_suffix_sorted_extend_suffix_local :
  forall l x l2,
    prefix_suffix_sorted l [x] ->
    prefix_suffix_sorted l l2 ->
    prefix_suffix_sorted l (x :: l2).
Proof.
  intros l x l2 Hsingle Hrest.
  unfold prefix_suffix_sorted in *.
  intros y Hy.
  specialize (Hsingle y Hy).
  specialize (Hrest y Hy).
  simpl in Hsingle.
  simpl.
  destruct Hsingle as [Hyx _].
  split; [exact Hyx | exact Hrest].
Qed.

Lemma prefix_suffix_sorted_last_local :
  forall l1 x l2,
    prefix_suffix_sorted l1 (x :: l2) ->
    match l1 with
    | nil => True
    | y :: l' => last_val_local y l' <= x
    end.
Proof.
  intros l1 x l2 Hsorted.
  destruct l1 as [ | y l' ]; simpl; auto.
  unfold prefix_suffix_sorted in Hsorted.
  specialize (Hsorted (last_val_local y l')).
  assert (Hin : In (last_val_local y l') (y :: l')).
  { apply last_val_local_in. }
  specialize (Hsorted Hin).
  simpl in Hsorted.
  tauto.
Qed.

Lemma prefix_suffix_sorted_snoc_local :
  forall l1 x l2,
    prefix_suffix_sorted l1 (x :: l2) ->
    lowerbound x l2 ->
    prefix_suffix_sorted (l1 ++ [x]) l2.
Proof.
  intros l1 x l2 Hsorted Hbound.
  unfold prefix_suffix_sorted in *.
  intros y Hy.
  apply in_app_or in Hy.
  destruct Hy as [Hy | Hy].
  - specialize (Hsorted y Hy).
    simpl in Hsorted.
    tauto.
  - simpl in Hy.
    destruct Hy as [Hy | Hy].
    + subst y. exact Hbound.
    + contradiction.
Qed.

Lemma replace_Znth_length_local {A: Type}:
  forall (l: list A) n a,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros l n.
  unfold replace_Znth.
  remember (Z.to_nat n) as k; clear Heqk.
  revert k; induction l; intros.
  - destruct k; simpl; easy.
  - destruct k; simpl; repeat rewrite Zlength_cons; auto.
    rewrite IHl; auto.
Qed.

Lemma replace_Znth_boundary_local {A: Type} :
  forall (prefix tail: list A) x y,
    replace_Znth (Zlength prefix) x (prefix ++ y :: tail) = prefix ++ x :: tail.
Proof.
  induction prefix; intros tail x y.
  - reflexivity.
  - simpl.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg prefix) as Hlen.
    assert (Hpos : Z.succ (Zlength prefix) > 0) by lia.
    rewrite (replace_Znth_cons (Z.succ (Zlength prefix)) x a (prefix ++ y :: tail)) by exact Hpos.
    replace (Z.succ (Zlength prefix) - 1) with (Zlength prefix) by lia.
    simpl.
    f_equal.
    apply IHprefix.
Qed.

Lemma replace_Znth_boundary_app_local {A: Type} :
  forall (prefix middle tail: list A) x y,
    replace_Znth (Zlength prefix) x ((prefix ++ y :: middle) ++ tail) =
    (prefix ++ x :: middle) ++ tail.
Proof.
  intros prefix middle tail x y.
  replace ((prefix ++ y :: middle) ++ tail) with (prefix ++ y :: (middle ++ tail)) by (rewrite <- app_assoc; reflexivity).
  replace ((prefix ++ x :: middle) ++ tail) with (prefix ++ x :: (middle ++ tail)) by (rewrite <- app_assoc; reflexivity).
  apply replace_Znth_boundary_local.
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

Lemma perm_swap_with_prefix:
  forall (l1 l2 l3: list Z) (x y: Z),
    Permutation (l1 ++ x :: l2 ++ y :: l3)
                (l1 ++ y :: l2 ++ x :: l3).
Proof.
  intros.
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.
