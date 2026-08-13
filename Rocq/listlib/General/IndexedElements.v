Require Import Lia.
Require Import Coq.Lists.List.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Forall.
Require Import ListLib.General.Length.
Require Import ZArith.ZArith.

Import ListNotations.
Import Length.

Local Open Scope Z.

Definition is_indexed_elements {A: Type} (l: list A) (il: list Z) (l0: list A): Prop :=
  Forall2 (fun i a => Znth_error l i = Some a) il l0.

Lemma is_indexed_elements_nil {A} (l: list A):
  is_indexed_elements l [] [].
Proof.
  unfold is_indexed_elements.
  apply Forall2_nil.
Qed.

Lemma is_indexed_elements_cons {A} (l: list A) (i: Z) (a: A) (il: list Z) (l0: list A):
  Znth_error l i = Some a ->
  is_indexed_elements l il l0 ->
  is_indexed_elements l (i :: il) (a :: l0).
Proof.
  unfold is_indexed_elements.
  intros H1 H2.
  apply Forall2_cons; auto.
Qed.

Lemma is_indexed_elements_cons_iff {A} (l: list A) (i: Z) (a: A) (il: list Z) (l0: list A):
  is_indexed_elements l (i :: il) (a :: l0) <->
  Znth_error l i = Some a /\ is_indexed_elements l il l0.
Proof.
  unfold is_indexed_elements.
  rewrite Forall2_cons_iff.
  reflexivity.
Qed.

Lemma is_indexed_elements_app {A} (l: list A) (il1 il2: list Z) (l1 l2: list A):
  is_indexed_elements l il1 l1 ->
  is_indexed_elements l il2 l2 ->
  is_indexed_elements l (il1 ++ il2) (l1 ++ l2).
Proof.
  unfold is_indexed_elements.
  intros H1 H2.
  apply Forall2_app; auto.
Qed.

Lemma is_indexed_elements_app_inv_r {A} (l: list A) (il': list Z) (l1' l2': list A):
  is_indexed_elements l il' (l1' ++ l2') ->
  exists il1 il2: list Z,
    is_indexed_elements l il1 l1' /\
    is_indexed_elements l il2 l2' /\
    il' = il1 ++ il2.
Proof.
  unfold is_indexed_elements.
  intros H.
  apply Forall2_app_inv_r in H.
  destruct H as (il1 & il2 & H1 & H2 & EQ).
  exists il1, il2.
  repeat split; auto.
Qed.

Lemma is_indexed_elements_app_inv_l {A} (l: list A) (il1 il2: list Z) (l': list A):
  is_indexed_elements l (il1 ++ il2) l' ->
  exists l1' l2': list A,
    is_indexed_elements l il1 l1' /\
    is_indexed_elements l il2 l2' /\
    l' = l1' ++ l2'.
Proof.
  unfold is_indexed_elements.
  intros H.
  apply Forall2_app_inv_l in H.
  destruct H as (l1' & l2' & H1 & H2 & EQ).
  exists l1', l2'.
  repeat split; auto.
Qed.

Lemma is_indexed_elements_nil_inv_l {A} (l : list A) l0 :
  is_indexed_elements l nil l0 ->
  l0 = nil.
Proof.
  intros H.
  unfold is_indexed_elements in H.
  now apply Forall2_cons_nil_l in H.
Qed.

Lemma is_indexed_elements_nil_inv_r {A} (l : list A) il :
  is_indexed_elements l il nil ->
  il = nil.
Proof.
  intros H.
  unfold is_indexed_elements in H.
  now apply Forall2_cons_nil_r in H.
Qed.

Lemma is_indexed_elements_cons_inv_r {A} (l : list A) il a l' :
  is_indexed_elements l il (a :: l') ->
  exists i il',
    il = i :: il' /\
    Znth_error l i = Some a /\
    is_indexed_elements l il' l'.
Proof.
  intros H.
  unfold is_indexed_elements in H.
  apply Forall2_cons_inv_r in H.
  destruct H as [i [il' [Hlen [Hnth Hrest]]]].
  exists i, il'.
  tauto.
Qed.

Lemma is_indexed_elements_cons_inv_l {A} (l : list A) i il l' :
  is_indexed_elements l (i :: il) l' ->
  exists a l0',
    Znth_error l i = Some a /\
    is_indexed_elements l il l0' /\
    l' = a :: l0'.
Proof.
  intros H.
  unfold is_indexed_elements in H.
  apply Forall2_cons_inv_l in H.
  destruct H as [a [l0' [Hlen [Hnth Hrest]]]].
  exists a, l0'.
  tauto.
Qed.

Fixpoint sincr_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x < y /\ sincr_aux l0 y
  end.

Definition sincr (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => sincr_aux l0 x
  end.

Lemma sincr_app_cons: forall l1 x l2,
  sincr (l1 ++ [x]) ->
  sincr (x :: l2) ->
  sincr (l1 ++ x :: l2).
Proof.
  intros.
  simpl in H0.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma sincr_app_cons_inv1: forall l1 x l2,
  sincr (l1 ++ x :: l2) ->
  sincr (l1 ++ [x]).
Proof.
  intros.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma sincr_app_cons_inv2: forall l1 x l2,
  sincr (l1 ++ x :: l2) ->
  sincr (x :: l2).
Proof.
  intros.
  simpl.
  induction l1; simpl in *.
  + tauto.
  + apply IHl1.
    destruct l1; simpl in *; tauto.
Qed.

Fixpoint is_subsequence {A: Type} (l1 l2: list A): Prop :=
  match l1, l2 with
  | nil, nil => True
  | nil, cons a2 l2' => True
  | cons a1 l1', nil => False
  | cons a1 l1', cons a2 l2' =>
      is_subsequence l1 l2' \/
      a1 = a2 /\ is_subsequence l1' l2'
  end.

Lemma sincr_add_1: forall l,
  sincr l ->
  sincr (map (fun z => z + 1) l).
Proof.
  intros.
  destruct l; [tauto |].
  simpl in *.
  revert z H; induction l; simpl; intros.
  { tauto. }
  split; [lia |].
  destruct H.
  apply IHl.
  tauto.
Qed.

Lemma sincr_sub_1: forall l,
  sincr l ->
  sincr (map (fun z => z - 1) l).
Proof.
  intros.
  destruct l; [tauto |].
  simpl in *.
  revert z H; induction l; simpl; intros.
  { tauto. }
  split; [lia |].
  destruct H.
  apply IHl.
  tauto.
Qed.

Lemma sincr_cons: forall a l,
  Forall (fun z => a < z) l ->
  sincr l ->
  sincr (a :: l).
Proof.
  intros.
  simpl.
  destruct l; simpl in *.
  { tauto. }
  apply Forall_cons_iff in H.
  tauto.
Qed.

Lemma sincr_cons_tail_Forall_lt: forall a l,
  sincr (a :: l) ->
  Forall (fun b => a < b) l.
Proof.
  simpl; intros.
  revert a H; induction l; simpl; intros.
  + apply Forall_nil.
  + pose proof IHl a ltac:(tauto).
    apply Forall_cons; [tauto |].
    revert H0; apply Forall_impl.
    intros; lia.
Qed.

Lemma sincr_cons_Forall_lt: forall a0 a l,
  a0 < a ->
  sincr (a :: l) ->
  Forall (fun b => a0 < b) (a :: l).
Proof.
  intros.
  pose proof sincr_cons_tail_Forall_lt _ _ H0.
  constructor; auto.
  revert H1; apply Forall_impl.
  intros; lia.
Qed.

Lemma is_indexed_elements_range {A} (l : list A) il l0 :
  is_indexed_elements l il l0 ->
  Forall (fun i => 0 <= i < Zlength l) il.
Proof.
  intros H.
  unfold is_indexed_elements in H.
  induction H as [| i a il l0 Hnth Hrest IH].
  - constructor.               (* nil 情况 *)
  - constructor; [ | apply IH].
    apply Znth_error_range in Hnth.
    tauto.
Qed.

Theorem is_subsequence_inv: forall {A: Type} (l1 l2: list A),
  is_subsequence l1 l2 ->
  exists il, sincr il /\ is_indexed_elements l2 il l1.
Proof.
  intros.
  revert l1 H; induction l2; simpl; intros.
  + destruct l1; try tauto.
    exists nil.
    pose proof is_indexed_elements_nil (@nil A).
    tauto.
  + destruct l1.
    - exists nil.
      pose proof is_indexed_elements_nil (a :: l2).
      tauto.
    - destruct H as [| [? ?] ].
      * set (l1' := a0 :: l1) in *.
        clearbody l1'.
        clear l1 a0.
        rename l1' into l1.
        apply IHl2 in H.
        destruct H as [il [? ?] ].
        exists (map (fun z => z + 1) il).
        split.
       ++ apply sincr_add_1, H.
       ++ unfold is_indexed_elements.
          apply Forall2_map1.
          revert H0; apply Forall2_impl.
          intros n a0 ?.
          apply (Znth_error_Some_cons n); tauto.
      * subst a0.
        apply IHl2 in H0.
        destruct H0 as [il [? ?] ].
        exists (0 :: map (fun z => z + 1) il).
        split.
       ++ apply sincr_cons.
         -- rewrite Forall_map.
            apply is_indexed_elements_range in H0.
            revert H0; apply Forall_impl.
            intros; lia.
         -- apply sincr_add_1, H.
       ++ apply is_indexed_elements_cons.
         -- apply Znth_error_cons_0.
         -- unfold is_indexed_elements.
            apply Forall2_map1.
            revert H0; apply Forall2_impl.
            intros n a0 ?.
            apply (Znth_error_Some_cons n); tauto.
Qed.

Theorem is_subsequence_spec:
  forall {A: Type} (l1 l2: list A) il,
    sincr il ->
    is_indexed_elements l2 il l1 ->
    is_subsequence l1 l2.
Proof.
  intros.
  revert il l1 H H0; induction l2; intros.
  + destruct l1 as [ | a l1]. 
    { simpl; tauto. }
    apply is_indexed_elements_cons_inv_r in H0.
    destruct H0 as [i [_ [_ [? _]]]].
    apply Znth_error_range in H0.
    change (Zlength []) with 0 in H0.
    lia.
  + destruct l1 as [ | b l1]. 
    { simpl; tauto. }
    pose proof is_indexed_elements_cons_inv_r _ _ _ _ H0.
    destruct H1 as [i [il' [? [? ?]]]].
    subst il; rename il' into il.
    destruct (Z_le_gt_dec i 0).
    - assert (i = 0). {
        apply Znth_error_range in H2.
        lia.
      }
      clear l.
      subst.
      rewrite Znth_error_cons_0 in H2.
      injection H2 as ?; subst b.
      simpl.
      right; split; [reflexivity |].
      apply (IHl2 (map (fun z => z - 1) il)).
      * apply sincr_sub_1.
        destruct il; simpl in *; tauto.
      * apply sincr_cons_tail_Forall_lt in H.
        unfold is_indexed_elements in H3 |- *.
        pose proof Forall2_and_Forall_l _ _ _ _ H H3.
        clear H H3.
        apply Forall2_map1.
        revert H1; apply Forall2_impl.
        intros n a0 [? ?].
        rewrite (Znth_error_cons (n - 1)) in H1 by lia.
        tauto.
    - simpl.
      left.
      apply (IHl2 (map (fun z => z - 1) (i :: il))).
      * apply sincr_sub_1.
        destruct il; simpl in *; tauto.
      * pose proof sincr_cons_Forall_lt 0 i _ ltac:(lia) H.
        clear H3.
        unfold is_indexed_elements in H0 |- *.
        pose proof Forall2_and_Forall_l _ _ _ _ H1 H0.
        clear H1 H0.
        apply Forall2_map1.
        revert H3; apply Forall2_impl.
        intros n a0 [? ?].
        rewrite (Znth_error_cons (n - 1)) in H1 by lia.
        tauto.
Qed.
