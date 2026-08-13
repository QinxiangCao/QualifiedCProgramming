Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersFacts.
Require Export SetsClass.SetsClass.
Require Import AUXLib.ListLib.
Require Import AUXLib.OrdersDecFact.
Local Open Scope sets.

Module Type NODE_SIG := Typ.

Module Type BIN_TREE_SIG (Node: NODE_SIG).

Parameter t: Type.
Parameter empty: t.
Parameter make_tree: Node.t -> t -> t -> t.

Axiom t_ind: forall P: t -> Prop,
  P empty ->
  (forall n l, P l -> forall r, P r -> P (make_tree n l r)) ->
  (forall tr, P tr).

Parameter t_rec: forall P: t -> Set,
  P empty ->
  (forall n l, P l -> forall r, P r -> P (make_tree n l r)) ->
  (forall tr, P tr).

Parameter t_rect: forall P: t -> Type,
  P empty ->
  (forall n l, P l -> forall r, P r -> P (make_tree n l r)) ->
  (forall tr, P tr).

Axiom t_rec_empty: forall P f1 f2,
  t_rec P f1 f2 empty = f1.

Axiom t_rec_make_tree: forall P f1 f2 n tr1 tr2,
  t_rec P f1 f2 (make_tree n tr1 tr2) =
  f2 n tr1 (t_rec P f1 f2 tr1) tr2 (t_rec P f1 f2 tr2).

Axiom t_rect_empty: forall P f1 f2,
  t_rect P f1 f2 empty = f1.

Axiom t_rect_make_tree: forall P f1 f2 n tr1 tr2,
  t_rect P f1 f2 (make_tree n tr1 tr2) =
  f2 n tr1 (t_rect P f1 f2 tr1) tr2 (t_rect P f1 f2 tr2).

Definition t_case: forall P: t -> Set,
  P empty ->
  (forall n l r, P (make_tree n l r)) ->
  (forall tr, P tr) :=
  fun P f1 f2 => t_rec P f1 (fun n l _ r _ => f2 n l r).

Definition t_caset: forall P: t -> Type,
  P empty ->
  (forall n l r, P (make_tree n l r)) ->
  (forall tr, P tr) :=
  fun P f1 f2 => t_rect P f1 (fun n l _ r _ => f2 n l r).

Lemma t_case_empty: forall P f1 f2, t_case P f1 f2 empty = f1.
Proof.
  unfold t_case; intros; apply t_rec_empty.
Qed.

Lemma t_case_make_tree: forall P f1 f2 n tr1 tr2,
  t_case P f1 f2 (make_tree n tr1 tr2) = f2 n tr1 tr2.
Proof.
  unfold t_case; intros; apply t_rec_make_tree.
Qed.

Lemma t_caset_empty: forall P f1 f2, t_caset P f1 f2 empty = f1.
Proof.
  unfold t_caset; intros; apply t_rect_empty.
Qed.

Lemma t_caset_make_tree: forall P f1 f2 n tr1 tr2,
  t_caset P f1 f2 (make_tree n tr1 tr2) = f2 n tr1 tr2.
Proof.
  unfold t_caset; intros; apply t_rect_make_tree.
Qed.

End BIN_TREE_SIG.

Module Type KEY_SIG (Node: NODE_SIG).
Include OrderedTypeFull.
Include LtIsTotal.
Include OrderedTypeFullFacts.
Include OrderedTypeFullDecFacts.
Parameter of_node: Node.t -> t.
End KEY_SIG.

Module Type KEY_NOTAIION_SIG (Node: NODE_SIG) (Key: KEY_SIG Node).
Include (EqLtLeNotation Key).
Include (CmpNotation Key Key).
Notation "x '.(key)'" := (Key.of_node x) (at level 1).

Definition Sets_singleton_setoid (k: Key.t): Key.t -> Prop :=
  fun k0 => k0 == k.

Definition key_keys_lt (k1: Key.t) (ks2: Key.t -> Prop): Prop :=
  forall k2, ks2 k2 -> k1 < k2.

Definition keys_key_lt (ks1: Key.t -> Prop) (k2: Key.t): Prop :=
  forall k1, ks1 k1 -> k1 < k2.

Definition keys_keys_lt (ks1 ks2: Key.t -> Prop): Prop :=
  forall k1 k2, ks1 k1 -> ks2 k2 -> k1 < k2.

Notation "x -<= y" := (key_keys_lt x y) (at level 70).
Notation "x =<- y" := (keys_key_lt x y) (at level 70).
Notation "x =<= y" := (keys_keys_lt x y) (at level 70).

#[local] Instance Sets_singleton_setoid_congr:
  Proper (Key.eq ==> Sets.equiv) Sets_singleton_setoid.
Proof.
  unfold Proper, respectful.
  intros.
  unfold Sets_singleton_setoid.
  sets_unfold.
  intros.
  split; intros; Key.order.
Qed.

#[local] Instance keys_keys_lt_congr:
  Proper (Sets.equiv ==> Sets.equiv ==> iff) keys_keys_lt.
Proof.
  unfold Proper, respectful.
  sets_unfold; unfold keys_keys_lt; intros.
  split; intros.
  + apply H1; rewrite ?H, ?H0; tauto.
  + apply H1; rewrite <- ?H, <- ?H0; tauto.
Qed.

#[local] Instance key_keys_lt_congr:
  Proper (Key.eq ==> Sets.equiv ==> iff) key_keys_lt.
Proof.
  unfold Proper, respectful.
  sets_unfold; unfold key_keys_lt; intros.
  split; intros.
  + rewrite <- H0 in H2. apply H1 in H2. Key.order.
  + rewrite H0 in H2. apply H1 in H2. Key.order.
Qed.

#[local] Instance keys_key_lt_congr:
  Proper (Sets.equiv ==> Key.eq ==> iff) keys_key_lt.
Proof.
  unfold Proper, respectful.
  sets_unfold; unfold keys_key_lt; intros.
  split; intros.
  + rewrite <- H in H2. apply H1 in H2. Key.order.
  + rewrite H in H2. apply H1 in H2. Key.order.
Qed.

Theorem empty_set_keys_keys_lt: forall ks, ∅ =<= ks.
Proof. intros ks ? ? []. Qed.

Theorem keys_keys_lt_empty_set: forall ks, ks =<= ∅.
Proof. intros ks ? ? ? []. Qed.

Theorem keys_keys_lt_union: forall ks1 ks2 ks3,
  ks1 =<= ks2 ∪ ks3 <->
  ks1 =<= ks2 /\ ks1 =<= ks3.
Proof.
  intros.
  split; intros.
  + split; intros k1 k ? ?.
    - apply H; sets_unfold; tauto.
    - apply H; sets_unfold; tauto.
  + destruct H.
    intros k1 k; sets_unfold.
    specialize (H k1 k).
    specialize (H0 k1 k).
    tauto.
Qed.

Theorem union_keys_keys_lt: forall ks1 ks2 ks3,
  ks1 ∪ ks2 =<= ks3 <->
  ks1 =<= ks3 /\ ks2 =<= ks3.
Proof.
  intros.
  split; intros.
  + split; intros k k3 ? ?.
    - apply H; sets_unfold; tauto.
    - apply H; sets_unfold; tauto.
  + destruct H.
    intros k k3; sets_unfold.
    specialize (H k k3).
    specialize (H0 k k3).
    tauto.
Qed.


Theorem keys_keys_lt_intersect: forall ks1 ks2 ks3,
  ks1 =<= ks2 \/ ks1 =<= ks3 ->
  ks1 =<= ks2 ∩ ks3.
Proof.
  intros.
  unfold keys_keys_lt in *.
  sets_unfold.
  intros.
  destruct H ; apply H; tauto.
Qed.

Theorem intersect_keys_keys_lt_l: forall ks1 ks2 ks3,
  ks1 =<= ks3 ->
  ks1 ∩ ks2 =<= ks3.
Proof.
  intros.
  unfold keys_keys_lt in *.
  sets_unfold.
  intros.
  apply H; tauto.
Qed.

Theorem intersect_keys_keys_lt_r: forall ks1 ks2 ks3,
  ks2 =<= ks3 ->
  ks1 ∩ ks2 =<= ks3.
Proof.
  intros.
  unfold keys_keys_lt in *.
  sets_unfold.
  intros.
  apply H; tauto.
Qed.

Fixpoint keys_union (kss: list (Key.t -> Prop)):
  Key.t -> Prop :=
  match kss with
  | nil => ∅
  | ks0 :: kss1 => ks0 ∪ keys_union kss1
  end.

Lemma keys_union_iff: forall kss,
  (forall k, keys_union kss k <-> exists ks, List.In ks kss /\ ks k).
Proof.
  intros.
  induction kss; simpl.
  + sets_unfold.
    split; [tauto |].
    intros [? [? ?]].
    tauto.
  + sets_unfold.
    rewrite IHkss; clear IHkss.
    split; intros.
    - destruct H as [? | [? [? ?]]].
      * exists a; tauto.
      * exists x; tauto.
    - destruct H as [ks [[? | ?] ?]].
      * left.
        subst.
        tauto.
      * right; exists ks.
        tauto.
Qed.

Fixpoint keys_list_lt (kss: list (Key.t -> Prop)): Prop :=
  match kss with
  | nil => True
  | ks0 :: kss1 =>
      ks0 =<= keys_union kss1 /\
      keys_list_lt kss1
  end.

Theorem key_key_lt_iff:
  forall k1 k2,
    k1 < k2 <-> Sets_singleton_setoid k1 =<= Sets_singleton_setoid k2.
Proof.
  intros.
  unfold Sets_singleton_setoid.
  unfold keys_keys_lt.
  split; intros.
  + Key.order.
  + specialize (H k1 k2 ltac:(reflexivity) ltac:(reflexivity)).
    tauto.
Qed.

Theorem keys_key_lt_iff:
  forall ks k,
    ks =<- k <-> ks =<= Sets_singleton_setoid k.
Proof.
  intros.
  unfold Sets_singleton_setoid.
  split.
  + intros H k1 k2.
    specialize (H k1).
    intros.
    rewrite H1; tauto.
  + intros H k1.
    specialize (H k1 k).
    simpl in H.
    assert (k == k) by reflexivity.
    tauto.
Qed.

Theorem key_keys_lt_iff:
  forall k ks,
    k -<= ks <-> Sets_singleton_setoid k =<= ks.
Proof.
  intros.
  unfold Sets_singleton_setoid.
  split.
  + intros H k1 k2.
    specialize (H k2).
    intros.
    rewrite H0; tauto.
  + intros H k2.
    specialize (H k k2).
    simpl in H.
    assert (k == k) by reflexivity.
    tauto.
Qed.

Theorem keys_key_keys_lt_trans :
  forall ks1 ks2 ks3,
    ks1 =<- ks2 ->
    ks2 -<= ks3 ->
    ks1 =<= ks3.
Proof.
  intros.
  unfold keys_key_lt, key_keys_lt, keys_keys_lt in *.
  intros.
  specialize (H k1 H1).
  specialize (H0 k2 H2).
  Key.order.
Qed.

Theorem key_key_keys_lt_trans :
  forall ks1 ks2 ks3,
    ks1 < ks2 ->
    ks2 -<= ks3 ->
    ks1 -<= ks3.
Proof.
  intros.
  unfold key_keys_lt in *.
  intros.
  specialize (H0 k2 H1).
  Key.order.
Qed.

Theorem keys_union_app:
  forall kss1 kss2,
    (keys_union (kss1 ++ kss2) ==
     keys_union kss1 ∪ keys_union kss2)%sets.
Proof.
  intros.
  induction kss1; simpl.
  + rewrite Sets_empty_union.
    reflexivity.
  + rewrite IHkss1.
    rewrite Sets_union_assoc.
    reflexivity.
Qed.

Theorem keys_list_lt_app_iff:
  forall kss1 kss2,
    keys_list_lt (kss1 ++ kss2) <->
    keys_list_lt kss1 /\
    keys_list_lt kss2 /\
    keys_union kss1 =<= keys_union kss2.
Proof.
  intros.
  induction kss1; simpl.
  + pose proof empty_set_keys_keys_lt (keys_union kss2).
    tauto.
  + rewrite keys_union_app.
    rewrite keys_keys_lt_union.
    rewrite union_keys_keys_lt.
    tauto.
Qed.

Theorem keys_sublist_lt:
  forall kss1 kss2 kss3,
    keys_list_lt (kss1 ++ kss2 ++ kss3) ->
    keys_list_lt kss2.
Proof.
  intros.
  rewrite !keys_list_lt_app_iff in H.
  tauto.
Qed.

Theorem keys_list_lt_replace_sublist:
  forall kss1 kss2 kss2' kss3,
    (keys_list_lt kss2 ->
      keys_list_lt kss2' /\
      (keys_union kss2 == keys_union kss2')%sets) ->
    keys_list_lt (kss1 ++ kss2 ++ kss3) ->
    keys_list_lt (kss1 ++ kss2' ++ kss3).
Proof.
  intros.
  revert H0.
  rewrite !keys_list_lt_app_iff.
  rewrite !keys_union_app.
  rewrite !keys_keys_lt_union.
  intros [? [? ?]].
  destruct H1 as [? [? ?]].
  specialize (H H1).
  destruct H.
  rewrite H5 in *.
  tauto.
Qed.

Theorem keys_list_lt_replace_1:
  forall kss1 ks2 ks2' kss3,
    (ks2 == ks2')%sets ->
    keys_list_lt (kss1 ++ ks2 :: kss3) ->
    keys_list_lt (kss1 ++ ks2' :: kss3).
Proof.
  intros.
  revert H0.
  rewrite !keys_list_lt_app_iff.
  simpl.
  rewrite !keys_keys_lt_union.
  rewrite H.
  tauto.
Qed.

Lemma keys_list_lt_len_2: forall ks1 ks2,
  keys_list_lt (ks1 :: ks2 :: nil) <-> ks1 =<= ks2.
Proof.
  intros.
  simpl.
  rewrite Sets_union_empty.
  pose proof keys_keys_lt_empty_set ks2.
  tauto.
Qed.

End KEY_NOTAIION_SIG.

Module Type VALUE_SIG (Node: NODE_SIG).
Parameter t: Type.
Parameter of_node: Node.t -> t.
Axiom eq_dec : forall x y : t, {x = y} + {x <> y}.
End VALUE_SIG.

Module Type VALUE_NOTAIION_SIG (Node: NODE_SIG) (Value: VALUE_SIG Node).
Notation "x '.(val)'" := (Value.of_node x) (at level 1).
End VALUE_NOTAIION_SIG.

Module Type BinaryTreeBasic
              (Node: NODE_SIG)
              (BinTree: BIN_TREE_SIG Node).

Definition elements: BinTree.t -> list Node.t :=
  BinTree.t_rect
    (fun _ => list Node.t)
    (nil)
    (fun n l el r er => n :: el ++ er).

Theorem elements_empty: elements BinTree.empty = nil.
Proof.
  unfold elements.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Theorem elements_make_tree:
  forall n l r n0,
    List.In n0 (elements (BinTree.make_tree n l r)) <->
    n = n0 \/ List.In n0 (elements l) \/ List.In n0 (elements r).
Proof.
  intros.
  unfold elements.
  rewrite BinTree.t_rect_make_tree.
  simpl List.In.
  rewrite in_app_iff.
  tauto.
Qed.

Definition In (n: Node.t) (tr: BinTree.t): Prop :=
  List.In n (elements tr).

Theorem not_in_empty: forall n, ~ In n BinTree.empty.
Proof.
  unfold In.
  rewrite elements_empty.
  simpl.
  tauto.
Qed.

Theorem in_empty_iff: forall n, In n BinTree.empty <-> False.
Proof.
  unfold In.
  rewrite elements_empty.
  simpl.
  tauto.
Qed.

Theorem in_make_tree_iff:
  forall n l r n0,
    In n0 (BinTree.make_tree n l r) <->
    n = n0 \/ In n0 l \/ In n0 r.
Proof.
  unfold In.
  apply elements_make_tree.
Qed.

Theorem forall_in_empty: forall (P: Node.t -> Prop),
  (forall n, In n BinTree.empty -> P n) <->
  True.
Proof.
  intros.
  split; [tauto |].
  intros.
  rewrite in_empty_iff in H0.
  tauto.
Qed.

Theorem forall_in_make_tree: forall (P: Node.t -> Prop) n l r,
  (forall n0, In n0 (BinTree.make_tree n l r) -> P n0) <->
  P n/\
  (forall n0, In n0 l -> P n0) /\
  (forall n0, In n0 r -> P n0).
Proof.
  intros.
  split; intros.
  + split; [| split].
    - specialize (H n).
      rewrite in_make_tree_iff in H.
      tauto.
    - intros n0; specialize (H n0).
      rewrite in_make_tree_iff in H.
      tauto.
    - intros n0; specialize (H n0).
      rewrite in_make_tree_iff in H.
      tauto.
  + destruct H as [? [? ?]].
    specialize (H1 n0).
    specialize (H2 n0).
    rewrite in_make_tree_iff in H0.
    destruct H0; [subst |]; tauto.
Qed.

End BinaryTreeBasic.

Module Type MAP_SIG
              (Node: NODE_SIG)
              (Key: KEY_SIG Node)
              (Value: VALUE_SIG Node).

Definition equiv (m1 m2: Key.t -> option Value.t): Prop :=
  forall k, m1 k = m2 k.

Definition empty: Key.t -> option Value.t :=
  fun k => None.

Definition singleton (k0: Key.t) (v0: Value.t): Key.t -> option Value.t :=
  fun k =>
    if Key.eq_dec k k0
    then Some v0
    else None.

Definition merge (m1 m2: Key.t -> option Value.t): Key.t -> option Value.t :=
  fun k =>
    match m1 k, m2 k with
    | Some v, None => Some v
    | None, Some v => Some v
    | Some v1, Some v2 =>
      if Value.eq_dec v1 v2
      then Some v1
      else None
    | _, _ => None
    end.

Definition filter_lt (k0: Key.t) (m: Key.t -> option Value.t):
  Key.t -> option Value.t :=
  fun k =>
    if Key.lt_ge_dec k k0
    then m k
    else None.

Definition filter_gt (k0: Key.t) (m: Key.t -> option Value.t):
  Key.t -> option Value.t :=
  fun k =>
    if Key.gt_le_dec k k0
    then m k
    else None.

Definition insert (k0: Key.t) (v0: Value.t) (m: Key.t -> option Value.t):
  Key.t -> option Value.t :=
  fun k =>
    if Key.eq_dec k k0
    then Some v0
    else m k.

Definition delete (k0: Key.t) (m: Key.t -> option Value.t):
  Key.t -> option Value.t :=
  fun k =>
    if Key.eq_dec k k0
    then None
    else m k.

Definition domain (m: Key.t -> option Value.t): Key.t -> Prop :=
  fun k =>
    match m k with
    | Some _ => True
    | _ => False
    end.

End MAP_SIG.

Module Type MapFacts
              (Node: NODE_SIG)
              (Key: KEY_SIG Node)
              (Value: VALUE_SIG Node)
              (Map: MAP_SIG Node Key Value)
              (Import KeyNotation: KEY_NOTAIION_SIG Node Key)
              (Import ValueNotation: VALUE_NOTAIION_SIG Node Value).

Notation "x '.(domain)'" := (Map.domain x) (at level 1).
Notation "x + y" := (Map.merge x y).
Notation "m1 === m2" := (equiv m1 m2) (at level 70).

Theorem empty_iff:
  forall k v,
    Map.empty k = Some v <-> False.
Proof.
  intros.
  unfold Map.empty.
  assert (None <> Some v) by congruence.
  tauto.
Qed.

Theorem single_iff:
  forall k v k0 v0,
    ((Map.singleton k v) k0 = Some v0 <-> k0 == k /\ v0 = v).
Proof.
  intros.
  unfold Map.singleton.
  destruct (Key.eq_dec k0 k).
  + assert (Some v = Some v0 <-> v0 = v) by (split; intros; congruence).
    tauto.
  + assert (None <> Some v0) by congruence.
    tauto.
Qed.

Theorem merge_iff:
  forall m1 m2 k v,
    m1.(domain) =<= m2.(domain) ->
    ((m1 + m2) k = Some v <-> m1 k = Some v \/ m2 k = Some v).
Proof.
  intros.
  unfold Map.merge.
  specialize (H k k).
  unfold Map.domain in H.
  destruct (m1 k), (m2 k).
  + specialize (H I I).
    Key.order.
  + assert (None <> Some v) by congruence.
    tauto.
  + assert (None <> Some v) by congruence.
    tauto.
  + tauto.
Qed.

Theorem filter_lt_iff:
  forall m k0 k v,
    (Map.filter_lt k0 m) k = Some v <->
    m k = Some v /\ k < k0.
Proof.
  intros.
  unfold Map.filter_lt.
  destruct (Key.lt_ge_dec k k0).
  + tauto.
  + assert (None <> Some v) by congruence.
    assert (~ k < k0) by Key.order.
    tauto.
Qed.

Theorem filter_gt_iff:
  forall m k0 k v,
    (Map.filter_gt k0 m) k = Some v <->
    m k = Some v /\ k0 < k.
Proof.
  intros.
  unfold Map.filter_gt.
  destruct (Key.gt_le_dec k k0).
  + tauto.
  + assert (None <> Some v) by congruence.
    assert (~ k0 < k) by Key.order.
    tauto.
Qed.

Theorem filter_lt_eq:
  forall m k0 k, k < k0 ->
  (Map.filter_lt k0 m) k = m k.
Proof.
  intros.
  unfold Map.filter_lt.
  destruct (Key.lt_ge_dec k k0).
  + reflexivity.
  + exfalso; Key.order.
Qed.

Theorem filter_gt_eq:
  forall m k0 k, k0 < k ->
  (Map.filter_gt k0 m) k = m k.
Proof.
  intros.
  unfold Map.filter_gt.
  destruct (Key.gt_le_dec k k0).
  + reflexivity.
  + exfalso; Key.order.
Qed.

Theorem insert_iff: forall k v m k0 v0,
  (Map.insert k v m) k0 = Some v0 <->
  k0 == k /\ v0 = v \/ k0 ~= k /\ m k0 = Some v0.
Proof.
  intros.
  unfold Map.insert.
  destruct (Key.eq_dec k0 k).
  + assert (Some v = Some v0 <-> v0 = v) by (split; intros; congruence).
    tauto.
  + tauto.
Qed.

Theorem delete_iff: forall k m k0 v0,
  (Map.delete k m) k0 = Some v0 <->
  k0 ~= k /\ m k0 = Some v0.
Proof.
  intros.
  unfold Map.delete.
  destruct (Key.eq_dec k0 k).
  + split ; intros.
    - congruence.
    - tauto.
  + tauto.
Qed.

Theorem empty_domain: (Map.empty.(domain) == ∅)%sets.
Proof.
  sets_unfold.
  intros k.
  unfold Map.domain.
  unfold Map.empty.
  tauto.
Qed.

Theorem singleton_domain:
  forall k v, ((Map.singleton k v).(domain) == Sets_singleton_setoid k)%sets.
Proof.
  unfold Sets_singleton_setoid.
  sets_unfold.
  intros k v k0.
  unfold Map.domain.
  unfold Map.singleton.
  destruct (Key.eq_dec k0 k).
  + tauto.
  + tauto.
Qed.

Theorem merge_domain: forall m1 m2,
  m1.(domain) =<= m2.(domain) ->
  ((m1 + m2).(domain) == m1.(domain) ∪ m2.(domain))%sets.
Proof.
  intros.
  sets_unfold.
  intros k.
  specialize (H k k).
  unfold Map.domain in *.
  unfold Map.merge.
  destruct (m1 k), (m2 k).
  + specialize (H I I).
    Key.order.
  + tauto.
  + tauto.
  + tauto.
Qed.

Theorem insert_domain: forall k v m,
  ((Map.insert k v m).(domain) == Sets_singleton_setoid k ∪ m.(domain))%sets.
Proof.
  intros; unfold Sets_singleton_setoid; sets_unfold; intros k0.
  unfold Map.domain, Map.insert.
  destruct (Key.eq_dec k0 k).
  + tauto.
  + tauto.
Qed.

Theorem delete_domain: forall k m,
  ((Map.delete k m).(domain) == m.(domain) ∩ (Sets.complement  (Sets_singleton_setoid k)))%sets.
Proof.
  intros ; unfold Sets_singleton_setoid; sets_unfold; intros k0.
  unfold Map.domain, Map.delete.
  destruct (Key.eq_dec k0 k).
  + tauto.
  + tauto.
Qed.

#[local] Existing Instance keys_keys_lt_congr.

Theorem domain_list_lt_merge:
  forall ms1 m2 m3 ms4,
    keys_list_lt
      (map Map.domain (ms1 ++ m2 :: m3 :: ms4)) ->
    keys_list_lt
      (map Map.domain (ms1 ++ (m2 + m3) :: ms4)).
Proof.
  intros ? ? ? ?.
  rewrite !map_app; simpl map.
  apply (keys_list_lt_replace_sublist
           (map Map.domain ms1)
           (m2.(domain) :: m3.(domain) :: nil)
           ((m2 + m3).(domain) :: nil)
           (map Map.domain ms4)).
  simpl.
  rewrite !Sets_union_empty.
  intros [? _].
  rewrite merge_domain by tauto.
  split.
  + pose proof keys_keys_lt_empty_set (m2.(domain) ∪ m3.(domain)).
    tauto.
  + reflexivity.
Qed.

Theorem domain_list_lt_unmerge:
  forall ms1 m2 m3 ms4,
    m2.(domain) =<= m3.(domain) ->
    keys_list_lt
      (map Map.domain (ms1 ++ (m2 + m3) :: ms4)) ->
    keys_list_lt
      (map Map.domain (ms1 ++ m2 :: m3 :: ms4)).
Proof.
  intros ? ? ? ? ?.
  rewrite !map_app; simpl map.
  apply (keys_list_lt_replace_sublist
           (map Map.domain ms1)
           ((m2 + m3).(domain) :: nil)
           (m2.(domain) :: m3.(domain) :: nil)
           (map Map.domain ms4)).
  simpl.
  rewrite !Sets_union_empty.
  rewrite merge_domain by tauto.
  intros _.
  pose proof keys_keys_lt_empty_set (m3.(domain)).
  split.
  + tauto.
  + reflexivity.
Qed.

Theorem domain_sublist_lt:
  forall ms1 ms2 ms3,
    keys_list_lt (map Map.domain (ms1 ++ ms2 ++ ms3)) ->
    keys_list_lt (map Map.domain ms2).
Proof.
  intros ? ? ?.
  rewrite !map_app.
  apply keys_sublist_lt.
Qed.

End MapFacts.

Module Type SearchTree
              (Node: NODE_SIG)
              (BinTree: BIN_TREE_SIG Node)
              (Key: KEY_SIG Node)
              (Import KeyNotation: KEY_NOTAIION_SIG Node Key)
              (Import BTB: BinaryTreeBasic Node BinTree).

Definition key_set (tr: BinTree.t): Key.t -> Prop :=
  keys_union
    (map Sets_singleton_setoid (map Key.of_node (elements tr))).

Notation "x '.(keys)'" := (key_set x) (at level 1).

Definition SearchTree: BinTree.t -> Prop :=
  BinTree.t_rect
    (fun _ => Prop)
    (True)
    (fun n l Pl r Pr =>
       l.(keys) =<- n.(key) /\
       n.(key) -<= r.(keys) /\
       Pl /\ Pr).

Theorem SearchTree_empty: SearchTree BinTree.empty.
Proof. unfold SearchTree. rewrite BinTree.t_rect_empty. tauto. Qed.

Theorem SearchTree_make_tree:
  forall n l r,
    SearchTree (BinTree.make_tree n l r) <->
    l.(keys) =<- n.(key) /\
    n.(key) -<= r.(keys) /\
    SearchTree l /\ SearchTree r.
Proof.
  unfold SearchTree.
  intros.
  rewrite BinTree.t_rect_make_tree.
  reflexivity.
Qed.

Lemma key_set_equiv : forall tr k, 
  tr.(keys) k <-> k ∈ tr.(keys).
Proof.
  intros.
  split.
  + tauto.
  + tauto.
Qed.

Theorem key_set_empty:
  (BinTree.empty.(keys) == ∅)%sets.
Proof.
  unfold key_set; sets_unfold; intros.
  rewrite elements_empty.
  simpl.
  tauto.
Qed.

Theorem key_set_make_tree:
  forall n l r,
    ((BinTree.make_tree n l r).(keys) ==
      (l.(keys) ∪ Sets_singleton_setoid n.(key) ∪ r.(keys)))%sets.
Proof.
  unfold key_set.
  intros.
  sets_unfold.
  intro k.
  rewrite keys_union_iff.
  rewrite map_map.
  pose proof in_map_iff (fun x : Node.t => Sets_singleton_setoid x.(key)).
  simpl in H.
  assert (forall P Q R: Prop, (P /\ (Q \/ R) <-> P /\ Q \/ P /\ R))
    by (intros; tauto).
  assert (forall P Q: Node.t -> Prop,
            (exists x, P x \/ Q x) <->
            (exists x, P x) \/ (exists x, Q x)) by firstorder.
  assert (forall P Q R: Prop, ((P \/ Q) /\ R <-> P /\ R \/ Q /\ R))
    by (intros; tauto).
  assert (forall P Q: (Key.t -> Prop) -> Prop,
            (exists x, P x \/ Q x) <->
            (exists x, P x) \/ (exists x, Q x)) by firstorder.
  assert (forall n y,
            List.In y (map (fun x => Sets_singleton_setoid x.(key)) (n :: nil)) 
            <->
            (exists x, Sets_singleton_setoid x.(key) = y /\ n = x)).
  {
    intros; simpl. firstorder. subst. tauto.
  }
  setoid_rewrite H.
  setoid_rewrite elements_make_tree.
  setoid_rewrite H0.
  setoid_rewrite H0.
  setoid_rewrite H1.
  setoid_rewrite H1.
  setoid_rewrite H2.
  setoid_rewrite H2.
  setoid_rewrite <- H.
  setoid_rewrite <- H4.
  rewrite H3.
  rewrite H3.
  rewrite <- (map_map Key.of_node Sets_singleton_setoid).
  rewrite <- (map_map Key.of_node Sets_singleton_setoid).
  rewrite <- (map_map Key.of_node Sets_singleton_setoid).
  rewrite <- keys_union_iff.
  rewrite <- keys_union_iff.
  rewrite <- keys_union_iff.
  simpl.
  sets_unfold.
  tauto.
Qed.

#[local] Existing Instance keys_keys_lt_congr.

Theorem key_set_list_lt_make_tree:
  forall kss1 kss2 n l r,
    SearchTree (BinTree.make_tree n l r) ->
    keys_list_lt
      (kss1 ++ (BinTree.make_tree n l r).(keys) :: kss2) ->
    keys_list_lt
      (kss1 ++ l.(keys) :: Sets_singleton_setoid n.(key) :: r.(keys) :: kss2).
Proof.
  intros.
  revert H0.
  apply (keys_list_lt_replace_sublist
           kss1
           ((BinTree.make_tree n l r).(keys) :: nil)
           (l.(keys) :: Sets_singleton_setoid n.(key) :: r.(keys) :: nil)
           kss2).
  intros _.
  split.
  + simpl.
    rewrite Sets_union_empty.
    pose proof keys_keys_lt_empty_set r.(keys).
    rewrite keys_keys_lt_union.
    rewrite <- keys_key_lt_iff.
    rewrite <- key_keys_lt_iff.
    rewrite SearchTree_make_tree in H.
    repeat split; try tauto.
    destruct H as [? [? _]].
    intros k1 k2 Hk1 Hk2.
    specialize (H k1 Hk1).
    specialize (H1 k2 Hk2).
    Key.order.
  + simpl.
    rewrite key_set_make_tree.
    rewrite !Sets_union_assoc.
    reflexivity.
Qed.

End SearchTree.

Module Type Abstraction
              (Node: NODE_SIG)
              (BinTree: BIN_TREE_SIG Node)
              (Key: KEY_SIG Node)
              (Value: VALUE_SIG Node)
              (Map: MAP_SIG Node Key Value)
              (Import KeyNotation: KEY_NOTAIION_SIG Node Key)
              (Import ValueNotation: VALUE_NOTAIION_SIG Node Value)
              (Import BTB: BinaryTreeBasic Node BinTree)
              (Import MF: MapFacts Node Key Value Map KeyNotation ValueNotation)
              (Import ST: SearchTree Node BinTree Key KeyNotation BTB).

Definition tree_kv (tr: BinTree.t) (k: Key.t) (v: Value.t): Prop :=
  exists n, In n tr /\ k == n.(key) /\ v = n.(val).

Lemma tree_kv_empty: forall k v,
  ~ tree_kv BinTree.empty k v.
Proof.
  intros.
  unfold tree_kv.
  intros [n [? _]].
  rewrite in_empty_iff in H.
  tauto.
Qed.

Lemma tree_kv_empty_iff: forall k v,
  tree_kv BinTree.empty k v <-> False.
Proof. intros. pose proof tree_kv_empty k v. tauto. Qed.

Lemma tree_kv_make_tree_iff: forall n l r k v,
  tree_kv (BinTree.make_tree n l r) k v <->
  tree_kv l k v \/
  k == n.(key) /\ v = n.(val) \/
  tree_kv r k v.
Proof.
  intros.
  unfold tree_kv.
  split.
  + intros [n0 [? [? ?]]].
    rewrite in_make_tree_iff in H.
    destruct H as [? | [? | ?]].
    - right; left.
      subst; tauto.
    - left.
      exists n0.
      tauto.
    - right; right.
      exists n0.
      tauto.
  + setoid_rewrite in_make_tree_iff.
    intros [? | [? | ?]].
    - destruct H as [n0 [? [? ?]]].
      exists n0.
      tauto.
    - exists n.
      tauto.
    - destruct H as [n0 [? [? ?]]].
      exists n0.
      tauto.
Qed.

Definition tree_kv_key_set: forall tr k v,
  tree_kv tr k v -> tr.(keys) k.
Proof.
  unfold tree_kv, key_set, In.
  intros.
  destruct H as [n [? [? ?]]].
  rewrite keys_union_iff.
  exists (Sets_singleton_setoid n.(key)).
  split.
  + apply in_map.
    apply in_map.
    tauto.
  + unfold Sets_singleton_setoid.
    tauto.
Qed.


Definition Abs (tr: BinTree.t) (m: Key.t -> option Value.t): Prop :=
  forall k v,
    m k = Some v <-> tree_kv tr k v.

Lemma Abs_domain:
  forall tr m,
    Abs tr m -> (tr.(keys) == m.(domain))%sets.
Proof.
  unfold Abs.
  sets_unfold.
  unfold In, Map.domain, key_set, Sets_singleton_setoid.
  intros.
  rewrite map_map.
  rewrite keys_union_iff.
  specialize (H a).
  destruct (m a).
  + specialize (H t).
    pose proof proj1 H eq_refl.
    destruct H0 as [n [? [? ?]]].
    split; [tauto | intros _].
    exists (fun k => k == n.(key)).
    subst.
    split; [| tauto].
    rewrite in_map_iff.
    exists n.
    tauto.
  + split; [| tauto].
    intros [ks [? ?]].
    rewrite in_map_iff in H0.
    destruct H0 as [n [? ?]].
    specialize (H n.(val)).
    pose proof proj2 H; clear H.
    assert (None <> Some n.(val)) by congruence.
    apply H; clear H.
    apply H3; clear H3.
    exists n.
    subst.
    tauto.
Qed.

Theorem Abs_empty: Abs BinTree.empty Map.empty.
Proof.
  unfold Abs; intros.
  unfold Map.empty.
  split; intros; [congruence |].
  destruct H as [n [? [? ?]]].
  rewrite in_empty_iff in H.
  tauto.
Qed.

Theorem Abs_empty_inv:
  forall m, Abs BinTree.empty m -> Map.equiv m Map.empty.
Proof.
  intros.
  unfold Abs in H.
  unfold Map.equiv, Map.empty.
  intros.
  specialize (H k).
  destruct (m k) as [v |]; [| reflexivity].
  specialize (H v).
  destruct H as [? _].
  specialize (H eq_refl).
  destruct H as [n ?].
  rewrite in_empty_iff in H.
  tauto.
Qed.

Ltac unfold_make_tree_in_keys_list_lt_rec f_ks1 ks2 H :=
  match ks2 with
  | nil =>
      let ks := eval cbv beta in (f_ks1 nil) in
      change (keys_list_lt ks) in H
  | cons (BinTree.make_tree ?n ?l ?r).(keys) ?ks2' =>
      apply (key_set_list_lt_make_tree (f_ks1 nil) ks2' n l r) in H; [| tauto];
      match goal with
      | H_ST: SearchTree (BinTree.make_tree n l r) |- _ =>
          rewrite SearchTree_make_tree in H_ST;
          destruct H_ST as [? [? [? ?]]]
      end;
      unfold_make_tree_in_keys_list_lt_rec
        f_ks1
        (l.(keys) :: Sets_singleton_setoid n.(key) :: r.(keys) :: ks2')
        H
  | cons ?k ?ks2' =>
      let f_ks1' := eval cbv beta in
        (fun ks0 => f_ks1 (cons k ks0))
      in
      unfold_make_tree_in_keys_list_lt_rec
        f_ks1'
        ks2'
        H
  end.

Ltac unfold_make_tree_in_keys_list_lt H :=
  match type of H with
  | keys_list_lt ?ks =>
      unfold_make_tree_in_keys_list_lt_rec
        (fun ks0: list (Key.t -> Prop) => ks0)
        ks
        H
  end.

Ltac from_tree_to_map_rec f_ms1 ks2 H :=
  match ks2 with
  | nil => 
      let ms1 := eval cbv beta in (f_ms1 nil) in
        change (keys_list_lt (map Map.domain ms1)) in H
  | cons (?tr).(keys) ?ks2' =>
      match goal with
      | H0: Abs tr ?m |- _ =>
          apply (keys_list_lt_replace_1
                   (map Map.domain (f_ms1 nil))
                   (tr.(keys))
                   (m.(domain))
                   ks2') in H; [| apply Abs_domain, H0];
          let f_ms1' := eval cbv beta in (fun ms => f_ms1 (cons m ms)) in
          from_tree_to_map_rec f_ms1' ks2' H
      end
  | cons (Sets_singleton_setoid (?n).(key)) ?ks2' =>
      apply (keys_list_lt_replace_1
               (map Map.domain (f_ms1 nil))
               (Sets_singleton_setoid (n).(key))
               ((Map.singleton n.(key) n.(val)).(domain))
               ks2') in H; [| symmetry; apply singleton_domain];
      let f_ms1' := eval cbv beta in (fun ms => f_ms1 (cons (Map.singleton n.(key) n.(val)) ms)) in
      from_tree_to_map_rec f_ms1' ks2' H
  end.

Ltac from_tree_to_map H :=
  match type of H with
  | keys_list_lt ?ks =>
      from_tree_to_map_rec
        (fun ms0: list (Key.t -> option Value.t) => ms0)
        ks
        H
  end.

Ltac build_keys_lt l :=
  assert (keys_list_lt (map Map.domain l));
  [ match goal with
    | H: SearchTree ?tr |- _ =>
           let H0 := fresh "H" in
           assert (keys_list_lt (tr.(keys) :: nil)) as H0 by
             (split; [apply keys_keys_lt_empty_set | exact I]);
           unfold_make_tree_in_keys_list_lt H0;
           from_tree_to_map H0; try exact H0
    end |].

Ltac unfold_merge_in_keys_list_lt_rec f_ms1 ms2 :=
  match ms2 with
  | nil =>
      let ms1 := eval cbv beta in (f_ms1 nil) in
      change (keys_list_lt (map Map.domain ms1))
  | cons (Map.merge ?m ?m') ?ms2' =>
      apply (domain_list_lt_merge (f_ms1 nil) m m' ms2');
      unfold_merge_in_keys_list_lt_rec
        f_ms1
        (m :: m' :: ms2')
  | cons ?m ?ms2' =>
      let f_ms1' := eval cbv beta in
        (fun ms0 => f_ms1 (cons m ms0))
      in
      unfold_merge_in_keys_list_lt_rec
        f_ms1'
        ms2'
  end.

Ltac prove_sublist_step2 ms1 ms2 ms3 ms3' H :=
  match ms3' with
  | nil => exact (domain_sublist_lt ms1 ms2 ms3 H)
  | cons ?m3 ?ms4' =>
      match ms3 with
      | cons m3 ?ms4 => prove_sublist_step2 ms1 (ms2 ++ m3 :: nil) ms4 ms4' H
      end
  end.

Ltac prove_sublist_step1 ms1 ms2 ms2' H :=
  match ms2 with
  | cons ?m2 ?ms3 =>
      match ms2' with
      | cons m2 ?ms3' => prove_sublist_step2 ms1 (@nil (Key.t -> option Value.t)) ms2 ms2' H
      | _ => prove_sublist_step1 (ms1 ++ m2 :: nil) ms3 ms2' H
      end
  | _ => prove_sublist_step2 ms1 nil ms2 ms2' H
  end.

Ltac prove_via_sublist :=
  match goal with
  | H: keys_list_lt (map Map.domain ?l) |- keys_list_lt (map Map.domain ?l') =>
      prove_sublist_step1 (@nil (Key.t -> option Value.t)) l l' H
  end.

Ltac prove_from_keys_lt :=
  rewrite <- keys_list_lt_len_2;
  match goal with
  | |- keys_list_lt (?m1.(domain) :: ?m2.(domain) :: nil) =>
         unfold_merge_in_keys_list_lt_rec
           (fun ms: list (Key.t -> option Value.t) => ms)
           (m1 :: m2 :: nil);
         try first [ assumption | prove_via_sublist]
  end.

Theorem Abs_make_tree:
  forall n l r ml mr,
    SearchTree (BinTree.make_tree n l r) ->
    Abs l ml ->
    Abs r mr ->
    Abs
      (BinTree.make_tree n l r)
      (ml + Map.singleton n.(key) n.(val) + mr).
Proof.
  intros.
  build_keys_lt (ml :: Map.singleton n.(key) n.(val) :: mr :: nil).
  unfold Abs; intros.
  rewrite merge_iff by prove_from_keys_lt.
  rewrite merge_iff by prove_from_keys_lt.
  rewrite tree_kv_make_tree_iff.
  specialize (H0 k v).
  specialize (H1 k v).
  rewrite single_iff.
  tauto.
Qed.

Theorem Abs_make_tree_revert:
  forall n l r m,
    SearchTree (BinTree.make_tree n l r) ->
    Abs (BinTree.make_tree n l r) m ->
    Abs l (Map.filter_lt n.(key) m) /\ Abs r (Map.filter_gt n.(key) m) /\ m n.(key) = Some n.(val).
Proof.
  intros.
  rewrite SearchTree_make_tree in H.
  destruct H as [? [? [? ?]]].
  split; [ | split].
  + unfold Abs in *; intros.
    specialize (H0 k v).
    rewrite tree_kv_make_tree_iff in H0.
    destruct H0.
    split; intros.
    - rewrite filter_lt_iff in H5.
      destruct H5.
      specialize (H0 H5).
      destruct H0; [apply H0 | destruct H0].
      destruct H0; Key.order.
      pose proof (tree_kv_key_set _ _ _ H0).
      unfold key_keys_lt in H1.
      specialize (H1 k H7).
      Key.order.
    - rewrite filter_lt_iff.
      split.
      apply H4.
      left.
      apply H5.
      pose proof (tree_kv_key_set _ _ _ H5).
      unfold keys_key_lt in H.
      specialize (H k H6).
      apply H.
  + unfold Abs in *; intros.
    specialize (H0 k v).
    rewrite tree_kv_make_tree_iff in H0.
    destruct H0.
    split; intros.
    - rewrite filter_gt_iff in H5.
      destruct H5.
      specialize (H0 H5).
      destruct H0; [ | destruct H0; [ | apply H0]].
      pose proof (tree_kv_key_set _ _ _ H0).
      unfold keys_key_lt in H.
      specialize (H k H7).
      Key.order.
      destruct H0; Key.order.
    - rewrite filter_gt_iff.
      split.
      apply H4.
      right; right.
      apply H5.
      pose proof (tree_kv_key_set _ _ _ H5).
      unfold key_keys_lt in H1.
      specialize (H1 k H6).
      apply H1.
  + unfold Abs in H0.
    specialize (H0 n.(key) n.(val)).
    destruct H0.
    apply H4.
    rewrite tree_kv_make_tree_iff.
    right; left.
    split; reflexivity.
Qed.

End Abstraction.

Module Type BinTreeLookup
              (Node: NODE_SIG)
              (BinTree: BIN_TREE_SIG Node)
              (Key: KEY_SIG Node)
              (Value: VALUE_SIG Node)
              (Map: MAP_SIG Node Key Value)
              (Import KeyNotation: KEY_NOTAIION_SIG Node Key)
              (Import ValueNotation: VALUE_NOTAIION_SIG Node Value)
              (Import BTB: BinaryTreeBasic Node BinTree)
              (Import ST: SearchTree Node BinTree Key KeyNotation BTB)
              (Import MF: MapFacts Node Key Value Map KeyNotation ValueNotation)
              (Import ABS: Abstraction Node BinTree Key Value Map KeyNotation ValueNotation BTB MF ST).

Definition look_up (key : Key.t) : BinTree.t -> option Value.t :=
  BinTree.t_rect
    (fun _ => option Value.t)
    None
    (fun n l tr_l r tr_r =>
       match Key.dec key n.(key) with
       | inleft (left _) => tr_l
       | inright _ => Some n.(val)
       | inleft (right _) => tr_r
       end).

Theorem look_up_empty:
  forall n, look_up n BinTree.empty = None.
Proof.
  intros.
  unfold look_up.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Theorem look_up_make_tree_lt:
  forall n0 n l r,
    n0 < n.(key) ->
    look_up n0 (BinTree.make_tree n l r) = look_up n0 l.
Proof.
  intros.
  unfold look_up.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec n0 n.(key)) as [[? | ?] | ?];
    first [reflexivity | Key.order]. 
Qed.

Theorem look_up_make_tree_eq:
  forall n0 n l r,
    n0 == n.(key) ->
    look_up n0 (BinTree.make_tree n l r) = Some n.(val).
Proof.
  intros.
  unfold look_up.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec n0 n.(key)) as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Theorem look_up_make_tree_gt:
  forall n0 n l r,
    n.(key) < n0 ->
    look_up n0 (BinTree.make_tree n l r) = look_up n0 r.
Proof.
  intros.
  unfold look_up.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec n0 n.(key)) as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

#[local] Existing Instance Sets_singleton_setoid_congr.
#[local] Existing Instance keys_keys_lt_congr.

Theorem look_up_Correctness:
  forall tr m n,
    SearchTree tr ->
    Abs tr m ->
    (forall k1 k2, k1 == k2 -> m k1 = m k2) ->
    look_up n tr = m n. 
Proof.
  refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite look_up_empty.
    apply Abs_empty_inv in H0.
    rewrite H0. reflexivity.
  + intros.
    apply Abs_make_tree_revert in H2 ; auto. 
    destruct H2 as [Hml [Hmr Hn]].
    destruct (Key.lt_total n.(key) n0) as [? | [? | ?]].
    - rewrite look_up_make_tree_gt by tauto.
      apply SearchTree_make_tree in H1.
      destruct H1 as [? [? [? ?]]].
      rewrite (H0 _ _ H6 Hmr) ; auto.
      * apply filter_gt_eq. tauto.
      * unfold Map.filter_gt. intros.
        destruct (Key.gt_le_dec k1 n.(key)) ; destruct (Key.gt_le_dec k2 n.(key)) ; try Key.order ; try auto.
    - rewrite look_up_make_tree_eq.
      2 : { rewrite H2. reflexivity. }
      rewrite <- Hn. apply H3 ; auto.
    - rewrite look_up_make_tree_lt by tauto.
      apply SearchTree_make_tree in H1.
      destruct H1 as [? [? [? ?]]].
      rewrite (H _ _ H5 Hml) ; auto.
      * apply filter_lt_eq. tauto.
      * unfold Map.filter_lt. intros.
        destruct (Key.lt_ge_dec k1 n.(key)) ; destruct (Key.lt_ge_dec k2 n.(key)) ; try Key.order ; try auto.
Qed.
      
End BinTreeLookup.


Module Type BinTreeInsert
              (Node: NODE_SIG)
              (BinTree: BIN_TREE_SIG Node)
              (Key: KEY_SIG Node)
              (Value: VALUE_SIG Node)
              (Map: MAP_SIG Node Key Value)
              (Import KeyNotation: KEY_NOTAIION_SIG Node Key)
              (Import ValueNotation: VALUE_NOTAIION_SIG Node Value)
              (Import BTB: BinaryTreeBasic Node BinTree)
              (Import ST: SearchTree Node BinTree Key KeyNotation BTB)
              (Import MF: MapFacts Node Key Value Map KeyNotation ValueNotation)
              (Import ABS: Abstraction Node BinTree Key Value Map KeyNotation ValueNotation BTB MF ST).

Definition insert (n0: Node.t): BinTree.t -> BinTree.t :=
  BinTree.t_rect
    (fun _ => BinTree.t)
    (BinTree.make_tree n0 BinTree.empty BinTree.empty)
    (fun n l tr_l r tr_r =>
       match Key.dec n0.(key) n.(key) with
       | inleft (left _) => BinTree.make_tree n tr_l r
       | inright _ => BinTree.make_tree n0 l r
       | inleft (right _) => BinTree.make_tree n l tr_r
       end).

Theorem insert_empty:
  forall n,
    insert n BinTree.empty =
    BinTree.make_tree n BinTree.empty BinTree.empty.
Proof.
  intros.
  unfold insert.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Theorem insert_make_tree_lt:
  forall n0 n l r,
    n0.(key) < n.(key) ->
    insert n0 (BinTree.make_tree n l r) =
    BinTree.make_tree n (insert n0 l) r.
Proof.
  intros.
  unfold insert.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec n0.(key) n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Theorem insert_make_tree_eq:
  forall n0 n l r,
    n0.(key) == n.(key) ->
    insert n0 (BinTree.make_tree n l r) =
    BinTree.make_tree n0 l r.
Proof.
  intros.
  unfold insert.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec n0.(key) n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Theorem insert_make_tree_gt:
  forall n0 n l r,
    n.(key) < n0.(key) ->
    insert n0 (BinTree.make_tree n l r) =
    BinTree.make_tree n l (insert n0 r).
Proof.
  intros.
  unfold insert.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec n0.(key) n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Theorem insert_key_set:
  forall n tr,
    ((insert n tr).(keys) == Sets_singleton_setoid n.(key) ∪ tr.(keys))%sets.
Proof.
  intros.
  revert tr; refine (BinTree.t_ind _ _ _).
  + rewrite insert_empty.
    rewrite key_set_make_tree.
    rewrite key_set_empty.
    rewrite Sets_empty_union.
    reflexivity.
  + intros n0 l IHl r IHr.
    destruct (Key.lt_total n.(key) n0.(key)) as [? | [? | ?]].
    - rewrite insert_make_tree_lt by tauto.
      rewrite !key_set_make_tree.
      rewrite IHl.
      sets_unfold; intros; tauto.
    - rewrite insert_make_tree_eq by tauto.
      rewrite !key_set_make_tree.
      sets_unfold; intros.
      unfold Sets_singleton_setoid.
      rewrite H; tauto.
    - rewrite insert_make_tree_gt by tauto.
      rewrite !key_set_make_tree.
      rewrite IHr.
      sets_unfold; intros; tauto.
Qed.

#[local] Existing Instance Sets_singleton_setoid_congr.
#[local] Existing Instance keys_keys_lt_congr.

Theorem insert_SearchTree:
  forall tr n,
    SearchTree tr ->
    SearchTree (insert n tr).
Proof.
  refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite insert_empty.
    rewrite SearchTree_make_tree.
    split; [| split; [| split]].
    - rewrite keys_key_lt_iff.
      rewrite key_set_empty. 
      apply empty_set_keys_keys_lt.
    - rewrite key_keys_lt_iff.
      rewrite key_set_empty. 
      apply keys_keys_lt_empty_set.
    - tauto.
    - tauto.
  + intros n l IHl r IHr n0 H.
    rewrite SearchTree_make_tree in H.
    destruct H as [? [? [? ?]]].
    destruct (Key.lt_total n0.(key) n.(key)) as [? | [? | ?]].
    - rewrite insert_make_tree_lt by tauto.
      rewrite SearchTree_make_tree.
      split; [| split; [| split]].
      * apply keys_key_lt_iff.
        rewrite insert_key_set.
        apply union_keys_keys_lt.
        rewrite <- key_key_lt_iff.
        rewrite <- keys_key_lt_iff.
        tauto.
      * tauto.
      * apply IHl; tauto.
      * tauto.
    - rewrite insert_make_tree_eq by tauto.
      rewrite SearchTree_make_tree.
      split; [| split; [| split]].
      * apply keys_key_lt_iff.
        rewrite H3.
        apply keys_key_lt_iff.
        tauto.
      * apply key_keys_lt_iff.
        rewrite H3.
        apply key_keys_lt_iff.
        tauto.
      * tauto.
      * tauto.
    - rewrite insert_make_tree_gt by tauto.
      rewrite SearchTree_make_tree.
      split; [| split; [| split]].
      * tauto.
      * apply key_keys_lt_iff.
        rewrite insert_key_set.
        apply keys_keys_lt_union.
        rewrite <- key_key_lt_iff.
        rewrite <- key_keys_lt_iff.
        tauto.
      * tauto.
      * apply IHr; tauto.
Qed.

Theorem insert_Abs:
  forall tr m n,
    SearchTree tr ->
    Abs tr m ->
    Abs (insert n tr) (Map.insert n.(key) n.(val) m).
Proof.
  unfold Abs.
  intros.
  specialize (H0 k v).
  rewrite insert_iff.
  rewrite H0.
  clear m H0.
  revert tr H; refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite insert_empty.
    rewrite tree_kv_make_tree_iff.
    rewrite tree_kv_empty_iff.
    tauto.
  + rename n into n0.
    intros n l IHl r IHr H.
    rewrite SearchTree_make_tree in H.
    destruct H as [? [? [? ?]]].
    destruct (Key.lt_total n0.(key) n.(key)) as [? | [? | ?]].
    - rewrite insert_make_tree_lt by tauto.
      rewrite !tree_kv_make_tree_iff.
      rewrite <- IHl by tauto.
      clear IHl IHr.
      assert (k == n.(key) -> k ~= n0.(key)) by Key.order.
      assert (tree_kv r k v -> k ~= n0.(key)). {
        intros.
        apply tree_kv_key_set in H5.
        pose proof H0 _ H5.
        Key.order.
      }
      tauto.
    - rewrite insert_make_tree_eq by tauto.
      rewrite !tree_kv_make_tree_iff.
      clear IHl IHr.
      rewrite H3.
      assert (tree_kv l k v -> k ~= n.(key)). {
        intros HH.
        apply tree_kv_key_set in HH.
        pose proof H _ HH.
        Key.order.
      }
      assert (tree_kv r k v -> k ~= n.(key)). {
        intros HH.
        apply tree_kv_key_set in HH.
        pose proof H0 _ HH.
        Key.order.
      }
      tauto.
    - rewrite insert_make_tree_gt by tauto.
      rewrite !tree_kv_make_tree_iff.
      rewrite <- IHr by tauto.
      clear IHl IHr.
      assert (k == n.(key) -> k ~= n0.(key)) by Key.order.
      assert (tree_kv l k v -> k ~= n0.(key)). {
        intros.
        apply tree_kv_key_set in H5.
        pose proof H _ H5.
        Key.order.
      }
      tauto.
Qed.

End BinTreeInsert.

Module Type BinTreeDelete
              (Node: NODE_SIG)
              (BinTree: BIN_TREE_SIG Node)
              (Key: KEY_SIG Node)
              (Value: VALUE_SIG Node)
              (Map: MAP_SIG Node Key Value)
              (Import KeyNotation: KEY_NOTAIION_SIG Node Key)
              (Import ValueNotation: VALUE_NOTAIION_SIG Node Value)
              (Import BTB: BinaryTreeBasic Node BinTree)
              (Import ST: SearchTree Node BinTree Key KeyNotation BTB)
              (Import MF: MapFacts Node Key Value Map KeyNotation ValueNotation)
              (Import ABS: Abstraction Node BinTree Key Value Map KeyNotation ValueNotation BTB MF ST).

Definition tree_pre_merge : BinTree.t -> BinTree.t -> BinTree.t :=
  BinTree.t_rect
    (fun _ => BinTree.t -> BinTree.t)
    (fun tr => tr)
    (fun n l IHl r IHr tr => BinTree.make_tree n l (IHr tr)).

Definition delete (key0: Key.t): BinTree.t -> BinTree.t :=
  BinTree.t_rect
    (fun _ => BinTree.t)
    (BinTree.empty)
    (fun n l tr_l r tr_r =>
       match Key.dec key0 n.(key) with
       | inleft (left _) => BinTree.make_tree n tr_l r
       | inright _ => tree_pre_merge l r
       | inleft (right _) => BinTree.make_tree n l tr_r
       end).

Theorem tree_pre_merge_empty:
  forall tr,
    tree_pre_merge BinTree.empty tr = tr.
Proof.
  intros.
  unfold tree_pre_merge.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Theorem tree_pre_merge_maketree:
  forall n l r tr,
    tree_pre_merge (BinTree.make_tree n l r) tr =
    BinTree.make_tree n l (tree_pre_merge r tr).
Proof.
  intros.
  unfold tree_pre_merge.
  rewrite BinTree.t_rect_make_tree.
  reflexivity.
Qed.

Theorem tree_pre_merge_key_set :
  forall tr1 tr2,
    ((tree_pre_merge tr1 tr2).(keys) == tr1.(keys) ∪ tr2.(keys))%sets.
Proof.
  refine (BinTree.t_ind _ _ _) ; intros.
  + rewrite tree_pre_merge_empty.
    rewrite key_set_empty.
    rewrite Sets_empty_union.
    reflexivity.
  + rewrite tree_pre_merge_maketree.
    rewrite !key_set_make_tree.
    rewrite (H0 tr2).
    rewrite !Sets_union_assoc.
    reflexivity.
Qed.

Theorem delete_empty:
  forall n,
    delete n BinTree.empty = BinTree.empty.
Proof.
  intros.
  unfold delete.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Theorem delete_make_tree_lt:
  forall key n l r,
    key < n.(key) ->
    delete key (BinTree.make_tree n l r) =
    BinTree.make_tree n (delete key l) r.
Proof.
  intros.
  unfold delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Theorem delete_make_tree_eq:
  forall key n l r,
    key == n.(key) ->
    delete key (BinTree.make_tree n l r) =
    tree_pre_merge l r.
Proof.
  intros.
  unfold delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Theorem delete_make_tree_gt:
  forall key n l r,
    n.(key) < key ->
    delete key (BinTree.make_tree n l r) =
    BinTree.make_tree n l (delete key r).
Proof.
  intros.
  unfold delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

#[local] Existing Instance Sets_singleton_setoid_congr.
#[local] Existing Instance keys_keys_lt_congr.
#[local] Existing Instance keys_key_lt_congr.
#[local] Existing Instance key_keys_lt_congr.

Theorem delete_key_set:
  forall n tr,
    SearchTree tr -> 
    ((delete n tr).(keys) == (Sets.complement (Sets_singleton_setoid n)) ∩ tr.(keys))%sets.
Proof.
  intros n.
  refine (BinTree.t_ind _ _ _) ; intros.
  - rewrite delete_empty.
    rewrite key_set_empty.
    rewrite Sets_intersect_empty.
    reflexivity.
  - rewrite key_set_make_tree.
    rewrite SearchTree_make_tree in H1.
    destruct H1 as [? [? [? ?]]].
    destruct (Key.lt_total n n0.(key)) as [? | [? | ?]].
    + rewrite delete_make_tree_lt by tauto.
      rewrite !key_set_make_tree.
      rewrite (H H3).
      rewrite !Sets_intersect_union_distr_l.
      assert (Sets.complement (Sets_singleton_setoid n) ∩ Sets_singleton_setoid n0.(key) == Sets_singleton_setoid n0.(key))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        rewrite H6. 
        Key.order. 
      }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ r.(keys) == r.(keys))%sets.
      {
        apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold key_keys_lt in H2.
        specialize (H2 a H7). 
        Key.order.  
      }
      rewrite H6. rewrite H7. reflexivity.
    + rewrite delete_make_tree_eq by tauto.
      rewrite tree_pre_merge_key_set.
      rewrite !Sets_intersect_union_distr_l.
      assert (Sets.complement (Sets_singleton_setoid n) ∩ Sets_singleton_setoid n0.(key) == ∅)%sets.
      { rewrite H5.
        rewrite Sets_complement_self_intersect. 
        reflexivity. }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ l.(keys) == l.(keys))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold keys_key_lt in H1.
        specialize (H1 a H7). 
        Key.order. 
      }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ r.(keys) == r.(keys))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold key_keys_lt in H2.
        specialize (H2 a H8). 
        Key.order.
      }
      rewrite H6. rewrite H7. rewrite H8.
      rewrite Sets_union_empty. 
      reflexivity.
    + rewrite delete_make_tree_gt by tauto.
      rewrite !key_set_make_tree.
      rewrite (H0 H4).
      rewrite !Sets_intersect_union_distr_l.
      assert (Sets.complement (Sets_singleton_setoid n) ∩ Sets_singleton_setoid n0.(key) == Sets_singleton_setoid n0.(key))%sets.
      {  
        apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        rewrite H6. 
        Key.order.
      }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ l.(keys) == l.(keys))%sets.
      { 
        apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold key_keys_lt in H1.
        specialize (H1 a H7). 
        Key.order. 
      }
      rewrite H6. rewrite H7. reflexivity.
Qed.

Theorem tree_pre_merge_SearchTree : 
  forall tr1 tr2,
    tr1.(keys) =<= tr2.(keys) ->
    SearchTree tr1 ->
    SearchTree tr2 ->
    SearchTree (tree_pre_merge tr1 tr2).
Proof.
  refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite tree_pre_merge_empty.
    tauto.
  + intros.
    rewrite tree_pre_merge_maketree.
    rewrite SearchTree_make_tree in H2.
    rewrite key_set_make_tree in H1.
    rewrite union_keys_keys_lt in H1.
    destruct H2 as [? [? [? ?]]].
    rewrite SearchTree_make_tree.
    split; [| split; [| split]] ; try tauto.
    - rewrite key_keys_lt_iff in *.
      rewrite tree_pre_merge_key_set.
      rewrite keys_keys_lt_union.
      rewrite union_keys_keys_lt in H1.
      split ; tauto.
    - apply H0 ; tauto.
Qed.

Theorem delete_SearchTree:
  forall tr n,
    SearchTree tr ->
    SearchTree (delete n tr).
Proof.
  refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite delete_empty.
    tauto.
  + intros n l IHl r IHr n0 H.
    rewrite SearchTree_make_tree in H.
    destruct H as [? [? [? ?]]].
    destruct (Key.lt_total n0 n.(key)) as [? | [? | ?]].
    - rewrite delete_make_tree_lt by tauto.
      rewrite SearchTree_make_tree.
      split; [| split; [| split]].
      * apply keys_key_lt_iff.
        rewrite delete_key_set ; auto.
        apply intersect_keys_keys_lt_r.
        rewrite keys_key_lt_iff in H.
        tauto.
      * tauto.
      * apply IHl; tauto.
      * tauto.
    - rewrite delete_make_tree_eq by tauto.
      apply tree_pre_merge_SearchTree ; auto.
      apply (keys_key_keys_lt_trans _ _ _ H H0).
    - rewrite delete_make_tree_gt by tauto.
      rewrite SearchTree_make_tree.
      split; [| split; [| split]].
      * tauto.
      * apply key_keys_lt_iff.
        rewrite delete_key_set ; auto.
        apply keys_keys_lt_intersect.
        right.
        rewrite key_keys_lt_iff in H0.
        tauto.
      * tauto.
      * apply IHr; tauto.
Qed.

Theorem tree_pre_merge_Abs : 
  forall tr1 tr2 m1 m2,
    tr1.(keys) =<= tr2.(keys) ->
    SearchTree tr1 ->
    SearchTree tr2 ->
    Abs tr1 m1 ->
    Abs tr2 m2 ->
    Abs (tree_pre_merge tr1 tr2) (Map.merge m1 m2).
Proof.
  intros.
  pose proof (Abs_domain tr1 m1 H2).
  pose proof (Abs_domain tr2 m2 H3).
  unfold Abs in *.
  intros.
  specialize (H2 k v).
  specialize (H3 k v).
  rewrite merge_iff.
  - rewrite H2.
    rewrite H3.
    clear m1 m2 H2 H3 H4 H5.
    revert tr1 tr2 H H0 H1; refine (BinTree.t_ind _ _ _).
    + intros.
      rewrite tree_pre_merge_empty.
      rewrite tree_kv_empty_iff.
      tauto.
    + intros.
      rewrite tree_pre_merge_maketree.
      rewrite !tree_kv_make_tree_iff.
      rewrite SearchTree_make_tree in H2.
      rewrite key_set_make_tree in H1.
      rewrite !union_keys_keys_lt in H1.
      rewrite <- H0 ; tauto.
  - rewrite <- H4 , <- H5. tauto.
Qed.

Theorem tree_pre_merge_tree_kv : 
  forall tr1 tr2 k v,
    tree_kv tr1 k v \/
    tree_kv tr2 k v <->
    tree_kv (tree_pre_merge tr1 tr2) k v.
Proof.
  refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite tree_pre_merge_empty.
    rewrite !tree_kv_empty_iff.
    tauto.
  + intros.
    rewrite tree_pre_merge_maketree.
    rewrite !tree_kv_make_tree_iff.
    rewrite <- (H0 tr2).
    tauto.
Qed.

Theorem delete_Abs:
  forall tr m n,
    SearchTree tr ->
    Abs tr m ->
    Abs (delete n tr) (Map.delete n m).
Proof.
  unfold Abs.
  intros.
  specialize (H0 k v).
  rewrite delete_iff.
  rewrite H0.
  clear m H0.
  revert tr H; refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite delete_empty.
    rewrite tree_kv_empty_iff.
    tauto.
  + rename n into n0.
    intros n l IHl r IHr H.
    rewrite SearchTree_make_tree in H.
    destruct H as [? [? [? ?]]].
    specialize (IHl H1).
    specialize (IHr H2).
    destruct (Key.lt_total n0 n.(key)) as [? | [? | ?]].
    - rewrite delete_make_tree_lt by tauto.
      rewrite !tree_kv_make_tree_iff.
      rewrite <- IHl by tauto.
      clear IHl IHr.
      assert (k == n.(key) -> k ~= n0) by Key.order.
      assert (tree_kv r k v -> k ~= n0). {
        intros.
        apply tree_kv_key_set in H5.
        pose proof H0 _ H5.
        Key.order.
      }
      tauto.
    - rewrite delete_make_tree_eq by tauto.
      rewrite !tree_kv_make_tree_iff.
      clear IHl IHr.
      rewrite H3.
      assert (tree_kv l k v -> k ~= n.(key)). {
        intros HH.
        apply tree_kv_key_set in HH.
        pose proof H _ HH.
        Key.order.
      }
      assert (tree_kv r k v -> k ~= n.(key)). {
        intros HH.
        apply tree_kv_key_set in HH.
        pose proof H0 _ HH.
        Key.order.
      }
      rewrite <- tree_pre_merge_tree_kv.
      tauto.
    - rewrite delete_make_tree_gt by tauto.
      rewrite !tree_kv_make_tree_iff.
      rewrite <- IHr by tauto.
      clear IHl IHr.
      assert (k == n.(key) -> k ~= n0) by Key.order.
      assert (tree_kv l k v -> k ~= n0). {
        intros.
        apply tree_kv_key_set in H5.
        pose proof H _ H5.
        Key.order.
      }
      tauto.
Qed.

Definition delete_min : BinTree.t -> BinTree.t :=
  BinTree.t_rect
    (fun _ => BinTree.t)
    (BinTree.empty)
    (fun n l tr_l r tr_r =>
       BinTree.t_caset
         (fun _ => BinTree.t)
         (r)
         (fun _ _ _ => BinTree.make_tree n tr_l r) l).

Definition min_node (n0 : Node.t) : BinTree.t -> Node.t :=
  BinTree.t_rect
    (fun _ => Node.t)
    (n0)
    (fun n l tr_l r tr_r =>
       BinTree.t_caset
         (fun _ => Node.t)
         (n)
         (fun _ _ _ => tr_l) l).

Definition swap_delete (key0: Key.t): BinTree.t -> BinTree.t :=
  BinTree.t_rect
    (fun _ => BinTree.t)
    (BinTree.empty)
    (fun n l tr_l r tr_r =>
       match Key.dec key0 n.(key) with
       | inleft (left _) => BinTree.make_tree n tr_l r
       | inright _ =>
           BinTree.t_caset
             (fun _ => BinTree.t)
             (l)
             (fun _ _ _ =>
                 BinTree.t_caset
                   (fun _ => BinTree.t)
                   (r)
                   (fun _ _ _ =>
                     BinTree.make_tree (min_node n r) l (delete_min r)
                   ) l
             ) r
       | inleft (right _) => BinTree.make_tree n l tr_r
       end).

Theorem delete_min_empty:
  delete_min BinTree.empty = BinTree.empty.
Proof.
  unfold delete_min.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Theorem min_node_empty:
  forall n,
    min_node n BinTree.empty = n.
Proof.
  intros.
  unfold min_node.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Theorem delete_min_size_1:
  forall n r,
    delete_min (BinTree.make_tree n BinTree.empty r) = r.
Proof.
  intros.
  unfold delete_min.
  rewrite BinTree.t_rect_make_tree.
  rewrite BinTree.t_caset_empty.
  reflexivity.
Qed.

Theorem delete_min_make_tree:
  forall n0 r0 n1 l1 r1,
    delete_min (BinTree.make_tree n0 (BinTree.make_tree n1 l1 r1) r0) =
    BinTree.make_tree n0 (delete_min (BinTree.make_tree n1 l1 r1)) r0.
Proof.
  intros.
  unfold delete_min.
  rewrite BinTree.t_rect_make_tree.
  rewrite BinTree.t_caset_make_tree.
  reflexivity.
Qed.

Theorem min_node_size_1:
  forall n n0 r,
    min_node n (BinTree.make_tree n0 BinTree.empty r) = n0.
Proof.
  intros.
  unfold min_node.
  rewrite BinTree.t_rect_make_tree.
  rewrite BinTree.t_caset_empty.
  reflexivity.
Qed.

Theorem min_node_make_tree:
  forall n n0 n1 l1 r1 r,
    min_node n (BinTree.make_tree n0 (BinTree.make_tree n1 l1 r1) r) =
    min_node n (BinTree.make_tree n1 l1 r1).
Proof.
  intros.
  unfold min_node.
  rewrite BinTree.t_rect_make_tree.
  rewrite BinTree.t_caset_make_tree.
  reflexivity.
Qed.

Theorem min_node_same_def:
  forall n0 n1 n l r,
    min_node n0 (BinTree.make_tree n l r) = min_node n1 (BinTree.make_tree n l r).
Proof.
  intros.
  revert n r.
  revert l.
  refine (BinTree.t_ind _ _ _) ; intros.
  + unfold min_node.
    rewrite BinTree.t_rect_make_tree.
    rewrite BinTree.t_caset_empty.
    rewrite BinTree.t_rect_make_tree.
    rewrite BinTree.t_caset_empty.
    reflexivity.
  + rewrite min_node_make_tree.
    rewrite min_node_make_tree.
    specialize (H n r).
    apply H.
Qed.

Theorem min_node_in_tree:
  forall n0 n l r,
    ((min_node n0 (BinTree.make_tree n l r)).(key) ∈ (BinTree.make_tree n l r).(keys))%sets.
Proof.
  intros.
  revert n0 n r.
  revert l.
  refine (BinTree.t_ind _ _ _) ; intros.
  + rewrite min_node_size_1.
    rewrite key_set_make_tree.
    sets_unfold.
    left.
    right.
    unfold Sets_singleton_setoid.
    reflexivity.
  + rewrite min_node_make_tree.
    rewrite key_set_make_tree.
    sets_unfold.
    left; left.
    specialize (H n0 n r).
    sets_unfold in H.
    apply H.
Qed.

Theorem min_node_set_in_tree:
  forall n0 n l r,
    (Sets_singleton_setoid ((min_node n0 (BinTree.make_tree n l r)).(key)) ⊆ (BinTree.make_tree n l r).(keys))%sets.
Proof.
  intros.
  revert n0 n r.
  revert l.
  refine (BinTree.t_ind _ _ _) ; intros.
  + rewrite min_node_size_1.
    rewrite key_set_make_tree.
    sets_unfold.
    left.
    right.
    apply H.
  + rewrite min_node_make_tree.
    rewrite key_set_make_tree.
    specialize (H n0 n r).
    sets_unfold.
    intros.
    left; left.
    sets_unfold in H.
    specialize (H a H1).
    apply H.
Qed. 

Theorem min_node_lt:
  forall n0 n l r,
    SearchTree (BinTree.make_tree n l r) ->
    (min_node n0 (BinTree.make_tree n l r)).(key) -<= (delete_min (BinTree.make_tree n l r)).(keys).
Proof.
  intros.
  revert n0 n r H.
  revert l.
  refine (BinTree.t_ind _ _ _) ; intros.
  + rewrite min_node_size_1.
    rewrite delete_min_size_1.
    rewrite SearchTree_make_tree in H.
    destruct H as [? [? [? ?]]].
    apply H0.
  + rewrite min_node_make_tree.
    rewrite delete_min_make_tree.
    rewrite SearchTree_make_tree in H1.
    destruct H1 as [? [? [? ?]]].
    specialize (H n0 n r H3).
    pose proof (key_set_make_tree n1 (delete_min (BinTree.make_tree n l r)) r0).
    sets_unfold in H5.
    unfold key_keys_lt.
    intros. 
    specialize (H5 k2).
    destruct H5.
    specialize (H5 H6).
    pose proof (min_node_set_in_tree n0 n l r).
    sets_unfold in H8.
    specialize (H8 (min_node n0 (BinTree.make_tree n l r)).(key)).
    unfold Sets_singleton_setoid in H8.
    assert ((min_node n0 (BinTree.make_tree n l r)).(key) == (min_node n0 (BinTree.make_tree n l r)).(key)); [reflexivity | ].
    specialize (H8 H9).
    destruct H5.
    destruct H5.
    unfold key_keys_lt in H.
    specialize (H k2 H5).
    apply H.
    rewrite keys_key_lt_iff in H1.
    unfold keys_keys_lt in H1.
    specialize (H1 (min_node n0 (BinTree.make_tree n l r)).(key) k2 H8 H5).
    apply H1.
    unfold keys_key_lt in H1.
    specialize (H1 (min_node n0 (BinTree.make_tree n l r)).(key) H8).
    unfold key_keys_lt in H2.
    specialize (H2 k2 H5).
    Key.order.
Qed.

Theorem swap_delete_empty:
  forall n,
    swap_delete n BinTree.empty = BinTree.empty.
Proof.
  intros.
  unfold swap_delete.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Theorem swap_delete_make_tree_lt:
  forall key n l r,
    key < n.(key) ->
    swap_delete key (BinTree.make_tree n l r) =
    BinTree.make_tree n (swap_delete key l) r.
Proof.
  intros.
  unfold swap_delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Theorem swap_delete_make_tree_eq_r_empty:
  forall key n l,
    key == n.(key) ->
    swap_delete key (BinTree.make_tree n l BinTree.empty) = l.
Proof.
  intros.
  unfold swap_delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?].
  Key.order.
  Key.order.
  rewrite BinTree.t_caset_empty.
  reflexivity.
Qed.

Theorem swap_delete_make_tree_eq_l_empty:
  forall key n r,
    key == n.(key) ->
    swap_delete key (BinTree.make_tree n BinTree.empty r) = r.
Proof.
  intros key n.
  refine (BinTree.t_ind _ _ _); intros; [apply swap_delete_make_tree_eq_r_empty; apply H | ].
  unfold swap_delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?].
  Key.order.
  Key.order.
  rewrite BinTree.t_caset_make_tree.
  rewrite BinTree.t_caset_empty.
  reflexivity.
Qed.

Theorem swap_delete_make_tree_eq:
  forall key n n1 l1 r1 n2 l2 r2,
    key == n.(key) ->
    swap_delete key (BinTree.make_tree n (BinTree.make_tree n1 l1 r1) (BinTree.make_tree n2 l2 r2)) =
    BinTree.make_tree (min_node n (BinTree.make_tree n2 l2 r2)) (BinTree.make_tree n1 l1 r1) (delete_min (BinTree.make_tree n2 l2 r2)).
Proof.
  intros.
  unfold swap_delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?].
  Key.order.
  Key.order.
  rewrite BinTree.t_caset_make_tree.
  rewrite BinTree.t_caset_make_tree.
  reflexivity.
Qed.

Theorem swap_delete_make_tree_gt:
  forall key n l r,
    n.(key) < key ->
    swap_delete key (BinTree.make_tree n l r) =
    BinTree.make_tree n l (swap_delete key r).
Proof.
  intros.
  unfold swap_delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Theorem delete_min_key_set:
  forall n l r,
    SearchTree (BinTree.make_tree n l r) ->
    ((delete_min (BinTree.make_tree n l r)).(keys) ==
    (BinTree.make_tree n l r).(keys) ∩ (Sets.complement (Sets_singleton_setoid (min_node n (BinTree.make_tree n l r)).(key))))%sets.
Proof.
  intros.
  revert r n H.
  revert l.
  refine (BinTree.t_ind _ _ _) ; intros.
  + rewrite delete_min_size_1.
    rewrite min_node_size_1.
    rewrite SearchTree_make_tree in H.
    destruct H as [? [? [? ?]]].
    rewrite key_set_make_tree.
    rewrite key_set_empty.
    rewrite Sets_empty_union.
    rewrite !Sets_intersect_union_distr_r.
    rewrite Sets_intersect_comm.
    rewrite Sets_complement_self_intersect.
    rewrite Sets_empty_union.
    assert (r.(keys) ∩ Sets.complement (Sets_singleton_setoid n.(key)) == r.(keys))%sets.
    apply Sets_intersect_absorb1.
    unfold Sets_singleton_setoid.
    sets_unfold. intros.
    unfold key_keys_lt in H0.
    specialize (H0 a H3).
    Key.order.
    rewrite H3.
    reflexivity.
  + rewrite delete_min_make_tree.
    rewrite key_set_make_tree.
    rewrite key_set_make_tree.
    rewrite min_node_make_tree.
    rewrite SearchTree_make_tree in H1.
    destruct H1 as [? [? [? ?]]].
    specialize (H r n H3).
    rewrite H.
    rewrite !Sets_intersect_union_distr_r.
    assert (Sets_singleton_setoid n0.(key) ∩ Sets.complement (Sets_singleton_setoid (min_node n0 (BinTree.make_tree n l r)).(key)) == Sets_singleton_setoid n0.(key))%sets.
    { apply Sets_intersect_absorb1.
      unfold Sets_singleton_setoid.
      sets_unfold. intros.
      pose proof (min_node_in_tree n0 n l r).
      sets_unfold in H6.
      unfold keys_key_lt in H1.
      specialize (H1 (min_node n0 (BinTree.make_tree n l r)).(key) H6).
      Key.order.
    }
    assert (r0.(keys) ∩ Sets.complement (Sets_singleton_setoid (min_node n0 (BinTree.make_tree n l r)).(key)) == r0.(keys))%sets.
    { apply Sets_intersect_absorb1.
      unfold Sets_singleton_setoid.
      sets_unfold. intros.
      pose proof (min_node_in_tree n0 n l r).
      sets_unfold in H7.
      unfold keys_key_lt in H1.
      specialize (H1 (min_node n0 (BinTree.make_tree n l r)).(key) H7).
      unfold key_keys_lt in H2.
      specialize (H2 a H6).
      Key.order.
    }
    rewrite H5. rewrite H6. rewrite (min_node_same_def n n0 n l r). reflexivity.
Qed.

Theorem swap_delete_key_set:
  forall n tr,
    SearchTree tr -> 
    ((swap_delete n tr).(keys) == (Sets.complement (Sets_singleton_setoid n)) ∩ tr.(keys))%sets.
Proof.
  intros n.
  refine (BinTree.t_ind _ _ _) ; intros.
  + rewrite swap_delete_empty.
    rewrite key_set_empty.
    rewrite Sets_intersect_empty.
    reflexivity.
  + rewrite key_set_make_tree.
    rewrite SearchTree_make_tree in H1.
    destruct H1 as [? [? [? ?]]].
    destruct (Key.lt_total n n0.(key)) as [? | [? | ?]].
    - rewrite swap_delete_make_tree_lt; [ | apply H5].
      rewrite key_set_make_tree.
      rewrite (H H3).
      rewrite !Sets_intersect_union_distr_l.
      assert (Sets.complement (Sets_singleton_setoid n) ∩ Sets_singleton_setoid n0.(key) == Sets_singleton_setoid n0.(key))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        rewrite H6.
        Key.order.
      }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ r.(keys) == r.(keys))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold key_keys_lt in H2.
        specialize (H2 a H7).
        Key.order.
      }
      rewrite H6. rewrite H7. reflexivity.
    - revert n n0 r H H0 H1 H2 H4 H5.
      revert l H3.
      refine (BinTree.t_ind _ _ _) ; intros.
      * rewrite swap_delete_make_tree_eq_l_empty; [ | apply H5].
        rewrite key_set_empty.
        rewrite Sets_empty_union.
        rewrite !Sets_intersect_union_distr_l.
        assert (Sets.complement (Sets_singleton_setoid n) ∩ Sets_singleton_setoid n0.(key) == ∅)%sets.
        { rewrite H5.
          rewrite Sets_complement_self_intersect.
          reflexivity.
        }
        assert (Sets.complement (Sets_singleton_setoid n) ∩ r.(keys) == r.(keys))%sets.
        { apply Sets_intersect_absorb2.
          unfold Sets_singleton_setoid.
          sets_unfold. intros.
          unfold key_keys_lt in H2.
          specialize (H2 a H7).
          Key.order.
        }
        rewrite H6. rewrite H7. rewrite Sets_empty_union. reflexivity.
      * revert n0 n1 n l r H H0 H1 H2 H3 H4 H5 H7.
        revert r0 H6.
        refine (BinTree.t_ind _ _ _) ; intros.
        ++rewrite swap_delete_make_tree_eq_r_empty; [ | apply H7].
          rewrite key_set_make_tree.
          rewrite key_set_empty.
          rewrite Sets_union_empty.
          rewrite !Sets_intersect_union_distr_l.
          assert (Sets.complement (Sets_singleton_setoid n0) ∩ Sets_singleton_setoid n1.(key) == ∅)%sets.
          { rewrite H7.
            rewrite Sets_complement_self_intersect.
            reflexivity.
          }
          unfold keys_key_lt in H4.
          pose proof (key_set_make_tree n l r).
          sets_unfold in H9.
          assert (Sets.complement (Sets_singleton_setoid n0) ∩ l.(keys) == l.(keys))%sets.
          { apply Sets_intersect_absorb2.
            unfold Sets_singleton_setoid.
            sets_unfold. intros.
            specialize (H9 a).
            destruct H9.
            assert ((l.(keys) a \/ Sets_singleton_setoid n.(key) a) \/ r.(keys) a); [left; left; apply H10 | ].
            specialize (H11 H12).
            specialize (H4 a H11).
            Key.order.
          }
          assert (Sets.complement (Sets_singleton_setoid n0) ∩ Sets_singleton_setoid n.(key) == Sets_singleton_setoid n.(key))%sets.
          { apply Sets_intersect_absorb2.
            unfold Sets_singleton_setoid.
            sets_unfold. intros.
            specialize (H9 a).
            destruct H9.
            assert ((l.(keys) a \/ Sets_singleton_setoid n.(key) a) \/ r.(keys) a); [left; right; tauto | ].
            specialize (H12 H13).
            specialize (H4 a H12).
            Key.order.
          }
          assert (Sets.complement (Sets_singleton_setoid n0) ∩ r.(keys) == r.(keys))%sets.
          { apply Sets_intersect_absorb2.
            unfold Sets_singleton_setoid.
            sets_unfold. intros.
            specialize (H9 a).
            destruct H9.
            assert ((l.(keys) a \/ Sets_singleton_setoid n.(key) a) \/ r.(keys) a); [right; tauto | ].
            specialize (H13 H14).
            specialize (H4 a H13).
            Key.order.
          }
          rewrite H8. rewrite H10. rewrite H11. rewrite H12. rewrite Sets_union_empty. reflexivity.
        ++rewrite swap_delete_make_tree_eq; [ | apply H9].
          rewrite key_set_make_tree.
          rewrite delete_min_key_set; [ | apply H6].
          rewrite (min_node_same_def n1 n n l r).
          rewrite H9.
          rewrite !Sets_intersect_union_distr_l.
          assert (Sets.complement (Sets_singleton_setoid n1.(key)) ∩ (BinTree.make_tree n2 l0 r0).(keys) == (BinTree.make_tree n2 l0 r0).(keys))%sets.
          { apply Sets_intersect_absorb2.
            unfold Sets_singleton_setoid.
            sets_unfold. intros.
            unfold key_keys_lt in H7.
            specialize (H7 a H10).
            Key.order.
          }
          assert (Sets.complement (Sets_singleton_setoid n1.(key)) ∩ Sets_singleton_setoid n1.(key) == ∅)%sets.
          { apply Sets_complement_self_intersect. }
          assert (Sets.complement (Sets_singleton_setoid n1.(key)) ∩ (BinTree.make_tree n l r).(keys) == (BinTree.make_tree n l r).(keys))%sets.
          { apply Sets_intersect_absorb2.
            unfold Sets_singleton_setoid.
            sets_unfold. intros.
            unfold keys_key_lt in H8.
            specialize (H8 a H12).
            Key.order.
          }
          rewrite H10. rewrite H11. rewrite H12. rewrite Sets_union_empty.
          rewrite Sets_union_assoc.
          assert (Sets_singleton_setoid (min_node n (BinTree.make_tree n l r)).(key) ∪ (BinTree.make_tree n l r).(keys) ∩ Sets.complement (Sets_singleton_setoid (min_node n (BinTree.make_tree n l r)).(key)) == (BinTree.make_tree n l r).(keys))%sets.
          { rewrite Sets_union_intersect_distr_l.
            rewrite (Sets_union_comm _ (Sets.complement (Sets_singleton_setoid (min_node n (BinTree.make_tree n l r)).(key)))).
            rewrite Sets_complement_self_union.
            rewrite Sets_intersect_full.
            pose proof min_node_set_in_tree n n l r.
            apply Sets_union_absorb2.
            apply H13.
          }
          rewrite H13.
          reflexivity.
    - rewrite swap_delete_make_tree_gt; [ | apply H5].
      rewrite key_set_make_tree.
      rewrite (H0 H4).
      rewrite !Sets_intersect_union_distr_l.
      assert (Sets.complement (Sets_singleton_setoid n) ∩ Sets_singleton_setoid n0.(key) == Sets_singleton_setoid n0.(key))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        rewrite H6.
        Key.order.
      }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ l.(keys) == l.(keys))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold key_keys_lt in H1.
        specialize (H1 a H7).
        Key.order.
      }
      rewrite H6. rewrite H7. reflexivity.
Qed.

Theorem delete_min_Searchtree:
  forall tr,
    SearchTree tr -> SearchTree (delete_min tr).
Proof.
  refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite delete_min_empty.
    apply H.
  + intros n.
    refine (BinTree.t_ind _ _ _).
    - intros.
      rewrite delete_min_size_1.
      rewrite SearchTree_make_tree in H1.
      destruct H1 as [? [? [? ?]]].
      apply H4.
    - intros.
      rewrite delete_min_make_tree.
      rewrite SearchTree_make_tree in H3.
      destruct H3 as [? [? [? ?]]].
      specialize (H1 H5).
      rewrite SearchTree_make_tree.
      split; [ | split; [apply H4 | split; [apply H1 | apply H6]]].
      apply keys_key_lt_iff.
      rewrite keys_key_lt_iff in H3.
      rewrite delete_min_key_set; [ | apply H5].
      sets_unfold.
      unfold keys_keys_lt.
      intros.
      destruct H7.
      unfold keys_keys_lt in H3.
      apply (H3 k1 k2 H7 H8).
Qed.

Theorem swap_delete_SearchTree:
  forall tr n,
    SearchTree tr ->
    SearchTree (swap_delete n tr).
Proof.
  refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite swap_delete_empty.
    apply H.
  + intros.
    destruct (Key.lt_total n0 n.(key)) as [? | [? | ?]].
    - rewrite swap_delete_make_tree_lt; [ | apply H2].
      revert l H H1.
      refine (BinTree.t_ind _ _ _).
      * intros.
        rewrite swap_delete_empty.
        apply H1.
      * intros.
        rewrite SearchTree_make_tree in H4.
        destruct H4 as [? [? [? ?]]].
        rewrite SearchTree_make_tree.
        split; [ | split; [apply H5 | split; [apply H3; apply H6 | apply H7]]].
        apply keys_key_lt_iff.
        rewrite swap_delete_key_set; [ | apply H6].
        apply intersect_keys_keys_lt_r.
        apply keys_key_lt_iff in H4.
        apply H4.
    - revert l H H1.
      refine (BinTree.t_ind _ _ _).
      * intros.
        rewrite swap_delete_make_tree_eq_l_empty; [ | apply H2].
        rewrite SearchTree_make_tree in H1.
        destruct H1 as [? [? [? ?]]].
        apply H5.
      * intros.
        revert r H H0 H1 H4.
        refine (BinTree.t_ind _ _ _).
        ++intros.
          rewrite swap_delete_make_tree_eq_r_empty; [ | apply H2].
          rewrite SearchTree_make_tree in H4.
          destruct H4 as [? [? [? ?]]].
          apply H6.
        ++intros.
          rewrite swap_delete_make_tree_eq; [ | apply H2].
          rewrite SearchTree_make_tree.
          rewrite SearchTree_make_tree in H6.
          destruct H6 as [? [? [? ?]]].
          split; [ | split; [ | split; [apply H8 | apply delete_min_Searchtree; apply H9]]].
          pose proof (min_node_in_tree n n2 l0 r).
          unfold keys_key_lt.
          intros.
          unfold keys_key_lt in H6.
          specialize (H6 k1 H11).
          unfold key_keys_lt in H7.
          sets_unfold in H10.
          specialize (H7 (min_node n (BinTree.make_tree n2 l0 r)).(key) H10).
          Key.order.
          unfold key_keys_lt.
          intros.
          pose proof (delete_min_key_set n2 l0 r H9).
          sets_unfold in H11.
          specialize (H11 k2).
          destruct H11.
          specialize (H11 H10).
          destruct H11.
          pose proof (min_node_lt n n2 l0 r H9).
          unfold key_keys_lt in H14.
          specialize (H14 k2 H10).
          apply H14.
    - rewrite swap_delete_make_tree_gt; [ | apply H2].
      revert r H0 H1.
      refine (BinTree.t_ind _ _ _).
      * intros.
        rewrite swap_delete_empty.
        apply H1.
      * intros.
        rewrite SearchTree_make_tree in H4.
        destruct H4 as [? [? [? ?]]].
        rewrite SearchTree_make_tree.
        split; [apply H4 | split; [ | split; [ apply H6 | apply H3; apply H7]]].
        apply key_keys_lt_iff.
        rewrite swap_delete_key_set; [ | apply H7].
        apply keys_keys_lt_intersect.
        right.
        apply key_keys_lt_iff in H5.
        apply H5.
Qed.        

Theorem delete_min_tree_kv:
  forall n l r k v,
    tree_kv (BinTree.make_tree n l r) k v <->
    (k == (min_node n (BinTree.make_tree n l r)).(key) /\ v = (min_node n (BinTree.make_tree n l r)).(val)) \/
    tree_kv (delete_min (BinTree.make_tree n l r)) k v.
Proof.
  intros n l.
  revert l n.
  refine (BinTree.t_ind _ _ _); intros.
  + rewrite delete_min_size_1.
    rewrite min_node_size_1.
    split; intros.
    rewrite tree_kv_make_tree_iff in H.
    destruct H.
    rewrite tree_kv_empty_iff in H; tauto.
    destruct H.
    left.
    apply H.
    right.
    apply H.
    rewrite tree_kv_make_tree_iff.
    destruct H.
    right; left; apply H.
    right; right; apply H.
  + rewrite delete_min_make_tree.
    rewrite min_node_make_tree.
    specialize (H n r k v).
    rewrite (min_node_same_def n0 n).
    split; intros.
    rewrite tree_kv_make_tree_iff in H1.
    destruct H1.
    destruct H.
    pose proof H H1.
    rewrite tree_kv_make_tree_iff.
    destruct H3.
    left.
    apply H3.
    right.
    left.
    apply H3.
    right.
    rewrite tree_kv_make_tree_iff.
    right.
    apply H1.
    destruct H1.
    rewrite tree_kv_make_tree_iff.
    left.
    rewrite H.
    left.
    apply H1.
    rewrite tree_kv_make_tree_iff.
    rewrite tree_kv_make_tree_iff in H1.
    destruct H1.
    left.
    rewrite H.
    right.
    apply H1.
    right.
    apply H1.
Qed.

Theorem swap_delete_Abs:
  forall tr m n,
    SearchTree tr ->
    Abs tr m ->
    Abs (swap_delete n tr) (Map.delete n m).
Proof.
  unfold Abs.
  intros.
  specialize (H0 k v).
  rewrite delete_iff.
  rewrite H0.
  clear m H0.
  revert tr H; refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite swap_delete_empty.
    rewrite tree_kv_empty_iff.
    tauto.
  + rename n into n0.
    intros n l IHl r IHr H.
    rewrite SearchTree_make_tree in H.
    destruct H as [? [? [? ?]]].
    specialize (IHl H1).
    specialize (IHr H2).
    destruct (Key.lt_total n0 n.(key)) as [? | [? | ?]].
    - rewrite swap_delete_make_tree_lt by tauto.
      rewrite !tree_kv_make_tree_iff.
      rewrite <- IHl by tauto.
      clear IHl IHr.
      assert (k == n.(key) -> k ~= n0) by Key.order.
      assert (tree_kv r k v -> k ~= n0). {
        intros.
        apply tree_kv_key_set in H5.
        pose proof H0 _ H5.
        Key.order.
      }
      tauto.
    - revert l IHl H H1.
      refine (BinTree.t_ind _ _ _).
      * intros.
        rewrite swap_delete_make_tree_eq_l_empty; try tauto.
        rewrite tree_kv_make_tree_iff.
        rewrite tree_kv_empty_iff.
        assert (tree_kv r k v -> k ~= n0).
        { intros.
          apply tree_kv_key_set in H4.
          pose proof H0 _ H4.
          Key.order.
        }
        rewrite H3.
        assert (False -> tree_kv r k v) by tauto.
        split.
        intros.
        destruct H6.
        destruct H7; try tauto.
        intros.
        split.
        rewrite <-H3.
        apply (H4 H6).
        right; right; apply H6.
      * intros.
        revert r IHr H H1 H0 H2.
        refine (BinTree.t_ind _ _ _).
        ++intros.
          rewrite swap_delete_make_tree_eq_r_empty by tauto.
          rewrite !tree_kv_make_tree_iff.
          rewrite tree_kv_empty_iff.
          rewrite SearchTree_make_tree in H5.
          destruct H5 as [? [? [? ?]]].
          clear IHl IHr H H1.
          rewrite H3.
          split; intros.
          destruct H.
          destruct H1 as [ | [ | ]]; try tauto.
          assert (k < n.(key)).
          { unfold keys_key_lt in H4.
            pose proof key_set_make_tree n1 l r0.
            sets_unfold in H1.
            specialize (H1 k).
            destruct H1.
            specialize (H4 k).
            apply H4.
            apply H9.
            unfold Sets_singleton_setoid.
            destruct H as [ | [ | ]].
            pose proof tree_kv_key_set _ _ _ H.
            tauto.
            tauto.
            pose proof tree_kv_key_set _ _ _ H.
            tauto.
          }
          split.
          Key.order.
          tauto.
        ++intros.
          rewrite swap_delete_make_tree_eq by tauto.
          rewrite !tree_kv_make_tree_iff.
          rewrite (min_node_same_def n n2).
          rewrite <-delete_min_tree_kv.
          rewrite <-!tree_kv_make_tree_iff.
          rewrite tree_kv_make_tree_iff.
          rewrite H3.
          assert (tree_kv (BinTree.make_tree n1 l r0) k v -> k ~= n.(key)). {
            intros HH.
            apply tree_kv_key_set in HH.
            pose proof H4 _ HH.
            Key.order.
          }
          assert (tree_kv (BinTree.make_tree n2 l0 r) k v -> k ~= n.(key)). {
            intros HH.
            apply tree_kv_key_set in HH.
            pose proof H6 _ HH.
            Key.order.
          }
          clear H3 IHl H4 H5 H H0 IHr H1 H2 H6 H7.
          tauto.
    - rewrite swap_delete_make_tree_gt by tauto.
      rewrite !tree_kv_make_tree_iff.
      rewrite <- IHr by tauto.
      clear IHl IHr.
      assert (k == n.(key) -> k ~= n0) by Key.order.
      assert (tree_kv l k v -> k ~= n0).
      { intros.
        apply tree_kv_key_set in H5.
        pose proof H _ H5.
        Key.order.
      }
      tauto.
Qed.

Definition pushdown_left (tl : BinTree.t) : BinTree.t -> BinTree.t :=
  BinTree.t_rect
    (fun _ => BinTree.t)
    (tl)
    (fun n l tr_l r tr_r => BinTree.make_tree n tr_l r).

Definition pushdown_delete (key0: Key.t): BinTree.t -> BinTree.t :=
  BinTree.t_rect
    (fun _ => BinTree.t)
    (BinTree.empty)
    (fun n l tr_l r tr_r =>
       match Key.dec key0 n.(key) with
       | inleft (left _) => BinTree.make_tree n tr_l r
       | inright _ => pushdown_left l r
       | inleft (right _) => BinTree.make_tree n l tr_r
       end).

Lemma pushdown_left_empty:
  forall tl,
    pushdown_left tl BinTree.empty = tl.
Proof.
  intros.
  unfold pushdown_left.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Lemma pushdown_delete_empty:
  forall n,
    pushdown_delete n BinTree.empty = BinTree.empty.
Proof.
  intros.
  unfold pushdown_delete.
  rewrite BinTree.t_rect_empty.
  reflexivity.
Qed.

Lemma pushdown_left_make_tree:
  forall n l1 l2 r,
    pushdown_left l1 (BinTree.make_tree n l2 r) = BinTree.make_tree n (pushdown_left l1 l2) r.
Proof.
  intros.
  unfold pushdown_left.
  rewrite BinTree.t_rect_make_tree.
  reflexivity.
Qed.

Lemma pushdown_delete_make_tree_lt:
  forall key n l r,
    key < n.(key) ->
    pushdown_delete key (BinTree.make_tree n l r) =
    BinTree.make_tree n (pushdown_delete key l) r.
Proof.
  intros.
  unfold pushdown_delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Lemma pushdown_delete_make_tree_eq:
  forall key n l r,
    key == n.(key) ->
    pushdown_delete key (BinTree.make_tree n l r) = 
    pushdown_left l r.
Proof.
  intros.
  unfold pushdown_delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?] ; 
  first [reflexivity | Key.order].
Qed.

Lemma pushdown_delete_make_tree_gt:
  forall key n l r,
    n.(key) < key ->
    pushdown_delete key (BinTree.make_tree n l r) =
    BinTree.make_tree n l (pushdown_delete key r).
Proof.
  intros.
  unfold pushdown_delete.
  rewrite BinTree.t_rect_make_tree.
  destruct (Key.dec key n.(key))
    as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Theorem pushdown_left_key_set:
  forall tl tr,
    ((pushdown_left tl tr).(keys) == (tl.(keys) ∪ tr.(keys)))%sets.
Proof.
  intros tl.
  refine (BinTree.t_ind _ _ _).
  + rewrite pushdown_left_empty.
    rewrite key_set_empty.
    rewrite Sets_union_empty.
    reflexivity.
  + intros n l IHl r IHr.
    rewrite pushdown_left_make_tree.
    rewrite !key_set_make_tree.
    rewrite IHl.
    rewrite !Sets_union_assoc.
    reflexivity.
Qed.

Theorem pushdown_delete_key_set:
  forall n tr,
    SearchTree tr ->
    ((pushdown_delete n tr).(keys) == (Sets.complement (Sets_singleton_setoid n) ∩ tr.(keys)))%sets.
Proof.
  intros n.
  refine (BinTree.t_ind _ _ _).
  + rewrite pushdown_delete_empty. 
    rewrite key_set_empty.
    rewrite Sets_intersect_empty.
    reflexivity.
  + intros n0 l IHl r IHr H1.
    rewrite key_set_make_tree.
    rewrite SearchTree_make_tree in H1.
    destruct H1 as [? [? [? ?]]].
    destruct (Key.lt_total n n0.(key)) as [? | [? | ?]].
    - rewrite pushdown_delete_make_tree_lt by tauto.
      rewrite !key_set_make_tree.
      rewrite IHl ; auto.
      rewrite !Sets_intersect_union_distr_l.
      assert (Sets.complement (Sets_singleton_setoid n) ∩ Sets_singleton_setoid n0.(key) == Sets_singleton_setoid n0.(key))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        rewrite H4.
        Key.order.
      }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ r.(keys) == r.(keys))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold key_keys_lt in H0.
        specialize (H0 a H5).
        Key.order.
      }
      rewrite H4. rewrite H5. reflexivity.
    - rewrite pushdown_delete_make_tree_eq by tauto.
      rewrite pushdown_left_key_set.
      rewrite !Sets_intersect_union_distr_l.
      assert (Sets.complement (Sets_singleton_setoid n) ∩ Sets_singleton_setoid n0.(key) == ∅)%sets.
      { rewrite H3.
        rewrite Sets_complement_self_intersect.
        reflexivity.
      }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ l.(keys) == l.(keys))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold keys_key_lt in H.
        specialize (H a H5).
        Key.order.
      }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ r.(keys) == r.(keys))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold key_keys_lt in H0.
        specialize (H0 a H6).
        Key.order.
      }
      rewrite H4, H5,  H6. rewrite Sets_union_empty. reflexivity.
    - rewrite pushdown_delete_make_tree_gt by tauto.
      rewrite !key_set_make_tree.
      rewrite IHr ; auto.
      rewrite !Sets_intersect_union_distr_l.
      assert (Sets.complement (Sets_singleton_setoid n) ∩ Sets_singleton_setoid n0.(key) == Sets_singleton_setoid n0.(key))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        rewrite H4.
        Key.order.
      }
      assert (Sets.complement (Sets_singleton_setoid n) ∩ l.(keys) == l.(keys))%sets.
      { apply Sets_intersect_absorb2.
        unfold Sets_singleton_setoid.
        sets_unfold. intros.
        unfold keys_key_lt in H.
        specialize (H a H5).
        Key.order.
      }
      rewrite H4. rewrite H5. reflexivity.
Qed.


Theorem pushdown_left_SearchTree:
  forall tl tr,
    SearchTree tl ->
    SearchTree tr ->
    tl.(keys) =<= tr.(keys) ->
    SearchTree (pushdown_left tl tr).
Proof.
  intros tl.
  refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite pushdown_left_empty.
    apply H.
  + intros n l IHl r IHr H H0 H1.
    rewrite pushdown_left_make_tree.
    rewrite SearchTree_make_tree in H0.
    destruct H0 as [? [? [? ?]]].
    apply SearchTree_make_tree.
    repeat split ; try auto.
    * rewrite pushdown_left_key_set.
      rewrite key_set_make_tree in H1.
      rewrite !keys_keys_lt_union in H1.
      rewrite keys_key_lt_iff in *.
      rewrite key_keys_lt_iff in *.
      rewrite union_keys_keys_lt.
      split ; try tauto.
    * apply IHl ; auto.
      rewrite key_set_make_tree in H1.
      rewrite !keys_keys_lt_union in H1.
      tauto.
Qed.

Theorem pushdown_delete_SearchTree:
  forall tr n,
    SearchTree tr ->
    SearchTree (pushdown_delete n tr).
Proof.
  refine (BinTree.t_ind _ _ _) ; intros.
  + rewrite pushdown_delete_empty ; auto.
  + rewrite SearchTree_make_tree in H1.
    destruct H1 as [? [? [? ?]]].  
    destruct (Key.lt_total n0 n.(key)) as [? | [? | ?]].
    - rewrite pushdown_delete_make_tree_lt by tauto.
      apply SearchTree_make_tree.
      repeat split ; try auto.
      rewrite pushdown_delete_key_set ; auto.
      rewrite keys_key_lt_iff in *. 
      apply intersect_keys_keys_lt_r. auto.
    - rewrite pushdown_delete_make_tree_eq by tauto.
      apply pushdown_left_SearchTree ; auto.
      eapply keys_key_keys_lt_trans ; eauto. 
    - rewrite pushdown_delete_make_tree_gt by tauto.
      apply SearchTree_make_tree.
      repeat split ; try auto.
      rewrite pushdown_delete_key_set ; auto.
      rewrite key_keys_lt_iff in *.
      apply keys_keys_lt_intersect. right. auto.
Qed.

Theorem pushdown_left_tree_kv:
  forall tl tr k v,
    tree_kv (pushdown_left tl tr) k v <->
    tree_kv tl k v \/ tree_kv tr k v.
Proof.
  intros tl.
  refine (BinTree.t_ind _ _ _) ; intros.
  + rewrite pushdown_left_empty.
    rewrite tree_kv_empty_iff.
    tauto.
  + rewrite pushdown_left_make_tree.
    rewrite tree_kv_make_tree_iff.
    rewrite H.
    rewrite tree_kv_make_tree_iff.
    tauto.
Qed.

Theorem pushdown_delete_Abs:
  forall tr m n,
    SearchTree tr ->
    Abs tr m ->
    Abs (pushdown_delete n tr) (Map.delete n m).
Proof.
  unfold Abs.
  intros.
  specialize (H0 k v).
  rewrite delete_iff.
  rewrite H0.
  clear m H0.
  revert tr H; refine (BinTree.t_ind _ _ _).
  + intros.
    rewrite pushdown_delete_empty.
    rewrite tree_kv_empty_iff.
    tauto.
  + rename n into n0.
    intros n l IHl r IHr H.
    rewrite SearchTree_make_tree in H.
    destruct H as [? [? [? ?]]].
    specialize (IHl H1).
    specialize (IHr H2).
    destruct (Key.lt_total n0 n.(key)) as [? | [? | ?]].
    - rewrite pushdown_delete_make_tree_lt by tauto.
      rewrite !tree_kv_make_tree_iff.
      rewrite <- IHl by tauto.
      clear IHl IHr.
      assert (k == n.(key) -> k ~= n0) by Key.order.
      assert (tree_kv r k v -> k ~= n0). {
        intros.
        apply tree_kv_key_set in H5.
        pose proof H0 _ H5.
        Key.order.
      }
      tauto.
    - rewrite pushdown_delete_make_tree_eq by tauto.
      rewrite pushdown_left_tree_kv.
      rewrite !tree_kv_make_tree_iff.
      split ; intros.
      * destruct H4.
        destruct H5 as [ | [ [? ?] | ]]; try tauto.
        Key.order.
      * destruct H4 as [ | ] ; split ; try tauto. 
        -- apply tree_kv_key_set in H4.
           apply H in H4. Key.order.
        -- apply tree_kv_key_set in H4.
           apply H0 in H4. Key.order.
    - rewrite pushdown_delete_make_tree_gt by tauto.
      rewrite !tree_kv_make_tree_iff.
      rewrite <- IHr by tauto.
      clear IHl IHr.
      assert (k == n.(key) -> k ~= n0) by Key.order.
      assert (tree_kv l k v -> k ~= n0).
      { intros.
        apply tree_kv_key_set in H5.
        pose proof H _ H5.
        Key.order.
      }
      tauto.
Qed.

End BinTreeDelete.

Notation "'LT'" := (inleft (left _)) (at level 1).
Notation "'EQ'" := (inright _) (at level 1).
Notation "'GT'" := (inleft (right _)) (at level 1).