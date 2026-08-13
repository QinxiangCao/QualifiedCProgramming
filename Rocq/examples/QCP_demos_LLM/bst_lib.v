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
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersFacts.
From AUXLib Require Import BinaryTree OrdersDecFact.

Definition key := Z.
Definition value := Z.

Inductive tree : Type :=
  | empty : tree
  | make_tree : tree -> key -> value -> tree -> tree.

Definition mapping: Type := key -> option value.

Module Node <: NODE_SIG.
Definition t := (key * value)%type.
End Node.

Module BinTree <: BIN_TREE_SIG Node.
Definition t := tree.
Definition empty := empty.
Definition make_tree n l r :=
  make_tree l (fst n) (snd n) r.

Definition t_ind:
  forall P: t -> Prop,
  P empty ->
  (forall n l, P l -> forall r, P r -> P (make_tree n l r)) ->
  (forall tr, P tr) :=
  fun P HE HM =>
    tree_ind P HE
      (fun l IHl k v r IHr => HM (k, v) l IHl r IHr).

Definition t_rec:
  forall P: t -> Set,
  P empty ->
  (forall n l, P l -> forall r, P r -> P (make_tree n l r)) ->
  (forall tr, P tr) :=
  fun P HE HM =>
    tree_rec P HE
      (fun l IHl k v r IHr => HM (k, v) l IHl r IHr).

Definition t_rect:
  forall P: t -> Type,
  P empty ->
  (forall n l, P l -> forall r, P r -> P (make_tree n l r)) ->
  (forall tr, P tr) :=
  fun P HE HM =>
    tree_rect P HE
      (fun l IHl k v r IHr => HM (k, v) l IHl r IHr).

Theorem t_rec_empty: forall P f1 f2,
  t_rec P f1 f2 empty = f1.
Proof. intros. reflexivity. Qed.

Theorem t_rec_make_tree: forall P f1 f2 n tr1 tr2,
  t_rec P f1 f2 (make_tree n tr1 tr2) =
  f2 n tr1 (t_rec P f1 f2 tr1) tr2 (t_rec P f1 f2 tr2).
Proof. intros. destruct n. reflexivity. Qed.

Theorem t_rect_empty: forall P f1 f2,
  t_rect P f1 f2 empty = f1.
Proof. intros. reflexivity. Qed.

Theorem t_rect_make_tree: forall P f1 f2 n tr1 tr2,
  t_rect P f1 f2 (make_tree n tr1 tr2) =
  f2 n tr1 (t_rect P f1 f2 tr1) tr2 (t_rect P f1 f2 tr2).
Proof. intros. destruct n. reflexivity. Qed.

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

End BinTree.

Module Key <: KEY_SIG Node.
Definition t := Z.
Definition eq := @eq Z.
Definition eq_equiv := @eq_equivalence Z.
Definition lt := Z.lt.
Definition lt_strorder := Z.lt_strorder.
Definition lt_compat := Z.lt_compat.
Definition compare := Z.compare.
Definition compare_spec := Z.compare_spec.
Definition eq_dec := Z.eq_dec.
Definition le := Z.le.
Definition le_lteq := Z.le_lteq.
Include LtIsTotal.
Include OrderedTypeFullFacts.
Include OrderedTypeFullDecFacts.
Definition of_node := @fst Z Z.
End Key.

Module Value <: VALUE_SIG Node.
Definition t := Z.
Definition of_node := @snd Z Z.
Definition eq_dec := Z.eq_dec.
End Value.

Module Map <: MAP_SIG Node Key Value.
Include MAP_SIG Node Key Value.
End Map.

Module BinTreeTheorems.

Include KEY_NOTAIION_SIG Node Key.
Include VALUE_NOTAIION_SIG Node Value.
Include BinaryTreeBasic Node BinTree.
Include MapFacts Node Key Value Map.
Include SearchTree Node BinTree Key.
Include Abstraction Node BinTree Key Value Map.
Include BinTreeInsert Node BinTree Key Value Map.
Include BinTreeDelete Node BinTree Key Value Map.

End BinTreeTheorems.

Export BinTreeTheorems.

Inductive half_tree : Type :=
  | LH : key -> value -> tree -> half_tree
  | RH : key -> value -> tree -> half_tree.

Definition partial_tree: Type := list half_tree.

Fixpoint combine_tree (pt: partial_tree) (t: tree) :=
  match pt with
  | nil => t
  | LH k v tr :: pt0 => combine_tree pt0 (make_tree t k v tr)
  | RH k v tl :: pt0 => combine_tree pt0 (make_tree tl k v t)
  end.

Definition empty_partial_tree: partial_tree := nil.

Theorem combine_tree_make_tree : forall pt k0 v0 tr1 tr,
  (combine_tree (pt ++ RH k0 v0 tr1 :: nil) tr) = 
    (make_tree tr1 k0 v0 (combine_tree pt tr)).
Proof.
  intros.
  revert k0 v0 tr1 tr.
  induction pt; intros; simpl; try tauto.
  destruct a; apply IHpt.
Qed.

Section Insert.

Variable (x: key) (v: value).

Fixpoint tree_insert (t: tree) : tree :=
  match t with
  | empty => make_tree empty x v empty
  | make_tree a y v' b =>
      match Key.dec x y with
      | LT => make_tree (tree_insert a) y v' b
      | EQ => make_tree a x v b
      | GT => make_tree a y v' (tree_insert b)
      end
  end.

End Insert.


Section Delete.

Fixpoint tree_pre_merge (tl : tree) : tree -> tree :=
  match tl with
  | empty => fun tr => tr
  | make_tree a y v b => fun tr => make_tree a y v (tree_pre_merge b tr)
  end.


Variable (x : key).

Fixpoint tree_delete (t: tree) : tree :=
  match t with
  | empty => empty
  | make_tree a y v b =>
      match Key.dec x y with
      | LT => make_tree (tree_delete a) y v b
      | EQ => tree_pre_merge a b
      | GT => make_tree a y v (tree_delete b)
      end
  end.

End Delete.

Module get_right_most.
Record result : Type := {
  pt : partial_tree;
  k : key;
  v : value;
  l_tree : tree;
}.
End get_right_most.

Notation "x '.(pt)'" := (get_right_most.pt x) (at level 1).
Notation "x '.(k)'" := (get_right_most.k x) (at level 1).
Notation "x '.(v)'" := (get_right_most.v x) (at level 1).
Notation "x '.(l_tree)'" := (get_right_most.l_tree x) (at level 1).

Fixpoint find_pre (t_left : tree) (k0 : key) (v0 : value) (t_right: tree) : 
                     get_right_most.result :=
  match t_right with
  | empty => {|
      get_right_most.pt := nil;
      get_right_most.k := k0;
      get_right_most.v := v0;
      get_right_most.l_tree := t_left; 
      |}
  | make_tree a y w b => let res := find_pre a y w b in {|
      get_right_most.pt := (res.(pt) ++ (RH k0 v0 t_left :: nil));
      get_right_most.k := res.(k);
      get_right_most.v := res.(v);
      get_right_most.l_tree := res.(l_tree); 
      |}
  end.

Fixpoint tree_delete' (x: key) (t: tree) : tree :=
  match t with
  | empty => empty
  | make_tree a y v b =>
      match Key.dec x y with
      | LT => make_tree (tree_delete' x a) y v b
      | EQ => 
        match a with
        | empty => b 
        | make_tree c z w d => 
          let find_pre_result := find_pre c z w d in 
        make_tree (combine_tree (find_pre_result).(pt) (find_pre_result).(l_tree))
           (find_pre_result).(k) (find_pre_result).(v) b
        end 
      | GT => make_tree a y v (tree_delete' x b)
      end
  end.

Theorem tree_insert_same_def:
  forall x v,
    tree_insert x v = BinTreeTheorems.insert (x, v).
Proof. intros. reflexivity. Qed.

Theorem tree_pre_merge_same_def:
  forall tl tr,
    tree_pre_merge tl tr = BinTreeTheorems.tree_pre_merge tl tr.
Proof. intros. reflexivity. Qed.

Theorem tree_delete_same_def:
  forall x t,
    tree_delete x t = BinTreeTheorems.delete x t.
Proof. intros. reflexivity. Qed.

Definition map_insert := Map.insert.
Definition map_delete := Map.delete.

Fixpoint store_tree (p: addr) (tr: tree): Assertion :=
  match tr with
  | empty =>
      “ p = NULL ” && emp
  | make_tree tr_l k v tr_r =>
      “ p <> NULL ” &&
      “ INT_MIN <= k <= INT_MAX ” &&
      EX pl pr: addr,
        &(p # "tree" ->ₛ "key") # Int |-> k **
        &(p # "tree" ->ₛ "value") # Int |-> v **
        &(p # "tree" ->ₛ "left") # Ptr |-> pl **
        &(p # "tree" ->ₛ "right") # Ptr |-> pr **
        store_tree pl tr_l **
        store_tree pr tr_r
  end.

Fixpoint store_ptb (p2 p2_root: addr) (pt: partial_tree): Assertion :=
  match pt with
  | nil =>
      “ p2 = p2_root ” && emp
  | LH k v tr :: pt' =>
      EX p_fa p2_fa p_bro ,
        “ p_fa <> NULL ” &&
        “ INT_MIN <= k <= INT_MAX ” &&
        “ &(p_fa # "tree" ->ₛ "left") = p2 ” &&
        p2_fa # Ptr |-> p_fa **
        &(p_fa # "tree" ->ₛ "key") # Int |-> k **
        &(p_fa # "tree" ->ₛ "value") # Int |-> v **
        &(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro **
        store_tree p_bro tr **
        store_ptb p2_fa p2_root pt'
  | RH k v tr :: pt' =>
      EX p_fa p2_fa p_bro ,
        “ p_fa <> NULL ” &&
        “ INT_MIN <= k <= INT_MAX ” &&
        “ &(p_fa # "tree" ->ₛ "right") = p2 ” &&
        p2_fa # Ptr |-> p_fa **
        &(p_fa # "tree" ->ₛ "key") # Int |-> k **
        &(p_fa # "tree" ->ₛ "value") # Int |-> v **
        &(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro **
        store_tree p_bro tr **
        store_ptb p2_fa p2_root pt'
  end.

Fixpoint store_pt (p p_root: Z) (pt: partial_tree): Assertion :=
  match pt with
  | nil =>
      “ p = p_root ” && emp
  | LH k v tr :: pt' =>
      EX p_fa p_bro,
        “ p_fa <> NULL ” &&
        “ INT_MIN <= k <= INT_MAX ” &&
        &(p_fa # "tree" ->ₛ "left") # Ptr |-> p **
        &(p_fa # "tree" ->ₛ "key") # Int |-> k **
        &(p_fa # "tree" ->ₛ "value") # Int |-> v **
        &(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro **
        store_tree p_bro tr **
        store_pt p_fa p_root pt'
  | RH k v tr :: pt' =>
      EX p_fa p_bro ,
        “ p_fa <> NULL ” &&
        “ INT_MIN <= k <= INT_MAX ” &&
        &(p_fa # "tree" ->ₛ "right") # Ptr |-> p **
        &(p_fa # "tree" ->ₛ "key") # Int |-> k **
        &(p_fa # "tree" ->ₛ "value") # Int |-> v **
        &(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro **
        store_tree p_bro tr **
        store_pt p_fa p_root pt'
  end.


Module Bst.

Definition store_map (p: addr) (m: mapping): Assertion :=
  EX tr: tree,
    “ SearchTree tr ” && “ Abs tr m ” && store_tree p tr.

End Bst.

Import Bst.

Theorem insert_SearchTree: forall tr k v,
  SearchTree tr ->
  SearchTree (tree_insert k v tr).
Proof. 
  intros. 
  exact (insert_SearchTree tr (k, v) H). 
Qed.

Theorem insert_Abs: forall tr m k v,
  SearchTree tr ->
  Abs tr m ->
  Abs (tree_insert k v tr) (map_insert k v m).
Proof. intros. exact (insert_Abs tr m (k, v) H H0). Qed.


Theorem delete_SearchTree: forall tr k,
  SearchTree tr ->
  SearchTree (tree_delete k tr).
Proof. 
  intros. 
  exact (delete_SearchTree tr k H). 
Qed.

Theorem delete_Abs: forall tr m k,
  SearchTree tr ->
  Abs tr m ->
  Abs (tree_delete k tr) (map_delete k m).
Proof. intros. exact (delete_Abs tr m k H H0). Qed.




(* Delete' Abstract *)

Lemma keys_inclusion_lt1 : forall ks1 ks2 ks3, 
  ks1 ⊆ ks2 -> ks2 =<- ks3 -> ks1 =<- ks3. 
Proof.
  sets_unfold.
  unfold keys_key_lt in *.
  intros.
  assert(ks2 k1) by apply (H k1 H1).
  apply H0.
  tauto.
Qed.

Lemma keys_inclusion_lt2 : forall ks1 ks2 ks3, 
  ks1 ⊆ ks2 -> ks3 -<= ks2 -> ks3 -<= ks1. 
Proof.
  sets_unfold.
  unfold key_keys_lt in *.
  intros.
  assert(ks2 k2) by apply (H k2 H1).
  apply H0.
  tauto.
Qed.

Ltac destruct_ST_make_tree H := 
  match type of H with 
  | SearchTree (make_tree ?tr1 ?k ?v ?tr2) =>
    let H1 := fresh "HHHHH" in 
    let H2 := fresh "HHHHH" in 
    pose proof (SearchTree_make_tree (k,v) tr1 tr2) as H1;
    pose proof H as H2;
    rewrite H1 in H2;
    destruct H2 as [? [? [? ?]]];
    clear H1
  end.

Lemma make_tree_keys_include : forall k v tr1 tr2 tr1' tr2', 
  tr1.(keys) ⊆ tr1'.(keys) -> 
  tr2.(keys) ⊆ tr2'.(keys) -> 
  (make_tree tr1 k v tr2).(keys) ⊆ (make_tree tr1' k v tr2').(keys).
Proof.
  intros.
  pose proof (key_set_make_tree (k,v) tr1 tr2).
  unfold BinTree.make_tree in H1. simpl in H1.
  rewrite H1. clear H1.
  pose proof (key_set_make_tree (k,v) tr1' tr2').
  unfold BinTree.make_tree in H1. simpl in H1.
  rewrite H1. clear H1.
  rewrite H. rewrite H0. reflexivity.
Qed.

Lemma key_set_combine_tree_app : forall pt tr k v tr',
  ((combine_tree (pt ++ RH k v tr' :: nil) tr).(keys)
  == (combine_tree pt tr).(keys) ∪ Sets_singleton_setoid k
  ∪ tr'.(keys))%sets.
Proof.
  intros.
  revert tr.
  induction pt.
  + intros. simpl.
    pose proof (key_set_make_tree (k,v) tr' tr).
    unfold BinTree.make_tree in H. simpl in H. rewrite H. clear H.
    sets_unfold; intros; tauto.
  + intros. 
    destruct a; simpl; rewrite IHpt; reflexivity.
Qed.

Lemma key_set_combine_tree_find_pre : forall tr1 k v tr2,
  ((combine_tree
  (find_pre tr1 k v tr2).(pt) (find_pre tr1 k v tr2).(l_tree)).(keys)
    ∪ Sets_singleton_setoid (find_pre tr1 k v tr2).(k)
     == (tr1).(keys) ∪ (tr2).(keys) ∪ 
     Sets_singleton_setoid k)%sets.
Proof.
  intros.
  revert tr1 k v.
  induction tr2.
  + intros. simpl. rewrite key_set_empty. sets_unfold.
    intros. tauto.
  + intros. simpl. 
    pose proof (key_set_make_tree (k,v) tr2_1 tr2_2).
    unfold BinTree.make_tree in H. simpl in H. rewrite H. clear H.
    rewrite key_set_combine_tree_app.
    rewrite Sets_union_comm.
    rewrite <- !Sets_union_assoc.
    rewrite (Sets_union_comm (Sets_singleton_setoid (find_pre tr2_1 k v tr2_2).(k))
     ((combine_tree (find_pre tr2_1 k v tr2_2).(pt)
     (find_pre tr2_1 k v tr2_2).(l_tree)).(keys))).
    rewrite (IHtr2_2 tr2_1 k v).
    sets_unfold.
    intros.
    tauto.
Qed.

Lemma delete_keys_include : forall k tr,
  SearchTree tr -> 
  (tree_delete' k tr).(keys) ⊆ tr.(keys).
Proof.
  intros.
  induction tr. 
  + simpl; sets_unfold; intros; tauto.
  + simpl. 
    pose proof SearchTree_make_tree.
    assert (SearchTree (BinTree.make_tree (k0,v) tr1 tr2)) by apply H.
    specialize (H0 (k0,v) tr1 tr2).
    destruct (Key.dec k k0).
    - destruct s.
      * apply make_tree_keys_include.
        ++ apply IHtr1. tauto.
        ++ reflexivity.
      * apply make_tree_keys_include.
        ++ reflexivity.
        ++ apply IHtr2. tauto.
    - destruct tr1.
      * pose proof (key_set_make_tree (k0,v) empty tr2).
        unfold BinTree.make_tree in H2. simpl in H2.
        rewrite H2. sets_unfold. intros. right. tauto.
      * pose proof (key_set_make_tree ((find_pre tr1_1 k1 v0 tr1_2).(k),(find_pre tr1_1 k1 v0 tr1_2).(v)) (combine_tree(find_pre tr1_1 k1 v0 tr1_2).(pt) (find_pre tr1_1 k1 v0 tr1_2).(l_tree)) tr2).
        unfold BinTree.make_tree in H2. simpl in H2. rewrite H2.
        pose proof (key_set_make_tree (k0,v) (make_tree tr1_1 k1 v0 tr1_2) tr2).
        unfold BinTree.make_tree in H3. simpl in H3. rewrite H3. 
        pose proof (key_set_make_tree (k1,v0) tr1_1 tr1_2).
        unfold BinTree.make_tree in H4. simpl in H4. rewrite H4.
        subst.
        rewrite key_set_combine_tree_find_pre.
        sets_unfold; intros; tauto.
Qed.

Lemma key_set_in_root : forall tr1 k v tr2,
  k ∈ (make_tree tr1 k v tr2).(keys).
Proof.
  intros.
  pose proof (key_set_make_tree (k,v) tr1 tr2).
  rewrite H.
  simpl. 
  sets_unfold.
  left. right. reflexivity.
Qed.

Lemma pre_key_subset_tree : forall tr1 k v tr2,
  SearchTree (make_tree tr1 k v tr2) ->
  (find_pre tr1 k v tr2).(k) ∈ (make_tree tr1 k v tr2).(keys).
Proof.
  intros.
  revert tr1 k v H.
  induction tr2.
  + intros. 
    simpl.
    apply key_set_in_root.
  + intros.
    simpl.
    pose proof (key_set_make_tree (k0,v0) tr1 (make_tree tr2_1 k v tr2_2)).
    unfold BinTree.make_tree in H0. simpl in H0.
    rewrite H0. clear H0.
    pose proof (SearchTree_make_tree (k0,v0) tr1 (make_tree tr2_1 k v tr2_2)).
    pose proof H. rewrite H0 in H1. destruct H1 as [? [? [? ?]]].
    pose proof (IHtr2_2 tr2_1 k v).
    sets_unfold in H5.
    sets_unfold.
    right. 
    tauto.
Qed.

Lemma pre_key_lt_root : forall tr1 k v tr2 k0 v0 tr,
  SearchTree (make_tree (make_tree tr1 k v tr2) k0 v0 tr) ->
    (find_pre tr1 k v tr2).(k) < k0.
Proof.
  intros.
  pose proof (SearchTree_make_tree (k0,v0) (make_tree tr1 k v tr2) tr).
  pose proof H.
  rewrite H0 in H1.
  destruct H1 as [? [? [? ?]]].
  simpl in H1.
  unfold keys_key_lt in H1.
  pose proof (pre_key_subset_tree tr1 k v tr2).
  sets_unfold in H5.
  apply H1.
  tauto.
Qed.

Lemma pre_key_gt_root : forall tr1 k v tr2 k0 v0 tr,
  SearchTree (make_tree tr k0 v0 (make_tree tr1 k v tr2)) ->
    k0 < (find_pre tr1 k v tr2).(k).
Proof.
  intros.
  pose proof (SearchTree_make_tree (k0,v0) tr (make_tree tr1 k v tr2)).
  pose proof H.
  rewrite H0 in H1.
  destruct H1 as [? [? [? ?]]].
  simpl in H2.
  unfold keys_key_lt in H2.
  pose proof (pre_key_subset_tree tr1 k v tr2).
  sets_unfold in H5.
  apply H2.
  tauto.
Qed.

Lemma pre_key_gt_left_tr_key : forall tr1 k v tr2,
  SearchTree (make_tree tr1 k v tr2) -> 
  (combine_tree (find_pre tr1 k v tr2).(pt)
    (find_pre tr1 k v tr2).(l_tree)).(keys) =<-
  (find_pre tr1 k v tr2).(k).
Proof.
  intros.
  revert tr1 k v H. 
  induction tr2.
  + intros.
    simpl.
    pose proof (SearchTree_make_tree (k,v) tr1 empty).
    pose proof H. rewrite H0 in H1.
    destruct H1 as [? [? [? ?]]].
    apply H1.
  + intros.
    simpl.
    pose proof (key_set_combine_tree_app (find_pre tr2_1 k v tr2_2).(pt) (find_pre tr2_1 k v tr2_2).(l_tree) k0 v0 tr1).
    unfold keys_key_lt.
    intros.
    rewrite key_set_equiv in H1.
    rewrite H0 in H1.
    sets_unfold in H1.
    destruct H1. 
    destruct H1.
    - pose proof (IHtr2_2 tr2_1 k v).
      unfold keys_key_lt in H2.
      apply H2; try tauto.
      pose proof (SearchTree_make_tree (k0,v0) tr1 (make_tree tr2_1 k v tr2_2)).
      pose proof H. rewrite H3 in H4.
      tauto.
    - rewrite H1.
      eapply pre_key_gt_root.
      eapply H.
    - pose proof (SearchTree_make_tree (k0,v0) tr1 (make_tree tr2_1 k v tr2_2)).
      pose proof H.
      rewrite H2 in H3.
      destruct H3 as [? [? [? ?]]].
      simpl in H3.
      unfold keys_key_lt in H3.
      transitivity k0.
      * apply H3. tauto.
      * eapply pre_key_gt_root.
      eapply H.
Qed.

Lemma rt_key_lt_combine_pre : forall k0 v0 tr0 k v tr1 tr2,
  SearchTree (make_tree tr0 k0 v0 (make_tree tr1 k v tr2)) ->
  k0 -<= (combine_tree (find_pre tr1 k v tr2).(pt) (find_pre tr1 k v tr2).(l_tree)).(keys).
Proof.
  intros.
  revert tr0 k0 v0 tr1 k v H.
  induction tr2; intros; simpl.
  + pose proof (SearchTree_make_tree (k0,v0) tr0 ((make_tree tr1 k v empty))).
    pose proof H. rewrite H0 in H1. destruct H1 as [? [? [? ?]]].
    simpl in H2.
    sets_unfold in H2.
    unfold key_keys_lt.
    intros.
    apply H2.
    pose proof (key_set_make_tree (k,v) tr1 empty).
    rewrite key_set_equiv.
    rewrite H6.
    sets_unfold.
    tauto.
  + unfold key_keys_lt.
    sets_unfold.
    intros.
    rewrite key_set_equiv in H0.
    rewrite key_set_combine_tree_app in H0.
    sets_unfold in H0.
    pose proof (SearchTree_make_tree (k0,v0) tr0 (make_tree tr1 k1 v1 (make_tree tr2_1 k v tr2_2))).
      pose proof H. rewrite H1 in H2. destruct H2 as [? [? [? ?]]].
    assert (k0 < k1). {
      pose proof (key_set_in_root tr1 k1 v1 (make_tree tr2_1 k v tr2_2)).
      unfold key_keys_lt in H3.
      pose proof (H3 k1).
      apply H7.
      eauto.
    }
    destruct H0. destruct H0.
    - unfold key_keys_lt in IHtr2_2.
      pose proof (IHtr2_2 tr1 k1 v1 tr2_1 k v).
      transitivity k1.
      * simpl in H3.
        pose proof (key_set_in_root tr1 k1 v1 (make_tree tr2_1 k v tr2_2)).
        unfold key_keys_lt in H3.
        specialize (H3 k1).
        apply H3.
        eauto.
      * do 3 eauto.
    - rewrite H0. tauto.
    - unfold key_keys_lt in H3.
      specialize (H3 k2).
      apply H3.
      rewrite key_set_equiv.
      pose proof (key_set_make_tree (k1,v1) tr1 (make_tree tr2_1 k v tr2_2)).
      rewrite H7.
      sets_unfold. tauto.
Qed. 

Lemma searchtree_pre_combine : forall tr1 k v tr2,
  SearchTree (make_tree tr1 k v tr2) ->
  SearchTree (combine_tree
    (find_pre tr1 k v tr2).(pt)
    (find_pre tr1 k v tr2).(l_tree)).
Proof.
  intros.
  revert tr1 k v H.
  induction tr2; intros; simpl.
  + pose proof (SearchTree_make_tree (k,v) tr1 empty).
    rewrite H0 in H. tauto.
  + rewrite combine_tree_make_tree.
    pose proof (SearchTree_make_tree (k0,v0) tr1 (make_tree tr2_1 k v tr2_2)).
    pose proof H. rewrite H0 in H1. 
    destruct H1 as [? [? [? ?]]].
    pose proof (SearchTree_make_tree (k0,v0) tr1 (combine_tree
    (find_pre tr2_1 k v tr2_2).(pt)
    (find_pre tr2_1 k v tr2_2).(l_tree))).
    rewrite H5. clear H5.
    split; try split; try split; try split; try tauto.
    - simpl. eapply rt_key_lt_combine_pre. eauto.
    - apply IHtr2_2. tauto.
Qed.

Theorem delete'_SearchTree: forall tr k,
  SearchTree tr ->
  SearchTree (tree_delete' k tr).
Proof. 
  induction tr. 
  + intros.
    simpl. 
    auto.
  + intros.
    simpl. 
    destruct (Key.dec k0 k).
    - destruct s.
      * pose proof SearchTree_make_tree.
        apply H0.
        pose proof (H0 (k, v) (tree_delete' k0 tr1) tr2).
        pose proof (H0 (k, v) tr1 tr2).
        pose proof H.
        rewrite H2 in H3.
        destruct H3 as [? [? [? ?]]].
        rewrite H0.
        split.
        ++ apply (keys_inclusion_lt1 ((tree_delete' k0 tr1).(keys)) (tr1.(keys))) ; auto.
           apply delete_keys_include.
           tauto.
        ++ split. 
          -- tauto.
          -- split; try tauto.
             apply IHtr1. tauto.
      * pose proof SearchTree_make_tree.
        apply H0.
        pose proof (H0 (k, v) tr1 (tree_delete' k0 tr2)).
        pose proof (H0 (k, v) tr1 tr2).
        pose proof H.
        rewrite H2 in H3.
        destruct H3 as [? [? [? ?]]].
        rewrite H0.
        split.
        ++ tauto.
        ++ split. 
          -- apply (keys_inclusion_lt2 ((tree_delete' k0 tr2).(keys)) (tr2.(keys))) ; auto.
             apply delete_keys_include.
             tauto.
          -- split; try tauto.
             apply IHtr2. tauto.
    - pose proof SearchTree_make_tree.
      pose proof H.
      pose proof (H0 (k, v) tr1 tr2).
      rewrite H2 in H1.
      destruct H1 as [? [? [? ?]]].
      destruct tr1.
      * tauto.
      * apply SearchTree_make_tree.
        pose proof (H0 ((find_pre tr1_1 k1 v0 tr1_2).(k), (find_pre tr1_1 k1 v0 tr1_2).(v)) (combine_tree (find_pre tr1_1 k1 v0 tr1_2).(pt) (find_pre tr1_1 k1 v0 tr1_2).(l_tree)) tr2).
        apply H6.
        split.
        ++ simpl. apply pre_key_gt_left_tr_key. tauto.
        ++ split. 
          -- simpl.
             apply (key_key_keys_lt_trans (find_pre tr1_1 k1 v0 tr1_2).(k) k tr2.(keys)).
             ** apply (pre_key_lt_root tr1_1 k1 v0 tr1_2 k v tr2). tauto.
             ** tauto.
          -- split; try tauto. 
             apply searchtree_pre_combine. tauto.
Qed.

Lemma tree_kv_make_tree_equiv : forall tr1 k v tr2 k0 v0,
  tree_kv (make_tree tr1 k v tr2) k0 v0 <-> 
  tree_kv (BinTree.make_tree (k,v) tr1 tr2) k0 v0.
Proof.
  intros.
  split; try tauto.
Qed.

Ltac destruct_kv_make := 
  rewrite tree_kv_make_tree_equiv;
  rewrite tree_kv_make_tree_iff.

Ltac destruct_kv_make_h H := 
  match type of H with 
  | tree_kv (make_tree ?tr1 ?k ?v ?tr2) ?k0 ?v0=>
    rewrite tree_kv_make_tree_equiv in H;
    rewrite tree_kv_make_tree_iff in H;
    destruct H as [? | [? | ?]];
    try tauto
  end.

Lemma tree_kv_key_l : forall tr1 k v tr2 k' v',
  SearchTree (make_tree tr1 k v tr2) -> 
  tree_kv tr1 k' v' ->
  k' < k. 
Proof.
  intros.
  destruct_ST_make_tree H.
  unfold keys_key_lt in H1.
  specialize (H1 k').
  pose proof tree_kv_key_set tr1 k' v' H0.
  pose proof H1 H5.
  tauto.
Qed.

Lemma tree_kv_key_r : forall tr1 k v tr2 k' v',
  SearchTree (make_tree tr1 k v tr2) -> 
  tree_kv tr2 k' v' ->
  k < k'. 
Proof.
  intros.
  destruct_ST_make_tree H.
  unfold key_keys_lt in H2.
  specialize (H2 k').
  pose proof tree_kv_key_set tr2 k' v' H0.
  pose proof H2 H5.
  tauto.
Qed.

Lemma tree_kv_key_l_del : forall tr1 k v tr2 k' v' k0,
  SearchTree (make_tree tr1 k v tr2) -> 
  tree_kv (tree_delete' k0 tr1) k' v' ->
  k' < k. 
Proof.
  intros.
  destruct_ST_make_tree H.
  unfold key_keys_lt in H1.
  specialize (H1 k').
  pose proof tree_kv_key_set (tree_delete' k0 tr1) k' v' H0.
  rewrite key_set_equiv in H5.
  pose proof delete_keys_include k0 tr1 H3.
  sets_unfold in H6.
  specialize (H6 k').
  pose proof (tree_kv_key_set (tree_delete' k0 tr1) k' v' H0).
  pose proof H6 H7.
  pose proof H1 H8.
  tauto.
Qed.

Lemma tree_kv_key_r_del : forall tr1 k v tr2 k' v' k0,
  SearchTree (make_tree tr1 k v tr2) -> 
  tree_kv (tree_delete' k0 tr2) k' v' ->
  k < k'. 
Proof.
  intros.
  destruct_ST_make_tree H.
  unfold key_keys_lt in H2.
  specialize (H2 k').
  pose proof tree_kv_key_set (tree_delete' k0 tr2) k' v' H0.
  rewrite key_set_equiv in H5.
  pose proof delete_keys_include k0 tr2 H4.
  sets_unfold in H6.
  specialize (H6 k').
  pose proof (tree_kv_key_set (tree_delete' k0 tr2) k' v' H0).
  pose proof H6 H7.
  pose proof H2 H8.
  tauto.
Qed.

Lemma tree_kv_combine_tree_iff : forall k0 v0 tr0 tr pt k v,
  tree_kv (combine_tree (pt ++ RH k0 v0 tr0 :: nil) tr) k v
  <-> tree_kv (combine_tree pt tr) k v \/
      tree_kv tr0 k v \/
      (k = k0 /\ v = v0).
Proof.
  intros.
  revert k0 v0 tr0 tr k v. 
  induction pt.
  + intros. simpl. split; intros.
    - destruct_kv_make_h H.
    - destruct_kv_make. tauto.
  + intros. split; intros.
    - destruct a; simpl; simpl in *.
      * rewrite IHpt in H. tauto.
      * rewrite IHpt in H. tauto.
    - destruct a; simpl; simpl in *.
      * rewrite <- IHpt in H. tauto.
      * rewrite <- IHpt in H. tauto.
Qed.

Lemma tree_kv_key_combine_lt : forall tr1_1 k1 v1 tr1_2 k v tr2 k0 v0,
  SearchTree (make_tree (make_tree tr1_1 k1 v1 tr1_2) k v tr2) ->
  tree_kv (combine_tree
           (find_pre tr1_1 k1 v1 tr1_2).(pt)
           (find_pre tr1_1 k1 v1 tr1_2).(l_tree))
          k0 v0 ->
  k0 < k.
Proof.
  intros.
  transitivity (find_pre tr1_1 k1 v1 tr1_2).(k).
  + pose proof (tree_kv_key_set (combine_tree(find_pre tr1_1 k1 v1 tr1_2).(pt) (find_pre tr1_1 k1 v1 tr1_2).(l_tree)) k0 v0 H0).
    destruct_ST_make_tree H.
    pose proof (pre_key_gt_left_tr_key tr1_1 k1 v1 tr1_2 H4).
    unfold keys_key_lt in H6.
    specialize (H6 k0).
    pose proof H6 H1.
    tauto.
  + apply (pre_key_lt_root tr1_1 k1 v1 tr1_2 k v tr2 H).
Qed.

Lemma tree_kv_key_combine_gt : forall tr1 k1 v1 tr2_1 k v tr2_2 k0 v0,
  SearchTree (make_tree tr1 k1 v1 (make_tree tr2_1 k v tr2_2)) ->
  tree_kv (combine_tree
           (find_pre tr2_1 k v tr2_2).(pt)
           (find_pre tr2_1 k v tr2_2).(l_tree))
          k0 v0 ->
  k1 < k0.
Proof.
  intros.
  revert tr1 k1 v1 tr2_1 k v k0 v0 H H0.
  induction tr2_2.
  + intros. simpl in H0.
    destruct_ST_make_tree H.
    simpl in H2.
    pose proof tree_kv_key_set tr2_1 k0 v0 H0.
    unfold key_keys_lt in H2.
    specialize (H2 k0).
    apply H2.
    pose proof key_set_make_tree (k,v) tr2_1 empty.
    rewrite key_set_equiv.
    rewrite H6.
    sets_unfold.
    tauto.
  + intros. simpl in H0.
    destruct_ST_make_tree H.
    rewrite tree_kv_combine_tree_iff in H0.
    destruct H0 as [? | [? | ?]].
    - pose proof IHtr2_2_2 tr2_1 k0 v0 tr2_2_1 k v k2 v2 H4 H0.
      transitivity k0; try Key.order.
      unfold key_keys_lt in H2.
      specialize (H2 k0).
      apply H2.
      apply key_set_in_root.
    - pose proof tree_kv_key_set tr2_1 k2 v2 H0.
      unfold key_keys_lt in H2.
      specialize (H2 k2).
      apply H2.
      rewrite key_set_equiv.
      pose proof key_set_make_tree (k0,v0) tr2_1 (make_tree tr2_2_1 k v tr2_2_2).
      rewrite H6.
      pose proof key_set_make_tree (k,v) tr2_2_1 tr2_2_2.
      rewrite H7.
      sets_unfold.
      tauto.
    - destruct H0. subst k2.
      unfold key_keys_lt in H2.
      specialize (H2 k0).
      apply H2.
      rewrite key_set_equiv.
      pose proof key_set_make_tree (k0,v0) tr2_1 (make_tree tr2_2_1 k v tr2_2_2).
      rewrite H0.
      sets_unfold.
      left. right. simpl. reflexivity.
Qed.

Lemma tree_kv_pre: forall tr1 k v tr2,
  SearchTree (make_tree tr1 k v tr2) ->
  tree_kv (make_tree tr1 k v tr2) 
    ((find_pre tr1 k v tr2).(k),
    (find_pre tr1 k v tr2).(v)).(key)
    ((find_pre tr1 k v tr2).(k),
    (find_pre tr1 k v tr2).(v)).(val).
Proof.
  intros.
  revert tr1 k v H.
  induction tr2.
  + intros. simpl. destruct_kv_make.
    right. left. split; simpl; tauto.
  + intros. simpl. destruct_kv_make.
    right. right.
    apply IHtr2_2.
    destruct_ST_make_tree H.
    tauto.
Qed.

Lemma tree_kv_lt_pre : forall tr1 k v tr2 k0 v0,
  SearchTree (make_tree tr1 k v tr2) ->
  tree_kv (make_tree tr1 k v tr2) k0 v0 ->
  (k0 < (find_pre tr1 k v tr2).(k)) ->
  tree_kv (combine_tree
     (find_pre tr1 k v tr2).(pt)
     (find_pre tr1 k v tr2).(l_tree))
  k0 v0.
Proof.
  intros.
  revert tr1 k v H H0 H1.
  induction tr2.
  + intros. simpl. simpl in *.
    destruct_kv_make_h H0.
    - simpl in H0. destruct H0. Key.order.
    - pose proof tree_kv_empty_iff k0 v0.
      tauto.
  + intros. simpl. rewrite tree_kv_combine_tree_iff; try tauto.
    destruct (Key.dec k0 k1); try destruct s.
    - right. left. 
      destruct_kv_make_h H0.
      * simpl in H0. destruct H0. Key.order.
      * pose proof tree_kv_key_r tr1 k1 v1 (make_tree tr2_1 k v tr2_2) k0 v0 H H0.
        Key.order.
    - left. simpl in H1.
      destruct_ST_make_tree H.
      destruct_kv_make_h H0.
      * pose proof tree_kv_key_l tr1 k1 v1 (make_tree tr2_1 k v tr2_2) k0 v0 H H0.
        Key.order.
      * destruct H0. simpl in H0. Key.order.
      * apply IHtr2_2; try tauto.
    - right. right. split; try tauto.
      destruct_kv_make_h H0.
      * pose proof tree_kv_key_l tr1 k1 v1 (make_tree tr2_1 k v tr2_2) k0 v0 H H0.
        Key.order.
      * pose proof tree_kv_key_r tr1 k1 v1 (make_tree tr2_1 k v tr2_2) k0 v0 H H0.
        Key.order.
Qed.


Lemma tree_kv_combine_make : forall tr1 k v tr2 k0 v0,
  SearchTree (make_tree tr1 k v tr2) ->
  tree_kv (combine_tree
          (find_pre tr1 k v tr2).(pt)
          (find_pre tr1 k v tr2).(l_tree))
          k0 v0 ->
  tree_kv (make_tree tr1 k v tr2) k0 v0.
Proof.
  intros.
  revert tr1 k v k0 v0 H H0.
  induction tr2.
  + intros. simpl in H0.
    destruct_kv_make. tauto.
  + intros. 
    destruct_ST_make_tree H.
    destruct_kv_make.
    destruct (Key.dec k1 k0); try destruct s. 
    - left. simpl in H0.
      rewrite tree_kv_combine_tree_iff in H0.
      destruct H0.
      * pose proof tree_kv_key_combine_gt tr1 k0 v0 tr2_1 k v tr2_2 k1 v1 H H0.
        Key.order.
      * destruct H0; try tauto.
        destruct H0. Key.order.
    - simpl in H0.
      rewrite tree_kv_combine_tree_iff in H0.
      destruct H0.
      * right. right.
        apply IHtr2_2. tauto. tauto.
      * destruct H0.
        ++ (* may be Ltac*)
          pose proof tree_kv_key_l tr1 k0 v0 (make_tree tr2_1 k v tr2_2) k1 v1 H H0.
          Key.order.
        ++ destruct H0. Key.order.
    - simpl in H0.
      rewrite tree_kv_combine_tree_iff in H0.
      destruct H0.
      * pose proof tree_kv_key_combine_gt tr1 k0 v0 tr2_1 k v tr2_2 k1 v1 H H0.
        Key.order.
      * destruct H0.
        ++ pose proof tree_kv_key_l tr1 k0 v0 (make_tree tr2_1 k v tr2_2) k1 v1 H H0.
          Key.order.
        ++ simpl. tauto.
Qed.

Lemma tree_kv_pre_max : forall tr1 k v tr2 k0 v0,
  SearchTree (make_tree tr1 k v tr2) ->
  tree_kv (make_tree tr1 k v tr2) k0 v0 ->
  ~(k0 > (find_pre tr1 k v tr2).(k)).
Proof.
  intros.
  revert tr1 k v k0 v0 H H0.
  induction tr2.
  + intros. simpl. 
    destruct_kv_make_h H0.
    - pose proof tree_kv_key_l tr1 k v empty k0 v0 H H0.
      Key.order.
    - destruct H0. simpl in H0. Key.order.
    - rewrite tree_kv_empty_iff in H0. tauto.
  + intros. simpl.
    destruct_ST_make_tree H.
    destruct_kv_make_h H0.
    - pose proof pre_key_gt_root tr2_1 k v tr2_2 k0 v0 tr1 H.
      pose proof tree_kv_key_l tr1 k0 v0 (make_tree tr2_1 k v tr2_2) k1 v1 H H0.
      unfold key_keys_lt in H2.
      Key.order.
    - pose proof pre_key_gt_root tr2_1 k v tr2_2 k0 v0 tr1 H.
      destruct H0.
      simpl in H0.
      Key.order.
    - pose proof (IHtr2_2 tr2_1 k v k1 v1 H4 H0).
      tauto.
Qed.

Lemma tree_kv_delete_neq : forall tr k v k0,
  SearchTree tr ->
  tree_kv (tree_delete' k0 tr) k v ->
  k0 ~= k.
Proof.
  intros.
  revert k v k0 H H0.
  induction tr. 
  + intros. simpl in H0.
    rewrite tree_kv_empty_iff in H0.
    tauto.
  + intros.
    simpl in H0.
    destruct (Key.dec k1 k); try destruct s. 
    - destruct_kv_make_h H0.
      * destruct_ST_make_tree H.
        pose proof IHtr1 k0 v0 k1 H3 H0.
        tauto.
      * destruct H0. simpl in H0. Key.order.
      * pose proof tree_kv_key_r tr1 k v tr2 k0 v0 H H0.
        Key.order.
    - destruct_kv_make_h H0.
      * pose proof tree_kv_key_l tr1 k v tr2 k0 v0 H H0.
        Key.order.
      * destruct H0. simpl in H0. Key.order.
      * destruct_ST_make_tree H.
        pose proof IHtr2 k0 v0 k1 H4 H0.
        tauto.
    - destruct tr1.
      * pose proof tree_kv_key_r empty k v tr2 k0 v0 H H0.
        Key.order.
      * destruct_kv_make_h H0.
        ++ destruct_ST_make_tree H.
          pose proof tree_kv_combine_make tr1_1 k2 v1 tr1_2 k0 v0 H3 H0.
          pose proof tree_kv_key_set (make_tree tr1_1 k2 v1 tr1_2) k0 v0 H5.
          unfold keys_key_lt in H1.
          specialize (H1 k0).
          pose proof H1 H6.
          simpl in H7.
          Key.order.
        ++ pose proof pre_key_lt_root tr1_1 k2 v1 tr1_2 k v tr2 H.
          destruct H0.
          simpl in H0. Key.order.
        ++ pose proof tree_kv_key_r (make_tree tr1_1 k2 v1 tr1_2) k v tr2 k0 v0 H H0.
          Key.order.
Qed.

Lemma tree_kv_unique_in_pre : forall tr1 k v tr2 k0 v0,
  SearchTree (make_tree tr1 k v tr2) ->
  tree_kv (make_tree tr1 k v tr2) k0 v0 ->
  k0 = (find_pre tr1 k v tr2).(k) ->
  v0 = (find_pre tr1 k v tr2).(v).
Proof.
  intros.
  revert tr1 k v k0 v0 H H0 H1.
  induction tr2.
  + intros. simpl. 
    destruct_kv_make_h H0.
    - simpl in H1.
      pose proof tree_kv_key_l tr1 k v empty k0 v0 H H0.
      Key.order.
    - rewrite tree_kv_empty_iff in H0.
      tauto.
  + intros. simpl in H1.
    destruct_ST_make_tree H.
    destruct_kv_make_h H0.
    - pose proof tree_kv_key_l tr1 k0 v0 (make_tree tr2_1 k v tr2_2) k1 v1 H H0.
      pose proof pre_key_gt_root tr2_1 k v tr2_2 k0 v0 tr1 H.
      Key.order.
    - simpl in H0. destruct H0.
      pose proof pre_key_gt_root tr2_1 k v tr2_2 k0 v0 tr1 H.
      Key.order.
    - pose proof IHtr2_2 tr2_1 k v k1 v1 H5 H0 H1. tauto.
Qed.

Theorem delete'_Abs: forall tr m k,
  SearchTree tr ->
  Abs tr m ->
  Abs (tree_delete' k tr) (map_delete k m).
Proof. 
  unfold Abs.
  intros.
  specialize (H0 k0 v).
  rewrite delete_iff.
  rewrite H0.
  clear m H0.
  revert k k0 v H.
  induction tr. 
  + intros. simpl. 
    rewrite tree_kv_empty_iff.
    tauto.
  + intros. 
    destruct_ST_make_tree H.
    destruct (Key.dec k0 k); try destruct s.
    - rewrite tree_kv_make_tree_equiv.
      rewrite !tree_kv_make_tree_iff.
      destruct (Key.dec k k1); try Key.order.
      destruct s.
      * simpl.
        destruct (Key.dec k0 k); try Key.order.
        destruct s; try Key.order.
        rewrite tree_kv_make_tree_equiv.
        rewrite !tree_kv_make_tree_iff.
        simpl. 
        split.
        ++ intros. destruct H4.
           destruct H5 as [? | [? | ?]]; try tauto.
           left.
           apply (IHtr1 k0 k1 v0); try tauto.
        ++ intros. destruct H4 as [? | [? | ?]]; try split; try Key.order; try tauto.
           left. 
           apply (IHtr1 k0 k1 v0); try tauto.
      * simpl.
        destruct (Key.dec k0 k); try Key.order.
        destruct s; try Key.order. clear l1.
        rewrite tree_kv_make_tree_equiv.
        rewrite !tree_kv_make_tree_iff.
        simpl. 
        split.
        ++ intros. destruct H4.
           destruct H5 as [? | [? | ?]]; try tauto.
           left.
           apply (IHtr1 k0 k1 v0); try tauto.
        ++ intros. destruct H4 as [? | [? | ?]]; try split; try Key.order; try tauto; 
           try apply (IHtr1 k0 k1 v0); try tauto.
           -- left.
              specialize (IHtr1 k0 k1 v0).
              pose proof (IHtr1 H2).
              destruct H5.
              pose proof (H6 H4).
              destruct H7.
              tauto.
           -- destruct H4. Key.order.
           -- pose proof (tree_kv_key_r tr1 k v tr2 k1 v0 H H4).
              Key.order.
      * simpl. 
        destruct (Key.dec k0 k); try Key.order.
        destruct s; try Key.order. clear l0.
        rewrite tree_kv_make_tree_equiv.
        rewrite !tree_kv_make_tree_iff.
        simpl. 
        split.
        ++ intros. destruct H4 as [? [? | [? |  ?]]]; try tauto.
          pose proof (tree_kv_key_l tr1 k v tr2 k1 v0 H H5).
          Key.order.
        ++ intros. destruct H4 as [? | [? | ?]]; try split; try Key.order; try tauto.
        pose proof (tree_kv_key_l_del tr1 k v tr2 k1 v0 k0 H H4).
        Key.order.
      - rewrite tree_kv_make_tree_equiv.
        rewrite !tree_kv_make_tree_iff.
        destruct (Key.dec k k1); try Key.order.
        destruct s.
        * simpl.
          destruct (Key.dec k0 k); try Key.order.
          destruct s; try Key.order.
          rewrite tree_kv_make_tree_equiv.
          rewrite !tree_kv_make_tree_iff.
          simpl. 
          split.
          ++ intros. destruct H4.
             destruct H5 as [? | [? | ?]]; try tauto.
             right. right.
             apply (IHtr2 k0 k1 v0); try tauto.
          ++ intros. destruct H4 as [? | [? | ?]].
            -- split; try tauto.
              pose proof (tree_kv_key_l tr1 k v tr2 k1 v0 H H4).
              Key.order.
            -- split; try tauto. destruct H4. rewrite H4. Key.order.
            -- split.
              ** apply (IHtr2 k0 k1 v0); try tauto.
              ** right. right. apply (IHtr2 k0 k1 v0); tauto.
        * simpl.
          destruct (Key.dec k0 k); try Key.order.
          destruct s; try Key.order. clear l1.
          rewrite tree_kv_make_tree_equiv.
          rewrite !tree_kv_make_tree_iff.
          simpl. 
          split.
          ++ intros. destruct H4.
             destruct H5 as [? | [? | ?]]; try tauto.
             pose proof (tree_kv_key_r tr1 k v tr2 k1 v0 H H5).
             Key.order.
          ++ intros. destruct H4 as [? | [? | ?]]; try split; try Key.order; try tauto; 
             try apply (IHtr1 k0 k1 v0); try tauto.
             pose proof (tree_kv_key_r_del tr1 k v tr2 k1 v0 k0 H H4).
             Key.order.
        * simpl. 
          destruct (Key.dec k0 k); try Key.order.
          destruct s; try Key.order. clear l0.
          rewrite tree_kv_make_tree_equiv.
          rewrite !tree_kv_make_tree_iff.
          simpl. 
          split.
          ++ intros. destruct H4 as [? [? | [? |  ?]]]; try tauto.
            pose proof (tree_kv_key_r tr1 k v tr2 k1 v0 H H5).
            Key.order.
          ++ intros. destruct H4 as [? | [? | ?]]; try split; try Key.order; try tauto.
            pose proof (tree_kv_key_r_del tr1 k v tr2 k1 v0 k0 H H4).
            Key.order.
    - rewrite tree_kv_make_tree_equiv.
      rewrite !tree_kv_make_tree_iff.
      destruct (Key.dec k k1); try Key.order.
      destruct s.
      * split. 
        ++ intros. simpl.
          destruct (Key.dec k0 k); try Key.order.
          destruct s; try Key.order. clear e0.
          destruct tr1.
          -- destruct H4 as [? [? | [? |  ?]]].
            ** pose proof tree_kv_empty k1 v0. tauto.
            ** simpl in H5. destruct H5. Key.order.
            ** tauto.
          -- destruct H4 as [? [? | [? |  ?]]].
            ** pose proof (tree_kv_key_l (make_tree tr1_1 k2 v1 tr1_2) k v tr2 k1 v0 H H5).
              Key.order.
            ** simpl in H5. 
              destruct H5. Key.order.
            ** rewrite tree_kv_make_tree_equiv.
              rewrite !tree_kv_make_tree_iff.
              tauto.
        ++ simpl. 
          destruct (Key.dec k0 k); try Key.order; try destruct s; simpl.
          -- rewrite tree_kv_make_tree_equiv.
            rewrite !tree_kv_make_tree_iff.
            intros.
            destruct H4 as [? | [[? ?] | ?]].
            ** pose proof (tree_kv_key_l_del tr1 k v tr2 k1 v0 k0 H H4).
              Key.order.
            ** simpl in H4. Key.order.
            ** split; try Key.order.
          -- rewrite tree_kv_make_tree_equiv.
            rewrite !tree_kv_make_tree_iff.
            intros.
            destruct H4 as [? | [[? ?] | ?]].
            ** pose proof (tree_kv_key_l tr1 k v tr2 k1 v0 H H4).
              Key.order.
            ** simpl in H4. Key.order.
            ** split; try Key.order.
          -- destruct tr1.
            ** intros. split; try Key.order.
              tauto.
            ** rewrite tree_kv_make_tree_equiv.
              rewrite !tree_kv_make_tree_iff.
              intros.
              destruct H4 as [? | [[? ?] | ?]].
              +++ pose proof (tree_kv_key_combine_lt tr1_1 k2 v1 tr1_2 k v tr2 k1 v0 H H4).
                Key.order.
              +++ simpl in H4.
                pose proof (pre_key_lt_root tr1_1 k2 v1 tr1_2 k v tr2 H).
                Key.order.
              +++ split; try Key.order.
                tauto.
      * split.
        ++ intros. destruct H4 as [? [? | ?]].
          -- simpl.
            destruct (Key.dec k0 k); try Key.order.
            destruct s; try Key.order. 
            destruct tr1.
            ** pose proof (tree_kv_empty k1 v0).
              tauto.
            ** rewrite tree_kv_make_tree_equiv.
              rewrite !tree_kv_make_tree_iff.
              destruct (Key.dec k1 ((find_pre tr1_1 k2 v1 tr1_2).(k),
              (find_pre tr1_1 k2 v1 tr1_2).(v)).(key)).
              destruct s. 
              +++ left. 
                  apply tree_kv_lt_pre. tauto. tauto. tauto.
              +++ pose proof (tree_kv_pre_max tr1_1 k2 v1 tr1_2 k1 v0 H2 H5).
                Key.order.
              +++ right. left. split; try tauto.
                simpl. simpl in e1.
                pose proof tree_kv_unique_in_pre tr1_1 k2 v1 tr1_2 k1 v0 H2 H5 e1.
                tauto.
          -- destruct H5. 
            ** destruct H5. simpl in H5. Key.order.
            ** pose proof (tree_kv_key_r tr1 k v tr2 k1 v0 H H5).
              Key.order.
        ++ simpl. 
          destruct (Key.dec k0 k); try Key.order.
          destruct s; try Key.order.
          destruct tr1.
          -- intros. 
            pose proof (tree_kv_key_r empty k v tr2 k1 v0 H H4).
            Key.order.
          -- rewrite tree_kv_make_tree_equiv.
            rewrite !tree_kv_make_tree_iff.
            intros.
            destruct H4 as [? | [[? ?] | ?]].
            ** split; try Key.order.
              left.
              apply tree_kv_combine_make.
              tauto. tauto.
            ** split; try Key.order.
              left.
              pose proof tree_kv_pre tr1_1 k2 v1 tr1_2 H2.
              subst k1 v0.
              tauto.
            ** split; try Key.order.
              pose proof (tree_kv_key_r (make_tree tr1_1 k2 v1 tr1_2) k v tr2 k1 v0 H H4).
              Key.order.
      * split.
        ++ intros. destruct H4. Key.order.
        ++ intros.
           pose proof tree_kv_delete_neq (make_tree tr1 k v tr2) k1 v0 k0 H H4. 
           Key.order.
Qed.

(*

match goal with
| |- context[tree_kv ?t ?k ?v] => pose k
end.


*)

Theorem store_ptb_LH:
  forall p2_fa p_fa p_bro k v tr,
    p_fa <> NULL ->
    INT_MIN <= k <= INT_MAX ->
    p2_fa # Ptr |-> p_fa **
    &(p_fa # "tree" ->ₛ "key") # Int |-> k **
    &(p_fa # "tree" ->ₛ "value") # Int |-> v **
    &(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro **
    store_tree p_bro tr |--
    store_ptb (&(p_fa # "tree" ->ₛ "left")) p2_fa
      (LH k v tr :: nil).
Proof.
  intros p2_fa p_fa p_bro k v tr Hfa Hk.
  simpl.
  Exists p_fa.
  Exists p2_fa.
  Exists p_bro.
  repeat (split_pure_spatial || split_pures).
  - cancel (p2_fa # Ptr |-> p_fa).
    cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro).
    cancel (store_tree p_bro tr).
  - dump_pre_spatial.
    exact Hfa.
  - dump_pre_spatial.
    exact Hk.
  - dump_pre_spatial.
    reflexivity.
  - dump_pre_spatial.
    reflexivity.
Qed.

Theorem store_pt_LH:
  forall p p_fa p_bro k v tr,
    p_fa <> NULL ->
    INT_MIN <= k <= INT_MAX ->
    &(p_fa # "tree" ->ₛ "key") # Int |-> k **
    &(p_fa # "tree" ->ₛ "value") # Int |-> v **
    &(p_fa # "tree" ->ₛ "left") # Ptr |-> p **
    &(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro **
    store_tree p_bro tr |--
    store_pt p p_fa (LH k v tr :: nil).
Proof.
  intros p p_fa p_bro k v tr Hfa Hk.
  simpl.
  Exists p_fa.
  Exists p_bro.
  repeat (split_pure_spatial || split_pures).
  - cancel (&(p_fa # "tree" ->ₛ "left") # Ptr |-> p).
    cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro).
    cancel (store_tree p_bro tr).
  - dump_pre_spatial.
    exact Hfa.
  - dump_pre_spatial.
    exact Hk.
  - dump_pre_spatial.
    reflexivity.
Qed.

Theorem store_ptb_RH:
  forall p2_fa p_fa p_bro k v tr,
    p_fa <> NULL ->
    INT_MIN <= k <= INT_MAX ->
    p2_fa # Ptr |-> p_fa **
    &(p_fa # "tree" ->ₛ "key") # Int |-> k **
    &(p_fa # "tree" ->ₛ "value") # Int |-> v **
    &(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro **
    store_tree p_bro tr |--
    store_ptb (&(p_fa # "tree" ->ₛ "right")) p2_fa
      (RH k v tr :: nil).
Proof.
  intros p2_fa p_fa p_bro k v tr Hfa Hk.
  simpl.
  Exists p_fa.
  Exists p2_fa.
  Exists p_bro.
  repeat (split_pure_spatial || split_pures).
  - cancel (p2_fa # Ptr |-> p_fa).
    cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro).
    cancel (store_tree p_bro tr).
  - dump_pre_spatial.
    exact Hfa.
  - dump_pre_spatial.
    exact Hk.
  - dump_pre_spatial.
    reflexivity.
  - dump_pre_spatial.
    reflexivity.
Qed.


Theorem store_pt_RH:
  forall p p_fa p_bro k v tr,
    p_fa <> NULL ->
    INT_MIN <= k <= INT_MAX ->
    &(p_fa # "tree" ->ₛ "key") # Int |-> k **
    &(p_fa # "tree" ->ₛ "value") # Int |-> v **
    &(p_fa # "tree" ->ₛ "right") # Ptr |-> p **
    &(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro **
    store_tree p_bro tr |--
    store_pt p p_fa (RH k v tr :: nil).
Proof.
  intros p p_fa p_bro k v tr Hfa Hk.
  simpl.
  Exists p_fa.
  Exists p_bro.
  repeat (split_pure_spatial || split_pures).
  - cancel (&(p_fa # "tree" ->ₛ "right") # Ptr |-> p).
    cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro).
    cancel (store_tree p_bro tr).
  - dump_pre_spatial.
    exact Hfa.
  - dump_pre_spatial.
    exact Hk.
  - dump_pre_spatial.
    reflexivity.
Qed.

Theorem store_ptb_app:
  forall p2 p2_mid p2_root pt1 pt2,
    store_ptb p2 p2_mid pt1 **
    store_ptb p2_mid p2_root pt2 |--
    store_ptb p2 p2_root (pt1 ++ pt2).
Proof.
  intros p2 p2_mid p2_root pt1.
  revert p2 p2_mid p2_root.
  induction pt1; intros p2 p2_mid p2_root pt2.
  - simpl.
    Intros_p Hp2.
    subst p2_mid.
    cancel.
  - destruct a.
    + simpl.
      Intros p_fa.
      Intros p2_fa.
      Intros p_bro.
      Exists p_fa.
      Exists p2_fa.
      Exists p_bro.
      repeat (split_pure_spatial || split_pures).
      * cancel (p2_fa # Ptr |-> p_fa).
        cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
        cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
        cancel (&(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro).
        cancel (store_tree p_bro t).
        apply (IHpt1 p2_fa p2_mid p2_root pt2).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * dump_pre_spatial.
        exact H1.
    + simpl.
      Intros p_fa.
      Intros p2_fa.
      Intros p_bro.
      Exists p_fa.
      Exists p2_fa.
      Exists p_bro.
      repeat (split_pure_spatial || split_pures).
      * cancel (p2_fa # Ptr |-> p_fa).
        cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
        cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
        cancel (&(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro).
        cancel (store_tree p_bro t).
        apply (IHpt1 p2_fa p2_mid p2_root pt2).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * dump_pre_spatial.
        exact H1.
Qed.

Theorem store_pt_app:
  forall p2 p2_mid p2_root pt1 pt2,
    store_pt p2 p2_mid pt1 **
    store_pt p2_mid p2_root pt2 |--
    store_pt p2 p2_root (pt1 ++ pt2).
Proof.
  intros p2 p2_mid p2_root pt1.
  revert p2 p2_mid p2_root.
  induction pt1; intros p2 p2_mid p2_root pt2.
  - simpl.
    Intros_p Hp.
    subst p2_mid.
    cancel.
  - destruct a.
    + simpl.
      Intros p_fa.
      Intros p_bro.
      Exists p_fa.
      Exists p_bro.
      repeat (split_pure_spatial || split_pures).
      * cancel (&(p_fa # "tree" ->ₛ "left") # Ptr |-> p2).
        cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
        cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
        cancel (&(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro).
        cancel (store_tree p_bro t).
        apply (IHpt1 p_fa p2_mid p2_root pt2).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
    + simpl.
      Intros p_fa.
      Intros p_bro.
      Exists p_fa.
      Exists p_bro.
      repeat (split_pure_spatial || split_pures).
      * cancel (&(p_fa # "tree" ->ₛ "right") # Ptr |-> p2).
        cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
        cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
        cancel (&(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro).
        cancel (store_tree p_bro t).
        apply (IHpt1 p_fa p2_mid p2_root pt2).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
Qed.

Theorem store_tree_zero:
  forall p tr,
    p = 0 -> store_tree p tr |-- “ tr = empty ” && emp.
Proof.
  intros p tr Hp.
  destruct tr.
  - simpl.
    subst p.
    split_pure_spatial.
    + Intros_p Hnull.
      cancel.
    + dump_pre_spatial.
      reflexivity.
  - simpl.
    subst p.
    Intros pl.
    Intros pr.
    contradiction.
Qed.

Theorem store_tree_not_zero:
  forall p tr,
    p <> 0 ->
    store_tree p tr |--
    EX l0 k v r0 pl pr,
      “ tr = make_tree l0 k v r0 ” &&
      “ INT_MIN <= k <= INT_MAX ” &&
      “ p <> NULL ” &&
      “ INT_MIN <= k <= INT_MAX ” &&
      &(p # "tree" ->ₛ "key") # Int |-> k **
      &(p # "tree" ->ₛ "value") # Int |-> v **
      &(p # "tree" ->ₛ "left") # Ptr |-> pl **
      &(p # "tree" ->ₛ "right") # Ptr |-> pr **
      store_tree pl l0 **
      store_tree pr r0.
Proof.
  intros p tr Hp.
  destruct tr.
  - simpl.
    Intros_p Hnull.
    contradiction.
  - simpl.
    Intros pl.
    Intros pr.
    Exists tr1.
    Exists k.
    Exists v.
    Exists tr2.
    Exists pl.
    Exists pr.
    repeat (split_pure_spatial || split_pures).
    + cancel (&(p # "tree" ->ₛ "key") # Int |-> k).
      cancel (&(p # "tree" ->ₛ "value") # Int |-> v).
      cancel (&(p # "tree" ->ₛ "left") # Ptr |-> pl).
      cancel (&(p # "tree" ->ₛ "right") # Ptr |-> pr).
      cancel (store_tree pl tr1).
      cancel (store_tree pr tr2).
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact H0.
    + dump_pre_spatial.
      exact H.
    + dump_pre_spatial.
      exact H0.
Qed.

Theorem store_tree_size_1:
  forall p k v,
    p <> 0 ->
    INT_MIN <= k <= INT_MAX ->
    &(p # "tree" ->ₛ "key") # Int |-> k **
    &(p # "tree" ->ₛ "value") # Int |-> v **
    &(p # "tree" ->ₛ "left") # Ptr |-> 0 **
    &(p # "tree" ->ₛ "right") # Ptr |-> 0
    |-- store_tree p (make_tree empty k v empty).
Proof.
  intros p k v Hp Hk.
  simpl.
  Exists 0.
  Exists 0.
  repeat (split_pure_spatial || split_pures).
  - cancel (&(p # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p # "tree" ->ₛ "left") # Ptr |-> 0).
    cancel (&(p # "tree" ->ₛ "right") # Ptr |-> 0).
  - dump_pre_spatial.
    exact Hp.
  - dump_pre_spatial.
    exact Hk.
  - dump_pre_spatial.
    reflexivity.
  - dump_pre_spatial.
    reflexivity.
Qed.

Theorem store_tree_make_tree:
  forall p k v pl pr l0 r0,
    p <> 0 ->
    INT_MIN <= k <= INT_MAX ->
    &(p # "tree" ->ₛ "key") # Int |-> k **
    &(p # "tree" ->ₛ "value") # Int |-> v **
    &(p # "tree" ->ₛ "left") # Ptr |-> pl **
    &(p # "tree" ->ₛ "right") # Ptr |-> pr **
    store_tree pl l0 **
    store_tree pr r0
    |-- store_tree p (make_tree l0 k v r0).
Proof.
  intros p k v pl pr l0 r0 Hp Hk.
  simpl.
  Exists pl.
  Exists pr.
  repeat (split_pure_spatial || split_pures).
  - cancel (&(p # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (&(p # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pl l0).
    cancel (store_tree pr r0).
  - dump_pre_spatial.
    exact Hp.
  - dump_pre_spatial.
    exact Hk.
Qed.

Theorem store_ptb_store_tree:
  forall p2_root p2 p pt tr,
    store_ptb p2 p2_root pt **
    p2 # Ptr |-> p **
    store_tree p tr
    |-- EX p_root,
          p2_root # Ptr |-> p_root **
          store_tree p_root (combine_tree pt tr).
Proof.
  intros p2_root p2 p pt tr.
  revert p2_root p2 p tr.
  induction pt; intros p2_root p2 p tr.
  - simpl.
    Intros_p Hp2.
    subst p2_root.
    Exists p.
    cancel.
  - destruct a.
    + simpl.
      Intros p_fa.
      Intros p2_fa.
      Intros p_bro.
      subst p2.
      sep_apply_l_atomic (store_tree_make_tree p_fa k v p p_bro tr t).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * sep_apply (IHpt p2_root p2_fa p_fa (make_tree tr k v t)).
        Intros p_root.
        Exists p_root.
        cancel.
    + simpl.
      Intros p_fa.
      Intros p2_fa.
      Intros p_bro.
      subst p2.
      sep_apply_l_atomic (store_tree_make_tree p_fa k v p_bro p t tr).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * sep_apply (IHpt p2_root p2_fa p_fa (make_tree t k v tr)).
        Intros p_root.
        Exists p_root.
        cancel.
Qed.

Theorem combine_tree_pt_assoc:
  forall pt_1 pt_2 tr,
    combine_tree pt_1 (combine_tree pt_2 tr) = 
      combine_tree (pt_2 ++ pt_1) tr.
Proof.
  intros.
  revert tr.
  induction pt_2.
  + simpl. tauto.
  + simpl. 
    destruct a.
    - intros.
      pose proof IHpt_2 (make_tree tr k v t).
      apply H.
    - intros.
      pose proof IHpt_2 (make_tree t k v tr).
      apply H.
Qed.


Theorem store_combine:
  forall p1 p2 pt tr,
    store_tree p2 tr ** 
    store_pt p2 p1 pt |--
    store_tree p1 (combine_tree pt tr).
Proof.
  intros p1 p2 pt tr.
  revert p1 p2 tr.
  induction pt; intros p1 p2 tr.
  - simpl.
    Intros_p Hp.
    subst p1.
    cancel.
  - destruct a.
    + simpl.
      Intros p_fa.
      Intros p_bro.
      sep_apply_l_atomic (store_tree_make_tree p_fa k v p2 p_bro tr t).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * apply (IHpt p1 p_fa (make_tree tr k v t)).
    + simpl.
      Intros p_fa.
      Intros p_bro.
      sep_apply_l_atomic (store_tree_make_tree p_fa k v p_bro p2 t tr).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * apply (IHpt p1 p_fa (make_tree t k v tr)).
Qed.