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

Theorem tree_insert_same_def:
  forall x v,
    tree_insert x v = BinTreeTheorems.insert (x, v).
Proof. intros. reflexivity. Qed.

Definition map_insert := Map.insert.

Section Delete.

Fixpoint min_key (n: key) (t: tree) : key :=
  match t with
  | empty => n
  | make_tree a x v b =>
      match a with 
      | empty => x
      | make_tree _ _ _ _ => min_key n a
      end
  end.

Fixpoint min_value (n: value) (t: tree) : value :=
  match t with
  | empty => n
  | make_tree a x v b =>
      match a with 
      | empty => v
      | make_tree _ _ _ _ => min_value n a
      end
  end.

Fixpoint delete_min (t: tree) : tree :=
  match t with
  | empty => empty
  | make_tree a x v b =>
      match a with
      | empty => b
      | make_tree _ _ _ _ => make_tree (delete_min a) x v b
      end
  end.

Fixpoint tree_delete (x: key) (t: tree) : tree :=
  match t with
  | empty => empty
  | make_tree a y v b =>
      match Key.dec x y with
      | LT => make_tree (tree_delete x a) y v b
      | EQ =>
          match b with
          | empty => a
          | make_tree _ _ _ _ =>
              match a with
              | empty => b
              | make_tree _ _ _ _ => make_tree a (min_key y b) (min_value v b) (delete_min b)
              end
          end
      | GT => make_tree a y v (tree_delete x b)
      end
  end.

End Delete.

Theorem delete_min_same_def:
  forall tr,
    delete_min tr = BinTreeTheorems.delete_min tr.
Proof.
  refine (BinTree.t_ind _ _ _); intros.
  reflexivity.
  revert n r H0.
  revert l H.
  refine (BinTree.t_ind _ _ _); intros.
  reflexivity.
  rewrite BinTreeTheorems.delete_min_make_tree.
  rewrite <-H1.
  reflexivity.
Qed.

Theorem min_node_same_def:
  forall tr n,
    ((min_key (fst n) tr), (min_value (snd n) tr)) = BinTreeTheorems.min_node (fst n, snd n) tr.
Proof.
  refine (BinTree.t_ind _ _ _); intros.
  reflexivity.
  revert l H.
  refine (BinTree.t_ind _ _ _); intros.
  reflexivity.
  rewrite BinTreeTheorems.min_node_make_tree.
  rewrite <-H2.
  reflexivity.
Qed.

Theorem tree_delete_same_def:
  forall x tr,
    tree_delete x tr = BinTreeTheorems.swap_delete x tr.
Proof.
  intros.
  revert tr.
  refine (BinTree.t_ind _ _ _); intros.
  reflexivity.
  simpl.
  destruct (Key.dec x (fst n)).
  destruct s.
  + rewrite H.
    reflexivity.
  + rewrite H0.
    reflexivity.
  + rewrite <-min_node_same_def.
    rewrite <-delete_min_same_def.
    revert r H0.
    refine (BinTree.t_ind _ _ _); intros.
    reflexivity.
    revert l H H0 H1.
    refine (BinTree.t_ind _ _ _); intros; reflexivity.
Qed.

Definition map_delete := Map.delete.

Fixpoint store_tree (p p_fa: addr) (tr: tree): Assertion :=
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
        &(p # "tree" ->ₛ "father") # Ptr |-> p_fa **
        store_tree pl p tr_l **
        store_tree pr p tr_r
  end.

Fixpoint store_ptb
           (p2 p2_root p_fa p_root_fa: addr)
           (pt: partial_tree): Assertion :=
  match pt with
  | nil =>
      “ p2 = p2_root ” && “ p_fa = p_root_fa ” && emp
  | LH k v tr :: pt' =>
      EX p2_fa p_bro p_gfa,
        “ p_fa <> NULL ” &&
        “ INT_MIN <= k <= INT_MAX ” &&
        “ &(p_fa # "tree" ->ₛ "left") = p2 ” &&
        p2_fa # Ptr |-> p_fa **
        &(p_fa # "tree" ->ₛ "key") # Int |-> k **
        &(p_fa # "tree" ->ₛ "value") # Int |-> v **
        &(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro **
        &(p_fa # "tree" ->ₛ "father") # Ptr |-> p_gfa **
        store_tree p_bro p_fa tr **
        store_ptb p2_fa p2_root p_gfa p_root_fa pt'
  | RH k v tr :: pt' =>
      EX p2_fa p_bro p_gfa,
        “ p_fa <> NULL ” &&
        “ INT_MIN <= k <= INT_MAX ” &&
        “ &(p_fa # "tree" ->ₛ "right") = p2 ” &&
        p2_fa # Ptr |-> p_fa **
        &(p_fa # "tree" ->ₛ "key") # Int |-> k **
        &(p_fa # "tree" ->ₛ "value") # Int |-> v **
        &(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro **
        &(p_fa # "tree" ->ₛ "father") # Ptr |-> p_gfa **
        store_tree p_bro p_fa tr **
        store_ptb p2_fa p2_root p_gfa p_root_fa pt'
  end.

Module Bst.

Definition store_map (p: addr) (m: mapping): Assertion :=
  EX tr: tree,
    “ SearchTree tr ” && “ Abs tr m ” && store_tree p 0 tr.

End Bst.

Import Bst.

Theorem insert_SearchTree: forall tr k v,
  SearchTree tr ->
  SearchTree (tree_insert k v tr).
Proof. intros. exact (insert_SearchTree tr (k, v) H). Qed.

Theorem insert_Abs: forall tr m k v,
  SearchTree tr ->
  Abs tr m ->
  Abs (tree_insert k v tr) (map_insert k v m).
Proof. intros. exact (insert_Abs tr m (k, v) H H0). Qed.

Theorem delete_SearchTree: forall tr k,
  SearchTree tr ->
  SearchTree (tree_delete k tr).
Proof. intros. rewrite tree_delete_same_def. exact (swap_delete_SearchTree tr k H). Qed.

Theorem delete_Abs: forall tr m k,
  SearchTree tr ->
  Abs tr m ->
  Abs (tree_delete k tr) (map_delete k m).
Proof. intros. rewrite tree_delete_same_def. exact (swap_delete_Abs tr m k H H0). Qed.

Theorem store_ptb_LH:
  forall p2_fa p_fa p_bro p_gfa k v tr,
    p_fa <> NULL ->
    INT_MIN <= k <= INT_MAX ->
    p2_fa # Ptr |-> p_fa **
    &(p_fa # "tree" ->ₛ "key") # Int |-> k **
    &(p_fa # "tree" ->ₛ "value") # Int |-> v **
    &(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro **
    &(p_fa # "tree" ->ₛ "father") # Ptr |-> p_gfa **
    store_tree p_bro p_fa tr |--
    store_ptb (&(p_fa # "tree" ->ₛ "left")) p2_fa p_fa p_gfa
      (LH k v tr :: nil).
Proof.
  intros p2_fa p_fa p_bro p_gfa k v tr Hfa Hk.
  simpl.
  Exists p2_fa.
  Exists p_bro.
  Exists p_gfa.
  repeat (split_pure_spatial || split_pures).
  - cancel (p2_fa # Ptr |-> p_fa).
    cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro).
    cancel (&(p_fa # "tree" ->ₛ "father") # Ptr |-> p_gfa).
    cancel (store_tree p_bro p_fa tr).
  - dump_pre_spatial.
    exact Hfa.
  - dump_pre_spatial.
    exact Hk.
  - dump_pre_spatial.
    reflexivity.
  - dump_pre_spatial.
    reflexivity.
  - dump_pre_spatial.
    reflexivity.
Qed.

Theorem store_ptb_RH:
  forall p2_fa p_fa p_bro p_gfa k v tr,
    p_fa <> NULL ->
    INT_MIN <= k <= INT_MAX ->
    p2_fa # Ptr |-> p_fa **
    &(p_fa # "tree" ->ₛ "key") # Int |-> k **
    &(p_fa # "tree" ->ₛ "value") # Int |-> v **
    &(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro **
    &(p_fa # "tree" ->ₛ "father") # Ptr |-> p_gfa **
    store_tree p_bro p_fa tr |--
    store_ptb (&(p_fa # "tree" ->ₛ "right")) p2_fa p_fa p_gfa
      (RH k v tr :: nil).
Proof.
  intros p2_fa p_fa p_bro p_gfa k v tr Hfa Hk.
  simpl.
  Exists p2_fa.
  Exists p_bro.
  Exists p_gfa.
  repeat (split_pure_spatial || split_pures).
  - cancel (p2_fa # Ptr |-> p_fa).
    cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro).
    cancel (&(p_fa # "tree" ->ₛ "father") # Ptr |-> p_gfa).
    cancel (store_tree p_bro p_fa tr).
  - dump_pre_spatial.
    exact Hfa.
  - dump_pre_spatial.
    exact Hk.
  - dump_pre_spatial.
    reflexivity.
  - dump_pre_spatial.
    reflexivity.
  - dump_pre_spatial.
    reflexivity.
Qed.

Theorem store_ptb_app:
  forall p2 p2_mid p2_root p_fa p_mid_fa p_root_fa pt1 pt2,
    store_ptb p2 p2_mid p_fa p_mid_fa pt1 **
    store_ptb p2_mid p2_root p_mid_fa p_root_fa pt2 |--
    store_ptb p2 p2_root p_fa p_root_fa (pt1 ++ pt2).
Proof.
  intros p2 p2_mid p2_root p_fa p_mid_fa p_root_fa pt1.
  revert p2 p2_mid p2_root p_fa p_mid_fa p_root_fa.
  induction pt1; intros p2 p2_mid p2_root p_fa p_mid_fa p_root_fa pt2.
  - simpl.
    Intros_p Hp2.
    Intros_p Hfa.
    subst p2_mid.
    subst p_mid_fa.
    cancel.
  - destruct a.
    + simpl.
      Intros p2_fa.
      Intros p_bro.
      Intros p_gfa.
      Exists p2_fa.
      Exists p_bro.
      Exists p_gfa.
      repeat (split_pure_spatial || split_pures).
      * cancel (p2_fa # Ptr |-> p_fa).
        cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
        cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
        cancel (&(p_fa # "tree" ->ₛ "right") # Ptr |-> p_bro).
        cancel (&(p_fa # "tree" ->ₛ "father") # Ptr |-> p_gfa).
        cancel (store_tree p_bro p_fa t).
        apply (IHpt1 p2_fa p2_mid p2_root p_gfa p_mid_fa p_root_fa pt2).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * dump_pre_spatial.
        exact H1.
    + simpl.
      Intros p2_fa.
      Intros p_bro.
      Intros p_gfa.
      Exists p2_fa.
      Exists p_bro.
      Exists p_gfa.
      repeat (split_pure_spatial || split_pures).
      * cancel (p2_fa # Ptr |-> p_fa).
        cancel (&(p_fa # "tree" ->ₛ "key") # Int |-> k).
        cancel (&(p_fa # "tree" ->ₛ "value") # Int |-> v).
        cancel (&(p_fa # "tree" ->ₛ "left") # Ptr |-> p_bro).
        cancel (&(p_fa # "tree" ->ₛ "father") # Ptr |-> p_gfa).
        cancel (store_tree p_bro p_fa t).
        apply (IHpt1 p2_fa p2_mid p2_root p_gfa p_mid_fa p_root_fa pt2).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * dump_pre_spatial.
        exact H1.
Qed.

Theorem store_tree_zero:
  forall p p_fa tr,
    p = 0 -> store_tree p p_fa tr |-- “ tr = empty ” && emp.
Proof.
  intros p p_fa tr Hp.
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
  forall p p_fa tr,
    p <> 0 ->
    store_tree p p_fa tr |--
    EX l0 k v r0 pl pr,
      “ tr = make_tree l0 k v r0 ” &&
      “ INT_MIN <= k <= INT_MAX ” &&
      “ p <> NULL ” &&
      “ INT_MIN <= k <= INT_MAX ” &&
      &(p # "tree" ->ₛ "key") # Int |-> k **
      &(p # "tree" ->ₛ "value") # Int |-> v **
      &(p # "tree" ->ₛ "left") # Ptr |-> pl **
      &(p # "tree" ->ₛ "right") # Ptr |-> pr **
      &(p # "tree" ->ₛ "father") # Ptr |-> p_fa **
      store_tree pl p l0 **
      store_tree pr p r0.
Proof.
  intros p p_fa tr Hp.
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
      cancel (&(p # "tree" ->ₛ "father") # Ptr |-> p_fa).
      cancel (store_tree pl p tr1).
      cancel (store_tree pr p tr2).
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
  forall p p_fa k v,
    p <> 0 ->
    INT_MIN <= k <= INT_MAX ->
    &(p # "tree" ->ₛ "key") # Int |-> k **
    &(p # "tree" ->ₛ "value") # Int |-> v **
    &(p # "tree" ->ₛ "left") # Ptr |-> 0 **
    &(p # "tree" ->ₛ "right") # Ptr |-> 0 **
    &(p # "tree" ->ₛ "father") # Ptr |-> p_fa
    |-- store_tree p p_fa (make_tree empty k v empty).
Proof.
  intros p p_fa k v Hp Hk.
  simpl.
  Exists 0.
  Exists 0.
  repeat (split_pure_spatial || split_pures).
  - cancel (&(p # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p # "tree" ->ₛ "left") # Ptr |-> 0).
    cancel (&(p # "tree" ->ₛ "right") # Ptr |-> 0).
    cancel (&(p # "tree" ->ₛ "father") # Ptr |-> p_fa).
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
  forall p k v pl pr p_fa l0 r0,
    p <> 0 ->
    INT_MIN <= k <= INT_MAX ->
    &(p # "tree" ->ₛ "key") # Int |-> k **
    &(p # "tree" ->ₛ "value") # Int |-> v **
    &(p # "tree" ->ₛ "left") # Ptr |-> pl **
    &(p # "tree" ->ₛ "right") # Ptr |-> pr **
    &(p # "tree" ->ₛ "father") # Ptr |-> p_fa **
    store_tree pl p l0 **
    store_tree pr p r0
    |-- store_tree p p_fa (make_tree l0 k v r0).
Proof.
  intros p k v pl pr p_fa l0 r0 Hp Hk.
  simpl.
  Exists pl.
  Exists pr.
  repeat (split_pure_spatial || split_pures).
  - cancel (&(p # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (&(p # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (&(p # "tree" ->ₛ "father") # Ptr |-> p_fa).
    cancel (store_tree pl p l0).
    cancel (store_tree pr p r0).
  - dump_pre_spatial.
    exact Hp.
  - dump_pre_spatial.
    exact Hk.
Qed.

Theorem store_ptb_store_tree:
  forall p2_root p2 p p_fa p_root_fa pt tr,
    store_ptb p2 p2_root p_fa p_root_fa pt **
    p2 # Ptr |-> p **
    store_tree p p_fa tr
    |-- EX p_root,
          p2_root # Ptr |-> p_root **
          store_tree p_root p_root_fa (combine_tree pt tr).
Proof.
  intros p2_root p2 p p_fa p_root_fa pt tr.
  revert p2_root p2 p p_fa p_root_fa tr.
  induction pt; intros p2_root p2 p p_fa p_root_fa tr.
  - simpl.
    Intros_p Hp2.
    Intros_p Hfa.
    subst p2_root.
    subst p_root_fa.
    Exists p.
    cancel.
  - destruct a.
    + simpl.
      Intros p2_fa.
      Intros p_bro.
      Intros p_gfa.
      subst p2.
      sep_apply_l_atomic (store_tree_make_tree p_fa k v p p_bro p_gfa tr t).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * sep_apply (IHpt p2_root p2_fa p_fa p_gfa p_root_fa (make_tree tr k v t)).
        Intros p_root.
        Exists p_root.
        cancel.
    + simpl.
      Intros p2_fa.
      Intros p_bro.
      Intros p_gfa.
      subst p2.
      sep_apply_l_atomic (store_tree_make_tree p_fa k v p_bro p p_gfa t tr).
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
      * sep_apply (IHpt p2_root p2_fa p_fa p_gfa p_root_fa (make_tree t k v tr)).
        Intros p_root.
        Exists p_root.
        cancel.
Qed.
