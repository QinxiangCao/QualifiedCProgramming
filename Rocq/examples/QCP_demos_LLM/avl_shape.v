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
  | make_tree : tree -> tree -> tree.

(* Definition valid_height (h hl hr: Z): Prop :=
    h = Z.max hl hr + 1. *)

Fixpoint store_tree (p: addr) (tr: tree): Assertion :=
    match tr with
    | empty =>
        “ p = NULL ” && emp
    | make_tree l r =>
        EX pl pr k v h,
            “ p <> NULL ” &&
            &(p # "tree" ->ₛ "key") # Int |-> k **
            &(p # "tree" ->ₛ "value") # Int |-> v **
            &(p # "tree" ->ₛ "height") # UChar |-> h **
            &(p # "tree" ->ₛ "lchild") # Ptr |-> pl **
            &(p # "tree" ->ₛ "rchild") # Ptr |-> pr **
            store_tree pl l **
            store_tree pr r
    end.

Definition store_tree_shape (p:addr): Assertion :=
    EX tr, store_tree p tr.

Definition store_non_empty_tree (p: addr): Assertion :=
    “ p <> NULL ” && store_tree_shape p.

Definition single_tree_node (p: addr) (k: key) (v: value) (h: Z) (l r: addr): Assertion :=
    &(p # "tree" ->ₛ "key") # Int |-> k **
    &(p # "tree" ->ₛ "value") # Int |-> v **
    &(p # "tree" ->ₛ "height") # UChar |-> h **
    &(p # "tree" ->ₛ "lchild") # Ptr |-> l **
    &(p # "tree" ->ₛ "rchild") # Ptr |-> r.

