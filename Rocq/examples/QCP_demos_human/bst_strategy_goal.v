Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.bst_lib.
Import get_right_most.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition bst_strategy0 :=
  forall (p : Z) (tr0 : tree),
    TT &&
    emp **
    ((store_tree p tr0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (tr1 : tree),
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_tree p tr1))
      ).

Definition bst_strategy1 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (pt : partial_tree) (q : Z) (p : Z),
    TT &&
    (“ (pt = ( empty_partial_tree)) ”) &&
    emp **
    ((poly_store FET_ptr p q)) -*
    TT &&
    emp **
    ((store_ptb p p pt)) **
    ((poly_store FET_ptr p q))
    ).

Definition bst_strategy2 :=
  forall (p : Z) (tr0 : partial_tree) (rt : Z),
    TT &&
    emp **
    ((store_ptb p rt tr0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (tr1 : partial_tree),
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_ptb p rt tr1))
      ).

Definition bst_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (pt : partial_tree) (q : Z) (p : Z),
    TT &&
    (“ (pt = ( empty_partial_tree)) ”) &&
    emp **
    ((poly_store FET_ptr p q)) -*
    TT &&
    emp **
    ((store_pt p p pt)) **
    ((poly_store FET_ptr p q))
    ).

Definition bst_strategy5 :=
  forall (p : Z) (tr0 : partial_tree) (rt : Z),
    TT &&
    emp **
    ((store_pt p rt tr0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (tr1 : partial_tree),
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_pt p rt tr1))
      ).

Module Type bst_Strategy_Correct.

  Axiom bst_strategy0_correctness : bst_strategy0.
  Axiom bst_strategy1_correctness : bst_strategy1.
  Axiom bst_strategy2_correctness : bst_strategy2.
  Axiom bst_strategy4_correctness : bst_strategy4.
  Axiom bst_strategy5_correctness : bst_strategy5.

End bst_Strategy_Correct.
