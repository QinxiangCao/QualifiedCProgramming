Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Require Import SimpleC.EE.QCP_demos_LLM.sll_queue_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sll_queue_strategy0 :=
  forall (p : Z) (l0 : (@list Z)),
    TT &&
    emp **
    ((store_queue p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_queue p l1))
      ).

Definition sll_queue_strategy1 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l1 : (@list Z)) (l2 : (@list Z)) (x2 : Z) (x1 : Z),
    TT &&
    (“ (x1 = x2) ”) &&
    (“ (l1 = l2) ”) &&
    emp -*
    TT &&
    (“ ((@cons Z x1 l1) = (@cons Z x2 l2)) ”) &&
    emp
    ).

Module Type sll_queue_Strategy_Correct.

  Axiom sll_queue_strategy0_correctness : sll_queue_strategy0.
  Axiom sll_queue_strategy1_correctness : sll_queue_strategy1.

End sll_queue_Strategy_Correct.
