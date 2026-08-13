Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.eval_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition eval_strategy0 :=
  forall (p : Z) (l0 : expr),
    TT &&
    emp **
    ((store_expr p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : expr),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_expr p l1))
      ).

Definition eval_strategy1 :=
  forall (p : Z) (l0 : expr) (q0 : Z),
    TT &&
    emp **
    ((store_expr_aux p q0 l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : expr) (q1 : Z),
      TT &&
      (“ (q0 = q1) ”) &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_expr_aux p q1 l1))
      ).

Module Type eval_Strategy_Correct.

  Axiom eval_strategy0_correctness : eval_strategy0.
  Axiom eval_strategy1_correctness : eval_strategy1.

End eval_Strategy_Correct.
