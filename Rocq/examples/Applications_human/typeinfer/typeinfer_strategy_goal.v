Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.typeinfer.typeinfer_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition typeinfer_strategy0 :=
  forall t (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((poly_store t p x))
    |--
    (
    TT &&
    (“ (x = y) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_store t p y))
    ).

Definition typeinfer_strategy1 :=
  forall (x : Z) (y : Z),
    TT &&
    (“ (x = y) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x = y) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    (“ (x = y) ”) &&
    emp
    ).

Definition typeinfer_strategy2 :=
  forall (x : Z) (y : Z),
    TT &&
    (“ (Z.lt x y) ”) &&
    emp
    |--
    (
    TT &&
    (“ (Z.lt x y) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    (“ (Z.lt x y) ”) &&
    emp
    ).

Definition typeinfer_strategy3 :=
  forall (x : Z) (y : Z),
    TT &&
    (“ (Z.le x y) ”) &&
    emp
    |--
    (
    TT &&
    (“ (Z.le x y) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    (“ (Z.le x y) ”) &&
    emp
    ).

Definition typeinfer_strategy4 :=
  forall (x : Z) (y : Z),
    TT &&
    (“ (x <> y) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x <> y) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    (“ (x <> y) ”) &&
    emp
    ).

Definition typeinfer_strategy5 :=
  forall (x : Z) (y : Z),
    TT &&
    (“ (x = y) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x = y) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    (“ (y = x) ”) &&
    emp
    ).

Definition typeinfer_strategy6 :=
  forall t (y : Z) (x : Z) (p : Z),
    TT &&
    (“ (y = x) ”) &&
    emp **
    ((poly_store t p x))
    |--
    (
    TT &&
    (“ (y = x) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_store t p y))
    ).

Definition typeinfer_strategy10 :=
  forall (p : Z) (x : sol),
    TT &&
    emp **
    ((store_solution p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : sol),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_solution p y))
      ).

Definition typeinfer_strategy11 :=
  forall (p : Z) (n : Z) (t : (@option TypeTree)) (x : Z) (s : sol),
    TT &&
    emp **
    ((store_solution_aux p s n x t))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (o : (@option TypeTree)),
      TT &&
      (“ (t = o) ”) &&
      emp -*
      TT &&
      emp **
      ((store_solution_aux p s n x o))
      ).

Definition typeinfer_strategy12 :=
  forall (n : Z) (t : TypeTree) (s : sol),
    TT &&
    (“ (solution_at s n t) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (x : TypeTree),
      TT &&
      (“ (t = x) ”) &&
      emp -*
      TT &&
      (“ (solution_at s n x) ”) &&
      emp
      ).

Definition typeinfer_strategy13 :=
  forall (p : Z) (x : TypeTree),
    TT &&
    emp **
    ((store_type p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : TypeTree),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_type p y))
      ).

Definition typeinfer_strategy14 :=
  forall (x : TypeTree) (y : TypeTree) (s : sol),
    TT &&
    (“ (repr_rel_node s x y) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (z : TypeTree),
      TT &&
      (“ (x = z) ”) &&
      emp -*
      TT &&
      (“ (repr_rel_node s z y) ”) &&
      emp
      ).

Definition typeinfer_strategy15 :=
  forall (x : Z) (z : Z) (p : Z) (n : Z) (t : (@option TypeTree)) (s : sol),
    TT &&
    (“ (x = z) ”) &&
    emp **
    ((store_solution_aux p s n x t))
    |--
    (
    TT &&
    (“ (x = z) ”) &&
    emp
    ) ** (
    ALL (w : (@option TypeTree)),
      TT &&
      (“ (t = w) ”) &&
      emp -*
      TT &&
      emp **
      ((store_solution_aux p s n z w))
      ).

Definition typeinfer_strategy16 :=
  forall (x : TypeTree) (y : TypeTree) (s : sol),
    TT &&
    (“ (repr_rel_node s x y) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (w : TypeTree) (z : TypeTree),
      TT &&
      (“ (x = z) ”) &&
      (“ (y = w) ”) &&
      emp -*
      TT &&
      (“ (repr_rel_node s z w) ”) &&
      emp
      ).

Definition typeinfer_strategy20 :=
  forall (p : Z) (x : TypeTree),
    TT &&
    emp **
    ((store_type p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_type p x))
    ).

Definition typeinfer_strategy21 :=
  forall (x : Z) (z : Z) (p : Z) (y : TypeTree),
    TT &&
    (“ (x = z) ”) &&
    emp **
    ((store_type_aux p x y))
    |--
    (
    TT &&
    (“ (x = z) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_type_aux p z y))
    ).

Definition typeinfer_strategy22 :=
  forall (p : Z) (y : TypeTree) (x : Z),
    TT &&
    emp **
    ((store_type_aux p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_type_aux p x y))
    ).

Definition typeinfer_strategy23 :=
  forall (p : Z) (x : sol),
    TT &&
    emp **
    ((store_solution p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_solution p x))
    ).

Definition typeinfer_strategy24 :=
  forall (z : Z) (x : Z) (p : Z) (y : TypeTree),
    TT &&
    (“ (z = x) ”) &&
    emp **
    ((store_type_aux p x y))
    |--
    (
    TT &&
    (“ (z = x) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_type_aux p z y))
    ).

Module Type typeinfer_Strategy_Correct.

  Axiom typeinfer_strategy0_correctness : typeinfer_strategy0.
  Axiom typeinfer_strategy1_correctness : typeinfer_strategy1.
  Axiom typeinfer_strategy2_correctness : typeinfer_strategy2.
  Axiom typeinfer_strategy3_correctness : typeinfer_strategy3.
  Axiom typeinfer_strategy4_correctness : typeinfer_strategy4.
  Axiom typeinfer_strategy5_correctness : typeinfer_strategy5.
  Axiom typeinfer_strategy6_correctness : typeinfer_strategy6.
  Axiom typeinfer_strategy10_correctness : typeinfer_strategy10.
  Axiom typeinfer_strategy11_correctness : typeinfer_strategy11.
  Axiom typeinfer_strategy12_correctness : typeinfer_strategy12.
  Axiom typeinfer_strategy13_correctness : typeinfer_strategy13.
  Axiom typeinfer_strategy14_correctness : typeinfer_strategy14.
  Axiom typeinfer_strategy15_correctness : typeinfer_strategy15.
  Axiom typeinfer_strategy16_correctness : typeinfer_strategy16.
  Axiom typeinfer_strategy20_correctness : typeinfer_strategy20.
  Axiom typeinfer_strategy21_correctness : typeinfer_strategy21.
  Axiom typeinfer_strategy22_correctness : typeinfer_strategy22.
  Axiom typeinfer_strategy23_correctness : typeinfer_strategy23.
  Axiom typeinfer_strategy24_correctness : typeinfer_strategy24.

End typeinfer_Strategy_Correct.
