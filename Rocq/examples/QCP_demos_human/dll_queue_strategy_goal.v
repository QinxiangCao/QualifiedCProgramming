Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.dll_queue_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition dll_queue_strategy0 :=
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

Definition dll_queue_strategy1 :=
  forall (p : Z) (q : Z) (l0 : (@list Z)) (r : Z),
    TT &&
    emp **
    ((dllseg p 0 q r l0))
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
      ((dllseg p 0 q r l1))
      ).

Module Type dll_queue_Strategy_Correct.

  Axiom dll_queue_strategy0_correctness : dll_queue_strategy0.
  Axiom dll_queue_strategy1_correctness : dll_queue_strategy1.

End dll_queue_Strategy_Correct.
