Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition safeexec_strategy3 :=
  forall (Sigma : Type) (A : Type) (x : (@ StateRelMonad.M  Sigma A)),
    TT &&
    (“ (equiv x x) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition safeexec_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (Sigma : Type) (A : Type) (x : (@ StateRelMonad.M  Sigma A)),
    TT &&
    emp -*
    TT &&
    (“ (equiv x x) ”) &&
    emp
    ).

Definition safeexec_strategy5 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (B : Type) (Sigma : Type) (c22 : (A -> (@ StateRelMonad.M  Sigma B))) (c12 : (A -> (@ StateRelMonad.M  Sigma B))) (c11 : (@ StateRelMonad.M  Sigma A)) (c21 : (@ StateRelMonad.M  Sigma A)),
    TT &&
    (“ (equiv c11 c21) ”) &&
    (“ (equiv c12 c22) ”) &&
    emp -*
    TT &&
    (“ (equiv ( bind c11 c12) ( bind c21 c22)) ”) &&
    emp
    ).

Definition safeexec_strategy8 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l1 : (@list Z)) (l2 : (@list Z)),
    TT &&
    (“ (l1 = l2) ”) &&
    emp -*
    TT &&
    (“ (equiv ( mergesortrec_loc1 l1) ( mergesortrec_loc1 l2)) ”) &&
    emp
    ).

Definition safeexec_strategy9 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l1 : (@list Z)) (l2 : (@list Z)),
    TT &&
    (“ (l1 = l2) ”) &&
    emp -*
    TT &&
    (“ (equiv ( mergesortrec_loc2 l1) ( mergesortrec_loc2 l2)) ”) &&
    emp
    ).

Definition safeexec_strategy6 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (Sigma : Type) (A : Type) (x : (@ StateRelMonad.M  Sigma A)) (y : (@ StateRelMonad.M  Sigma A)),
    TT &&
    (“ (equiv x y) ” || “ (equiv y x) ”) &&
    emp -*
    TT &&
    (“ (equiv x y) ” || “ (equiv y x) ”) &&
    emp
    ).

Definition safeexec_strategy7 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (B : Type) (Sigma : Type) (x : (A -> (@ StateRelMonad.M  Sigma B))) (y : (A -> (@ StateRelMonad.M  Sigma B))),
    TT &&
    (“ (equiv x y) ” || “ (equiv y x) ”) &&
    emp -*
    TT &&
    (“ (equiv x y) ” || “ (equiv y x) ”) &&
    emp
    ).

Definition safeexec_strategy1 :=
  forall (Sigma : Type) (A : Type) (c : (@ StateRelMonad.M  Sigma A)) (X : (A -> (Sigma -> Prop))) (P : (Sigma -> Prop)),
    TT &&
    (“ (safeExec P c X) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (B : Type) (c2 : (@ StateRelMonad.M  Sigma B)) (X2 : (B -> (Sigma -> Prop))) (P2 : (Sigma -> Prop)),
      TT &&
      (“ (safeExec P2 c2 X2) ”) &&
      emp -*
      TT &&
      (“ (safeExec P c X) ”) &&
      (“ (safeExec P2 c2 X2) ”) &&
      emp
      ).

Definition safeexec_strategy2 :=
  forall (Sigma : Type) (A : Type) (c : (@ StateRelMonad.M  Sigma A)) (X : (A -> (Sigma -> Prop))) (P : (Sigma -> Prop)),
    TT &&
    (“ (safeExec P c X) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (c2 : (@ StateRelMonad.M  Sigma A)),
      TT &&
      (“ (equiv c c2) ”) &&
      emp -*
      TT &&
      (“ (safeExec P c2 X) ”) &&
      emp
      ).

Module Type safeexec_Strategy_Correct.

  Axiom safeexec_strategy3_correctness : safeexec_strategy3.
  Axiom safeexec_strategy4_correctness : safeexec_strategy4.
  Axiom safeexec_strategy5_correctness : safeexec_strategy5.
  Axiom safeexec_strategy8_correctness : safeexec_strategy8.
  Axiom safeexec_strategy9_correctness : safeexec_strategy9.
  Axiom safeexec_strategy6_correctness : safeexec_strategy6.
  Axiom safeexec_strategy7_correctness : safeexec_strategy7.
  Axiom safeexec_strategy1_correctness : safeexec_strategy1.
  Axiom safeexec_strategy2_correctness : safeexec_strategy2.

End safeexec_Strategy_Correct.
