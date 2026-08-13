Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition safeexec_fme_gmp_strategy3 :=
  forall (Sigma : Type) (A : Type) (x : (@ MonadErr.M  Sigma A)),
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

Definition safeexec_fme_gmp_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (Sigma : Type) (A : Type) (x : (@ MonadErr.M  Sigma A)),
    TT &&
    emp -*
    TT &&
    (“ (equiv x x) ”) &&
    emp
    ).

Definition safeexec_fme_gmp_strategy5 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (B : Type) (Sigma : Type) (c22 : (A -> (@ MonadErr.M  Sigma B))) (c12 : (A -> (@ MonadErr.M  Sigma B))) (c11 : (@ MonadErr.M  Sigma A)) (c21 : (@ MonadErr.M  Sigma A)),
    TT &&
    (“ (equiv c11 c21) ”) &&
    (“ (equiv c12 c22) ”) &&
    emp -*
    TT &&
    (“ (equiv ( bind c11 c12) ( bind c21 c22)) ”) &&
    emp
    ).

Definition safeexec_fme_gmp_strategy6 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (Sigma : Type) (A : Type) (x : (@ MonadErr.M  Sigma A)) (y : (@ MonadErr.M  Sigma A)),
    TT &&
    (“ (equiv x y) ” || “ (equiv y x) ”) &&
    emp -*
    TT &&
    (“ (equiv x y) ” || “ (equiv y x) ”) &&
    emp
    ).

Definition safeexec_fme_gmp_strategy7 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (B : Type) (Sigma : Type) (x : (A -> (@ MonadErr.M  Sigma B))) (y : (A -> (@ MonadErr.M  Sigma B))),
    TT &&
    (“ (equiv x y) ” || “ (equiv y x) ”) &&
    emp -*
    TT &&
    (“ (equiv x y) ” || “ (equiv y x) ”) &&
    emp
    ).

Definition safeexec_fme_gmp_strategy1 :=
  forall (Sigma : Type) (A : Type) (c : (@ MonadErr.M  Sigma A)) (X : (A -> (Sigma -> Prop))) (P : (Sigma -> Prop)),
    TT &&
    (“ (safeExec P c X) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (B : Type) (c2 : (@ MonadErr.M  Sigma B)) (X2 : (B -> (Sigma -> Prop))) (P2 : (Sigma -> Prop)),
      TT &&
      (“ (safeExec P2 c2 X2) ”) &&
      emp -*
      TT &&
      (“ (safeExec P c X) ”) &&
      (“ (safeExec P2 c2 X2) ”) &&
      emp
      ).

Definition safeexec_fme_gmp_strategy2 :=
  forall (Sigma : Type) (A : Type) (c : (@ MonadErr.M  Sigma A)) (X : (A -> (Sigma -> Prop))) (P : (Sigma -> Prop)),
    TT &&
    (“ (safeExec P c X) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (c2 : (@ MonadErr.M  Sigma A)),
      TT &&
      (“ (equiv c c2) ”) &&
      emp -*
      TT &&
      (“ (safeExec P c2 X) ”) &&
      emp
      ).

Module Type safeexec_fme_gmp_Strategy_Correct.

  Axiom safeexec_fme_gmp_strategy3_correctness : safeexec_fme_gmp_strategy3.
  Axiom safeexec_fme_gmp_strategy4_correctness : safeexec_fme_gmp_strategy4.
  Axiom safeexec_fme_gmp_strategy5_correctness : safeexec_fme_gmp_strategy5.
  Axiom safeexec_fme_gmp_strategy6_correctness : safeexec_fme_gmp_strategy6.
  Axiom safeexec_fme_gmp_strategy7_correctness : safeexec_fme_gmp_strategy7.
  Axiom safeexec_fme_gmp_strategy1_correctness : safeexec_fme_gmp_strategy1.
  Axiom safeexec_fme_gmp_strategy2_correctness : safeexec_fme_gmp_strategy2.

End safeexec_fme_gmp_Strategy_Correct.
