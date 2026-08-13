Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

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

Module Type safeexec_Strategy_Correct.

  Axiom safeexec_strategy1_correctness : safeexec_strategy1.

End safeexec_Strategy_Correct.
