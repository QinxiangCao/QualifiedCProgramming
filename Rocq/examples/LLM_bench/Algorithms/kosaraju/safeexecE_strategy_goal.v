Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition safeexecE_strategy1 :=
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

Module Type safeexecE_Strategy_Correct.

  Axiom safeexecE_strategy1_correctness : safeexecE_strategy1.

End safeexecE_Strategy_Correct.
