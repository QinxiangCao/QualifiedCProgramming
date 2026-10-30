From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
From SimpleC.Verification Require Import SafeExecPrelude.
Local Open Scope sac.

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
