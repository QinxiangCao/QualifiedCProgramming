From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.Verification Require Import safeexec_strategy_goal.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.
Local Open Scope string.

Lemma safeexec_strategy1_correctness : safeexec_strategy1.
  pre_process_default.
Qed.
