From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib.
Local Open Scope sac.

(* Part 12: one expensive safety subproof. *)

Lemma proof_of_solver_safety_wit_45_split_goal_2 : solver_safety_wit_45_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | |- context [Z.rem ?x 998244353] =>
      pose proof (P082_mod_plus_bounds__safety_updates_a x) as Hbounds
  end.
  lia.
Qed.
