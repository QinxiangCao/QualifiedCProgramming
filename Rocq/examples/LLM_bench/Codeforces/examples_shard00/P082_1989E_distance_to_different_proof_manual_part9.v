From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib.
Local Open Scope sac.

(* Part 9: one expensive safety subproof. *)

Lemma proof_of_solver_safety_wit_41_split_goal_1 : solver_safety_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH34 as [[[Hdl [Hpl [Hrange _]]] _] _].
  assert (Hidx_pref_left :
    0 <= (i - 1) * W + (j - 1) < Zlength dl) by (rewrite Hdl; lia).
  assert (Hidx_dp_left :
    0 <= (i - 2) * W + (j - 1) < Zlength dl) by (rewrite Hdl; lia).
  assert (Hidx_pref_right :
    0 <= (i - 1) * W + k_pre < Zlength dl) by (rewrite Hdl; lia).
  assert (Hidx_dp_right :
    0 <= (i - 2) * W + k_pre < Zlength dl) by (rewrite Hdl; lia).
  pose proof (Hrange _ Hidx_pref_left) as [_ Hpref_left].
  pose proof (Hrange _ Hidx_dp_left) as [Hdp_left _].
  pose proof (Hrange _ Hidx_pref_right) as [_ Hpref_right].
  pose proof (Hrange _ Hidx_dp_right) as [Hdp_right _].
  unfold P082Modulus in *.
  dump_pre_spatial.
  lia.
Qed.
