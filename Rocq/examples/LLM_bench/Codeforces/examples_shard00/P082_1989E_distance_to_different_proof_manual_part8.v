From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib.
Local Open Scope sac.

(* Part 8: one expensive safety subproof. *)

Lemma proof_of_solver_safety_wit_34_split_goal_2 : solver_safety_wit_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH25 as [[[Hdl [Hpl [Hrange _]]] _] _].
  assert (Hidx_left :
    0 <= (i - 1) * W + (j - 1) < Zlength dl) by (rewrite Hdl; lia).
  assert (Hidx_right :
    0 <= (i - 1) * W + k_pre < Zlength dl) by (rewrite Hdl; lia).
  pose proof (Hrange _ Hidx_left) as [_ Hleft].
  pose proof (Hrange _ Hidx_right) as [_ Hright].
  unfold P082Modulus in *.
  dump_pre_spatial.
  lia.
Qed.
