From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib.
Local Open Scope sac.

(* Part 2: one expensive safety subproof. *)

Lemma proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold P082InitState in PreH17.
  destruct PreH17 as [Hlen_dp [Hlen_pref [Hrange _]]].
  assert (Hidx : 0 <= (i - 1) * W + 1 < Zlength dl) by nia.
  specialize (Hrange ((i - 1) * W + 1) Hidx).
  destruct Hrange as [_ Hpref].
  dump_pre_spatial.
  lia.
Qed.
