From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib.
Local Open Scope sac.

(* Part 6: one expensive safety subproof. *)

Lemma proof_of_solver_safety_wit_31_split_goal_2 : solver_safety_wit_31_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold P082ColumnProgress in PreH29.
  destruct PreH29 as [Hcols _].
  unfold P082ColumnsState in Hcols.
  destruct Hcols as [Hbase _].
  unfold P082BaseColumns in Hbase.
  destruct Hbase as [Hlen_dp [Hlen_pref [Hrange _]]].
  assert (Hidx1 : 0 <= (i - 1) * W + (j - 1) < Zlength dl) by nia.
  assert (Hidx2 : 0 <= (i - 2) * W + (j - 1) < Zlength dl) by nia.
  assert (Hidx3 : 0 <= (i - 1) * W + k_pre < Zlength dl) by nia.
  pose proof (Hrange ((i - 1) * W + (j - 1)) Hidx1) as Hr1.
  pose proof (Hrange ((i - 2) * W + (j - 1)) Hidx2) as Hr2.
  pose proof (Hrange ((i - 1) * W + k_pre) Hidx3) as Hr3.
  destruct Hr1 as [_ Hp1].
  destruct Hr2 as [Hd2 _].
  destruct Hr3 as [_ Hp3].
  unfold P082Modulus in *.
  dump_pre_spatial.
  lia.
Qed.
