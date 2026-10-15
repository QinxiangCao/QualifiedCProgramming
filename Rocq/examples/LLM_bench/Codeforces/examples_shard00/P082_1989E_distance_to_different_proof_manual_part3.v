Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib.
Local Open Scope sac.

(* Part 3: one expensive safety subproof. *)

Lemma proof_of_solver_safety_wit_26_split_goal_1 : solver_safety_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P082ColumnProgress in PreH22.
  destruct PreH22 as [Hcols _].
  unfold P082ColumnsState in Hcols.
  destruct Hcols as [Hbase _].
  unfold P082BaseColumns in Hbase.
  destruct Hbase as [Hlen_dp [Hlen_pref [Hrange _]]].
  assert (Hidx1 : 0 <= (i - 1) * W + (j - 1) < Zlength dl) by nia.
  assert (Hidx2 : 0 <= (i - 2) * W + (j - 1) < Zlength dl) by nia.
  pose proof (Hrange ((i - 1) * W + (j - 1)) Hidx1) as Hr1.
  pose proof (Hrange ((i - 2) * W + (j - 1)) Hidx2) as Hr2.
  destruct Hr1 as [_ Hp1].
  destruct Hr2 as [Hd2 _].
  unfold P082Modulus in *.
  dump_pre_spatial.
  lia.
Qed.
