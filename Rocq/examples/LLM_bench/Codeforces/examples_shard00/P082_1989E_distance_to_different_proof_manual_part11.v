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

(* Part 11: one expensive safety subproof. *)

Lemma proof_of_solver_safety_wit_45_split_goal_1 : solver_safety_wit_45_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | |- context [Z.rem ?x 998244353] =>
      pose proof (P082_mod_plus_bounds__safety_updates_a x) as Hbounds
  end.
  lia.
Qed.
