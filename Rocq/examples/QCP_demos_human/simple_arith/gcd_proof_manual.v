Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_human.simple_arith Require Import gcd_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_gcd_return_wit_2 : gcd_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
  subst.
  rewrite Z.gcd_0_r.
  reflexivity.
Qed.

Lemma proof_of_gcd_return_wit_1 : gcd_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
  subst.
  pose proof Z.gcd_rem x_pre y_pre ltac:(lia).
  rewrite Z.gcd_comm, H, Z.gcd_comm.
  reflexivity.
Qed.

Lemma proof_of_gcd_partial_solve_wit_2_pure : gcd_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range  (&("y")) y_pre).
  Intros.
  change (Int.min_signed) with (-2147483648) in H.
  change (Int.max_signed) with (2147483647) in H.
  pose proof Z.rem_bound_pos_pos x_pre y_pre.
  pose proof Z.rem_bound_neg_pos x_pre y_pre.
  pose proof Z.rem_bound_pos_neg x_pre y_pre.
  pose proof Z.rem_bound_neg_neg x_pre y_pre.
  repeat (split_pure_spatial || split_pures).
  - cancel.
    dump_pre_spatial; lia.
  - dump_pre_spatial; lia.
Qed.
