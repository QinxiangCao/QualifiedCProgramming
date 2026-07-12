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
From SimpleC.EE.QCP_demos_tutorial Require Import branch_join_private_condition_goal.
From SimpleC.EE.QCP_demos_tutorial Require Import branch_join_private_condition_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.branch_join_private_condition_lib.
Local Open Scope sac.

Lemma proof_of_f_entail_wit_1_1 : f_entail_wit_1_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - dump_pre_spatial.
    unfold step.
    assert (Z.even x_pre = true) as Heven.
    {
      replace x_pre with (2 * (Z.quot x_pre 2)).
      - rewrite Z.even_even.
        reflexivity.
      - pose proof (Z.quot_rem x_pre 2 ltac:(lia)) as Hdiv.
        lia.
    }
    rewrite Heven.
    rewrite Z.quot_div_nonneg by lia.
    reflexivity.
Qed.

Lemma proof_of_f_entail_wit_1_2 : f_entail_wit_1_2.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - dump_pre_spatial.
    unfold step.
    assert (Z.rem x_pre 2 = 1) as Hmod.
    {
      pose proof (Z.rem_bound_pos_pos x_pre 2 ltac:(lia) ltac:(lia)) as Hbound.
      lia.
    }
    assert (Z.even x_pre = false) as Hodd.
    {
      replace x_pre with (2 * (Z.quot x_pre 2) + 1).
      - rewrite Z.even_odd.
        reflexivity.
      - pose proof (Z.quot_rem x_pre 2 ltac:(lia)) as Hdiv.
        lia.
    }
    rewrite Hodd.
    reflexivity.
Qed.

