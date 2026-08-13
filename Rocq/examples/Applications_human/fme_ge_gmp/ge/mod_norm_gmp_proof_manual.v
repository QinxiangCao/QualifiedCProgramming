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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import mod_norm_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import mod_norm_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_mod_norm_gmp_entail_wit_1_1 : mod_norm_gmp_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Left.
  Exists rv_2.
  Exists qv_2.
  split_pure_spatial.
  - cancel (store_Z r_pre rv_2).
    cancel (store_Z x_pre zx_low_level_spec).
    cancel (store_Z p_pre zp_low_level_spec).
  - repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mod_norm_gmp_entail_wit_1_2 : mod_norm_gmp_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Right.
  Exists rv_2.
  Exists qv_2.
  split_pure_spatial.
  - cancel (store_Z r_pre rv_2).
    cancel (store_Z x_pre zx_low_level_spec).
    cancel (store_Z p_pre zp_low_level_spec).
  - repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mod_norm_gmp_entail_wit_3_split_goal_1 :
  mod_norm_gmp_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mod_norm_spec, mod_congruent.
  split.
  { lia. }
  split.
  { rewrite Z.abs_neq in PreH5 by lia. lia. }
  { subst zx_low_level_spec.
    replace (rv + zp_low_level_spec) with (rv + 1 * zp_low_level_spec) by lia.
    rewrite Z.mod_add by lia.
    replace (qv * zp_low_level_spec + rv) with (rv + qv * zp_low_level_spec) by lia.
    rewrite Z.mod_add by lia.
    reflexivity. }
Qed.

Lemma proof_of_mod_norm_gmp_entail_wit_3 : mod_norm_gmp_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mod_norm_gmp_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_mod_norm_gmp_entail_wit_4_1 : mod_norm_gmp_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Right.
  split_pure_spatial.
  - cancel (store_Z r_pre rv).
    cancel (store_Z x_pre zx_low_level_spec).
    cancel (store_Z p_pre zp_low_level_spec).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold mod_norm_spec, mod_congruent.
    split.
    { lia. }
    split.
    { rewrite Z.abs_eq in PreH6 by lia. lia. }
    { subst zx_low_level_spec.
      replace (qv * zp_low_level_spec + rv) with (rv + qv * zp_low_level_spec) by lia.
      rewrite Z.mod_add by lia.
      reflexivity. }
Qed.

Lemma proof_of_mod_norm_gmp_entail_wit_4_2 : mod_norm_gmp_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Left.
  split_pure_spatial.
  - cancel (store_Z r_pre rv).
    cancel (store_Z x_pre zx_low_level_spec).
    cancel (store_Z p_pre zp_low_level_spec).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold mod_norm_spec, mod_congruent.
    split.
    { lia. }
    split.
    { subst rv. lia. }
    { subst zx_low_level_spec.
      subst rv.
      replace (qv * zp_low_level_spec + 0) with (0 + qv * zp_low_level_spec) by lia.
      rewrite Z.mod_add by lia.
      reflexivity. }
Qed.

Lemma proof_of_mod_norm_gmp_entail_wit_4_3_split_goal_1 :
  mod_norm_gmp_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mod_norm_spec, mod_congruent.
  split.
  { lia. }
  split.
  { rewrite Z.abs_eq in PreH6 by lia. lia. }
  { replace (qv * zp_low_level_spec + rv) with (rv + qv * zp_low_level_spec) by lia.
    rewrite Z.mod_add by lia.
    reflexivity. }
Qed.

Lemma proof_of_mod_norm_gmp_entail_wit_4_3 : mod_norm_gmp_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mod_norm_gmp_entail_wit_4_3_split_goal_1.
Qed.
