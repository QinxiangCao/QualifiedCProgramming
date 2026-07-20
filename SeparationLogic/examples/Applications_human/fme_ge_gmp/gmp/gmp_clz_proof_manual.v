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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_clz_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_clz_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_gmp_clz_entail_wit_1 : gmp_clz_entail_wit_1.
Proof.
  unfold gmp_clz_entail_wit_1.
  left.
  intros.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; cbn; lia.
Qed.

Lemma proof_of_gmp_clz_entail_wit_2 : gmp_clz_entail_wit_2.
Proof.
  unfold gmp_clz_entail_wit_2.
  left.
  intros.
  pose proof (gmp_clz_shift8_step x_pre x c LOCAL_SHIFT_BITS
                PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
    as (H_eq & H_mod & H_nonneg & H_bound & H_pos & H_lt).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact H_eq.
    + dump_pre_spatial. exact H_mod.
    + dump_pre_spatial. exact H_nonneg.
    + dump_pre_spatial. exact H_bound.
    + dump_pre_spatial. exact H_pos.
    + dump_pre_spatial. exact H_lt.
    + dump_pre_spatial. exact PreH8.
Qed.

Lemma proof_of_gmp_clz_entail_wit_5 : gmp_clz_entail_wit_5.
Proof.
  unfold gmp_clz_entail_wit_5.
  left.
  intros.
  pose proof (gmp_clz_shift1_step x_pre x c LOCAL_SHIFT_BITS
                PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)
    as (H_eq & H_nonneg & H_bound & H_pos & H_lt).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact H_eq.
    + dump_pre_spatial. exact H_nonneg.
    + dump_pre_spatial. exact H_bound.
    + dump_pre_spatial. exact H_pos.
    + dump_pre_spatial. exact H_lt.
    + dump_pre_spatial. exact PreH7.
Qed.

Lemma proof_of_gmp_clz_return_wit_1 : gmp_clz_return_wit_1.
Proof.
  unfold gmp_clz_return_wit_1.
  left.
  intros.
  pose proof (gmp_clz_highbit_nonzero_ge31 x ltac:(split; lia) PreH1) as Hge_x.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. rewrite <- PreH2. exact Hge_x.
    + dump_pre_spatial. rewrite <- PreH2. exact PreH6.
Qed.
