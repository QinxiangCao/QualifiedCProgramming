Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma array2_strategy1_correctness : array2_strategy1.
Proof.
  pre_process_default.
  prop_apply (IntArray2.full_Zlength p n m rows).
  Intros.
  sep_apply_l_atomic (IntArray2.full_split_to_missing_i p i n m rows).
  - dump_pre_spatial.
    lia.
  - rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
    sep_apply_l_atomic
      (IntArray.full_split_to_missing_i
        (p + i * m * sizeof_front_end_type FET_int)
        j m (Znth i rows __default_app1_Z) 0).
    + dump_pre_spatial.
      lia.
    + cancel (IntArray2.missing_i p i 0 n m rows).
      cancel (IntArray.missing_i
        (p + i * m * sizeof_front_end_type FET_int)
        j 0 m (Znth i rows __default_app1_Z)).
      Intros_r v.
      apply_sepcon_adjoint.
      Intros_p Hval.
      subst v.
      cancel.
Qed.

Lemma array2_strategy4_correctness : array2_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst rows2.
  cancel.
Qed.

Lemma array2_strategy5_correctness : array2_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma array2_strategy2_correctness : array2_strategy2.
Proof.
  pre_process_default.
  prop_apply (IntArray2.missing_i_Zlength p i 0 n m rows).
  Intros.
  pose proof (IntArray2.missing_i_merge_to_full
        p i n m rows (Znth i rows __default_app1_Z)).
  change (IntArray2.ElemArray.full (IntArray2.row_addr p m i)
m (Znth i rows __default_app1_Z)) with (IntArray.full (p + i * m * sizeof ( INT )) m
(Znth i rows __default_app1_Z)) in H2.
  sep_apply H2 ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.


Lemma array2_strategy6_correctness : array2_strategy6.
Proof.
  pre_process_default.
  prop_apply (IntArray2.full_Zlength p n m rows). Intros.
  sep_apply (IntArray2.full_split_to_missing_i p i n m rows) ; try lia.
  entailer!.
  replace (Znth i rows nil) with (Znth i rows __default_app1_Z).
  change (IntArray2.ElemArray.full (IntArray2.row_addr p m i) m (Znth i rows __default_app1_Z)) with
    (IntArray.full (p + i * m * sizeof ( INT )) m (Znth i rows __default_app1_Z)).
  sep_apply (IntArray.full_split_to_missing_i (p + i * m * sizeof ( INT )) j m (Znth i rows __default_app1_Z ) 0) ; try lia.
  entailer!.
  Intros_r v.
  pre_process_default.
  Intros. subst.
  replace ((i * m + j) * sizeof ( INT )) with (i * m * sizeof ( INT ) + j * sizeof ( INT )) by lia.
  rewrite Z.add_assoc.
  entailer!.
  apply Znth_indep ; try lia.
Qed.