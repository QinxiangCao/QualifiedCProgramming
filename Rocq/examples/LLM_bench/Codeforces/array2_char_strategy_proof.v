Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma array2_char_strategy1_correctness : array2_char_strategy1.
Proof.
  pre_process_default.
  prop_apply (CharArray2.full_Zlength p n m rows).
  Intros.
  sep_apply_l_atomic (CharArray2.full_split_to_missing_i p i n m rows).
  - dump_pre_spatial.
    lia.
  - rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
    sep_apply_l_atomic
      (CharArray.full_split_to_missing_i
        (p + i * m * sizeof_front_end_type FET_char)
        j m (Znth i rows __default_app1_Z) 0).
    + dump_pre_spatial.
      lia.
    + cancel (CharArray2.missing_i p i 0 n m rows).
      replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
        by (rewrite sizeof_char; lia).
      replace (p + i * m * sizeof (CHAR) + j * 1)
        with (p + i * m * sizeof (CHAR) + j * sizeof (CHAR))
        by (rewrite sizeof_char; lia).
      cancel (CharArray.missing_i
        (p + i * m * sizeof_front_end_type FET_char)
        j 0 m (Znth i rows __default_app1_Z)).
      Intros_r v.
      apply_sepcon_adjoint.
      Intros_p Hval.
      subst v.
      cancel.
Qed.

Lemma array2_char_strategy4_correctness : array2_char_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst rows2.
  cancel.
Qed.

Lemma array2_char_strategy5_correctness : array2_char_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma array2_char_strategy2_correctness : array2_char_strategy2.
Proof.
  pre_process_default.
  prop_apply (CharArray2.missing_i_Zlength p i 0 n m rows).
  Intros.
  pose proof (CharArray2.missing_i_merge_to_full
        p i n m rows (Znth i rows __default_app1_Z)).
  change (CharArray2.ElemArray.full (CharArray2.row_addr p m i)
m (Znth i rows __default_app1_Z)) with (CharArray.full (p + i * m * sizeof ( CHAR )) m
(Znth i rows __default_app1_Z)) in H2.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; lia).
  sep_apply H2 ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.


Lemma array2_char_strategy6_correctness : array2_char_strategy6.
Proof.
  pre_process_default.
  prop_apply (CharArray2.full_Zlength p n m rows). Intros.
  sep_apply (CharArray2.full_split_to_missing_i p i n m rows) ; try lia.
  cancel (CharArray2.missing_i p i 0 n m rows).
  replace (Znth i rows nil) with (Znth i rows __default_app1_Z).
  change (CharArray2.ElemArray.full (CharArray2.row_addr p m i) m (Znth i rows __default_app1_Z)) with
    (CharArray.full (p + i * m * sizeof ( CHAR )) m (Znth i rows __default_app1_Z)).
  sep_apply (CharArray.full_split_to_missing_i (p + i * m * sizeof ( CHAR )) j m (Znth i rows __default_app1_Z ) 0) ; try lia.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; lia).
  replace (p + (i * m + j) * 1) with (p + (i * m + j) * sizeof (CHAR))
    by (rewrite sizeof_char; lia).
  cancel (CharArray.missing_i (p + i * m * sizeof (CHAR)) j 0 m (Znth i rows __default_app1_Z)).
  apply derivable1s_allp_r.
  intro v.
  pre_process_default.
  Intros. subst.
  replace ((i * m + j) * sizeof ( CHAR )) with (i * m * sizeof ( CHAR ) + j * sizeof ( CHAR )) by lia.
  rewrite Z.add_assoc.
  cancel.
  apply Znth_indep ; try lia.
Qed.

Lemma array2_char_strategy7_correctness : array2_char_strategy7.
Proof.
  pre_process_default.
  subst w.
  prop_apply (CharArray2.full_Zlength p n m rows). Intros.
  sep_apply (CharArray2.full_split_to_missing_i p i n m rows) ; try lia.
  cancel (CharArray2.missing_i p i 0 n m rows).
  replace (Znth i rows nil) with (Znth i rows __default_app1_Z).
  change (CharArray2.ElemArray.full (CharArray2.row_addr p m i) m (Znth i rows __default_app1_Z)) with
    (CharArray.full (p + i * m * sizeof ( CHAR )) m (Znth i rows __default_app1_Z)).
  sep_apply (CharArray.full_split_to_missing_i (p + i * m * sizeof ( CHAR )) j m (Znth i rows __default_app1_Z ) 0) ; try lia.
  replace (p + i *
    match m with
    | 0 => 0
    | Z.pos y => Z.pos y
    | Z.neg y => Z.neg y
    end) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; destruct m; lia).
  replace (p + i *
    match m with
    | 0 => 0
    | Z.pos y => Z.pos y
    | Z.neg y => Z.neg y
    end + j * 1) with
    (p + i * m * sizeof (CHAR) + j * sizeof (CHAR))
    by (rewrite sizeof_char; destruct m; lia).
  cancel (CharArray.missing_i (p + i * m * sizeof (CHAR)) j 0 m (Znth i rows __default_app1_Z)).
  apply derivable1s_allp_r.
  intro v.
  pre_process_default.
  Intros. subst.
  replace (p + i * m * sizeof (CHAR) + j * 1)
    with (p + i * m * sizeof (CHAR) + j * sizeof (CHAR))
    by (rewrite sizeof_char; lia).
  cancel.
  apply Znth_indep ; try lia.
Qed.

Lemma array2_char_strategy8_correctness : array2_char_strategy8.
Proof.
  pre_process_default.
  subst w.
  prop_apply (CharArray2.missing_i_Zlength p i 0 n m rows).
  Intros.
  pose proof (CharArray2.missing_i_merge_to_full
        p i n m rows (Znth i rows __default_app1_Z)) as Hmerge.
  change (CharArray2.ElemArray.full (CharArray2.row_addr p m i)
    m (Znth i rows __default_app1_Z)) with
    (CharArray.full (p + i * m * sizeof (CHAR)) m
      (Znth i rows __default_app1_Z)) in Hmerge.
  replace (p + i * (sizeof_front_end_type FET_char * m))
    with (p + i * m * sizeof (CHAR)) by (rewrite sizeof_char; lia).
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma array2_char_strategy9_correctness : array2_char_strategy9.
Proof.
  exact array2_char_strategy2_correctness.
Qed.
