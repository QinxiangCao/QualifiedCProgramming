Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

(* All 2D lemmas below come from SimpleC.SL Array2LibCore; the row-level ones
   from ArrayLibCore.  Nothing new is assumed -- these rules only wire lemmas
   that already exist into the strategy engine. *)

Lemma array2_ext_strategy1_correctness : array2_ext_strategy1.
Proof.
  pre_process_default.
  prop_apply (IntArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (IntArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (IntArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (IntArray2.ElemArray.mixed_full (IntArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (IntArray.mixed_full (p + i * m * sizeof (INT)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (IntArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (INT)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  replace (p + i * m * 4) with (p + i * m * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel (IntArray.mixed_missing_i (p + i * m * sizeof (INT)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  Intros_r v.
  apply derivable1s_wand_sepcon_adjoint.
  Intros_p Hval.
  Intros_p Hdef.
  subst v.
  rewrite (Array2.mixed_def_val _ _ Hdef).
  unfold IntArray.mixedstoreA.
  replace (p + i * m * sizeof (INT) + j * 4) with (p + i * m * sizeof (INT) + j * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel.
Qed.

Lemma array2_ext_strategy2_correctness : array2_ext_strategy2.
Proof.
  pre_process_default.
  prop_apply (IntArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (IntArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (IntArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (IntArray2.ElemArray.mixed_full (IntArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (IntArray.mixed_full (p + i * m * sizeof (INT)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (IntArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (INT)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  replace (p + i * m * 4) with (p + i * m * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel (IntArray.mixed_missing_i (p + i * m * sizeof (INT)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  Intros_r v.
  apply derivable1s_wand_sepcon_adjoint.
  Intros_p Hval.
  Intros_p Hdef.
  subst v.
  rewrite (Array2.mixed_def_val _ _ Hdef).
  unfold IntArray.mixedstoreA.
  replace (p + (i * m + j) * 4) with (p + i * m * sizeof (INT) + j * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel.
Qed.

Lemma array2_ext_strategy3_correctness : array2_ext_strategy3.
Proof.
  pre_process_default.
  try (replace (p + i * (sizeof (INT) * w)) with (p + i * w * sizeof (INT)) by nia).
  try replace (p + i * match w with
                   | 0 => 0
                   | Z.pos y' => Z.pos (xO (xO y'))
                   | Z.neg y' => Z.neg (xO (xO y'))
                   end)
    with (p + i * w * sizeof (INT))
    by (rewrite sizeof_int; destruct w; lia).
  subst w.
  prop_apply (IntArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (IntArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (IntArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (IntArray2.ElemArray.mixed_full (IntArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (IntArray.mixed_full (p + i * m * sizeof (INT)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (IntArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (INT)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  cancel (IntArray.mixed_missing_i (p + i * m * sizeof (INT)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  Intros_r v.
  apply derivable1s_wand_sepcon_adjoint.
  Intros_p Hval.
  Intros_p Hdef.
  subst v.
  rewrite (Array2.mixed_def_val _ _ Hdef).
  unfold IntArray.mixedstoreA.
  replace (p + i * m * sizeof (INT) + j * 4) with (p + i * m * sizeof (INT) + j * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel.
Qed.

Lemma array2_ext_strategy4_correctness : array2_ext_strategy4.
Proof.
  pre_process_default.
  prop_apply (IntArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (IntArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (IntArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (IntArray2.ElemArray.mixed_full (IntArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (IntArray.mixed_full (p + i * m * sizeof (INT)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (IntArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (INT)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  replace (p + i * m * 4) with (p + i * m * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel (IntArray.mixed_missing_i (p + i * m * sizeof (INT)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  apply derivable1s_wand_sepcon_adjoint.
  sep_apply (IntArray.mixedstoreA_to_undefstoreA
               (p + i * m * sizeof (INT)) j
               (Znth j (Znth i rows __default_app1_app1_Z) None)).
  replace (p + i * m * sizeof (INT) + j * 4) with (p + i * m * sizeof (INT) + j * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel.
Qed.

Lemma array2_ext_strategy5_correctness : array2_ext_strategy5.
Proof.
  pre_process_default.
  prop_apply (IntArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (IntArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (IntArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (IntArray2.ElemArray.mixed_full (IntArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (IntArray.mixed_full (p + i * m * sizeof (INT)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (IntArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (INT)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  replace (p + i * m * 4) with (p + i * m * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel (IntArray.mixed_missing_i (p + i * m * sizeof (INT)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  apply derivable1s_wand_sepcon_adjoint.
  sep_apply (IntArray.mixedstoreA_to_undefstoreA
               (p + i * m * sizeof (INT)) j
               (Znth j (Znth i rows __default_app1_app1_Z) None)).
  replace (p + (i * m + j) * 4) with (p + i * m * sizeof (INT) + j * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel.
Qed.

Lemma array2_ext_strategy6_correctness : array2_ext_strategy6.
Proof.
  pre_process_default.
  try (replace (p + i * (sizeof (INT) * w)) with (p + i * w * sizeof (INT)) by nia).
  try replace (p + i * match w with
                   | 0 => 0
                   | Z.pos y' => Z.pos (xO (xO y'))
                   | Z.neg y' => Z.neg (xO (xO y'))
                   end)
    with (p + i * w * sizeof (INT))
    by (rewrite sizeof_int; destruct w; lia).
  subst w.
  prop_apply (IntArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (IntArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (IntArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (IntArray2.ElemArray.mixed_full (IntArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (IntArray.mixed_full (p + i * m * sizeof (INT)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (IntArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (INT)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  cancel (IntArray.mixed_missing_i (p + i * m * sizeof (INT)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  apply derivable1s_wand_sepcon_adjoint.
  sep_apply (IntArray.mixedstoreA_to_undefstoreA
               (p + i * m * sizeof (INT)) j
               (Znth j (Znth i rows __default_app1_app1_Z) None)).
  replace (p + i * m * sizeof (INT) + j * 4) with (p + i * m * sizeof (INT) + j * sizeof (INT))
    by (rewrite sizeof_int; nia).
  cancel.
Qed.

Lemma array2_ext_strategy7_correctness : array2_ext_strategy7.
Proof.
  pre_process_default.
  unfold Array2.replace_mixed_row.
  pose proof (IntArray2.mixed_missing_i_merge_to_mixed_full p i n m rows row) as Hm.
  change (IntArray2.ElemArray.mixed_full (IntArray2.row_addr p m i) m row)
    with (IntArray.mixed_full (p + i * m * sizeof (INT)) m row) in Hm.
  replace (p + i * m * 4) with (p + i * m * sizeof (INT))
    by (rewrite sizeof_int; nia).
  sep_apply Hm; try lia.
  cancel.
Qed.

Lemma array2_ext_strategy8_correctness : array2_ext_strategy8.
Proof.
  pre_process_default.
  try (replace (p + i * (sizeof (INT) * w)) with (p + i * w * sizeof (INT)) by nia).
  try replace (p + i * match w with
                   | 0 => 0
                   | Z.pos y' => Z.pos (xO (xO y'))
                   | Z.neg y' => Z.neg (xO (xO y'))
                   end)
    with (p + i * w * sizeof (INT))
    by (rewrite sizeof_int; destruct w; lia).
  subst w.
  unfold Array2.replace_mixed_row.
  pose proof (IntArray2.mixed_missing_i_merge_to_mixed_full p i n m rows row) as Hm.
  change (IntArray2.ElemArray.mixed_full (IntArray2.row_addr p m i) m row)
    with (IntArray.mixed_full (p + i * m * sizeof (INT)) m row) in Hm.
  sep_apply Hm; try lia.
  cancel.
Qed.

Lemma array2_ext_strategy9_correctness : array2_ext_strategy9.
Proof.
  pre_process_default.
  unfold Array2.replace_mixed_row.
  pose proof (IntArray2.mixed_missing_i_merge_to_mixed_full p i n m rows row) as Hm.
  change (IntArray2.ElemArray.mixed_full (IntArray2.row_addr p m i) m row)
    with (IntArray.mixed_full (p + i * m * sizeof (INT)) m row) in Hm.
  replace (p + i * m * 4) with (p + i * m * sizeof (INT))
    by (rewrite sizeof_int; nia).
  sep_apply Hm; try lia.
  cancel.
Qed.

Lemma array2_ext_strategy10_correctness : array2_ext_strategy10.
Proof.
  pre_process_default.
  pose proof (IntArray2.undef_full_split_to_undef_missing_i p i n m) as Hm.
  change (IntArray2.ElemArray.undef_full (IntArray2.row_addr p m i) m)
    with (IntArray.undef_full (p + i * m * sizeof (INT)) m) in Hm.
  replace (p + i * m * 4) with (p + i * m * sizeof (INT))
    by (rewrite sizeof_int; nia).
  sep_apply Hm; try lia.
  cancel.
  apply derivable1s_wand_sepcon_adjoint.
  asrt_simpl.
  cancel.
Qed.

Lemma array2_ext_strategy11_correctness : array2_ext_strategy11.
Proof.
  pre_process_default.
  pose proof (IntArray2.undef_full_split_to_undef_missing_i p i n m) as Hm.
  change (IntArray2.ElemArray.undef_full (IntArray2.row_addr p m i) m)
    with (IntArray.undef_full (p + i * m * sizeof (INT)) m) in Hm.
  replace (p + i * m * 4) with (p + i * m * sizeof (INT))
    by (rewrite sizeof_int; nia).
  sep_apply Hm; try lia.
  cancel.
  apply derivable1s_wand_sepcon_adjoint.
  asrt_simpl.
  cancel.
Qed.

Lemma array2_ext_strategy12_correctness : array2_ext_strategy12.
Proof.
  pre_process_default.
  try (replace (p + i * (sizeof (INT) * w)) with (p + i * w * sizeof (INT)) by nia).
  try replace (p + i * match w with
                   | 0 => 0
                   | Z.pos y' => Z.pos (xO (xO y'))
                   | Z.neg y' => Z.neg (xO (xO y'))
                   end)
    with (p + i * w * sizeof (INT))
    by (rewrite sizeof_int; destruct w; lia).
  subst w.
  pose proof (IntArray2.undef_full_split_to_undef_missing_i p i n m) as Hm.
  change (IntArray2.ElemArray.undef_full (IntArray2.row_addr p m i) m)
    with (IntArray.undef_full (p + i * m * sizeof (INT)) m) in Hm.
  sep_apply Hm; try lia.
  cancel.
  apply derivable1s_wand_sepcon_adjoint.
  asrt_simpl.
  cancel.
Qed.

Lemma array2_ext_strategy13_correctness : array2_ext_strategy13.
Proof.
  pre_process_default.
  Intros_p Hrows.
  rewrite Hrows.
  sep_apply (Array2Convert.int_mixed_full_to_full p n m l).
  cancel.
Qed.

Lemma array2_ext_strategy14_correctness : array2_ext_strategy14.
Proof.
  pre_process_default.
  sep_apply (IntArray2.mixed_full_to_undef_full p n m rows).
  cancel.
Qed.

Lemma array2_ext_strategy15_correctness : array2_ext_strategy15.
Proof.
  pre_process_default.
  sep_apply (IntArray2.full_to_undef_full p n m rows).
  cancel.
Qed.

Lemma array2_ext_strategy16_correctness : array2_ext_strategy16.
Proof.
  pre_process_default.
  unfold Array2.replace_row.
  pose proof (CharArray2.missing_i_merge_to_full p i n m rows row) as Hm.
  change (CharArray2.ElemArray.full (CharArray2.row_addr p m i) m row)
    with (CharArray.full (p + i * m * sizeof (CHAR)) m row) in Hm.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  sep_apply Hm; try lia.
  cancel.
Qed.

Lemma array2_ext_strategy17_correctness : array2_ext_strategy17.
Proof.
  pre_process_default.
  try (replace (p + i * (sizeof (CHAR) * w)) with (p + i * w * sizeof (CHAR)) by nia).
  try replace (p + i * match w with
                   | 0 => 0
                   | Z.pos y' => Z.pos y'
                   | Z.neg y' => Z.neg y'
                   end)
    with (p + i * w * sizeof (CHAR))
    by (rewrite sizeof_char; destruct w; lia).
  subst w.
  unfold Array2.replace_row.
  pose proof (CharArray2.missing_i_merge_to_full p i n m rows row) as Hm.
  change (CharArray2.ElemArray.full (CharArray2.row_addr p m i) m row)
    with (CharArray.full (p + i * m * sizeof (CHAR)) m row) in Hm.
  sep_apply Hm; try lia.
  cancel.
Qed.

Lemma array2_ext_strategy18_correctness : array2_ext_strategy18.
Proof.
  pre_process_default.
  unfold Array2.replace_row.
  pose proof (CharArray2.missing_i_merge_to_full p i n m rows row) as Hm.
  change (CharArray2.ElemArray.full (CharArray2.row_addr p m i) m row)
    with (CharArray.full (p + i * m * sizeof (CHAR)) m row) in Hm.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  sep_apply Hm; try lia.
  cancel.
Qed.

Lemma array2_ext_strategy19_correctness : array2_ext_strategy19.
Proof.
  pre_process_default.
  prop_apply (CharArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (CharArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (CharArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (CharArray2.ElemArray.mixed_full (CharArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (CharArray.mixed_full (p + i * m * sizeof (CHAR)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (CharArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (CHAR)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel (CharArray.mixed_missing_i (p + i * m * sizeof (CHAR)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  Intros_r v.
  apply derivable1s_wand_sepcon_adjoint.
  Intros_p Hval.
  Intros_p Hdef.
  subst v.
  rewrite (Array2.mixed_def_val _ _ Hdef).
  unfold CharArray.mixedstoreA.
  replace (p + i * m * sizeof (CHAR) + j * 1) with (p + i * m * sizeof (CHAR) + j * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel.
Qed.

Lemma array2_ext_strategy20_correctness : array2_ext_strategy20.
Proof.
  pre_process_default.
  prop_apply (CharArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (CharArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (CharArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (CharArray2.ElemArray.mixed_full (CharArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (CharArray.mixed_full (p + i * m * sizeof (CHAR)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (CharArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (CHAR)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel (CharArray.mixed_missing_i (p + i * m * sizeof (CHAR)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  Intros_r v.
  apply derivable1s_wand_sepcon_adjoint.
  Intros_p Hval.
  Intros_p Hdef.
  subst v.
  rewrite (Array2.mixed_def_val _ _ Hdef).
  unfold CharArray.mixedstoreA.
  replace (p + (i * m + j) * 1) with (p + i * m * sizeof (CHAR) + j * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel.
Qed.

Lemma array2_ext_strategy21_correctness : array2_ext_strategy21.
Proof.
  pre_process_default.
  try (replace (p + i * (sizeof (CHAR) * w)) with (p + i * w * sizeof (CHAR)) by nia).
  try replace (p + i * match w with
                   | 0 => 0
                   | Z.pos y' => Z.pos y'
                   | Z.neg y' => Z.neg y'
                   end)
    with (p + i * w * sizeof (CHAR))
    by (rewrite sizeof_char; destruct w; lia).
  subst w.
  prop_apply (CharArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (CharArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (CharArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (CharArray2.ElemArray.mixed_full (CharArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (CharArray.mixed_full (p + i * m * sizeof (CHAR)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (CharArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (CHAR)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  cancel (CharArray.mixed_missing_i (p + i * m * sizeof (CHAR)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  Intros_r v.
  apply derivable1s_wand_sepcon_adjoint.
  Intros_p Hval.
  Intros_p Hdef.
  subst v.
  rewrite (Array2.mixed_def_val _ _ Hdef).
  unfold CharArray.mixedstoreA.
  replace (p + i * m * sizeof (CHAR) + j * 1) with (p + i * m * sizeof (CHAR) + j * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel.
Qed.

Lemma array2_ext_strategy22_correctness : array2_ext_strategy22.
Proof.
  pre_process_default.
  prop_apply (CharArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (CharArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (CharArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (CharArray2.ElemArray.mixed_full (CharArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (CharArray.mixed_full (p + i * m * sizeof (CHAR)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (CharArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (CHAR)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel (CharArray.mixed_missing_i (p + i * m * sizeof (CHAR)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  apply derivable1s_wand_sepcon_adjoint.
  sep_apply (CharArray.mixedstoreA_to_undefstoreA
               (p + i * m * sizeof (CHAR)) j
               (Znth j (Znth i rows __default_app1_app1_Z) None)).
  replace (p + i * m * sizeof (CHAR) + j * 1) with (p + i * m * sizeof (CHAR) + j * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel.
Qed.

Lemma array2_ext_strategy23_correctness : array2_ext_strategy23.
Proof.
  pre_process_default.
  prop_apply (CharArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (CharArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (CharArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (CharArray2.ElemArray.mixed_full (CharArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (CharArray.mixed_full (p + i * m * sizeof (CHAR)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (CharArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (CHAR)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel (CharArray.mixed_missing_i (p + i * m * sizeof (CHAR)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  apply derivable1s_wand_sepcon_adjoint.
  sep_apply (CharArray.mixedstoreA_to_undefstoreA
               (p + i * m * sizeof (CHAR)) j
               (Znth j (Znth i rows __default_app1_app1_Z) None)).
  replace (p + (i * m + j) * 1) with (p + i * m * sizeof (CHAR) + j * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel.
Qed.

Lemma array2_ext_strategy24_correctness : array2_ext_strategy24.
Proof.
  pre_process_default.
  try (replace (p + i * (sizeof (CHAR) * w)) with (p + i * w * sizeof (CHAR)) by nia).
  try replace (p + i * match w with
                   | 0 => 0
                   | Z.pos y' => Z.pos y'
                   | Z.neg y' => Z.neg y'
                   end)
    with (p + i * w * sizeof (CHAR))
    by (rewrite sizeof_char; destruct w; lia).
  subst w.
  prop_apply (CharArray2.mixed_full_Zlength p n m rows). Intros.
  sep_apply (CharArray2.mixed_full_split_to_mixed_missing_i p i n m rows); try lia.
  cancel (CharArray2.mixed_missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i nil __default_app1_app1_Z) by lia.
  change (CharArray2.ElemArray.mixed_full (CharArray2.row_addr p m i) m
            (Znth i rows __default_app1_app1_Z))
    with (CharArray.mixed_full (p + i * m * sizeof (CHAR)) m
            (Znth i rows __default_app1_app1_Z)).
  sep_apply (CharArray.mixed_full_split_to_mixed_missing_i
               (p + i * m * sizeof (CHAR)) j m
               (Znth i rows __default_app1_app1_Z) None); try lia.
  cancel (CharArray.mixed_missing_i (p + i * m * sizeof (CHAR)) j 0 m
            (Znth i rows __default_app1_app1_Z)).
  apply derivable1s_wand_sepcon_adjoint.
  sep_apply (CharArray.mixedstoreA_to_undefstoreA
               (p + i * m * sizeof (CHAR)) j
               (Znth j (Znth i rows __default_app1_app1_Z) None)).
  replace (p + i * m * sizeof (CHAR) + j * 1) with (p + i * m * sizeof (CHAR) + j * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  cancel.
Qed.

Lemma array2_ext_strategy25_correctness : array2_ext_strategy25.
Proof.
  pre_process_default.
  unfold Array2.replace_mixed_row.
  pose proof (CharArray2.mixed_missing_i_merge_to_mixed_full p i n m rows row) as Hm.
  change (CharArray2.ElemArray.mixed_full (CharArray2.row_addr p m i) m row)
    with (CharArray.mixed_full (p + i * m * sizeof (CHAR)) m row) in Hm.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  sep_apply Hm; try lia.
  cancel.
Qed.

Lemma array2_ext_strategy26_correctness : array2_ext_strategy26.
Proof.
  pre_process_default.
  try (replace (p + i * (sizeof (CHAR) * w)) with (p + i * w * sizeof (CHAR)) by nia).
  try replace (p + i * match w with
                   | 0 => 0
                   | Z.pos y' => Z.pos y'
                   | Z.neg y' => Z.neg y'
                   end)
    with (p + i * w * sizeof (CHAR))
    by (rewrite sizeof_char; destruct w; lia).
  subst w.
  unfold Array2.replace_mixed_row.
  pose proof (CharArray2.mixed_missing_i_merge_to_mixed_full p i n m rows row) as Hm.
  change (CharArray2.ElemArray.mixed_full (CharArray2.row_addr p m i) m row)
    with (CharArray.mixed_full (p + i * m * sizeof (CHAR)) m row) in Hm.
  sep_apply Hm; try lia.
  cancel.
Qed.

Lemma array2_ext_strategy27_correctness : array2_ext_strategy27.
Proof.
  pre_process_default.
  unfold Array2.replace_mixed_row.
  pose proof (CharArray2.mixed_missing_i_merge_to_mixed_full p i n m rows row) as Hm.
  change (CharArray2.ElemArray.mixed_full (CharArray2.row_addr p m i) m row)
    with (CharArray.mixed_full (p + i * m * sizeof (CHAR)) m row) in Hm.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  sep_apply Hm; try lia.
  cancel.
Qed.

Lemma array2_ext_strategy28_correctness : array2_ext_strategy28.
Proof.
  pre_process_default.
  pose proof (CharArray2.undef_full_split_to_undef_missing_i p i n m) as Hm.
  change (CharArray2.ElemArray.undef_full (CharArray2.row_addr p m i) m)
    with (CharArray.undef_full (p + i * m * sizeof (CHAR)) m) in Hm.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  sep_apply Hm; try lia.
  cancel.
  apply derivable1s_wand_sepcon_adjoint.
  asrt_simpl.
  cancel.
Qed.

Lemma array2_ext_strategy29_correctness : array2_ext_strategy29.
Proof.
  pre_process_default.
  pose proof (CharArray2.undef_full_split_to_undef_missing_i p i n m) as Hm.
  change (CharArray2.ElemArray.undef_full (CharArray2.row_addr p m i) m)
    with (CharArray.undef_full (p + i * m * sizeof (CHAR)) m) in Hm.
  replace (p + i * m * 1) with (p + i * m * sizeof (CHAR))
    by (rewrite sizeof_char; nia).
  sep_apply Hm; try lia.
  cancel.
  apply derivable1s_wand_sepcon_adjoint.
  asrt_simpl.
  cancel.
Qed.

Lemma array2_ext_strategy30_correctness : array2_ext_strategy30.
Proof.
  pre_process_default.
  try (replace (p + i * (sizeof (CHAR) * w)) with (p + i * w * sizeof (CHAR)) by nia).
  try replace (p + i * match w with
                   | 0 => 0
                   | Z.pos y' => Z.pos y'
                   | Z.neg y' => Z.neg y'
                   end)
    with (p + i * w * sizeof (CHAR))
    by (rewrite sizeof_char; destruct w; lia).
  subst w.
  pose proof (CharArray2.undef_full_split_to_undef_missing_i p i n m) as Hm.
  change (CharArray2.ElemArray.undef_full (CharArray2.row_addr p m i) m)
    with (CharArray.undef_full (p + i * m * sizeof (CHAR)) m) in Hm.
  sep_apply Hm; try lia.
  cancel.
  apply derivable1s_wand_sepcon_adjoint.
  asrt_simpl.
  cancel.
Qed.

Lemma array2_ext_strategy31_correctness : array2_ext_strategy31.
Proof.
  pre_process_default.
  Intros_p Hrows.
  rewrite Hrows.
  sep_apply (Array2Convert.char_mixed_full_to_full p n m l).
  cancel.
Qed.

Lemma array2_ext_strategy32_correctness : array2_ext_strategy32.
Proof.
  pre_process_default.
  sep_apply (CharArray2.mixed_full_to_undef_full p n m rows).
  cancel.
Qed.

Lemma array2_ext_strategy33_correctness : array2_ext_strategy33.
Proof.
  pre_process_default.
  sep_apply (CharArray2.full_to_undef_full p n m rows).
  cancel.
Qed.
