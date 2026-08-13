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
From SimpleC.EE.LLM_bench.Engineering.string Require Import strcat_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_strcat_safety_wit_3 : strcat_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_lt : i < string_lib.string_length dst_str).
  { eapply string_lib.c_string_nonzero_index_lt; eauto. }
  split_pures; dump_pre_spatial;
    unfold string_lib.string_length in *;
    pose proof (Zlength_nonneg dst_str);
    pose proof (Zlength_nonneg src_str);
    lia.
Qed.

Lemma proof_of_strcat_safety_wit_7 : strcat_safety_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  - dump_pre_spatial.
    unfold string_lib.string_length in *.
    pose proof (Zlength_nonneg dst_str).
    pose proof (Zlength_nonneg src_str).
    lia.
  - dump_pre_spatial.
    lia.
Qed.

Lemma proof_of_strcat_entail_wit_1 : strcat_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  cancel.
  split_pures; dump_pre_spatial; auto; try lia; apply Zlength_nonneg.
Qed.

Lemma proof_of_strcat_entail_wit_2 : strcat_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold string_lib.store_string; split_pure_spatial.
  cancel.
  split_pures; dump_pre_spatial; auto; try lia.
  assert (i <> string_lib.string_length dst_str) by
    (intro Hi; apply PreH1; rewrite Hi; unfold string_lib.c_string, string_lib.string_length;
     rewrite app_Znth2 by lia; rewrite Z.sub_diag; apply Znth0_cons).
  lia.
  intros k Hk.
  destruct (Z_lt_ge_dec k i).
  - match goal with
    | Hprefix : forall k : Z, 0 <= k < i -> Znth k dst_str 0 <> 0 |- _ =>
        apply Hprefix; lia
    end.
  - assert (k = i) by lia.
    subst.
    assert (Hi_lt : i < string_lib.string_length dst_str) by
      (assert (i <> string_lib.string_length dst_str) by
         (intro Hi; apply PreH1; rewrite Hi; unfold string_lib.c_string, string_lib.string_length;
          rewrite app_Znth2 by lia; rewrite Z.sub_diag; apply Znth0_cons);
       lia).
    intro Hz; apply PreH1.
    unfold string_lib.c_string.
    rewrite app_Znth1 by (unfold string_lib.string_length in *; lia).
    exact Hz.
Qed.

Lemma proof_of_strcat_entail_wit_3 : strcat_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = string_lib.string_length dst_str) by
    (match goal with
     | Hvalid : string_lib.valid_string dst_str |- _ =>
         destruct Hvalid as [_ Hnul]
     end;
     destruct (Z.eq_dec i (string_lib.string_length dst_str)) as [Heq | Hneq];
     [exact Heq |
      assert (i < string_lib.string_length dst_str) by lia;
      exfalso; apply (Hnul i);
      [unfold string_lib.string_length in *; lia |
       unfold string_lib.c_string in PreH1;
       rewrite app_Znth1 in PreH1 by (unfold string_lib.string_length in *; lia);
       exact PreH1]]).
  replace (string_lib.string_length dst_str + 0) with
    (string_lib.string_length dst_str) by lia.
  unfold string_lib.store_string; split_pure_spatial.
  replace (dst_str ++ sublist 0 0 src_str) with dst_str by
    (rewrite Zsublist_nil by lia; rewrite app_nil_r; reflexivity).
  sep_apply (CharArray.full_split_to_full dest_pre
               (string_lib.string_length dst_str)
               (string_lib.string_length dst_str + 1)
               (string_lib.c_string dst_str)); [ | lia ].
  replace (sublist 0 (string_lib.string_length dst_str)
             (string_lib.c_string dst_str)) with dst_str by
    (unfold string_lib.c_string, string_lib.string_length;
     rewrite sublist_app_exact1; reflexivity).
  replace (string_lib.string_length dst_str + 1 -
             string_lib.string_length dst_str) with 1 by lia.
  replace (sublist (string_lib.string_length dst_str)
             (string_lib.string_length dst_str + 1)
             (string_lib.c_string dst_str)) with (0 :: nil) by
    (unfold string_lib.c_string, string_lib.string_length;
     rewrite sublist_split_app_r with (len := Zlength dst_str);
     [replace (Zlength dst_str - Zlength dst_str) with 0 by lia;
      replace (Zlength dst_str + 1 - Zlength dst_str) with 1 by lia;
      reflexivity | reflexivity | lia]).
  cancel.
  rewrite CharArray.full_unfold.
  replace (dest_pre + string_lib.string_length dst_str * sizeof ( CHAR ) +
             0 * sizeof ( CHAR ))
    with (dest_pre + string_lib.string_length dst_str * sizeof ( CHAR )) by lia.
  rewrite CharArray.seg_empty.
  Intros_p Hstore_byte_valid.
  cancel.
  split_pures; dump_pre_spatial; auto; try lia; apply Zlength_nonneg.
Qed.

Lemma proof_of_strcat_entail_wit_4 : strcat_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hj_lt : j < string_lib.string_length src_str) by
    (assert (j <> string_lib.string_length src_str) by
       (intro Hj; apply PreH1; rewrite Hj; unfold string_lib.c_string, string_lib.string_length;
        rewrite app_Znth2 by lia; rewrite Z.sub_diag; apply Znth0_cons);
     lia).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_strcat_entail_wit_5 : strcat_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst i.
  assert (Hprefix_len :
            Zlength (dst_str ++ sublist 0 j src_str) =
              string_lib.string_length dst_str + j) by
    (unfold string_lib.string_length in *; rewrite Zlength_app;
     rewrite Zlength_sublist0 by lia; lia).
  assert (Hsrc_at :
            Znth j (string_lib.c_string src_str) 0 = Znth j src_str 0) by
    (unfold string_lib.c_string;
     rewrite app_Znth1 by (unfold string_lib.string_length in *; lia);
     reflexivity).
  assert (Hsub_next :
            sublist 0 (j + 1) src_str =
              sublist 0 j src_str ++ Znth j src_str 0 :: nil) by
    (rewrite (sublist_split 0 (j + 1) j src_str) by
       (unfold string_lib.string_length in *; lia);
     rewrite (sublist_single 0 j src_str) by
       (unfold string_lib.string_length in *; lia);
     reflexivity).
  assert (Hprefix_next_len :
            Zlength (dst_str ++ sublist 0 (j + 1) src_str) =
              string_lib.string_length dst_str + (j + 1)) by
    (unfold string_lib.string_length in *; rewrite Zlength_app;
     rewrite Zlength_sublist0 by lia; lia).
  replace (((dst_str ++ sublist 0 j src_str) ++
              Znth j (string_lib.c_string src_str) 0 :: nil) ++ 0 :: nil)
    with ((dst_str ++ sublist 0 (j + 1) src_str) ++ 0 :: nil) by
    (rewrite Hsrc_at, Hsub_next; repeat rewrite app_assoc; reflexivity).
  replace (string_lib.string_length dst_str + j + 1 + 1)
    with (string_lib.string_length dst_str + (j + 1) + 1) by lia.
  unfold string_lib.store_string; split_pure_spatial.
  sep_apply (CharArray.full_split_to_full dest_pre
               (string_lib.string_length dst_str + (j + 1))
               (string_lib.string_length dst_str + (j + 1) + 1)
               ((dst_str ++ sublist 0 (j + 1) src_str) ++ 0 :: nil)); [ | lia ].
  replace (sublist 0 (string_lib.string_length dst_str + (j + 1))
             ((dst_str ++ sublist 0 (j + 1) src_str) ++ 0 :: nil))
    with (dst_str ++ sublist 0 (j + 1) src_str) by
    (rewrite <- Hprefix_next_len; rewrite sublist_app_exact1; reflexivity).
  replace (string_lib.string_length dst_str + (j + 1) + 1 -
             (string_lib.string_length dst_str + (j + 1))) with 1 by lia.
  replace (sublist (string_lib.string_length dst_str + (j + 1))
             (string_lib.string_length dst_str + (j + 1) + 1)
             ((dst_str ++ sublist 0 (j + 1) src_str) ++ 0 :: nil))
    with (0 :: nil) by
    (rewrite <- Hprefix_next_len;
     rewrite sublist_split_app_r with
       (len := Zlength (dst_str ++ sublist 0 (j + 1) src_str));
     [replace (Zlength (dst_str ++ sublist 0 (j + 1) src_str) -
                 Zlength (dst_str ++ sublist 0 (j + 1) src_str)) with 0 by lia;
      replace (Zlength (dst_str ++ sublist 0 (j + 1) src_str) + 1 -
                 Zlength (dst_str ++ sublist 0 (j + 1) src_str)) with 1 by lia;
      reflexivity | reflexivity | lia]).
  cancel.
  rewrite CharArray.full_unfold.
  replace (dest_pre + (string_lib.string_length dst_str + (j + 1)) *
             sizeof ( CHAR ) + 0 * sizeof ( CHAR ))
    with (dest_pre + (string_lib.string_length dst_str + (j + 1)) *
             sizeof ( CHAR )) by lia.
  rewrite CharArray.seg_empty.
  Intros_p Hstore_byte_valid.
  cancel.
  split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_strcat_return_wit_1 : strcat_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hj_eq : j = string_lib.string_length src_str).
  {
    destruct (Z_lt_ge_dec j (string_lib.string_length src_str));
      [ exfalso | lia ].
    assert (Hj_zero : Znth j src_str 0 = 0).
    {
      unfold string_lib.c_string in PreH1.
      rewrite app_Znth1 in PreH1 by (unfold string_lib.string_length in l; lia).
      exact PreH1.
    }
    match goal with
    | Hvalid : string_lib.valid_string src_str |- _ =>
        destruct Hvalid as [_ Hno]
    end.
    specialize (Hno j).
    assert (0 <= j < Zlength src_str) as Hrange
      by (unfold string_lib.string_length in l; lia).
    specialize (Hno Hrange).
    contradiction.
  }
  subst j.
  unfold string_lib.store_string.
  split_pure_spatial.
  - unfold string_lib.c_string, string_lib.string_length in *.
    rewrite sublist_self by reflexivity.
    rewrite Zlength_app.
    cancel (CharArray.full src_pre (Zlength src_str + 1) (src_str ++ 0 :: nil)).
    rewrite CharArray.undef_seg_empty.
    cancel.
    sep_apply_l_atomic
      (helper_chararray_full_snoc dest_pre
         (Zlength dst_str + Zlength src_str) (dst_str ++ src_str) 0).
    + dump_pre_spatial.
      pose proof (Zlength_nonneg dst_str).
      pose proof (Zlength_nonneg src_str).
      lia.
    + cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma proof_of_strncat_entail_wit_1 : strncat_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel (string_lib.store_string dest_pre dst_str).
    cancel (CharArray.undef_seg dest_pre
              (string_lib.string_length dst_str + 1)
              (string_lib.string_length dst_str + n_pre + 1)).
    cancel (string_lib.store_string src_pre src_str).
  - split_pures.
    all: dump_pre_spatial;
      unfold string_lib.string_length in *;
      try pose proof (Zlength_nonneg dst_str);
      try pose proof (Zlength_nonneg src_str);
      auto; try lia.
Qed.

Lemma proof_of_strncat_entail_wit_2 : strncat_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold string_lib.store_string.
  split_pure_spatial.
  - cancel (CharArray.full dest_pre (string_lib.string_length dst_str + 1)
              (string_lib.c_string dst_str)).
    cancel (CharArray.full src_pre (string_lib.string_length src_str + 1)
              (string_lib.c_string src_str)).
    cancel (CharArray.undef_seg dest_pre
              (string_lib.string_length dst_str + 1)
              (string_lib.string_length dst_str + n_pre + 1)).
  - assert (Hi_lt : i < string_lib.string_length dst_str).
    {
      unfold string_lib.c_string in PreH1.
      unfold string_lib.string_length in *.
      destruct (Z_lt_ge_dec i (Zlength dst_str)); [ lia | ].
      rewrite app_Znth2 in PreH1 by lia.
      assert (Hi_off : i - Zlength dst_str = 0) by lia.
      rewrite Hi_off in PreH1.
      simpl in PreH1.
      contradiction PreH1; reflexivity.
    }
    assert (Hi_dst : Znth i dst_str 0 <> 0).
    {
      unfold string_lib.c_string in PreH1.
      rewrite app_Znth1 in PreH1 by (unfold string_lib.string_length in Hi_lt; lia).
      exact PreH1.
    }
    split_pures.
    all: dump_pre_spatial; auto; try lia.
    intros k Hk.
    destruct (Z_lt_ge_dec k i).
    + match goal with
      | Hprefix : forall k : Z, 0 <= k < i -> Znth k dst_str 0 <> 0 |- _ =>
          apply Hprefix; lia
      end.
    + assert (k = i) by lia.
      subst k.
      exact Hi_dst.
Qed.

Lemma proof_of_strncat_entail_wit_3 : strncat_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_eq : i = string_lib.string_length dst_str).
  {
    destruct (Z_lt_ge_dec i (string_lib.string_length dst_str));
      [ exfalso | lia ].
    assert (Hi_zero : Znth i dst_str 0 = 0).
    {
      unfold string_lib.c_string in PreH1.
      rewrite app_Znth1 in PreH1 by (unfold string_lib.string_length in l; lia).
      exact PreH1.
    }
    match goal with
    | Hvalid : string_lib.valid_string dst_str |- _ =>
        destruct Hvalid as [_ Hno]
    end.
    specialize (Hno i).
    assert (0 <= i < Zlength dst_str) as Hrange
      by (unfold string_lib.string_length in l; lia).
    specialize (Hno Hrange).
    contradiction.
  }
  subst i.
  unfold string_lib.store_string.
  split_pure_spatial.
  - rewrite Zsublist_nil by lia.
    rewrite app_nil_r.
    replace (string_lib.string_length dst_str + 0)
      with (string_lib.string_length dst_str) by lia.
    replace (string_lib.string_length dst_str + 0 + 1)
      with (string_lib.string_length dst_str + 1) by lia.
    sep_apply (CharArray.full_split_to_full dest_pre
                 (string_lib.string_length dst_str)
                 (string_lib.string_length dst_str + 1)
                 (string_lib.c_string dst_str) ltac:(lia)).
    unfold string_lib.c_string, string_lib.string_length in *.
    rewrite sublist_app_exact1.
    replace (sublist (Zlength dst_str) (Zlength dst_str + 1)
               (dst_str ++ 0 :: nil)) with (0 :: nil).
    2: {
      rewrite sublist_split_app_r with (len := Zlength dst_str) by lia.
      replace (Zlength dst_str - Zlength dst_str) with 0 by lia.
      replace (Zlength dst_str + 1 - Zlength dst_str) with 1 by lia.
      simpl.
      reflexivity.
    }
    cancel (CharArray.full dest_pre (Zlength dst_str) dst_str).
    replace (Zlength dst_str + 1 - Zlength dst_str) with 1 by lia.
    rewrite CharArray.full_unfold.
    replace (dest_pre + Zlength dst_str * sizeof ( CHAR ) + 0 * sizeof ( CHAR ))
      with (dest_pre + Zlength dst_str * sizeof ( CHAR )) by lia.
    cancel ((dest_pre + Zlength dst_str * sizeof ( CHAR )) # Char |-> 0).
    rewrite CharArray.seg_empty.
    Intros.
    cancel (CharArray.undef_seg dest_pre (Zlength dst_str + 1)
              (Zlength dst_str + n_pre + 1)).
    cancel (CharArray.full src_pre (Zlength src_str + 1) (src_str ++ 0 :: nil)).
  - split_pures.
    all: dump_pre_spatial; auto;
      try (unfold string_lib.string_length in *;
           pose proof (Zlength_nonneg src_str);
           pose proof (Zlength_nonneg dst_str);
           lia).
Qed.

Lemma proof_of_strncat_entail_wit_4 : strncat_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hj_lt : j < string_lib.string_length src_str) by
    (assert (j <> string_lib.string_length src_str) by
       (intro Hj; apply PreH1; rewrite Hj; unfold string_lib.c_string, string_lib.string_length;
        rewrite app_Znth2 by lia; rewrite Z.sub_diag; apply Znth0_cons);
     lia).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_strncat_entail_wit_5 : strncat_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst i.
  split_pure_spatial.
  - unfold string_lib.store_string, string_lib.string_length,
      string_lib.c_string in *.
    cancel (CharArray.full src_pre (Zlength src_str + 1) (src_str ++ 0 :: nil)).
    replace (Zlength dst_str + (j + 1) + 1) with (Zlength dst_str + j + 1 + 1) by lia. 
    cancel (CharArray.undef_seg dest_pre (Zlength dst_str + j + 1 + 1)
      (Zlength dst_str + n_pre + 1)).
    replace (((dst_str ++ sublist 0 j src_str) ++
                Znth j (src_str ++ 0 :: nil) 0 :: nil) ++ 0 :: nil)
      with ((dst_str ++ sublist 0 (j + 1) src_str) ++ 0 :: nil) by
      (rewrite app_Znth1 by lia;
       rewrite helper_sublist_snoc_Z with (d := 0) by lia;
       repeat rewrite app_assoc; reflexivity).
    sep_apply (CharArray.full_split_to_full dest_pre
                 (Zlength dst_str + (j + 1))
                 (Zlength dst_str + j + 1 + 1)
                 ((dst_str ++ sublist 0 (j + 1) src_str) ++ 0 :: nil) ltac:(lia)).
    replace (Zlength dst_str + j + 1 + 1 - (Zlength dst_str + (j + 1)))
      with 1 by lia.
    replace (Zlength dst_str + (j + 1))
          with (Zlength (dst_str ++ sublist 0 (j + 1) src_str)) at 2 4 by
          (rewrite Zlength_app, Zlength_sublist0; lia).
    rewrite sublist_app_exact1.
    cancel.
    replace (Zlength dst_str + j + 1 + 1)
          with (Zlength (dst_str ++ sublist 0 (j + 1) src_str) + 1) by
          (rewrite Zlength_app, Zlength_sublist0; lia).
    rewrite helper_sublist_app_last_Z.
    sep_apply helper_chararray_full_single_point.
    cancel.
  - unfold string_lib.string_length in *.
    split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_strncat_return_wit_1 : strncat_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst i.
  assert (j = n_pre) by lia; subst j.
  Exists (dst_str ++ sublist 0 n_pre src_str).
  split_pure_spatial.
  - unfold string_lib.store_string, string_lib.string_length,
      string_lib.c_string in *.
    replace (Zlength (dst_str ++ sublist 0 n_pre src_str) + 1)
      with (Zlength dst_str + n_pre + 1) by
      (rewrite Zlength_app, Zlength_sublist0; lia).
    cancel (CharArray.full src_pre (Zlength src_str + 1) (src_str ++ 0 :: nil)).
    cancel (CharArray.undef_seg dest_pre (Zlength dst_str + n_pre + 1)
      (Zlength dst_str + n_pre + 1)).
    apply helper_chararray_full_snoc.
    pose proof (Zlength_nonneg dst_str).
    lia.
  - split_pures; dump_pre_spatial; auto.
    unfold strncat_result, string_lib.string_length in *.
    split; [lia|].
    destruct (Z.eq_dec n_pre (Zlength src_str)).
    + left.
      split; [lia|].
      subst n_pre.
      rewrite sublist_self by reflexivity.
      reflexivity.
    + right.
      split; [lia|reflexivity].
Qed. 

Lemma proof_of_strncat_return_wit_2 : strncat_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst i.
  assert (j = string_lib.string_length src_str) as Hj.
  {
    apply helper_c_string_zero_index; auto; lia.
  }
  subst j.
  Exists (dst_str ++ src_str).
  split_pure_spatial.
  - unfold string_lib.store_string, string_lib.string_length,
      string_lib.c_string in *.
    replace (sublist 0 (Zlength src_str) src_str) with src_str by
      (symmetry; apply sublist_self; reflexivity).
    replace (Zlength (dst_str ++ src_str) + 1)
      with (Zlength dst_str + Zlength src_str + 1) by
      (rewrite Zlength_app; lia).
    cancel (CharArray.full src_pre (Zlength src_str + 1) (src_str ++ 0 :: nil)).
    cancel (CharArray.undef_seg dest_pre (Zlength dst_str + Zlength src_str + 1)
      (Zlength dst_str + n_pre + 1)).
    apply helper_chararray_full_snoc.
    pose proof (Zlength_nonneg dst_str).
    pose proof (Zlength_nonneg src_str).
    lia.
  - split_pures; dump_pre_spatial; auto.
    unfold strncat_result, string_lib.string_length in *.
    split; [lia|].
    left.
    split; [lia|reflexivity].
Qed. 
