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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P018_1146B_hate_a_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P018_1146B_hate_a_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P018_1146B_hate_a_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_9_split_goal_1 : solver_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (nonnegative_land_one_zero_div2__parity_setup k PreH8 PreH12)
    as (Hquot_nonneg & Hexact & Hquot_le).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_9_split_goal_2 : solver_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (nonnegative_land_one_zero_div2__parity_setup k PreH8 PreH12)
    as (Hquot_nonneg & Hexact & Hquot_le).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    assert (Hvalid : valid_string given_data);
    [ unfold valid_string, all_ascii, no_inner_nul;
      split; intros k Hk; destruct (PreH4 k Hk); lia
    | unfold string_length; lia ]).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    assert (Hvalid : valid_string given_data);
    [ unfold valid_string, all_ascii, no_inner_nul;
      split; intros k Hk; destruct (PreH4 k Hk); lia
    | unfold string_length; lia ]).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold valid_string, all_ascii, no_inner_nul.
  split; intros k Hk; destruct (PreH4 k Hk); lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold c_string, string_length.
  replace (CharArray.undef_full out_pre (Zlength given_data + 1)) with
    (CharArray.undef_full
       (out_pre + 0 * sizeof (CHAR)) (Zlength given_data + 1 - 0)) by
    (f_equal; lia).
  sep_apply_r_atomic
    (CharArray.undef_seg_to_undef_full
       out_pre 0 (Zlength given_data + 1)).
  cancel.
  sep_apply_r_atomic
    (CharArray.undef_full_split_to_undef_seg
       out_pre (Zlength given_data + 1) 100005 ltac:(lia)).
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - unfold c_string, string_length.
    replace (CharArray.undef_full out_pre (Zlength given_data + 1)) with
        (CharArray.undef_full
           (out_pre + 0 * sizeof (CHAR)) (Zlength given_data + 1 - 0)) by
        (f_equal; lia).
    sep_apply_r_atomic
      (CharArray.undef_seg_to_undef_full
         out_pre 0 (Zlength given_data + 1)).
    cancel.
    sep_apply_r_atomic
      (CharArray.undef_full_split_to_undef_seg
         out_pre (Zlength given_data + 1) 100005 ltac:(lia)).
    cancel.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_spatial : solver_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold string_length, c_string.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite app_Znth1 by lia.
  assert (Hcurrent : Znth i given_data 0 <> 97).
  {
    rewrite <- (@app_Znth1 Z 0 given_data (0 :: nil) i) by lia.
    exact PreH1.
  }
  eapply filtered_prefix_step_non_a__filter_update.
  - lia.
  - exact Hcurrent.
  - exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_2 : solver_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcurrent : Znth i given_data 0 = 97).
  {
    rewrite <- (@app_Znth1 Z 0 given_data (0 :: nil) i) by lia.
    exact PreH1.
  }
  eapply filtered_prefix_step_a__filter_update.
  - lia.
  - exact Hcurrent.
  - exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NoAInterval.
  intros j Hj.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (nonnegative_land_one_zero_div2__parity_setup k PreH8 PreH12)
    as (Hquot_nonneg & Hexact & Hquot_le).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (nonnegative_land_one_zero_div2__parity_setup k PreH8 PreH12)
    as (Hquot_nonneg & Hexact & Hquot_le).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (nonnegative_land_one_zero_div2__parity_setup k PreH8 PreH12)
    as (Hquot_nonneg & Hexact & Hquot_le).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (nonnegative_land_one_zero_div2__parity_setup k PreH8 PreH12)
    as (Hquot_nonneg & Hexact & Hquot_le).
  exact Hexact.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_6 : solver_entail_wit_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (nonnegative_land_one_zero_div2__parity_setup k PreH8 PreH12)
    as (Hquot_nonneg & Hexact & Hquot_le).
  exact Hquot_nonneg.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_7 : solver_entail_wit_4_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace n with i by lia.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_8 : solver_entail_wit_4_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH5 j H).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_7.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_8.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NoAInterval in *.
  intros j Hj.
  destruct Hj as [Hlo Hhi].
  assert (j < i \/ j = i) as [Hlt | Heq] by lia.
  - apply PreH19. lia.
  - subst j.
    unfold Znth in PreH1.
    rewrite app_nth1 in PreH1.
    + exact PreH1.
    + apply Z2Nat.inj_lt in PreH3; try lia.
      rewrite PreH4, Zlength_correct in PreH3.
      rewrite Nat2Z.id in PreH3.
      exact PreH3.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MatchedSuffixPrefix.
  intros j Hj.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NoAInterval in *.
  intros j Hj.
  apply PreH17.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold MatchedSuffixPrefix in *.
  intros j Hj.
  assert (j < i \/ j = i) as [Hlt | Heq] by lia.
  - rewrite <- PreH14.
    apply PreH20.
    lia.
  - subst j.
    rewrite <- PreH14.
    unfold Znth in PreH1 |- *.
    rewrite app_nth1 in PreH1.
    + exact PreH1.
    + assert (0 <= prefix + i < n) as Hbound by lia.
      destruct Hbound as [Hnonneg Hltbound].
      apply Z2Nat.inj_lt in Hltbound; try lia.
      rewrite PreH4, Zlength_correct, Nat2Z.id in Hltbound.
      exact Hltbound.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = suffix) by lia.
  subst i.
  set (result := sublist 0 prefix given_data).
  assert (Hgenerated :
      given_data = result ++
        filter (fun c => negb (Z.eqb c 97)) result).
  { unfold result.
    eapply matched_result_shape__result_spec; eauto; lia. }
  assert (Hresult_len : Zlength result = prefix).
  { unfold result. rewrite Zlength_sublist by lia. lia. }
  Exists result.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray.full_split_to_full out_pre
         (Zlength result + 1) (Zlength given_data + 1)
         (replace_Znth prefix 0 (given_data ++ (0 :: nil)))).
    + dump_pre_spatial. lia.
    + replace
        (sublist 0 (Zlength result + 1)
          (replace_Znth prefix 0 (given_data ++ (0 :: nil))))
        with (result ++ (0 :: nil)).
      2: { symmetry. apply written_prefix__result_spec.
           - lia.
           - symmetry. exact Hresult_len.
           - exact Hgenerated. }
      sep_apply_l_atomic
        (CharArray.full_to_undef_full
          (out_pre + (Zlength result + 1) * sizeof(CHAR))
          (Zlength given_data + 1 - (Zlength result + 1))
          (sublist (Zlength result + 1) (Zlength given_data + 1)
            (replace_Znth prefix 0 (given_data ++ (0 :: nil))))).
      sep_apply_l_atomic
        (CharArray.undef_full_to_undef_seg
          (out_pre + (Zlength result + 1) * sizeof(CHAR))
          (Zlength given_data + 1 - (Zlength result + 1))).
      rewrite <- (CharArray.undef_seg_shift out_pre
        (Zlength result + 1) 0
        (Zlength given_data + 1 - (Zlength result + 1))).
      replace (Zlength result + 1 + 0) with (Zlength result + 1) by lia.
      replace
        (Zlength result + 1 +
          (Zlength given_data + 1 - (Zlength result + 1)))
        with (Zlength given_data + 1) by lia.
      sep_apply_l_atomic
        (CharArray.undef_seg_merge_to_undef_seg out_pre
          (Zlength result + 1) (Zlength given_data + 1) 100005).
      * dump_pre_spatial. lia.
      * cancel.
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      unfold Spec.
      left.
      exists result.
      split; [reflexivity |].
      exact Hgenerated.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros source Hgen.
  destruct (generates_filter_twice__result_spec source given_data Hgen)
    as [Htwice Htwice_len].
  destruct (generates_prefix_suffix_shape__result_spec source given_data Hgen)
    as [Hgiven_len [Hsuffix_shape Hfilter_prefix]].
  unfold FilteredPrefix in PreH12.
  rewrite (sublist_self given_data n PreH5) in PreH12.
  assert (Hsuffix_len :
      suffix = Zlength (filter (fun c => negb (Z.eqb c 97)) source)).
  { rewrite <- PreH12 in Htwice_len. lia. }
  assert (Hsource_len : prefix = Zlength source) by lia.
  apply PreH2.
  rewrite PreH12, Htwice.
  rewrite app_Znth1 by lia.
  rewrite app_Znth1 by lia.
  rewrite Hsource_len.
  symmetry.
  apply Hsuffix_shape.
  lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros source Hgen.
  destruct (generates_filter_twice__result_spec source given_data Hgen)
    as [Htwice Htwice_len].
  destruct (generates_prefix_suffix_shape__result_spec source given_data Hgen)
    as [Hgiven_len [Hsuffix_shape Hfilter_prefix]].
  unfold FilteredPrefix in PreH12.
  rewrite (sublist_self given_data n PreH5) in PreH12.
  assert (Hsuffix_len :
      suffix = Zlength (filter (fun c => negb (Z.eqb c 97)) source)).
  { rewrite <- PreH12 in Htwice_len. lia. }
  assert (Hsource_len : prefix = Zlength source) by lia.
  rewrite app_Znth1 in PreH2 by lia.
  pose proof (filter_contains_no_a__result_spec source
    (i - Zlength source) ltac:(lia)) as Hnoa.
  apply Hnoa.
  rewrite <- (Hsuffix_shape (i - Zlength source) ltac:(lia)).
  replace (Zlength source + (i - Zlength source)) with i by lia.
  exact PreH2.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros source Hgen.
  destruct (generates_filter_twice__result_spec source given_data Hgen)
    as [Htwice Htwice_len].
  assert (i = n) by lia. subst i.
  unfold FilteredPrefix in PreH13.
  rewrite (sublist_self given_data n PreH4) in PreH13.
  assert (Hk :
      k = 2 * Zlength (filter (fun c => negb (Z.eqb c 97)) source)).
  { rewrite <- PreH13 in Htwice_len. lia. }
  apply PreH14.
  rewrite Hk.
  apply even_land_one__result_spec.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (CharArray.full_Zlength (&( "stripped" )) k filtered_2).
  Intros_p Hlen.
  assert (Hnonneg : 0 <= k).
  { rewrite <- Hlen. apply Zlength_nonneg. }
  prop_apply (CharArray.undef_seg_valid (&( "stripped" )) k 100005).
  Intros_p Hbound.
  Exists filtered_2.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.full_to_undef_full
                          (&( "stripped" )) k filtered_2).
    sep_apply_l_atomic (CharArray.undef_full_to_undef_seg
                          (&( "stripped" )) k).
    sep_apply_l_atomic (CharArray.undef_seg_merge_to_undef_full
                          (&( "stripped" )) 0 k 100005
                          (conj Hnonneg Hbound)).
    replace (&( "stripped" ) + 0 * sizeof (CHAR))
      with (&( "stripped" )) by lia.
    replace (100005 - 0) with 100005 by lia.
    cancel.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (CharArray.full_Zlength (&( "stripped" )) k filtered_2).
  Intros_p Hlen.
  assert (Hnonneg : 0 <= k).
  { rewrite <- Hlen. apply Zlength_nonneg. }
  prop_apply (CharArray.undef_seg_valid (&( "stripped" )) k 100005).
  Intros_p Hbound.
  Exists filtered_2.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.full_to_undef_full
                          (&( "stripped" )) k filtered_2).
    sep_apply_l_atomic (CharArray.undef_full_to_undef_seg
                          (&( "stripped" )) k).
    sep_apply_l_atomic (CharArray.undef_seg_merge_to_undef_full
                          (&( "stripped" )) 0 k 100005
                          (conj Hnonneg Hbound)).
    replace (&( "stripped" ) + 0 * sizeof (CHAR))
      with (&( "stripped" )) by lia.
    replace (100005 - 0) with 100005 by lia.
    cancel.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_which_implies_wit_3 : solver_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (CharArray.full_Zlength (&( "stripped" )) k filtered_2).
  Intros_p Hlen.
  assert (Hnonneg : 0 <= k).
  { rewrite <- Hlen. apply Zlength_nonneg. }
  prop_apply (CharArray.undef_seg_valid (&( "stripped" )) k 100005).
  Intros_p Hbound.
  Exists filtered_2.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.full_to_undef_full
                          (&( "stripped" )) k filtered_2).
    sep_apply_l_atomic (CharArray.undef_full_to_undef_seg
                          (&( "stripped" )) k).
    sep_apply_l_atomic (CharArray.undef_seg_merge_to_undef_full
                          (&( "stripped" )) 0 k 100005
                          (conj Hnonneg Hbound)).
    replace (&( "stripped" ) + 0 * sizeof (CHAR))
      with (&( "stripped" )) by lia.
    replace (100005 - 0) with 100005 by lia.
    cancel.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_which_implies_wit_4 : solver_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (CharArray.full_Zlength (&( "stripped" )) k filtered_2).
  Intros_p Hlen.
  assert (Hnonneg : 0 <= k).
  { rewrite <- Hlen. apply Zlength_nonneg. }
  prop_apply (CharArray.undef_seg_valid (&( "stripped" )) k 100005).
  Intros_p Hbound.
  Exists filtered_2.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.full_to_undef_full
                          (&( "stripped" )) k filtered_2).
    sep_apply_l_atomic (CharArray.undef_full_to_undef_seg
                          (&( "stripped" )) k).
    sep_apply_l_atomic (CharArray.undef_seg_merge_to_undef_full
                          (&( "stripped" )) 0 k 100005
                          (conj Hnonneg Hbound)).
    replace (&( "stripped" ) + 0 * sizeof (CHAR))
      with (&( "stripped" )) by lia.
    replace (100005 - 0) with 100005 by lia.
    cancel.
  - dump_pre_spatial. lia.
Qed.
