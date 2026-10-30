From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P087_1513F_swapping_problem_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P087_1513F_swapping_problem_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P087_1513F_swapping_problem_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P087_1513F_swapping_problem_lib.
Local Open Scope sac.

Lemma proof_of_overlap_safety_wit_23_split_goal_1 : overlap_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (prefix_right_maxima_value_bounds__priority_overlap_safety_bounds
       sorted prefix nb_pre (lo - 1) PreH15 PreH19 PreH21 ltac:(lia))
    as Hprefix_bounds.
  pose proof
    (segments_bounded_znth_bounds__priority_overlap_safety_bounds
       left i __default__Prod_Z_Z PreH17 ltac:(lia)) as Hleft_bounds.
  destruct Hprefix_bounds as [Hprefix_lower Hprefix_upper].
  destruct Hleft_bounds as [Hleft_lower [Hleft_proper Hleft_upper]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_overlap_safety_wit_23_split_goal_2 : overlap_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (prefix_right_maxima_value_bounds__priority_overlap_safety_bounds
       sorted prefix nb_pre (lo - 1) PreH15 PreH19 PreH21 ltac:(lia))
    as Hprefix_bounds.
  pose proof
    (segments_bounded_znth_bounds__priority_overlap_safety_bounds
       left i __default__Prod_Z_Z PreH17 ltac:(lia)) as Hleft_bounds.
  destruct Hprefix_bounds as [Hprefix_lower Hprefix_upper].
  destruct Hleft_bounds as [Hleft_lower [Hleft_proper Hleft_upper]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_overlap_safety_wit_23 : overlap_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_overlap_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_overlap_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_overlap_safety_wit_24_split_goal_1 : overlap_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (segments_bounded_znth_bounds__priority_overlap_safety_bounds
       left i __default__Prod_Z_Z PreH17 ltac:(lia)) as Hleft_bounds.
  destruct Hleft_bounds as [Hleft_lower [Hleft_proper Hleft_upper]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_overlap_safety_wit_24_split_goal_2 : overlap_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (segments_bounded_znth_bounds__priority_overlap_safety_bounds
       left i __default__Prod_Z_Z PreH17 ltac:(lia)) as Hleft_bounds.
  destruct Hleft_bounds as [Hleft_lower [Hleft_proper Hleft_upper]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_overlap_safety_wit_24 : overlap_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_overlap_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_overlap_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_overlap_entail_wit_1 : overlap_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists sorted_2 (@nil Z).
  unfold PrefixRightMaxima.
  simpl Zlength.
  split_pure_spatial.
  - rewrite (IntArray.full_empty retval 0).
    replace (retval + (0 * sizeof(INT))) with retval by lia.
    replace (nb_pre - 0) with nb_pre by lia.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - split_pures.
    all: dump_pre_spatial.
    all: (try lia; try assumption).
    + reflexivity.
    + split; [reflexivity | intros; lia].
Qed.

Lemma proof_of_overlap_entail_wit_2 : overlap_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists sorted_2 prefix_2.
  split_pure_spatial.
  - cancel (SegArray.full a_pre na_pre left).
    unfold SegArray.full, store_array.
    sep_apply_l_atomic
      (store_array_rec_split_to_rec__overlap_prefix_construction
         (Z * Z) store_segment b_pre 0 i nb_pre sorted_2 ltac:(lia)).
    replace (i - 0) with i by lia.
    replace (nb_pre - 0) with nb_pre by lia.
    sep_apply_l_atomic
      (store_array_rec_split_to_rec__overlap_prefix_construction
         (Z * Z) store_segment b_pre i (i + 1) nb_pre
         (sublist i nb_pre sorted_2) ltac:(lia)).
    replace (i + 1 - i) with 1 by lia.
    rewrite !Zsublist_Zsublist by lia.
    replace (0 + i) with i by lia.
    replace (1 + i) with (i + 1) by lia.
    replace (nb_pre - i + i) with nb_pre by lia.
    rewrite (sublist_single __default__Prod_Z_Z i sorted_2) by lia.
    cbn [store_array_rec store_segment].
    sep_apply_l_atomic
      (segarray_rec_shift__overlap_prefix_construction
         b_pre (i + 1) (i + 1) nb_pre
         (sublist (i + 1) nb_pre sorted_2)).
    replace (i + 1 - (i + 1)) with 0 by lia.
    replace (nb_pre - (i + 1)) with ((nb_pre - i) - 1) by lia.
    Intros_p Hseg_end.
    Intros_p Hseg_nil.
    sep_apply_l_atomic
      (IntArray.undef_full_split_to_undef_full
         (pref + i * sizeof(INT)) 1 (nb_pre - i) ltac:(lia)).
    replace (pref + i * sizeof(INT) + 1 * sizeof(INT)) with
      (pref + (i + 1) * sizeof(INT)) by ring.
    rewrite (IntArray.undef_full_unfold
      (pref + i * sizeof(INT)) 0 (@nil Z)) by lia.
    rewrite (IntArray.undef_seg_empty (pref + i * sizeof(INT)) 1).
    unfold store_segment.
    replace (pref + i * sizeof(INT) + 0 * sizeof(INT)) with
      (pref + i * sizeof(INT)) by ring.
    asrt_simpl.
    cancel (IntArray.full pref i prefix_2).
    cancel (IntArray.undef_full
      (pref + (i + 1) * sizeof(INT)) (nb_pre - i - 1)).
    cancel ((pref + i * sizeof(INT)) # Int |->_).
    cancel (store_array_rec store_segment b_pre 0 i
      (sublist 0 i sorted_2)).
    cancel (store_array_rec store_segment
      (b_pre + (i + 1) * sizeof_alias_type "<anonymous struct>")
      0 (nb_pre - i - 1) (sublist (i + 1) nb_pre sorted_2)).
    reflexivity.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_overlap_entail_wit_3_1 : overlap_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists sorted_2
    (prefix_2 ++ (Znth (i - 1) prefix_2 0 :: nil)).
  split_pure_spatial.
  - cancel (SegArray.full a_pre na_pre left).
    unfold SegArray.full, store_array.
    sep_apply_r_atomic
      (store_array_rec_sublist_merge_to_rec__overlap_prefix_construction
         (Z * Z) store_segment b_pre 0 i nb_pre sorted_2
         ltac:(lia) ltac:(lia)).
    replace (i - 0) with i by lia.
    replace (nb_pre - 0) with nb_pre by lia.
    sepcon_assoc_change.
    sep_apply_r_atomic
      (store_array_rec_sublist_merge_to_rec__overlap_prefix_construction
         (Z * Z) store_segment b_pre i (i + 1) nb_pre
         (sublist i nb_pre sorted_2) ltac:(lia)
         ltac:(rewrite Zlength_sublist; lia)).
    replace (i + 1 - i) with 1 by lia.
    rewrite !Zsublist_Zsublist by lia.
    replace (0 + i) with i by lia.
    replace (1 + i) with (i + 1) by lia.
    replace (nb_pre - i + i) with nb_pre by lia.
    rewrite (sublist_single __default__Prod_Z_Z i sorted_2) by lia.
    cbn [store_array_rec store_segment].
    sep_apply_l_atomic
      (segarray_rec_shift__overlap_prefix_construction
         (b_pre + (i + 1) * sizeof_alias_type "<anonymous struct>")
         (-(i + 1)) 0 (nb_pre - i - 1)
         (sublist (i + 1) nb_pre sorted_2)).
    assert (Hsize :
      sizeof_front_end_type (FET_alias "<anonymous struct>") =
      sizeof_alias_type "<anonymous struct>") by reflexivity.
    rewrite Hsize.
    replace
      (b_pre + (i + 1) * sizeof_alias_type "<anonymous struct>" +
       -(i + 1) * sizeof_alias_type "<anonymous struct>")
      with b_pre by ring.
    replace (0 - -(i + 1)) with (i + 1) by lia.
    replace (nb_pre - i - 1 - -(i + 1)) with nb_pre by lia.
    sepcon_assoc_change.
    sep_apply_l_atomic
      (int_full_snoc_cell_merge__overlap_prefix_construction
         pref i prefix_2 (Znth (i - 1) prefix_2 0)
         PreH11).
    split_pure_spatial.
    + unfold store_segment.
      rewrite Hsize.
      replace (nb_pre - (i + 1)) with (nb_pre - i - 1) by lia.
      cancel (IntArray.full pref (i + 1)
        (prefix_2 ++ (Znth (i - 1) prefix_2 0 :: nil))).
      cancel (IntArray.undef_full
        (pref + (i + 1) * sizeof(INT)) (nb_pre - i - 1)).
      cancel (store_array_rec store_segment b_pre 0 i
        (sublist 0 i sorted_2)).
      cancel (store_array_rec store_segment b_pre (i + 1) nb_pre
        (sublist (i + 1) nb_pre sorted_2)).
      reflexivity.
    + split_pures; dump_pre_spatial; reflexivity.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
    all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    assert (Hnew :
      snd (Znth i sorted_2 (0, 0)) < Znth (i - 1) prefix_2 0).
    { rewrite (Znth_indep sorted_2 i (0, 0) __default__Prod_Z_Z) by lia.
      lia. }
    rewrite <- (Z.max_l
      (Znth (i - 1) prefix_2 0)
      (snd (Znth i sorted_2 (0, 0)))) by lia.
    apply prefix_right_maxima_snoc__overlap_prefix_construction.
    + lia.
    + exact PreH17.
Qed.

Lemma proof_of_overlap_entail_wit_3_2 : overlap_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnth :
    Znth i sorted_2 __default__Prod_Z_Z = Znth i sorted_2 (0, 0)).
  { apply Znth_indep. lia. }
  rewrite Hnth in *.
  Exists sorted_2
    (prefix_2 ++ (snd (Znth i sorted_2 (0, 0)) :: nil)).
  split_pure_spatial.
  - cancel (SegArray.full a_pre na_pre left).
    unfold SegArray.full, store_array.
    sep_apply_r_atomic
      (store_array_rec_sublist_merge_to_rec__overlap_prefix_construction
         (Z * Z) store_segment b_pre 0 i nb_pre sorted_2
         ltac:(lia) ltac:(lia)).
    replace (i - 0) with i by lia.
    replace (nb_pre - 0) with nb_pre by lia.
    sepcon_assoc_change.
    sep_apply_r_atomic
      (store_array_rec_sublist_merge_to_rec__overlap_prefix_construction
         (Z * Z) store_segment b_pre i (i + 1) nb_pre
         (sublist i nb_pre sorted_2) ltac:(lia)
         ltac:(rewrite Zlength_sublist; lia)).
    replace (i + 1 - i) with 1 by lia.
    rewrite !Zsublist_Zsublist by lia.
    replace (0 + i) with i by lia.
    replace (1 + i) with (i + 1) by lia.
    replace (nb_pre - i + i) with nb_pre by lia.
    rewrite (sublist_single __default__Prod_Z_Z i sorted_2) by lia.
    cbn [store_array_rec store_segment].
    sep_apply_l_atomic
      (segarray_rec_shift__overlap_prefix_construction
         (b_pre + (i + 1) * sizeof_alias_type "<anonymous struct>")
         (-(i + 1)) 0 (nb_pre - i - 1)
         (sublist (i + 1) nb_pre sorted_2)).
    assert (Hsize :
      sizeof_front_end_type (FET_alias "<anonymous struct>") =
      sizeof_alias_type "<anonymous struct>") by reflexivity.
    rewrite Hsize.
    replace
      (b_pre + (i + 1) * sizeof_alias_type "<anonymous struct>" +
       -(i + 1) * sizeof_alias_type "<anonymous struct>")
      with b_pre by ring.
    replace (0 - -(i + 1)) with (i + 1) by lia.
    replace (nb_pre - i - 1 - -(i + 1)) with nb_pre by lia.
    sepcon_assoc_change.
    sep_apply_l_atomic
      (int_full_snoc_cell_merge__overlap_prefix_construction
         pref i prefix_2 (snd (Znth i sorted_2 (0, 0)))
         PreH10).
    split_pure_spatial.
    + unfold store_segment.
      rewrite Hsize.
      rewrite Hnth.
      replace (nb_pre - (i + 1)) with (nb_pre - i - 1) by lia.
      cancel (IntArray.full pref (i + 1)
        (prefix_2 ++ (snd (Znth i sorted_2 (0, 0)) :: nil))).
      cancel (IntArray.undef_full
        (pref + (i + 1) * sizeof(INT)) (nb_pre - i - 1)).
      cancel (store_array_rec store_segment b_pre 0 i
        (sublist 0 i sorted_2)).
      cancel (store_array_rec store_segment b_pre (i + 1) nb_pre
        (sublist (i + 1) nb_pre sorted_2)).
      reflexivity.
    + split_pures; dump_pre_spatial; reflexivity.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
    all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    assert (Hprefix_nil : prefix_2 = nil).
    { destruct prefix_2 as [|value values].
      - reflexivity.
      - rewrite Zlength_cons in PreH10.
        pose proof (Zlength_nonneg values). lia. }
    rewrite Hprefix_nil. simpl.
    rewrite PreH1.
    apply prefix_right_maxima_singleton__overlap_prefix_construction.
    lia.
Qed.

Lemma proof_of_overlap_entail_wit_3_3 : overlap_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnth :
    Znth i sorted_2 __default__Prod_Z_Z = Znth i sorted_2 (0, 0)).
  { apply Znth_indep. lia. }
  rewrite Hnth in *.
  Exists sorted_2
    (prefix_2 ++ (snd (Znth i sorted_2 (0, 0)) :: nil)).
  split_pure_spatial.
  - cancel (SegArray.full a_pre na_pre left).
    unfold SegArray.full, store_array.
    sep_apply_r_atomic
      (store_array_rec_sublist_merge_to_rec__overlap_prefix_construction
         (Z * Z) store_segment b_pre 0 i nb_pre sorted_2
         ltac:(lia) ltac:(lia)).
    replace (i - 0) with i by lia.
    replace (nb_pre - 0) with nb_pre by lia.
    sepcon_assoc_change.
    sep_apply_r_atomic
      (store_array_rec_sublist_merge_to_rec__overlap_prefix_construction
         (Z * Z) store_segment b_pre i (i + 1) nb_pre
         (sublist i nb_pre sorted_2) ltac:(lia)
         ltac:(rewrite Zlength_sublist; lia)).
    replace (i + 1 - i) with 1 by lia.
    rewrite !Zsublist_Zsublist by lia.
    replace (0 + i) with i by lia.
    replace (1 + i) with (i + 1) by lia.
    replace (nb_pre - i + i) with nb_pre by lia.
    rewrite (sublist_single __default__Prod_Z_Z i sorted_2) by lia.
    cbn [store_array_rec store_segment].
    sep_apply_l_atomic
      (segarray_rec_shift__overlap_prefix_construction
         (b_pre + (i + 1) * sizeof_alias_type "<anonymous struct>")
         (-(i + 1)) 0 (nb_pre - i - 1)
         (sublist (i + 1) nb_pre sorted_2)).
    assert (Hsize :
      sizeof_front_end_type (FET_alias "<anonymous struct>") =
      sizeof_alias_type "<anonymous struct>") by reflexivity.
    rewrite Hsize.
    replace
      (b_pre + (i + 1) * sizeof_alias_type "<anonymous struct>" +
       -(i + 1) * sizeof_alias_type "<anonymous struct>")
      with b_pre by ring.
    replace (0 - -(i + 1)) with (i + 1) by lia.
    replace (nb_pre - i - 1 - -(i + 1)) with nb_pre by lia.
    sepcon_assoc_change.
    sep_apply_l_atomic
      (int_full_snoc_cell_merge__overlap_prefix_construction
         pref i prefix_2 (snd (Znth i sorted_2 (0, 0)))
         PreH11).
    split_pure_spatial.
    + unfold store_segment.
      rewrite Hsize.
      rewrite Hnth.
      replace (nb_pre - (i + 1)) with (nb_pre - i - 1) by lia.
      cancel (IntArray.full pref (i + 1)
        (prefix_2 ++ (snd (Znth i sorted_2 (0, 0)) :: nil))).
      cancel (IntArray.undef_full
        (pref + (i + 1) * sizeof(INT)) (nb_pre - i - 1)).
      cancel (store_array_rec store_segment b_pre 0 i
        (sublist 0 i sorted_2)).
      cancel (store_array_rec store_segment b_pre (i + 1) nb_pre
        (sublist (i + 1) nb_pre sorted_2)).
      reflexivity.
    + split_pures; dump_pre_spatial; reflexivity.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
    all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    rewrite <- (Z.max_r
      (Znth (i - 1) prefix_2 0)
      (snd (Znth i sorted_2 (0, 0)))) by lia.
    apply prefix_right_maxima_snoc__overlap_prefix_construction.
    + lia.
    + exact PreH17.
Qed.

Lemma proof_of_overlap_entail_wit_4 : overlap_entail_wit_4.
Proof.
  unfold overlap_entail_wit_4.
  left.
  intros.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = nb_pre) by lia.
  subst i.
  Exists prefix_2 sorted_2.
  rewrite Hi in *.
  replace (nb_pre - nb_pre) with 0 by lia.
  rewrite IntArray.undef_full_empty.
  split_pure_spatial.
  - cancel (SegArray.full a_pre na_pre left).
    cancel (SegArray.full b_pre nb_pre sorted_2).
    cancel (IntArray.full pref nb_pre prefix_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
    apply directed_overlap_maximum_prefix_zero__overlap_prefix_construction.
Qed.

Lemma proof_of_overlap_entail_wit_5_split_goal_1 : overlap_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH12.
  apply upper_bound_bracket_initial__overlap_binary_search.
Qed.

Lemma proof_of_overlap_entail_wit_5 : overlap_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_overlap_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_overlap_entail_wit_6 : overlap_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmid_bounds : lo <= (lo + hi) ÷ 2 < hi).
  {
    rewrite zdiv_equiv by lia.
    pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
    pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
    lia.
  }
  assert (Hmid_array : 0 <= (lo + hi) ÷ 2 < nb_pre) by lia.
  Exists prefix_2 sorted_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (seg_array_full_split_at__overlap_binary_search
         a_pre na_pre left i __default__Prod_Z_Z (eq_sym PreH2) ltac:(lia)).
    sep_apply_l_atomic
      (seg_array_full_split_at__overlap_binary_search
         b_pre nb_pre sorted_2 ((lo + hi) ÷ 2) __default__Prod_Z_Z
         PreH15 Hmid_array).
    unfold store_segment.
    cancel ((&(((a_pre + (i * sizeof ("<anonymous struct>"))))
                  # "anonymous struct 1" ->ₛ "l")) # Int
              |-> fst (Znth i left __default__Prod_Z_Z)).
    cancel ((&(((a_pre + (i * sizeof ("<anonymous struct>"))))
                  # "anonymous struct 1" ->ₛ "r")) # Int
              |-> snd (Znth i left __default__Prod_Z_Z)).
    cancel ((&(((b_pre + (((lo + hi) ÷ 2) * sizeof ("<anonymous struct>"))))
                  # "anonymous struct 1" ->ₛ "l")) # Int
              |-> fst (Znth ((lo + hi) ÷ 2) sorted_2 __default__Prod_Z_Z)).
    cancel ((&(((b_pre + (((lo + hi) ÷ 2) * sizeof ("<anonymous struct>"))))
                  # "anonymous struct 1" ->ₛ "r")) # Int
              |-> snd (Znth ((lo + hi) ÷ 2) sorted_2 __default__Prod_Z_Z)).
    cancel (SegArray.full a_pre i (sublist 0 i left)).
    cancel (SegArray.full
      (a_pre + (i + 1) * sizeof ("<anonymous struct>"))
      (na_pre - i - 1) (sublist (i + 1) na_pre left)).
    cancel (SegArray.full b_pre ((lo + hi) ÷ 2)
      (sublist 0 ((lo + hi) ÷ 2) sorted_2)).
    cancel (SegArray.full
      (b_pre + (((lo + hi) ÷ 2) + 1) * sizeof ("<anonymous struct>"))
      (nb_pre - ((lo + hi) ÷ 2) - 1)
      (sublist (((lo + hi) ÷ 2) + 1) nb_pre sorted_2)).
    cancel (IntArray.full pref nb_pre prefix_2).
  - split_pures; dump_pre_spatial; try assumption; try lia; int_auto.
Qed.

Lemma proof_of_overlap_entail_wit_7_1 : overlap_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmd_default :
    Znth md sorted_2 __default__Prod_Z_Z = Znth md sorted_2 (0, 0)).
  {
    apply Znth_indep.
    rewrite PreH16.
    lia.
  }
  assert (Hmd_key :
    fst (Znth md sorted_2 (0, 0)) <=
    fst (Znth i left __default__Prod_Z_Z)).
  { rewrite <- Hmd_default. lia. }
  assert (Hbracket :
    UpperBoundBracket sorted_2 (fst (Znth i left __default__Prod_Z_Z))
      (md + 1) hi).
  {
    eapply upper_bound_bracket_advance_lo__overlap_binary_search.
    - exact PreH21.
    - exact PreH24.
    - exact PreH10.
    - exact PreH11.
    - exact PreH12.
    - rewrite PreH16. exact PreH13.
    - exact Hmd_key.
  }
  Exists prefix_2 sorted_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (seg_array_full_merge_at_flat__overlap_binary_search
         a_pre na_pre left i __default__Prod_Z_Z (eq_sym PreH2) ltac:(lia)).
    sep_apply_l_atomic
      (seg_array_full_merge_at_flat__overlap_binary_search
         b_pre nb_pre sorted_2 md __default__Prod_Z_Z PreH16 ltac:(lia)).
    cancel (SegArray.full a_pre na_pre left).
    cancel (SegArray.full b_pre nb_pre sorted_2).
    cancel (IntArray.full pref nb_pre prefix_2).
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_overlap_entail_wit_7_2 : overlap_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmd_default :
    Znth md sorted_2 __default__Prod_Z_Z = Znth md sorted_2 (0, 0)).
  {
    apply Znth_indep.
    rewrite PreH16.
    lia.
  }
  assert (Hkey_md :
    fst (Znth i left __default__Prod_Z_Z) <
    fst (Znth md sorted_2 (0, 0))).
  { rewrite <- Hmd_default. lia. }
  assert (Hbracket :
    UpperBoundBracket sorted_2 (fst (Znth i left __default__Prod_Z_Z))
      lo md).
  {
    eapply upper_bound_bracket_lower_hi__overlap_binary_search.
    - exact PreH21.
    - exact PreH24.
    - exact PreH10.
    - exact PreH11.
    - exact PreH12.
    - rewrite PreH16. exact PreH13.
    - exact Hkey_md.
  }
  Exists prefix_2 sorted_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (seg_array_full_merge_at_flat__overlap_binary_search
         a_pre na_pre left i __default__Prod_Z_Z (eq_sym PreH2) ltac:(lia)).
    sep_apply_l_atomic
      (seg_array_full_merge_at_flat__overlap_binary_search
         b_pre nb_pre sorted_2 md __default__Prod_Z_Z PreH16 ltac:(lia)).
    cancel (SegArray.full a_pre na_pre left).
    cancel (SegArray.full b_pre nb_pre sorted_2).
    cancel (IntArray.full pref nb_pre prefix_2).
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_overlap_entail_wit_8 : overlap_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists prefix_2 sorted_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (seg_array_full_split_at__overlap_binary_search
         a_pre na_pre left i __default__Prod_Z_Z (eq_sym PreH2) ltac:(lia)).
    unfold store_segment.
    cancel ((&(((a_pre + (i * sizeof ("<anonymous struct>"))))
                  # "anonymous struct 1" ->ₛ "l")) # Int
              |-> fst (Znth i left __default__Prod_Z_Z)).
    cancel ((&(((a_pre + (i * sizeof ("<anonymous struct>"))))
                  # "anonymous struct 1" ->ₛ "r")) # Int
              |-> snd (Znth i left __default__Prod_Z_Z)).
    cancel (SegArray.full a_pre i (sublist 0 i left)).
    cancel (SegArray.full
      (a_pre + (i + 1) * sizeof ("<anonymous struct>"))
      (na_pre - i - 1) (sublist (i + 1) na_pre left)).
    cancel (SegArray.full b_pre nb_pre sorted_2).
    cancel (IntArray.full pref nb_pre prefix_2).
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_overlap_entail_wit_9_1 : overlap_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hz : Znth i left __default__Prod_Z_Z = Znth i left (0, 0)).
  { apply Znth_indep. lia. }
  rewrite Hz in *.
  pose proof (directed_overlap_step_prefix_grow__overlap_directed_scan_step
    left right sorted_2 prefix_2 nb_pre i lo hi best ltac:(lia) PreH18
    PreH19 PreH22 PreH24 PreH16 PreH12 ltac:(lia) ltac:(lia)
    PreH1 PreH2 PreH14 PreH23) as Hnext.
  assert (Hcap : Znth (lo - 1) prefix_2 0 -
      fst (Znth i left (0, 0)) <= 1000000000).
  { pose proof PreH22 as Hpref_for_bound.
    destruct Hpref_for_bound as [_ Hmax].
    specialize (Hmax (lo - 1) ltac:(lia)).
    unfold MaxMin.max_value_of_subset,
      MaxMin.max_object_of_subset in Hmax.
    destruct Hmax as [k [[Hkrange _] Heq]].
    change (0 <= k <= lo - 1) in Hkrange.
    pose proof (bounded_Znth__overlap_directed_scan_step
      sorted_2 k (0, 0) PreH20 ltac:(lia)) as [_ [_ Hright]].
    pose proof (bounded_Znth__overlap_directed_scan_step
      left i (0, 0) PreH18 ltac:(lia)) as [Hleft _].
    lia. }
  Exists prefix_2 sorted_2.
  split_pure_spatial.
  - cancel (IntArray.full pref nb_pre prefix_2).
    cancel (SegArray.full b_pre nb_pre sorted_2).
    sep_apply_l_atomic
      (store_segment_fold__overlap_directed_scan_step
        a_pre i (Znth i left (0, 0))).
    sep_apply_l_atomic
      (seg_array_merge_current__overlap_directed_scan_step
        a_pre na_pre i left (0, 0) PreH3 ltac:(lia)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_overlap_entail_wit_9_2 : overlap_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hz : Znth i left __default__Prod_Z_Z = Znth i left (0, 0)).
  { apply Znth_indep. lia. }
  rewrite Hz in *.
  pose proof (directed_overlap_step_left_grow__overlap_directed_scan_step
    left right sorted_2 prefix_2 nb_pre i lo hi best ltac:(lia) PreH18
    PreH19 PreH22 PreH24 PreH16 PreH12 ltac:(lia) ltac:(lia)
    PreH1 ltac:(lia) PreH23) as Hnext.
  pose proof (bounded_Znth__overlap_directed_scan_step
    left i (0, 0) PreH18 ltac:(lia)) as [Hleft [_ Hright]].
  Exists prefix_2 sorted_2.
  split_pure_spatial.
  - cancel (IntArray.full pref nb_pre prefix_2).
    cancel (SegArray.full b_pre nb_pre sorted_2).
    sep_apply_l_atomic
      (store_segment_fold__overlap_directed_scan_step
        a_pre i (Znth i left (0, 0))).
    sep_apply_l_atomic
      (seg_array_merge_current__overlap_directed_scan_step
        a_pre na_pre i left (0, 0) PreH3 ltac:(lia)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_overlap_entail_wit_9_3 : overlap_entail_wit_9_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hz : Znth i left __default__Prod_Z_Z = Znth i left (0, 0)).
  { apply Znth_indep. lia. }
  rewrite Hz in *.
  pose proof (directed_overlap_step_prefix_keep__overlap_directed_scan_step
    left right sorted_2 prefix_2 nb_pre i lo hi best PreH19 PreH22
    PreH24 PreH16 PreH12 ltac:(lia) ltac:(lia) PreH1 PreH14 PreH23)
    as Hnext.
  Exists prefix_2 sorted_2.
  split_pure_spatial.
  - cancel (IntArray.full pref nb_pre prefix_2).
    cancel (SegArray.full b_pre nb_pre sorted_2).
    sep_apply_l_atomic
      (store_segment_fold__overlap_directed_scan_step
        a_pre i (Znth i left (0, 0))).
    sep_apply_l_atomic
      (seg_array_merge_current__overlap_directed_scan_step
        a_pre na_pre i left (0, 0) PreH3 ltac:(lia)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_overlap_entail_wit_9_4 : overlap_entail_wit_9_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hz : Znth i left __default__Prod_Z_Z = Znth i left (0, 0)).
  { apply Znth_indep. lia. }
  rewrite Hz in *.
  pose proof (directed_overlap_step_left_keep__overlap_directed_scan_step
    left right sorted_2 prefix_2 nb_pre i lo hi best ltac:(lia) PreH18
    PreH19 PreH22 PreH24 PreH16 PreH12 ltac:(lia) ltac:(lia)
    PreH1 ltac:(lia) PreH23) as Hnext.
  Exists prefix_2 sorted_2.
  split_pure_spatial.
  - cancel (IntArray.full pref nb_pre prefix_2).
    cancel (SegArray.full b_pre nb_pre sorted_2).
    sep_apply_l_atomic
      (store_segment_fold__overlap_directed_scan_step
        a_pre i (Znth i left (0, 0))).
    sep_apply_l_atomic
      (seg_array_merge_current__overlap_directed_scan_step
        a_pre na_pre i left (0, 0) PreH3 ltac:(lia)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_overlap_entail_wit_9_5 : overlap_entail_wit_9_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hz : Znth i left __default__Prod_Z_Z = Znth i left (0, 0)).
  { apply Znth_indep. lia. }
  rewrite Hz in *.
  pose proof (directed_overlap_step_empty_keep__overlap_directed_scan_step
    left right sorted_2 i lo hi best PreH17 PreH22 PreH10 PreH23 PreH21)
    as Hnext.
  Exists prefix_2 sorted_2.
  split_pure_spatial.
  - cancel (IntArray.full pref nb_pre prefix_2).
    cancel (SegArray.full b_pre nb_pre sorted_2).
    sep_apply_l_atomic
      (store_segment_fold__overlap_directed_scan_step
        a_pre i (Znth i left (0, 0))).
    sep_apply_l_atomic
      (seg_array_merge_current__overlap_directed_scan_step
        a_pre na_pre i left (0, 0) PreH1 ltac:(lia)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_overlap_return_wit_1_split_goal_1 : overlap_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DirectedOverlapMaximum.
  rewrite <- PreH2.
  replace i with na_pre in PreH19 by lia.
  exact PreH19.
Qed.

Lemma proof_of_overlap_return_wit_1 : overlap_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_overlap_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_overlap_return_wit_2_split_goal_1 : overlap_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply directed_overlap_maximum_empty_left__overlap_returns_and_contract.
  lia.
Qed.

Lemma proof_of_overlap_return_wit_2_split_goal_2 : overlap_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(apply Permutation_refl).
Qed.

Lemma proof_of_overlap_return_wit_2 : overlap_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_overlap_return_wit_2_split_goal_1.
  - Goal_apply proof_of_overlap_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_overlap_return_wit_3_split_goal_1 : overlap_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply directed_overlap_maximum_empty_right__overlap_returns_and_contract.
  lia.
Qed.

Lemma proof_of_overlap_return_wit_3_split_goal_2 : overlap_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(apply Permutation_refl).
Qed.

Lemma proof_of_overlap_return_wit_3 : overlap_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_overlap_return_wit_3_split_goal_1.
  - Goal_apply proof_of_overlap_return_wit_3_split_goal_2.
Qed.

Lemma proof_of_overlap_partial_solve_wit_1_pure_split_goal_1 : overlap_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SegmentAllocationSize.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_overlap_partial_solve_wit_1_pure : overlap_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_overlap_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (@nil (Z * Z)) (@nil (Z * Z)).
  pose proof
    (solver_scan_state_zero__solver_initialization_and_frame values b_data)
    as Hzero.
  destruct Hzero as [Hscan [Hbound1 Hbound2]].
  unfold SegArray.full, store_array.
  simpl.
  split_pure_spatial.
  - replace (retval + 0) with retval by lia.
    replace (retval_2 + 0) with retval_2 by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (SegArray.undef_full retval_2 n_pre).
    cancel (SegArray.undef_full retval n_pre).
    cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.full b_pre n_pre b_data).
  - split_pures; dump_pre_spatial; simpl in *; try lia; eauto.
    + intros k Hk. apply PreH6. lia.
    + intros k Hk. apply PreH7. lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists decreasing_2 increasing_2.
  unfold SegArray.undef_full, store_undef_array in *.
  replace (Z.to_nat (n_pre - nx))
    with (S (Z.to_nat ((n_pre - nx) - 1))) by lia.
  simpl store_undef_array_rec.
  split_pure_spatial.
  - sep_apply
      (undef_segment_rec_shift__solver_initialization_and_frame
        (Z.to_nat (n_pre - nx - 1))
        (x + nx * sizeof_front_end_type (FET_alias "<anonymous struct>"))
        1 1 (n_pre - nx)).
    replace
      (x + nx * sizeof_front_end_type (FET_alias "<anonymous struct>") +
       1 * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      with
      (x + (nx + 1) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      by lia.
    unfold undef_segment.
    cancel (IntArray.full b_pre n_pre b_data).
    cancel (IntArray.full a_pre n_pre values).
    cancel (SegArray.full x nx increasing_2).
    cancel (SegArray.full y ny decreasing_2).
    replace (1 - 1) with 0 by lia.
    change (sizeof ("<anonymous struct>"))
      with (sizeof_alias_type "<anonymous struct>") in *.
    replace
      (x + nx * sizeof_alias_type "<anonymous struct>" +
       0 * sizeof_alias_type "<anonymous struct>")
      with (x + nx * sizeof_alias_type "<anonymous struct>") by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; eauto.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists decreasing_2 increasing_2.
  unfold SegArray.undef_full, store_undef_array in *.
  replace (Z.to_nat (n_pre - ny))
    with (S (Z.to_nat ((n_pre - ny) - 1))) by lia.
  simpl store_undef_array_rec.
  split_pure_spatial.
  - sep_apply
      (undef_segment_rec_shift__solver_initialization_and_frame
        (Z.to_nat (n_pre - ny - 1))
        (y + ny * sizeof_front_end_type (FET_alias "<anonymous struct>"))
        1 1 (n_pre - ny)).
    replace
      (y + ny * sizeof_front_end_type (FET_alias "<anonymous struct>") +
       1 * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      with
      (y + (ny + 1) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      by lia.
    unfold undef_segment.
    cancel (IntArray.full b_pre n_pre b_data).
    cancel (IntArray.full a_pre n_pre values).
    cancel (SegArray.full x nx increasing_2).
    cancel (SegArray.full y ny decreasing_2).
    replace (1 - 1) with 0 by lia.
    change (sizeof ("<anonymous struct>"))
      with (sizeof_alias_type "<anonymous struct>") in *.
    replace
      (y + ny * sizeof_alias_type "<anonymous struct>" +
       0 * sizeof_alias_type "<anonymous struct>")
      with (y + ny * sizeof_alias_type "<anonymous struct>") by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlt : Znth i values 0 < Znth i b_data 0) by lia.
  pose proof (PreH5 i ltac:(lia)) as Haval.
  pose proof (PreH6 i ltac:(lia)) as Hbval.
  assert (Hstate_next :
    SolverScanState values b_data (i + 1) (base - d)
      (increasing_2 ++ (Znth i values 0, Znth i b_data 0) :: nil)%list decreasing_2).
  {
    replace (base - d) with
      (base + (Znth i b_data 0 - Znth i values 0)) by lia.
    apply solver_scan_state_step_lt__solver_scan_transitions_and_exit;
      assumption.
  }
  assert (Hbounded_next :
    SegmentsBounded
      (increasing_2 ++ (Znth i values 0, Znth i b_data 0) :: nil)%list).
  {
    apply segments_bounded_snoc__solver_scan_transitions_and_exit;
      try assumption; lia.
  }
  Exists decreasing_2
    (increasing_2 ++ (Znth i values 0, Znth i b_data 0) :: nil)%list.
  split_pure_spatial.
  - sep_apply
      (segarray_full_snoc_lr__solver_scan_transitions_and_exit
         x nx increasing_2 (Znth i values 0) (Znth i b_data 0)
         ltac:(lia)).
    replace (n_pre - nx - 1) with (n_pre - (nx + 1)) by lia.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hgt : Znth i b_data 0 < Znth i values 0) by lia.
  pose proof (PreH5 i ltac:(lia)) as Haval.
  pose proof (PreH6 i ltac:(lia)) as Hbval.
  assert (Hstate_next :
    SolverScanState values b_data (i + 1) (base + d) increasing_2
      (decreasing_2 ++ (Znth i b_data 0, Znth i values 0) :: nil)%list).
  {
    replace (base + d) with
      (base + (Znth i values 0 - Znth i b_data 0)) by lia.
    apply solver_scan_state_step_gt__solver_scan_transitions_and_exit;
      assumption.
  }
  assert (Hbounded_next :
    SegmentsBounded
      (decreasing_2 ++ (Znth i b_data 0, Znth i values 0) :: nil)%list).
  {
    apply segments_bounded_snoc__solver_scan_transitions_and_exit;
      try assumption; lia.
  }
  Exists
    (decreasing_2 ++ (Znth i b_data 0, Znth i values 0) :: nil)%list
    increasing_2.
  split_pure_spatial.
  - sep_apply
      (segarray_full_snoc_lr__solver_scan_transitions_and_exit
         y ny decreasing_2 (Znth i b_data 0) (Znth i values 0)
         ltac:(lia)).
    replace (n_pre - ny - 1) with (n_pre - (ny + 1)) by lia.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply solver_scan_state_step_eq__solver_scan_transitions_and_exit;
    try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  pose proof (solver_scan_state_at_length__solver_scan_transitions_and_exit
    values b_data i base increasing decreasing (eq_trans Hi PreH2) PreH18)
    as [Hinc [Hdec Hbase]].
  rewrite <- PreH2 in Hinc, Hdec.
  rewrite <- Hdec.
  dump_pre_spatial.
  exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  pose proof (solver_scan_state_at_length__solver_scan_transitions_and_exit
    values b_data i base increasing decreasing (eq_trans Hi PreH2) PreH18)
    as [Hinc [Hdec Hbase]].
  rewrite <- PreH2 in Hinc, Hdec.
  rewrite <- Hinc.
  dump_pre_spatial.
  exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  pose proof (solver_scan_state_at_length__solver_scan_transitions_and_exit
    values b_data i base increasing decreasing (eq_trans Hi PreH2) PreH18)
    as [Hinc [Hdec Hbase]].
  rewrite <- PreH2 in Hinc, Hdec.
  dump_pre_spatial.
  exact Hbase.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  pose proof (solver_scan_state_at_length__solver_scan_transitions_and_exit
    values b_data i base increasing decreasing (eq_trans Hi PreH2) PreH18)
    as [Hinc [Hdec Hbase]].
  rewrite <- PreH2 in Hinc, Hdec.
  rewrite <- Hdec.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_5 : solver_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  pose proof (solver_scan_state_at_length__solver_scan_transitions_and_exit
    values b_data i base increasing decreasing (eq_trans Hi PreH2) PreH18)
    as [Hinc [Hdec Hbase]].
  rewrite <- PreH2 in Hinc, Hdec.
  rewrite <- Hinc.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_6 : solver_entail_wit_5_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_7 : solver_entail_wit_5_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_spatial : solver_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  pose proof (solver_scan_state_at_length__solver_scan_transitions_and_exit
    values b_data i base increasing decreasing (eq_trans Hi PreH2) PreH18)
    as [Hinc [Hdec Hbase]].
  rewrite <- PreH2 in Hinc, Hdec.
  rewrite <- Hinc, <- Hdec.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_1 : solver_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  assert (Hreverse : DirectedOverlapMaximum
    (DecreasingIntervals values b_data (Zlength values))
    (IncreasingIntervals values b_data (Zlength values)) retval_2).
  { eapply directed_overlap_maximum_permutation_left__solver_final_maximum_and_spec.
    - apply Permutation_sym. exact PreH9.
    - exact PreH5. }
  assert (Hmaximum : SwappingOverlapMaximum values b_data retval).
  { eapply swapping_overlap_maximum_from_directed__solver_final_maximum_and_spec;
      eauto; lia. }
  eapply spec_from_swapping_overlap_maximum__solver_final_maximum_and_spec;
    eauto.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_2 : solver_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  assert (Hreverse : DirectedOverlapMaximum
    (DecreasingIntervals values b_data (Zlength values))
    (IncreasingIntervals values b_data (Zlength values)) retval_2).
  { eapply directed_overlap_maximum_permutation_left__solver_final_maximum_and_spec.
    - apply Permutation_sym. exact PreH9.
    - exact PreH5. }
  eapply swapping_overlap_maximum_from_directed__solver_final_maximum_and_spec;
    eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_1 : solver_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  assert (Hreverse : DirectedOverlapMaximum
    (DecreasingIntervals values b_data (Zlength values))
    (IncreasingIntervals values b_data (Zlength values)) retval).
  { eapply directed_overlap_maximum_permutation_left__solver_final_maximum_and_spec.
    - apply Permutation_sym. exact PreH9.
    - exact PreH5. }
  assert (Hmaximum : SwappingOverlapMaximum values b_data retval).
  { eapply swapping_overlap_maximum_from_directed_reverse__solver_final_maximum_and_spec;
      eauto; lia. }
  eapply spec_from_swapping_overlap_maximum__solver_final_maximum_and_spec;
    eauto.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_2 : solver_entail_wit_6_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  assert (Hreverse : DirectedOverlapMaximum
    (DecreasingIntervals values b_data (Zlength values))
    (IncreasingIntervals values b_data (Zlength values)) retval).
  { eapply directed_overlap_maximum_permutation_left__solver_final_maximum_and_spec.
    - apply Permutation_sym. exact PreH9.
    - exact PreH5. }
  eapply swapping_overlap_maximum_from_directed_reverse__solver_final_maximum_and_spec;
    eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_2_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_11_pure_split_goal_1 : solver_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite <- PreH27; apply Zlength_nonneg).
Qed.

Lemma proof_of_solver_partial_solve_wit_11_pure_split_goal_2 : solver_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SegArray.undef_full at 2.
  unfold store_undef_array.
  destruct (Z_le_gt_dec 0 (n_pre - ny)) as [Hnonneg | Hneg].
  - dump_pre_spatial.
    lia.
  - replace (Z.to_nat (n_pre - ny)) with 0%nat by lia.
    simpl store_undef_array_rec.
    Intros_p Hzero.
    dump_pre_spatial.
    lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_11_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_11_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure_split_goal_1 : solver_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite <- PreH26; apply Zlength_nonneg).
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure_split_goal_2 : solver_partial_solve_wit_12_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SegArray.undef_full.
  unfold store_undef_array.
  destruct (Z_le_gt_dec 0 (n_pre - nx)) as [Hnonneg | Hneg].
  - dump_pre_spatial.
    lia.
  - replace (Z.to_nat (n_pre - nx)) with 0%nat by lia.
    simpl store_undef_array_rec.
    Intros_p Hzero.
    dump_pre_spatial.
    lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_12_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_12_pure_split_goal_2.
Qed.
