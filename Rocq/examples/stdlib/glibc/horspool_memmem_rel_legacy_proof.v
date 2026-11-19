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
From SimpleC.EE.stdlib.glibc Require Import horspool_memmem_rel_legacy_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.stdlib.glibc.horspool_memmem_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_hp_hash2_entail_wit_1 : hp_hash2_entail_wit_1.
Proof.
pre_process. subst pointer_pre. split_pure_spatial.
- rewrite <- UCharArray.seg_shift. replace (index + (0 - index)) with 0 by lia. replace (index + (length - index)) with length by lia. apply UCharArray.full_to_seg.
- split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_hp_hash2_return_wit_1 : hp_hash2_return_wit_1.
Proof.
pre_process. subst pointer_pre. split_pure_spatial.
- eapply derivable1_trans; [apply UCharArray.seg_to_full|]. replace (base + index * sizeof ( UCHAR ) + (0 - index) * sizeof ( UCHAR )) with base by ring. replace (length - index - (0 - index)) with length by ring. cancel.
- split_pures; dump_pre_spatial.
  + unfold hp_hash_at, hp_hash. replace (0 - (0 - index)) with index by lia. replace (-1 - (0 - index)) with (index - 1) by lia. rewrite unsigned_unsigned_sub_r by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.rem_mod_nonneg by (try lia; apply (proj1 (unsigned_Lastnbits_range _ 64 ltac:(lia)))). unfold unsigned_last_nbits. change 256 with (2^8). rewrite <- Pow2Mod_less by lia. f_equal. ring.
  + apply Z.rem_nonneg; [lia|apply (proj1 (unsigned_Lastnbits_range _ 64 ltac:(lia)))].
  + apply (proj2 (Z.rem_bound_pos _ 256 (proj1 (unsigned_Lastnbits_range _ 64 ltac:(lia))) ltac:(lia))).
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_1 : horspool_memmem_refinement_entail_wit_1.
Proof.
  unfold horspool_memmem_refinement_entail_wit_1; intros; Intros.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring].
  all: unfold unsigned_last_nbits; rewrite Z.mod_small; [lia | cbn; lia].
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_2 : horspool_memmem_refinement_entail_wit_2.
Proof.
  unfold horspool_memmem_refinement_entail_wit_2; intros; Intros.
  Exists (repeat_Z 0 256); split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia].
  unfold hp_table_prefix, repeat_Z; split; [reflexivity | intros hash Hr; rewrite Znth_repeat; unfold hp_rightmost; repeat split; auto; intros; lia].
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_3 : horspool_memmem_refinement_entail_wit_3.
Proof.
  unfold horspool_memmem_refinement_entail_wit_3; intros; Intros.
  assert (Hi : unsigned_last_nbits i 64 = i) by (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia).
  rewrite Hi in H2.
  Exists (replace_Znth retval i table_2); split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia].
  destruct H26 as [Hlen Htab]; split; [rewrite Zlength_replace_Znth; exact Hlen | intros hash Hr; destruct (Z.eq_dec hash retval) as [Heq|Hne]].
  - subst hash; rewrite Znth_replace_Znth_Same by lia; unfold hp_rightmost; repeat split; auto; try lia; intros; lia.
  - rewrite Znth_replace_Znth_Diff by lia; specialize (Htab hash Hr); unfold hp_rightmost in Htab |- *.
    destruct Htab as [Hb [Hv Hmax]]; split; [lia | split; [exact Hv | intros j Hj Hhash; destruct (Z.eq_dec j i); [subst; congruence | apply Hmax; auto; lia]]].
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_4 : horspool_memmem_refinement_entail_wit_4.
Proof.
  unfold horspool_memmem_refinement_entail_wit_4; intros; Intros.
  assert (Hi : unsigned_last_nbits i 64 = i) by (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia).
  rewrite Hi in H5; assert (Ei : i = m1) by lia; subst i.
  pose proof (proj2 H29 retval (conj H3 H4)) as Hb; destruct Hb as [Hb _].
  assert (Hv : unsigned_last_nbits (Znth retval table 0) 64 = Znth retval table 0) by (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia).
  rewrite Hv.
  assert (Hs : unsigned_last_nbits (m1 - Znth retval table 0) 64 = m1 - Znth retval table 0) by (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia).
  rewrite Hs.
  Exists (replace_Znth retval_2 m1 table); Exists 0; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia].
  - unfold hp_table_final; exists table.
    replace (needleoff_low_level_spec + ne_len_pre - 1) with (needleoff_low_level_spec + m1) by lia.
    rewrite <- H21; split; [exact H29 | split; congruence].
  - unfold hp_filter_offset; intros; lia.
  - unfold hp_no_match_before; intros; lia.
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_5 : horspool_memmem_refinement_entail_wit_5.
Proof.
  unfold horspool_memmem_refinement_entail_wit_5; intros; Intros.
  Exists table_2; Exists (position_2 + m1).
  replace (position_2 + m1 - m1) with position_2 by lia.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring].
  rewrite sizeof_uchar in H18, H25; lia.
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_6 : horspool_memmem_refinement_entail_wit_6.
Proof.
  unfold horspool_memmem_refinement_entail_wit_6; intros; Intros.
  rewrite sizeof_uchar in *.
  Exists table_2 (position_2 + m1).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    + unfold hp_search_from in H14 at 1; prog_nf in H14.
      unfold_loop in H14; prog_nf in H14.
      unfold hp_search_body in H14 at 1; prog_nf in H14.
      safe_choice_r H14. safe_choice_r H14; [|lia].
      prog_nf in H14.
      apply safeExec_any_bind with (a := position_2 + m1 - m1) in H14.
      prog_nf in H14. safe_step H14.
      * unfold continue in H14 at 1; prog_nf in H14. exact H14.
      * unfold hp_valid_skip. split; [lia|]. intros c Hc.
        eapply (hp_endpoint_skip bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre table_2 shift1 position_2 tmp); eauto; try lia.
        rewrite <- H16; exact H30.
    + replace (position_2 + m1 - m1) with (position_2 - tmp) by lia.
      eapply hp_endpoint_skip; eauto; try lia.
      rewrite <- H16; exact H30.
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_7 : horspool_memmem_refinement_entail_wit_7.
Proof.
  unfold horspool_memmem_refinement_entail_wit_7; intros; Intros.
  rewrite sizeof_uchar in *.
  Exists table position_2. split_pure_spatial; [cancel|].
  split_pures; dump_pre_spatial; auto; try lia.
  all: try solve [rewrite H; f_equal; f_equal; lia].
  all: destruct H21 as (internal & (Hlen & Hp) & Hshift & ->);
    specialize (Hp retval ltac:(lia)); destruct Hp as (Hb & _);
    destruct (Z.eq_dec (hp_hash_at bytes_low_level_spec (needleoff_low_level_spec + ne_len_pre - 1)) retval) as [He|He].
  all: try solve [rewrite He, Znth_replace_Znth_Same by lia; lia].
  all: rewrite Znth_replace_Znth_Diff; try lia; try assumption;
    rewrite Hlen; unfold hp_hash_at, hp_hash; apply Z.mod_pos_bound; lia.
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_8_1 : horspool_memmem_refinement_entail_wit_8_1.
Proof.
  unfold horspool_memmem_refinement_entail_wit_8_1; intros; Intros.
  rewrite sizeof_uchar in *.
  Exists table_2 (position_2 - tmp).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    + unfold hp_search_from in H14 at 1; prog_nf in H14.
      unfold_loop in H14; prog_nf in H14.
      unfold hp_search_body in H14 at 1; prog_nf in H14.
      safe_choice_r H14. safe_choice_r H14; [|lia].
      prog_nf in H14.
      apply safeExec_any_bind with (a := position_2 - tmp) in H14.
      prog_nf in H14. safe_step H14.
      * unfold continue in H14 at 1; prog_nf in H14. exact H14.
      * unfold hp_valid_skip. split; [lia|]. intros c Hc.
        eapply (hp_endpoint_skip bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre table_2 shift1 position_2 tmp); eauto; try lia.
        rewrite <- H16; exact H30.
    + eapply hp_endpoint_skip; eauto; try lia.
      rewrite <- H16; exact H30.
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_8_2 : horspool_memmem_refinement_entail_wit_8_2.
Proof.
  unfold horspool_memmem_refinement_entail_wit_8_2; intros; Intros.
  rewrite sizeof_uchar in *.
  Exists table_2 (position_2 - tmp).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    + destruct (Z.eq_dec tmp m1) as [->|Hne]; [exact H13|].
      unfold hp_search_from in H13 at 1; prog_nf in H13.
      unfold_loop in H13; prog_nf in H13.
      unfold hp_search_body in H13 at 1; prog_nf in H13.
      safe_choice_r H13. safe_choice_r H13; [|lia].
      prog_nf in H13.
      apply safeExec_any_bind with (a := position_2 - tmp) in H13.
      prog_nf in H13. safe_step H13.
      * unfold continue in H13 at 1; prog_nf in H13. exact H13.
      * unfold hp_valid_skip. split; [lia|]. intros c Hc.
        eapply (hp_endpoint_skip bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre table_2 shift1 position_2 tmp); eauto; try lia.
        rewrite <- H15; exact H29.
    + eapply hp_endpoint_skip; eauto; try lia.
      rewrite <- H15; exact H29.
    + intros E; split; [lia|].
      replace (hayoff_low_level_spec + (position_2 - tmp) + m1) with (hayoff_low_level_spec + position_2) by lia.
      replace (needleoff_low_level_spec + m1) with (needleoff_low_level_spec + ne_len_pre - 1) by lia.
      destruct H19 as (internal & (Hlen & Hp) & Hshift & Et).
      rewrite Et in H28.
      destruct (Z.eq_dec (hp_hash_at bytes_low_level_spec (needleoff_low_level_spec + ne_len_pre - 1)) (hp_hash_at bytes_low_level_spec (hayoff_low_level_spec + position_2))) as [He|He]; [symmetry; exact He|].
      assert (Bh : 0 <= hp_hash_at bytes_low_level_spec (hayoff_low_level_spec + position_2) < 256) by (unfold hp_hash_at, hp_hash; apply Z.mod_pos_bound; lia).
      assert (Bn : 0 <= hp_hash_at bytes_low_level_spec (needleoff_low_level_spec + ne_len_pre - 1) < 256) by (unfold hp_hash_at, hp_hash; apply Z.mod_pos_bound; lia).
      rewrite Znth_replace_Znth_Diff in H28 by (try rewrite Hlen; auto).
      specialize (Hp _ Bh). destruct Hp as (Hb & _). lia.
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_1 : horspool_memmem_refinement_entail_wit_9_1.
Proof.
  unfold horspool_memmem_refinement_entail_wit_9_1; intros; Intros.
  rewrite sizeof_uchar in *.
  Exists table_2 position_2. split_pure_spatial; [cancel|].
  specialize (H35 ltac:(lia)). destruct H35 as [Hguard Hhash].
  assert (Hmiss : ~ hp_match_at bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2).
  { eapply hp_memcmp_failure_excludes_match with (offset := 0) (count := m1) (result := retval); try lia; try exact H0.
    replace (hayoff_low_level_spec + position_2 + 0) with (hs - base_low_level_spec) by lia.
    replace (needleoff_low_level_spec + 0) with needleoff_low_level_spec by lia. exact H1. }
  assert (Hskip : hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 + shift1)).
  { eapply hp_tail_aligned_mismatch_skip; eauto. rewrite <- H21.
    replace (needleoff_low_level_spec + ne_len_pre - 1) with (needleoff_low_level_spec + m1) by lia. exact Hhash. }
  split_pures; dump_pre_spatial; auto; try lia.
  - unfold hp_search_from in H19 at 1; prog_nf in H19.
    unfold_loop in H19; prog_nf in H19.
    unfold hp_search_body in H19 at 1; prog_nf in H19.
    safe_choice_r H19. safe_choice_r H19. prog_nf in H19.
    apply safeExec_any_bind with (a := position_2 + shift1) in H19.
    prog_nf in H19. safe_step H19.
    + unfold continue in H19 at 1; prog_nf in H19; exact H19.
    + unfold hp_valid_skip; split; [lia|]. intros c Hc; apply Hskip; lia.
  - unfold hp_filter_offset; lia.
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_2 : horspool_memmem_refinement_entail_wit_9_2.
Proof.
  unfold horspool_memmem_refinement_entail_wit_9_2; intros; Intros.
  rewrite sizeof_uchar in *.
  Exists table_2 position_2. split_pure_spatial; [cancel|].
  specialize (H35 ltac:(lia)). destruct H35 as [Hguard Hhash].
  assert (Hmiss : ~ hp_match_at bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2).
  { eapply hp_memcmp_failure_excludes_match with (offset := 0) (count := m1) (result := retval); try lia; try exact H0.
    replace (hayoff_low_level_spec + position_2 + 0) with (hs - base_low_level_spec) by lia.
    replace (needleoff_low_level_spec + 0) with needleoff_low_level_spec by lia. exact H1. }
  assert (Hskip : hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 + shift1)).
  { eapply hp_tail_aligned_mismatch_skip; eauto. rewrite <- H21.
    replace (needleoff_low_level_spec + ne_len_pre - 1) with (needleoff_low_level_spec + m1) by lia. exact Hhash. }
  split_pures; dump_pre_spatial; auto; try lia.
  - unfold hp_search_from in H19 at 1; prog_nf in H19.
    unfold_loop in H19; prog_nf in H19.
    unfold hp_search_body in H19 at 1; prog_nf in H19.
    safe_choice_r H19. safe_choice_r H19. prog_nf in H19.
    apply safeExec_any_bind with (a := position_2 + shift1) in H19.
    prog_nf in H19. safe_step H19.
    + unfold continue in H19 at 1; prog_nf in H19; exact H19.
    + unfold hp_valid_skip; split; [lia|]. intros c Hc; apply Hskip; lia.
  - unfold hp_filter_offset; lia.
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_3 : horspool_memmem_refinement_entail_wit_9_3.
Proof.
  unfold horspool_memmem_refinement_entail_wit_9_3; intros.
  do 41 (let H := fresh "H" in Intros_p H).
  Exists table_2 position_2. split_pure_spatial.
  - cancel.
  - assert (Et : tmp = m1) by lia.
    destruct (H39 Et) as [Bound Tail].
    assert (Mismatch : ~ hp_match_at bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2).
    { eapply hp_memcmp_failure_excludes_match with (offset := 0) (count := m1) (result := retval_2); try lia.
      rewrite sizeof_uchar in H10, H35.
      replace (hayoff_low_level_spec + position_2 + 0) with (hs - base_low_level_spec) by lia.
      replace (needleoff_low_level_spec + 0) with needleoff_low_level_spec by lia.
      exact H1. }
    assert (Before : hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 + shift1)).
    { eapply hp_tail_aligned_mismatch_skip; eauto.
      replace (needleoff_low_level_spec + ne_len_pre - 1) with (needleoff_low_level_spec + m1) by lia.
      rewrite <- H25. exact Tail. }
    split_pures; try (dump_pre_spatial; assumption).
    + unfold hp_search_from in H23 at 1. prog_nf in H23.
      unfold_loop in H23. prog_nf in H23.
      unfold hp_search_body in H23 at 1. prog_nf in H23.
      safe_choice_r H23. safe_choice_r H23.
      prog_nf in H23.
      apply safeExec_any_bind with (a := position_2 + shift1) in H23.
      prog_nf in H23. apply safeExec_test_bind in H23.
      2: { unfold hp_valid_skip. split; [lia | intros c HC; apply Before; lia]. }
      unfold continue in H23 at 1. prog_nf in H23.
      dump_pre_spatial. exact H23.
    + dump_pre_spatial. unfold hp_filter_offset in *.
      specialize (H32 ltac:(lia)). unfold unsigned_last_nbits.
      rewrite Z.mod_small; [lia | cbn; lia].
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_4 : horspool_memmem_refinement_entail_wit_9_4.
Proof.
  unfold horspool_memmem_refinement_entail_wit_9_4; intros.
  do 41 (let H := fresh "H" in Intros_p H).
  Exists table_2 position_2. split_pure_spatial.
  - cancel.
  - assert (Et : tmp = m1) by lia.
    destruct (H39 Et) as [Bound Tail].
    assert (Mismatch : ~ hp_match_at bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2).
    { eapply hp_memcmp_failure_excludes_match with (offset := 0) (count := m1) (result := retval_2); try lia.
      rewrite sizeof_uchar in H10, H35.
      replace (hayoff_low_level_spec + position_2 + 0) with (hs - base_low_level_spec) by lia.
      replace (needleoff_low_level_spec + 0) with needleoff_low_level_spec by lia.
      exact H1. }
    assert (Before : hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 + shift1)).
    { eapply hp_tail_aligned_mismatch_skip; eauto.
      replace (needleoff_low_level_spec + ne_len_pre - 1) with (needleoff_low_level_spec + m1) by lia.
      rewrite <- H25. exact Tail. }
    split_pures; try (dump_pre_spatial; assumption).
    + unfold hp_search_from in H23 at 1. prog_nf in H23.
      unfold_loop in H23. prog_nf in H23.
      unfold hp_search_body in H23 at 1. prog_nf in H23.
      safe_choice_r H23. safe_choice_r H23.
      prog_nf in H23.
      apply safeExec_any_bind with (a := position_2 + shift1) in H23.
      prog_nf in H23. apply safeExec_test_bind in H23.
      2: { unfold hp_valid_skip. split; [lia | intros c HC; apply Before; lia]. }
      unfold continue in H23 at 1. prog_nf in H23.
      dump_pre_spatial. exact H23.
    + dump_pre_spatial. unfold hp_filter_offset in *.
      specialize (H32 ltac:(lia)). unfold unsigned_last_nbits.
      rewrite Z.mod_small; [lia | cbn; lia].
Qed. 

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_5 : horspool_memmem_refinement_entail_wit_9_5.
Proof.
  unfold horspool_memmem_refinement_entail_wit_9_5; intros.
  do 36 (let H := fresh "H" in Intros_p H).
  Exists table_2 position_2. split_pure_spatial.
  - cancel.
  - assert (Et : tmp = m1) by lia.
    destruct (H34 Et) as [Bound Tail].
    assert (Mismatch : ~ hp_match_at bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2).
    { pose proof (H27 ltac:(lia)) as Off.
      eapply hp_memcmp_failure_excludes_match with (offset := offset) (count := 8) (result := retval); try lia.
      rewrite sizeof_uchar in H5, H30.
      replace (hayoff_low_level_spec + position_2 + offset) with (hs - base_low_level_spec + offset) by lia.
      exact H0. }
    assert (Before : hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 + shift1)).
    { eapply hp_tail_aligned_mismatch_skip; eauto.
      replace (needleoff_low_level_spec + ne_len_pre - 1) with (needleoff_low_level_spec + m1) by lia.
      rewrite <- H20. exact Tail. }
    split_pures; try (dump_pre_spatial; assumption).
    + unfold hp_search_from in H18 at 1. prog_nf in H18.
      unfold_loop in H18. prog_nf in H18.
      unfold hp_search_body in H18 at 1. prog_nf in H18.
      safe_choice_r H18. safe_choice_r H18.
      prog_nf in H18.
      apply safeExec_any_bind with (a := position_2 + shift1) in H18.
      prog_nf in H18. apply safeExec_test_bind in H18.
      2: { unfold hp_valid_skip. split; [lia | intros c HC; apply Before; lia]. }
      unfold continue in H18 at 1. prog_nf in H18.
      dump_pre_spatial. exact H18.
Qed. 

Lemma proof_of_horspool_memmem_refinement_return_wit_1 : horspool_memmem_refinement_return_wit_1.
Proof.
  unfold horspool_memmem_refinement_return_wit_1; intros.
  do 30 (let H := fresh "H" in Intros_p H).
  split_pure_spatial.
  - cancel.
  - rewrite sizeof_uchar in *.
    match goal with H : safeExec _ _ _ |- _ =>
      unfold hp_search_from in H at 1; prog_nf in H;
      unfold_loop in H; prog_nf in H;
      unfold hp_search_body in H at 1; prog_nf in H;
      safe_choice_l H;
      [ unfold break in H at 1; prog_nf in H; dump_pre_spatial; exact H | lia ]
    end.
Qed. 

Lemma proof_of_horspool_memmem_refinement_return_wit_2 : horspool_memmem_refinement_return_wit_2.
Proof.
  unfold horspool_memmem_refinement_return_wit_2; intros.
  do 40 (let H := fresh "H" in Intros_p H).
  split_pure_spatial.
  - cancel.
  - assert (Et : tmp = m1) by lia.
    destruct (H38 Et) as [Bound Tail].
    rewrite sizeof_uchar in *.
    assert (Addr : hs - base_low_level_spec = hayoff_low_level_spec + position) by lia.
    rewrite Addr in H0.
    pose proof ((proj1 H0) H) as Prefix.
    assert (Match : hp_match_at bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position).
    { unfold hp_match_at. split; [lia | ]. split; [exact Bound | ].
      intros i Hi. destruct (Z_lt_ge_dec i m1) as [Less | Last].
      { apply Prefix; lia. }
      assert (Ei : i = m1) by lia. subst i.
      unfold hp_hash_at in Tail.
      assert (Prev : Znth (hayoff_low_level_spec + position + m1 - 1) bytes_low_level_spec 0 =
                     Znth (needleoff_low_level_spec + m1 - 1) bytes_low_level_spec 0).
      { replace (hayoff_low_level_spec + position + m1 - 1) with (hayoff_low_level_spec + position + (m1 - 1)) by lia.
        replace (needleoff_low_level_spec + m1 - 1) with (needleoff_low_level_spec + (m1 - 1)) by lia.
        apply Prefix; lia. }
      rewrite Prev in Tail.
      eapply hp_hash_last_byte_injective; [ | | exact Tail];
        assert (Bytes : Forall (fun v : Z => 0 <= v <= 255) bytes_low_level_spec)
          by (unfold hp_inputs in H21; tauto);
        unfold Znth;
        match goal with |- 0 <= nth ?i ?l 0 < 256 =>
          destruct (lt_dec i (List.length l)) as [InRange | OutRange];
          [ pose proof (proj1 (@Forall_nth Z (fun v => 0 <= v <= 255) bytes_low_level_spec) Bytes _ 0 InRange) as B;
            cbv beta in B; lia
          | rewrite nth_overflow by lia; lia ]
        end. }
    unfold hp_search_from in H22 at 1. prog_nf in H22.
    unfold_loop in H22. prog_nf in H22.
    unfold hp_search_body in H22 at 1. prog_nf in H22.
    safe_choice_r H22. safe_choice_l H22.
    unfold break in H22 at 1. prog_nf in H22.
    dump_pre_spatial. unfold hp_ptr_result.
    destruct (Z.eq_dec hs 0); [lia | ].
    replace (hs - (base_low_level_spec + hayoff_low_level_spec)) with position by lia.
    exact H22.
Qed. 

Lemma proof_of_horspool_memmem_refinement_return_wit_3 : horspool_memmem_refinement_return_wit_3.
Proof.
unfold horspool_memmem_refinement_return_wit_3; intros; Rename ltac:(pre_process_pure).
split_pure_spatial.
- cancel.
- dump_pre_spatial.
  assert (Etmp : tmp = m1) by lia.
  destruct (H34 Etmp) as [Hfit Hhash].
  rewrite sizeof_uchar in H5, H30.
  assert (Ehs : hs - base_low_level_spec = hayoff_low_level_spec + position) by lia.
  unfold hp_memcmp_result in H0. pose proof ((proj1 H0) H) as Hcmp.
  rewrite Ehs in Hcmp.
  assert (Hb : forall z, 0 <= Znth z bytes_low_level_spec 0 < 256).
  { unfold hp_inputs in H17. destruct H17 as (_ & _ & _ & _ & _ & _ & _ & _ & Hall).
    intro z. unfold Znth. destruct (lt_dec (Z.to_nat z) (List.length bytes_low_level_spec)).
    - pose proof (proj1 (Forall_nth _ _) Hall _ 0 l) as Hz. cbn beta in Hz. lia.
    - rewrite nth_overflow by lia. lia. }
  assert (Hmatch : hp_match_at bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position).
  { unfold hp_match_at. repeat split; try lia. intros i Hi.
    destruct (Z_lt_ge_dec i m1).
    - apply Hcmp; lia.
    - assert (Ei : i = m1) by lia. subst i.
      unfold hp_hash_at in Hhash.
      replace (hayoff_low_level_spec + position + m1 - 1) with (hayoff_low_level_spec + position + (m1 - 1)) in Hhash by ring.
      replace (needleoff_low_level_spec + m1 - 1) with (needleoff_low_level_spec + (m1 - 1)) in Hhash by ring.
      rewrite (Hcmp (m1 - 1) ltac:(lia)) in Hhash.
      eapply hp_hash_last_byte_injective; [apply Hb|apply Hb|exact Hhash]. }
  unfold hp_search_from in H18 at 1. prog_nf in H18.
  unfold_loop in H18. prog_nf in H18.
  unfold hp_search_body in H18 at 1. prog_nf in H18.
  safe_choice_r H18. safe_choice_l H18.
  unfold break in H18. prog_nf in H18.
  unfold hp_ptr_result. destruct (Z.eq_dec hs 0); [exfalso; lia|].
  replace (hs - (base_low_level_spec + hayoff_low_level_spec)) with position by lia.
  exact H18.
Qed.

Lemma proof_of_horspool_memmem_refinement_return_wit_4 : horspool_memmem_refinement_return_wit_4.
Proof.
pre_process.
split_pure_spatial.
- cancel.
- dump_pre_spatial.
  unfold hp_search_from in H13 at 1. prog_nf in H13.
  unfold_loop in H13. prog_nf in H13.
  unfold hp_search_body in H13 at 1. prog_nf in H13.
  safe_choice_l H13.
  + unfold break in H13. prog_nf in H13. exact H13.
Qed. 

Lemma proof_of_horspool_memmem_refinement_partial_solve_wit_10_pure : horspool_memmem_refinement_partial_solve_wit_10_pure.
Proof.
  unfold horspool_memmem_refinement_partial_solve_wit_10_pure; intros.
  do 32 (let H := fresh "H" in Intros_p H).
  assert (Et : tmp = m1) by lia.
  match goal with H : tmp = m1 -> _ |- _ => destruct (H Et) as [Bound Tail] end.
  match goal with H : hp_filter_offset m1 offset |- _ => specialize (H ltac:(lia)) end.
  rewrite sizeof_uchar in *.
  split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_horspool_memmem_refinement_derive_high_level_spec_by_low_level_spec : horspool_memmem_refinement_derive_high_level_spec_by_low_level_spec.
Proof.
  unfold horspool_memmem_refinement_derive_high_level_spec_by_low_level_spec; intros.
  Intros.
  Exists base_high_level_spec; Exists length_high_level_spec; Exists bytes_high_level_spec.
  Exists hayoff_high_level_spec; Exists needleoff_high_level_spec.
  Exists (MonadErr.nrm (hp_search_from bytes_high_level_spec hayoff_high_level_spec hs_len_pre needleoff_high_level_spec ne_len_pre 0) tt).
  split_pure_spatial.
  - cancel; apply derivable1_wand_sepcon_adjoint; Intros retval; Intros.
    Exists retval; split_pure_spatial; [cancel | split_pures; dump_pre_spatial].
    pose proof (Hoare_safeexec_compose _ _ _
      (hp_rel_g0_search_entry_correct bytes_high_level_spec hayoff_high_level_spec hs_len_pre needleoff_high_level_spec ne_len_pre)
      _ _ _ H12 I) as [st [Hpost _]].
    unfold hp_ptr_result in Hpost; destruct (Z.eq_dec retval 0) as [Hz|Hz].
    + left; split; assumption.
    + right; exists (retval - (base_high_level_spec + hayoff_high_level_spec)).
      split; [lia | exact Hpost].
  - split_pures; dump_pre_spatial; auto.
    apply safeExec_monad_Atrue_finnal.
    exact (proj2 (hp_rel_g0_search_entry_correct bytes_high_level_spec hayoff_high_level_spec hs_len_pre needleoff_high_level_spec ne_len_pre) tt I).
Qed.
