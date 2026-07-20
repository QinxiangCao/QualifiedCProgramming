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
From SimpleC.EE.LLM_bench.Algorithms.manacher Require Import manacher_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Algorithms.manacher.manacher_lib.
Local Open Scope sac.

Lemma proof_of_longestPalindrom_entail_wit_1 : longestPalindrom_entail_wit_1.
Proof.
  pre_process.
  Exists (0 :: nil).
  Exists (36 :: nil).
  split_pure_spatial.
  - unfold store_string.
    sep_apply (CharArray.seg_single &( "s2") 0 36).
    sep_apply (IntArray.seg_single &( "p") 0 0).
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    replace (2 * 0 + 1) with (0 + 1) by lia.
    replace 1 with (0 + 1) by lia.
    cancel (CharArray.seg &( "s2") 0 (0 + 1) (36 :: nil)).
    replace (0 + (0 + 1)) with (0 + 1) by lia.
    cancel (CharArray.undef_seg &( "s2") (0 + 1) 2003).
    cancel (IntArray.seg &( "p") 0 (0 + 1) (0 :: nil)).
    assert (Hundef_p:
      IntArray.undef_missing_i &( "p") 0 0 2003 |--
      IntArray.undef_seg &( "p") (0 + 1) 2003).
    { apply IntArray.undef_missing_i_to_undef_seg_head; lia. }
    cancel (IntArray.undef_seg &( "p") (0 + 1) 2003).
  - split_pures; dump_pre_spatial; simpl; auto; try lia.
    unfold ManacherTransformedPrefix; simpl; repeat split; try apply Zlength_nonneg; try lia.
Qed.

Lemma proof_of_longestPalindrom_entail_wit_2 : longestPalindrom_entail_wit_2.
Proof.
  pre_process.
  Exists p_pre_2.
  Exists ((s2_pre_2 ++ 35 :: nil) ++ Znth i (c_string str) 0 :: nil).
  split_pure_spatial.
  - unfold store_string.
    replace (2 * (i + 1) + 1) with (2 * i + 1 + 1 + 1) by lia.
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (2 * i + 1 + 1 + 1)
      ((s2_pre_2 ++ 35 :: nil) ++ Znth i (c_string str) 0 :: nil)).
    replace (2 * i + 2 + 1) with (2 * i + 1 + 1 + 1) by lia.
    cancel (CharArray.undef_seg &( "s2") (2 * i + 1 + 1 + 1) 2003).
    cancel (IntArray.seg &( "p") 0 1 p_pre_2).
    cancel (IntArray.undef_seg &( "p") 1 2003).
  - split_pures; dump_pre_spatial; auto; try lia.
    + rewrite !Zlength_app_cons, PreH19. lia.
    + replace (Znth i (c_string str) 0) with (Znth i str 0).
      * apply manacher_transformed_prefix_append_char; auto.
        unfold string_length in PreH5. lia.
      * unfold c_string. rewrite app_Znth1; auto.
      unfold string_length in PreH5. lia.
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_3 : longestPalindrom_entail_wit_3.
Proof.
  pre_process.
  Exists p_pre_2.
  Exists ((s2_pre ++ 35 :: nil) ++ 0 :: nil).
  split_pure_spatial.
  - unfold store_string.
    replace (2 * i + 2 + 1) with (2 * i + 1 + 1 + 1) by lia.
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (2 * i + 1 + 1 + 1)
      ((s2_pre ++ 35 :: nil) ++ 0 :: nil)).
    cancel (CharArray.undef_seg &( "s2") (2 * i + 1 + 1 + 1) 2003).
    cancel (IntArray.seg &( "p") 0 1 p_pre_2).
    cancel (IntArray.undef_seg &( "p") 1 2003).
  - split_pures; dump_pre_spatial; auto; try lia.
    + rewrite !Zlength_app_cons, PreH19. lia.
    + apply manacher_transformed_prefix_close_string; auto.
      unfold naive_C_Rules.string_length.
      unfold string_length in PreH5.
      lia.
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_4 : longestPalindrom_entail_wit_4.
Proof.
  pre_process.
  subst i id limit maxLen maxId j r mirror ret.
  Exists p_pre.
  Exists s2_full_2.
  split_pure_spatial.
  - cancel (store_string s_pre str).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 1 p_pre).
    cancel (IntArray.undef_seg &( "p") 1 2003).
  - split_pures; dump_pre_spatial; simpl; auto; try lia.
    unfold ManacherLoopState.
    fold (ManacherTransformedString str s2_full_2 len).
    fold (RadiusTablePrefix s2_full_2 len p_pre 1).
    fold (CurrentRightmostWindow s2_full_2 len 0 0).
    fold (BestRadiusPrefix s2_full_2 len p_pre 1 0 0).
    split; [exact PreH19|].
    split.
    + unfold RadiusTablePrefix; repeat split; auto; try lia; try (intros; lia).
    + split; [lia|].
      split.
      * unfold CurrentRightmostWindow; repeat split; try lia.
      * unfold BestRadiusPrefix; repeat split; try lia; try (left; split; lia); try (intros; lia).
Qed.

Lemma proof_of_longestPalindrom_entail_wit_5 : longestPalindrom_entail_wit_5.
Proof.
  pre_process.
  Exists p_cur_2.
  Exists s2_full_2.
  split_pure_spatial.
  - cancel (store_string s_pre str).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 i p_cur_2).
    cancel (IntArray.undef_seg &( "p") i 2003).
  - split_pures; dump_pre_spatial; simpl; auto; try lia.
    all:
      unfold ManacherLoopState, CurrentRightmostWindow, CenterRadiusPalindrome in PreH26;
      destruct PreH26 as [_ [_ [[? ?] [Hwindow _]]]];
      destruct Hwindow as [_ [_ Hwindow]];
      assert (Hid_lt_limit : id < limit) by lia;
      specialize (Hwindow Hid_lt_limit);
      destruct Hwindow as [_ [_ [? _]]];
      try change (0 <= 2 * id - i);
      try change (2 * id - i < i);
      lia.
Qed.

Lemma proof_of_longestPalindrom_entail_wit_6_3 : longestPalindrom_entail_wit_6_3.
Proof.
  pre_process.
  pose proof PreH27 as Hloop_state.
  destruct PreH27 as (Htrans & Hprefix & Hid_range & Hwindow & Hbest).
  destruct Hprefix as (Hplen & Hi_range & Hprefix_max).
  pose proof Hbest as Hbest_orig.
  assert (Hcandidate: ExpansionCandidate s2_full_2 len i 1).
  {
    unfold ExpansionCandidate.
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split.
    - unfold CenterRadiusPalindrome.
      repeat split; try lia.
      intros d Hd.
      replace d with 0 by lia.
      replace (i - 0) with i by lia.
      replace (i + 0) with i by lia.
      reflexivity.
    - intros Heq.
      unfold ManacherTransformedString in Htrans.
      destruct Htrans as (_ & _ & Hstart & _ & Hend & Hnot36 & _ & Hnonzero).
      split.
      + destruct (Z_lt_ge_dec (i + 1) len); [lia|].
        assert (i + 1 = len) by lia.
        assert (0 <= i - 1 < len) by lia.
        specialize (Hnonzero (i - 1) H0).
        replace (i + 1) with len in Heq by lia.
        rewrite Hend in Heq.
        congruence.
      + destruct (Z_lt_ge_dec 0 (i - 1)); [lia|].
        assert (i - 1 = 0) by lia.
        assert (0 < i + 1 < len) by lia.
        specialize (Hnot36 (i + 1) H0).
        replace (i - 1) with 0 in Heq by lia.
        rewrite Hstart in Heq.
        congruence.
  }
  assert (Hp_len:
    Zlength (p_cur ++ 1 :: nil) = i + 1).
  {
    rewrite Zlength_app, Hplen. simpl.
    change (Zlength (1 :: nil)) with 1.
    lia.
  }
  assert (Hp_sub:
    sublist 0 i (p_cur ++ 1 :: nil) = p_cur).
  {
    replace i with (Zlength p_cur) by lia.
    apply sublist_app_exact1.
  }
  assert (Hp_i:
    Znth i (p_cur ++ 1 :: nil) 0 = 1).
  {
    rewrite app_Znth2 by lia.
    replace (i - Zlength p_cur) with 0 by lia.
    reflexivity.
  }
  assert (Hloop:
    ExpansionLoopState str s2_full_2 len
      (p_cur ++ 1 :: nil) i 1 id limit maxId maxLen).
  {
    unfold ExpansionLoopState.
    split; [exact Hp_len|].
    split.
    - rewrite Hp_sub.
      exact Hloop_state.
    - split; [exact Hp_i|exact Hcandidate].
  }
  Exists (p_cur ++ 1 :: nil).
  Exists s2_full_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (IntArray.seg &( "p") 0 (i + 1)
      (p_cur ++ 1 :: nil)).
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.undef_seg &( "p") (i + 1) 2003).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_6_2 : longestPalindrom_entail_wit_6_2.
Proof.
  pre_process.
  pose proof PreH22 as H20_orig.
  destruct PreH22 as (Htrans & Hprefix & Hid_range & Hwindow & Hbest).
  destruct Hprefix as (Hplen & Hi_range & Hprefix_max).
  destruct Hwindow as (Hid_len & Hlimit_range & Hwindow_pal).
  pose proof Hbest as Hbest_orig.
  destruct Hbest as (Hbest_range & HmaxLen_nonneg & HmaxId_range & Hbest_pal & Hbest_le & Hbest_attain).
  pose proof (Hwindow_pal ltac:(lia)) as Hwin_pal.
  assert (Hmirror_pos : 0 < mirror).
  {
    eapply manacher_mirror_positive; eauto; lia.
  }
  pose proof (Hprefix_max mirror ltac:(lia)) as Hmirror_max.
  destruct Hmirror_max as (Hmirror_pal & Hmirror_stop).
  assert (Hcandidate:
    ExpansionCandidate s2_full_2 len i (limit - i)).
  {
    replace (Znth (mirror - 0) p_cur 0) with (Znth mirror p_cur 0) in PreH1
      by (replace (mirror - 0) with mirror by lia; reflexivity).
    eapply manacher_mirror_candidate_at_limit; eauto; lia.
  }
  assert (Hp_len:
    Zlength (p_cur ++ limit - i :: nil) = i + 1).
  {
    rewrite Zlength_app, Hplen. simpl.
    change (Zlength (limit - i :: nil)) with 1.
    lia.
  }
  assert (Hp_sub:
    sublist 0 i (p_cur ++ limit - i :: nil) = p_cur).
  {
    replace i with (Zlength p_cur) by lia.
    apply sublist_app_exact1.
  }
  assert (Hp_i:
    Znth i (p_cur ++ limit - i :: nil) 0 = limit - i).
  {
    rewrite app_Znth2 by lia.
    replace (i - Zlength p_cur) with 0 by lia.
    reflexivity.
  }
  assert (Hloop:
    ExpansionLoopState str s2_full_2 len
      (p_cur ++ limit - i :: nil) i
      (limit - i) id limit maxId maxLen).
  {
    unfold ExpansionLoopState.
    split; [exact Hp_len|].
    split.
    - rewrite Hp_sub.
      exact H20_orig.
    - split; [exact Hp_i|exact Hcandidate].
  }
  Exists (p_cur ++ limit - i :: nil).
  Exists s2_full_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (IntArray.seg &( "p") 0 (i + 1) (p_cur ++ limit - i :: nil)).
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.undef_seg &( "p") (i + 1) 2003).
  - split_pures; dump_pre_spatial; auto; try lia.
    + eapply best_radius_prefix_maxLen_bound; [exact Hbest_orig|exact PreH8].
    + unfold ExpansionCandidate in Hcandidate; tauto.
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_6_1 : longestPalindrom_entail_wit_6_1.
Proof.
  pre_process.
  pose proof PreH22 as Hloop_state.
  destruct PreH22 as (Htrans & Hprefix & Hid_range & Hwindow & Hbest).
  destruct Hprefix as (Hplen & Hi_range & Hprefix_max).
  destruct Hwindow as (Hid_len & Hlimit_range & Hwindow_pal).
  pose proof Hbest as Hbest_orig.
  destruct Hbest as (Hbest_range & HmaxLen_nonneg & HmaxId_range & Hbest_pal & Hbest_le & Hbest_attain).
  pose proof (Hwindow_pal ltac:(lia)) as Hwin_pal.
  assert (Hmirror_pos : 0 < mirror).
  {
    eapply manacher_mirror_positive; eauto; lia.
  }
  pose proof (Hprefix_max mirror ltac:(lia)) as Hmirror_max.
  destruct Hmirror_max as (Hmirror_pal & Hmirror_stop).
  pose proof Hmirror_pal as Hmirror_pal_copy.
  unfold CenterRadiusPalindrome in Hmirror_pal_copy.
  destruct Hmirror_pal_copy as (_ & Hmirror_radius_pos & _ & _ & _).
  assert (Hcandidate:
    ExpansionCandidate s2_full_2 len i (Znth (mirror - 0) p_cur 0)).
  {
    replace (Znth (mirror - 0) p_cur 0) with (Znth mirror p_cur 0)
      by (replace (mirror - 0) with mirror by lia; reflexivity).
    eapply (manacher_mirror_candidate_inside
      str s2_full_2 len id limit i mirror (Znth mirror p_cur 0)).
    - exact Htrans.
    - exact PreH14.
    - lia.
    - lia.
    - lia.
    - exact Hwin_pal.
    - exact Hmirror_pal.
    - split; [exact Hmirror_radius_pos|].
      replace (Znth mirror p_cur 0) with (Znth (mirror - 0) p_cur 0)
        by (replace (mirror - 0) with mirror by lia; reflexivity).
      exact PreH1.
  }
  assert (Hp_len:
    Zlength (p_cur ++ Znth (mirror - 0) p_cur 0 :: nil) = i + 1).
  {
    rewrite Zlength_app, Hplen. simpl.
    change (Zlength (Znth (mirror - 0) p_cur 0 :: nil)) with 1.
    lia.
  }
  assert (Hp_sub:
    sublist 0 i (p_cur ++ Znth (mirror - 0) p_cur 0 :: nil) = p_cur).
  {
    replace i with (Zlength p_cur) by lia.
    apply sublist_app_exact1.
  }
  assert (Hp_i:
    Znth i (p_cur ++ Znth (mirror - 0) p_cur 0 :: nil) 0 =
    Znth (mirror - 0) p_cur 0).
  {
    rewrite app_Znth2 by lia.
    replace (i - Zlength p_cur) with 0 by lia.
    reflexivity.
  }
  assert (Hloop:
    ExpansionLoopState str s2_full_2 len
      (p_cur ++ Znth (mirror - 0) p_cur 0 :: nil) i
      (Znth (mirror - 0) p_cur 0) id limit maxId maxLen).
  {
    unfold ExpansionLoopState.
    split; [exact Hp_len|].
    split.
    - rewrite Hp_sub.
      exact Hloop_state.
    - split; [exact Hp_i|exact Hcandidate].
  }
  assert (Hcandidate_left : 0 <= i - Znth (mirror - 0) p_cur 0).
  {
    pose proof Hcandidate as Hcandidate_copy.
    unfold ExpansionCandidate in Hcandidate_copy.
    tauto.
  }
  Exists (p_cur ++ Znth (mirror - 0) p_cur 0 :: nil).
  Exists s2_full_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 (i + 1) (p_cur ++ Znth (mirror - 0) p_cur 0 :: nil)).
    cancel (IntArray.undef_seg &( "p") (i + 1) 2003).
  - split_pures; dump_pre_spatial; simpl; auto; try lia.
    + replace (mirror - 0) with mirror by lia.
      exact Hmirror_radius_pos.
    + eapply best_radius_prefix_maxLen_bound; [exact Hbest_orig|exact PreH8].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_8 : longestPalindrom_entail_wit_8.
Proof.
  pre_process.
  Exists p_written_2.
  Exists s2_full_2.
  split_pure_spatial.
  - cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 (i + 1) p_written_2).
    cancel (IntArray.undef_seg &( "p") (i + 1) 2003).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    unfold store_string.
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
  - split_pures; dump_pre_spatial; simpl; auto; try lia.
    all: assert (Hmatch_bounds: i + r < len /\ 0 < i - r) by
      (unfold ExpansionCandidate in PreH30;
       destruct PreH30 as [_ [_ [_ [_ [_ Hnext]]]]];
       apply Hnext;
       replace (i - r) with (i - r - 0) by lia;
       replace (i + r) with (i + r - 0) by lia;
        symmetry; exact PreH1).
    all: destruct Hmatch_bounds as [Hrlt Hrpos].
    + exact Hrpos.
    + exact Hrlt.
    + unfold ExpansionAfterMatch.
      split; [exact PreH30|].
      split; [exact Hrlt|].
      split; [exact Hrpos|].
      replace (i - r) with (i - r - 0) by lia.
      replace (i + r) with (i + r - 0) by lia.
      symmetry; exact PreH1.
Qed.

Lemma proof_of_longestPalindrom_entail_wit_9 : longestPalindrom_entail_wit_9.
Proof.
  pre_process.
  Exists (replace_Znth i (r + 1) p_written_2).
  Exists s2_full_2.
  split_pure_spatial.
  - cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.undef_seg &( "p") (i + 1) 2003).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    unfold store_string.
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    apply IntArray.full_to_seg.
  - split_pures; dump_pre_spatial; simpl; auto; try lia.
    all:
      unfold ExpansionAfterMatch in PreH29;
      destruct PreH29 as [Hcand_r [Hrlt [Hrpos Heq_r]]].
    + rewrite Zlength_replace_Znth, PreH27; reflexivity.
    + unfold ExpansionLoopState in *.
      destruct PreH28 as [Hlen_written [Hloop [Hzr _]]].
      split.
       * rewrite Zlength_replace_Znth, PreH27; reflexivity.
      * split.
        -- replace (sublist 0 i (replace_Znth i (r + 1) p_written_2))
             with (sublist 0 i p_written_2).
           ++ exact Hloop.
           ++ apply (proj2 (list_eq_ext _ _ 0)); split.
              ** repeat rewrite Zlength_sublist; try lia.
                  rewrite Zlength_replace_Znth, PreH27; lia.
              ** intros k Hk.
                 assert (Hk_i: 0 <= k < i).
                 {
                   rewrite Zlength_sublist in Hk; try lia.
                 }
                 rewrite Znth_sublist0 by lia.
                 rewrite Znth_sublist0 by lia.
                 rewrite Znth_replace_Znth_Diff; try lia.
        -- split.
           ++ rewrite Znth_replace_Znth_Same; try lia.
           ++ unfold ExpansionCandidate in Hcand_r.
              destruct Hcand_r as [Hci [Hr1 [Hleft [Hcand_right [Hcenter _]]]]].
              unfold CenterRadiusPalindrome in Hcenter.
              destruct Hcenter as [_ [_ [Hcenter_l [Hcenter_r Hpal]]]].
              unfold ExpansionCandidate, CenterRadiusPalindrome.
              split; [lia|].
              split; [lia|].
              split; [lia|].
              split; [lia|].
              split.
              ** split; [lia|].
                 split; [lia|].
                 split; [lia|].
                 split; [lia|].
                 intros d Hd.
                 destruct (Z_lt_ge_dec d r) as [Hdr | Hdr].
                 --- apply Hpal; lia.
                 --- assert (d = r) by lia.
                     subst d.
                     exact Heq_r.
              ** intro Heq_next.
                 unfold ManacherLoopState, ManacherTransformedString in Hloop.
                 destruct Hloop as [Htrans _].
                 destruct Htrans as [_ [_ [Hs0 [_ [Hsend [Hnot36 [_ Hnot0]]]]]]].
                 assert (Hrnext: i + (r + 1) < len).
                 {
                   destruct (Z.eq_dec (i + (r + 1)) len) as [Hend | ?]; [|lia].
                     assert (Hright: Znth (i + (r + 1)) s2_full_2 0 = 0) by
                       (rewrite Hend; exact Hsend).
                     assert (Hleft_in: 0 <= i - (r + 1) < len) by lia.
                     specialize (Hnot0 (i - (r + 1)) Hleft_in).
                     congruence.
                 }
                 assert (Hlnext: 0 < i - (r + 1)).
                 {
                   destruct (Z.eq_dec (i - (r + 1)) 0) as [Hstart | ?]; [|lia].
                     assert (Hleft0: Znth (i - (r + 1)) s2_full_2 0 = 36) by
                       (rewrite Hstart; exact Hs0).
                     assert (Hright_in: 0 < i + (r + 1) < len) by lia.
                     specialize (Hnot36 (i + (r + 1)) Hright_in).
                     congruence.
                 }
                 split; assumption.
    + unfold ExpansionCandidate in Hcand_r.
      destruct Hcand_r as [Hci [Hr1 [Hleft [Hcand_right [Hcenter _]]]]].
      unfold CenterRadiusPalindrome in Hcenter.
      destruct Hcenter as [_ [_ [Hcenter_l [Hcenter_r Hpal]]]].
      unfold ExpansionLoopState in PreH28.
      destruct PreH28 as [_ [Hloop _]].
      unfold ExpansionCandidate, CenterRadiusPalindrome.
      split; [lia|].
      split; [lia|].
      split; [lia|].
      split; [lia|].
      split.
      * split; [lia|].
        split; [lia|].
        split; [lia|].
        split; [lia|].
        intros d Hd.
        destruct (Z_lt_ge_dec d r) as [Hdr | Hdr].
        -- apply Hpal; lia.
        -- assert (d = r) by lia.
           subst d.
           exact Heq_r.
      * intro Heq_next.
        unfold ManacherLoopState, ManacherTransformedString in Hloop.
        destruct Hloop as [Htrans _].
        destruct Htrans as [_ [_ [Hs0 [_ [Hsend [Hnot36 [_ Hnot0]]]]]]].
        assert (Hrnext: i + (r + 1) < len).
        {
          destruct (Z.eq_dec (i + (r + 1)) len) as [Hend | ?]; [|lia].
           assert (Hright: Znth (i + (r + 1)) s2_full_2 0 = 0) by
             (rewrite Hend; exact Hsend).
           assert (Hleft_in: 0 <= i - (r + 1) < len) by lia.
           specialize (Hnot0 (i - (r + 1)) Hleft_in).
           congruence.
        }
        assert (Hlnext: 0 < i - (r + 1)).
        {
          destruct (Z.eq_dec (i - (r + 1)) 0) as [Hstart | ?]; [|lia].
           assert (Hleft0: Znth (i - (r + 1)) s2_full_2 0 = 36) by
             (rewrite Hstart; exact Hs0).
           assert (Hright_in: 0 < i + (r + 1) < len) by lia.
           specialize (Hnot36 (i + (r + 1)) Hright_in).
           congruence.
        }
        split; assumption.
Qed.

Lemma proof_of_longestPalindrom_entail_wit_10_4 : longestPalindrom_entail_wit_10_4.
Proof.
  pre_process.
  Exists p_written.
  Exists s2_full_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 (i + 1) p_written).
    cancel (IntArray.undef_seg &( "p") (i + 1) 2003).
  - split_pures.
    all: try (dump_pre_spatial; auto; try lia).
    destruct PreH31 as [HpLen [HLoop [HpI Hcand]]].
    eapply manacher_best_radius_keep_after_mismatch; eauto.
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_10_3 : longestPalindrom_entail_wit_10_3.
Proof.
  pre_process.
  Exists p_written.
  Exists s2_full_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 (i + 1) p_written).
    cancel (IntArray.undef_seg &( "p") (i + 1) 2003).
  - split_pures.
    all: try (dump_pre_spatial; auto; try lia).
    destruct PreH31 as [HpLen [HLoop [HpI Hcand]]].
    eapply manacher_best_radius_keep_after_mismatch_new_window; eauto.
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_10_2 : longestPalindrom_entail_wit_10_2.
Proof.
  pre_process.
  Exists p_written. Exists s2_full_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 (i + 1) p_written).
    cancel (IntArray.undef_seg &( "p") (i + 1) 2003).
  - split_pures; dump_pre_spatial; try lia; try auto.
    eapply (expansion_loop_best_update_inside
      str s2_full_2 len p_written i r id limit maxId maxLen);
      try exact PreH31; eauto; lia.
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_10_1 : longestPalindrom_entail_wit_10_1.
Proof.
  pre_process.
  Exists p_written. Exists s2_full_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 (i + 1) p_written).
    cancel (IntArray.undef_seg &( "p") (i + 1) 2003).
  - split_pures; dump_pre_spatial; try lia; try auto.
    eapply (expansion_loop_best_update_extend
      str s2_full_2 len p_written i r id limit maxId maxLen);
      try exact PreH31; eauto; lia.
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_11 : longestPalindrom_entail_wit_11.
Proof.
  pre_process.
  Exists p_next.
  Exists s2_full_2.
  split_pure_spatial.
  - cancel (store_string s_pre str).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 i p_next).
    cancel (IntArray.undef_seg &( "p") i 2003).
  - split_pures; dump_pre_spatial; simpl; auto; try lia.
    all:
      match goal with
      | Hstate : ManacherLoopState _ _ _ _ _ _ _ _ _ |- _ =>
          unfold ManacherLoopState, CurrentRightmostWindow in Hstate;
          destruct Hstate as [_ [_ [[? ?] [[? ?] _]]]]
      end;
      lia.
Qed.

Lemma proof_of_longestPalindrom_entail_wit_12 : longestPalindrom_entail_wit_12.
Proof.
  pre_process.
  assert (Hi_len : i = len) by lia.
  pose proof PreH25 as Hstate_len.
  rewrite Hi_len in Hstate_len.
  pose proof (manacher_final_selected_window_bounds
    str s2_full_2 p_cur len id limit maxId maxLen n_pre PreH4 PreH5 PreH7 Hstate_len)
    as [HmaxLen_pos [Hstart_nonneg Hend_lt]].
  Exists p_cur. Exists s2_full_2. Exists (@nil Z).
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    rewrite Hi_len.
    cancel (IntArray.seg &( "p") 0 len p_cur).
    cancel (IntArray.undef_seg &( "p") len 2003).
  - split_pures; try solve [dump_pre_spatial; eauto; lia].
    + dump_pre_spatial.
      apply output_copy_prefix_nil; lia.
    + dump_pre_spatial.
      intros cur Hcur.
      eapply (manacher_output_copy_bound_from_selected_window
        str s2_full_2 len p_cur id limit maxId maxLen n_pre cur); eauto.
Qed.

Lemma proof_of_longestPalindrom_entail_wit_13 : longestPalindrom_entail_wit_13.
Proof.
  pre_process.
  subst j. subst out_pre.
  Exists p_done_2. Exists s2_full_2. Exists nil.
  split_pure_spatial.
  - sep_apply (char_undef_full_to_full0_undef output_pre (n_pre + 1) ltac:(lia)).
    cancel (store_string s_pre str).
    cancel (CharArray.full output_pre 0 nil).
    cancel (CharArray.undef_seg output_pre 0 (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 len p_done_2).
    cancel (IntArray.undef_seg &( "p") len 2003).
  - split_pures; try solve [dump_pre_spatial; eauto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_14_1 : longestPalindrom_entail_wit_14_1.
Proof.
  pre_process.
  pose proof (output_copy_prefix_step_nonhash
    s2_full_2 out_prefix_2 (maxId - maxLen) i j maxLen
    PreH23 (PreH24 (i + 1) ltac:(lia)) PreH1) as [Hpref_step Hj_step].
  Exists p_done_2. Exists s2_full_2.
  Exists (out_prefix_2 ++ Znth (i - 0) s2_full_2 0 :: nil).
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.full output_pre (j + 1)
      (out_prefix_2 ++ Znth (i - 0) s2_full_2 0 :: nil)).
    cancel (CharArray.undef_seg output_pre (j + 1) (n_pre + 1)).
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 len p_done_2).
    cancel (IntArray.undef_seg &( "p") len 2003).
  - split_pures; try solve [dump_pre_spatial; eauto; lia].
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_14_2 : longestPalindrom_entail_wit_14_2.
Proof.
  pre_process.
  pose proof (output_copy_prefix_step_hash
    s2_full_2 out_prefix_2 (maxId - maxLen) i j maxLen
    PreH23 (PreH24 (i + 1) ltac:(lia)) PreH1) as Hpref_step.
  Exists p_done_2. Exists s2_full_2. Exists out_prefix_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.seg &( "s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.full output_pre j out_prefix_2).
    cancel (CharArray.undef_seg output_pre j (n_pre + 1)).
    cancel (CharArray.undef_seg &( "s2") (len + 1) 2003).
    cancel (IntArray.seg &( "p") 0 len p_done_2).
    cancel (IntArray.undef_seg &( "p") len 2003).
  - split_pures; try solve [dump_pre_spatial; eauto; lia].
Qed. 

Lemma proof_of_longestPalindrom_entail_wit_15 : longestPalindrom_entail_wit_15.
Proof.
  pre_process.
  assert (Hi_done : i = maxId + maxLen + 1) by lia.
  assert (Hj_done : j = maxLen).
  {
    rewrite Hi_done in PreH22.
    eapply (manacher_output_copy_prefix_full_j
      str s2_full_2 len p_done_2 id limit maxId maxLen n_pre out_prefix j); eauto.
  }
  subst i.
  rewrite Hj_done.
  rewrite Hj_done in PreH22.
  pose proof PreH26 as Hstate_bounds.
  unfold ManacherLoopState in Hstate_bounds.
  destruct Hstate_bounds as [_ [_ [Hid_bounds [Hlimit_bounds _]]]].
  unfold CurrentRightmostWindow in Hlimit_bounds.
  destruct Hlimit_bounds as [Hid_limit [Hlimit_range _]].
  assert (Hcopy_done :
    OutputCopyDone str s2_full_2 out_prefix len maxId maxLen maxLen).
  {
    eapply (manacher_output_copy_done_from_final_prefix
      str s2_full_2 len p_done_2 id limit maxId maxLen n_pre out_prefix); eauto.
  }
  assert (Hlong_done : LongestPalindromeResult str out_prefix maxLen).
  {
    eapply (manacher_longest_result_from_final_prefix
      str s2_full_2 len p_done_2 id limit maxId maxLen n_pre out_prefix); eauto.
  }
  Exists p_done_2. Exists s2_full_2. Exists out_prefix.
  split_pure_spatial.
  - unfold store_string.
    sep_apply (CharArray.seg_to_undef_seg &( "s2") 0 (len + 1) s2_full_2).
    sep_apply (char_undef_seg0_merge_to_undef_full &( "s2") (len + 1) 2003 ltac:(lia)).
    sep_apply (IntArray.seg_to_undef_seg &( "p") 0 len p_done_2).
    sep_apply (int_undef_seg0_merge_to_undef_full &( "p") len 2003 ltac:(lia)).
    cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.full output_pre (maxLen + 1) (out_prefix ++ 0 :: nil)).
    cancel (CharArray.undef_seg output_pre (maxLen + 1) (n_pre + 1)).
    cancel (CharArray.undef_full &( "s2") 2003).
    cancel (IntArray.undef_full &( "p") 2003).
  - split_pures; try solve [dump_pre_spatial; eauto; lia].
Qed.
