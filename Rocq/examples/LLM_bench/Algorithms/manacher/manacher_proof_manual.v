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

Lemma expansion_seed_append : forall str s2 len p i r id limit maxId maxLen,
  ManacherLoopState str s2 len p i id limit maxId maxLen ->
  Zlength p = i -> CenterRadiusPalindrome s2 len i r ->
  ExpansionLoopState str s2 len (p ++ r :: nil) i r id limit maxId maxLen.
Proof.
  intros str s2 len p i r id limit maxId maxLen Hloop Hlen Hpal.
  unfold ExpansionLoopState. split.
  - rewrite <- Hlen at 1. rewrite sublist_app_exact1. exact Hloop.
  - split; [|exact Hpal]. rewrite app_Znth2 by lia.
    replace (i - Zlength p) with 0 by lia. reflexivity.
Qed.

Lemma manacher_match_bounds : forall str s2 len i r,
  ManacherTransformedString str s2 len ->
  1 <= i < len -> 1 <= r -> 0 <= i - r -> i + r <= len ->
  Znth (i - r) s2 0 = Znth (i + r) s2 0 ->
  0 < i - r /\ i + r < len.
Proof.
  intros str s2 len i r Htrans Hi Hr Hl Hu Heq.
  rewrite manacher_transformed_string_iff in Htrans.
  destruct Htrans as [_ [_ [Hstart [_ [Hend [H36 [_ H0]]]]]]].
  assert (Hright : i + r < len).
  { destruct (Z.eq_dec (i + r) len); [|lia].
    specialize (H0 (i - r) ltac:(lia)). rewrite e, Hend in Heq. congruence. }
  split; [|exact Hright].
  destruct (Z.eq_dec (i - r) 0); [|lia].
  specialize (H36 (i + r) ltac:(lia)). rewrite e, Hstart in Heq. congruence.
Qed.

Lemma expansion_write_next : forall str s2 len p i r id limit maxId maxLen,
  ExpansionLoopState str s2 len p i r id limit maxId maxLen ->
  0 <= i < Zlength p -> 0 < i - r -> i + r < len ->
  Znth (i - r) s2 0 = Znth (i + r) s2 0 ->
  ExpansionLoopState str s2 len (replace_Znth i (r + 1) p)
    i (r + 1) id limit maxId maxLen.
Proof.
  intros str s2 len p i r id limit maxId maxLen [Hloop [Hpi Hpal]] Hi Hl Hu Heq.
  unfold ExpansionLoopState. split.
  - assert (Hsub : sublist 0 i (replace_Znth i (r + 1) p) = sublist 0 i p).
    { apply (proj2 (list_eq_ext _ _ 0)); split.
      - repeat rewrite Zlength_sublist; try rewrite Zlength_replace_Znth; lia.
      - intros k Hk. rewrite Zlength_sublist in Hk by (rewrite ?Zlength_replace_Znth; lia).
        rewrite !Znth_sublist0 by lia. rewrite Znth_replace_Znth_Diff by lia.
        reflexivity. }
    rewrite Hsub. exact Hloop.
  - split; [rewrite Znth_replace_Znth_Same by lia; reflexivity|].
    unfold CenterRadiusPalindrome in *.
    destruct Hpal as [Hcenter [Hradius [Hleft [Hright Hsym]]]].
    repeat split; try lia. intros d Hd.
    destruct (Z_lt_ge_dec d r); [apply Hsym; lia|].
    assert (d = r) by lia. subst d. exact Heq.
Qed.

(* The proofs below reuse the former spatial cancellation and mathematical
   arguments, with ranges extracted from array resources when needed. *)





























Lemma nonhash_sublist_length_mono : forall xs start cur finish,
  0 <= start <= cur -> cur <= finish -> finish <= Zlength xs ->
  Zlength (NonHashChars (sublist start cur xs)) <=
  Zlength (NonHashChars (sublist start finish xs)).
Proof.
  intros xs start cur finish Hstart Hcur Hfinish.
  rewrite (sublist_split start finish cur xs) by lia.
  unfold NonHashChars. rewrite filter_app, Zlength_app.
  pose proof (Zlength_nonneg (filter (fun z => negb (Z.eqb z 35)) (sublist cur finish xs))).
  lia.
Qed.










Lemma proof_of_longestPalindrom_entail_wit_1 : longestPalindrom_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  LLM_pre_process ltac:(int_auto).
  prop_apply (CharArray.seg_Zlength &("s2") 0 (2 * i + 1 + 1 + 1)
    ((s2_pre_2 ++ 35 :: nil) ++ Znth i (c_string str) 0 :: nil)).
  Intros_p Hs2. rewrite !Zlength_app_cons in Hs2.
  assert (Hprefix_len : Zlength s2_pre_2 = 2 * i + 1) by lia.
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
    replace (Znth i (c_string str) 0) with (Znth i str 0).
      * eapply manacher_transformed_prefix_append_char; eauto.
        unfold string_length in PreH4. lia.
      * unfold c_string. rewrite app_Znth1; auto.
      unfold string_length in PreH4. lia.
Qed.

Lemma proof_of_longestPalindrom_entail_wit_3 : longestPalindrom_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (CharArray.seg_Zlength &("s2") 0 (2 * i + 1 + 1 + 1)
    ((s2_pre ++ 35 :: nil) ++ 0 :: nil)).
  Intros_p Hs2. rewrite !Zlength_app_cons in Hs2.
  assert (Htrans : ManacherTransformedString str
      ((s2_pre ++ 35 :: nil) ++ 0 :: nil) (2 * i + 2)).
  { eapply manacher_transformed_prefix_close_string; eauto; try lia.
    change (Zlength str = i). change (Zlength str = n_pre) in PreH4. lia. }
  assert (Hstate : ManacherLoopState str
      ((s2_pre ++ 35 :: nil) ++ 0 :: nil) (2 * i + 2) p_pre 1 0 0 0 0).
  { unfold ManacherLoopState. split; [exact Htrans|].
    split; [intros k Hk; lia|]. split; [intros Hlt; lia|].
    rewrite best_radius_prefix_iff. repeat split; auto; intros; lia. }
  Exists ((s2_pre ++ 35 :: nil) ++ 0 :: nil). Exists p_pre.
  unfold store_string.
  replace (2 * i + 2 + 1) with (2 * i + 1 + 1 + 1) by lia.
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_4 : longestPalindrom_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH22 as Hstate.
  destruct PreH22 as [Ht [Hp [Hw Hb]]].
  pose proof (Hw ltac:(lia)) as Hpal.
  destruct Hpal as [_ [_ [Hleft _]]].
  Exists s2_full_2. Exists p_cur_2. repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_5_1 : longestPalindrom_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(int_auto). replace (mirror - 0) with mirror in * by lia.
  prop_apply (IntArray.seg_Zlength &("p") 0 (i + 1)
    (p_cur ++ Znth mirror p_cur 0 :: nil)).
  Intros_p Hplen. rewrite Zlength_app_cons in Hplen.
  pose proof PreH24 as Hstate.
  destruct PreH24 as [Ht [Hp [Hw Hb]]].
  pose proof (Hw ltac:(lia)) as Hwin.
  assert (Hmirpos : 0 < mirror) by (eapply manacher_mirror_positive; eauto; lia).
  pose proof (Hp mirror ltac:(lia)) as Hmir.
  rewrite center_radius_maximal_iff in Hmir. destruct Hmir as [Hmir _].
  assert (Hrad : 1 <= Znth mirror p_cur 0) by
    (unfold CenterRadiusPalindrome in Hmir; lia).
  pose proof (manacher_mirror_candidate_inside str s2_full_2 len id limit i mirror
    (Znth mirror p_cur 0) Ht PreH14 ltac:(lia) ltac:(lia) ltac:(lia)
    Hwin Hmir ltac:(lia)) as [_ [_ [Hleft [Hright [Hpal _]]]]].
  pose proof (expansion_seed_append str s2_full_2 len p_cur i (Znth mirror p_cur 0)
    id limit maxId maxLen Hstate ltac:(lia) Hpal) as Hexp.
  Exists s2_full_2. Exists (p_cur ++ Znth mirror p_cur 0 :: nil).
  unfold store_string. repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_5_2 : longestPalindrom_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(int_auto). replace (mirror - 0) with mirror in * by lia.
  prop_apply (IntArray.seg_Zlength &("p") 0 (i + 1) (p_cur ++ (limit - i) :: nil)).
  Intros_p Hplen. rewrite Zlength_app_cons in Hplen.
  pose proof PreH24 as Hstate.
  destruct PreH24 as [Ht [Hp [Hw Hb]]].
  pose proof (Hw ltac:(lia)) as Hwin.
  assert (Hmirpos : 0 < mirror) by (eapply manacher_mirror_positive; eauto; lia).
  pose proof (Hp mirror ltac:(lia)) as Hmir.
  rewrite center_radius_maximal_iff in Hmir. destruct Hmir as [Hmir _].
  pose proof (manacher_mirror_candidate_at_limit str s2_full_2 len id limit i mirror
    (Znth mirror p_cur 0) Ht PreH14 ltac:(lia) ltac:(lia) ltac:(lia)
    Hwin Hmir PreH1) as [_ [_ [Hleft [Hright [Hpal _]]]]].
  pose proof (expansion_seed_append str s2_full_2 len p_cur i (limit - i)
    id limit maxId maxLen Hstate ltac:(lia) Hpal) as Hexp.
  Exists s2_full_2. Exists (p_cur ++ (limit - i) :: nil).
  unfold store_string. repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_5_3 : longestPalindrom_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.seg_Zlength &("p") 0 (i + 1) (p_cur ++ 1 :: nil)).
  Intros_p Hplen. rewrite Zlength_app_cons in Hplen.
  assert (Hpal : CenterRadiusPalindrome s2_full_2 len i 1).
  { unfold CenterRadiusPalindrome. repeat split; try lia.
    intros d Hd. assert (d = 0) by lia. subst d.
    replace (i - 0) with i by lia. replace (i + 0) with i by lia. reflexivity. }
  pose proof (expansion_seed_append str s2_full_2 len p_cur i 1
    id limit maxId maxLen PreH23 ltac:(lia) Hpal) as Hexp.
  Exists s2_full_2. Exists (p_cur ++ 1 :: nil).
  unfold store_string. repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_6 : longestPalindrom_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Ht : ManacherTransformedString str s2_full_2 len) by
    (destruct PreH25 as [[Ht _] _]; exact Ht).
  replace (i + r - 0) with (i + r) in PreH1 by lia.
  replace (i - r - 0) with (i - r) in PreH1 by lia.
  pose proof (manacher_match_bounds str s2_full_2 len i r Ht
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(symmetry; exact PreH1))
    as [Hl Hu].

  prop_apply (IntArray.full_Zlength &("p") (i + 1)
    (replace_Znth i (r + 1) p_written_2)).
  Intros_p Hplen. rewrite Zlength_replace_Znth in Hplen.
  pose proof (expansion_write_next str s2_full_2 len p_written_2 i r
    id limit maxId maxLen PreH25 ltac:(lia) Hl Hu ltac:(symmetry; exact PreH1)) as Hexp.
  Exists s2_full_2. Exists (replace_Znth i (r + 1) p_written_2).
  unfold store_string.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (string_length str + 1) (c_string str)).
    cancel (CharArray.undef_full output_pre (n_pre + 1)).
    cancel (CharArray.seg &("s2") 0 (len + 1) s2_full_2).
    cancel (CharArray.undef_seg &("s2") (len + 1) 2003).
    cancel (IntArray.undef_seg &("p") (i + 1) 2003).
    apply IntArray.full_to_seg.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_longestPalindrom_entail_wit_7_1 : longestPalindrom_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH27 as [Hloop [Hpi Hpal]].
  replace (i + r - 0) with (i + r) in PreH3 by lia.
  replace (i - r - 0) with (i - r) in PreH3 by lia.
  pose proof (manacher_loop_step str s2_full_2 len p_written i r id limit maxId maxLen
    Hloop Hpal PreH3 Hpi PreH10) as Hnext.
  destruct (Z_lt_dec limit (i + r)) in Hnext; try lia;
    destruct (Z_lt_dec maxLen (r - 1)) in Hnext; try lia.
  Exists s2_full_2. Exists p_written.
  unfold store_string.
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_7_2 : longestPalindrom_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH27 as [Hloop [Hpi Hpal]].
  replace (i + r - 0) with (i + r) in PreH3 by lia.
  replace (i - r - 0) with (i - r) in PreH3 by lia.
  pose proof (manacher_loop_step str s2_full_2 len p_written i r id limit maxId maxLen
    Hloop Hpal PreH3 Hpi PreH10) as Hnext.
  destruct (Z_lt_dec limit (i + r)) in Hnext; try lia;
    destruct (Z_lt_dec maxLen (r - 1)) in Hnext; try lia.
  Exists s2_full_2. Exists p_written.
  unfold store_string.
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_7_3 : longestPalindrom_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH27 as [Hloop [Hpi Hpal]].
  replace (i + r - 0) with (i + r) in PreH3 by lia.
  replace (i - r - 0) with (i - r) in PreH3 by lia.
  pose proof (manacher_loop_step str s2_full_2 len p_written i r id limit maxId maxLen
    Hloop Hpal PreH3 Hpi PreH10) as Hnext.
  destruct (Z_lt_dec limit (i + r)) in Hnext; try lia;
    destruct (Z_lt_dec maxLen (r - 1)) in Hnext; try lia.
  Exists s2_full_2. Exists p_written.
  unfold store_string.
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_7_4 : longestPalindrom_entail_wit_7_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH27 as [Hloop [Hpi Hpal]].
  replace (i + r - 0) with (i + r) in PreH3 by lia.
  replace (i - r - 0) with (i - r) in PreH3 by lia.
  pose proof (manacher_loop_step str s2_full_2 len p_written i r id limit maxId maxLen
    Hloop Hpal PreH3 Hpi PreH10) as Hnext.
  destruct (Z_lt_dec limit (i + r)) in Hnext; try lia;
    destruct (Z_lt_dec maxLen (r - 1)) in Hnext; try lia.
  Exists s2_full_2. Exists p_written.
  unfold store_string.
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_8 : longestPalindrom_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = len) by lia. subst i.
  pose proof (manacher_final_selected_window_bounds
    str s2_full_2 p_cur len id limit maxId maxLen n_pre
    PreH3 PreH4 PreH6 PreH21) as [Hpositive [Hleft Hright]].
  pose proof (manacher_selected_window_nonhash_length
    str s2_full_2 len p_cur id limit maxId maxLen n_pre
    PreH2 PreH3 PreH4 PreH6 PreH21) as Hcopy_len.
  assert (Hcopy : OutputCopyPrefix s2_full_2
    (NonHashChars (sublist (maxId - maxLen) (maxId + maxLen + 1) s2_full_2))
    (maxId - maxLen) (maxId + maxLen + 1) maxLen).
  { split; [reflexivity|symmetry; exact Hcopy_len]. }
  pose proof (manacher_longest_result_from_final_prefix
    str s2_full_2 len p_cur id limit maxId maxLen n_pre _
    PreH2 PreH3 PreH4 PreH6 PreH21 Hcopy) as Hresult.
  assert (Hempty : OutputCopyPrefix s2_full_2 nil (maxId - maxLen) (maxId - maxLen) 0).
  { unfold OutputCopyPrefix. rewrite Zsublist_nil by lia. split; reflexivity. }
  Exists p_cur. Exists s2_full_2. Exists (@nil Z).
  sep_apply (char_undef_full_to_full0_undef output_pre (n_pre + 1) ltac:(lia)).
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_9_1 : longestPalindrom_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (CharArray.seg_Zlength &("s2") 0 (len + 1) s2_full_2).
  Intros_p Hs2.
  pose proof PreH23 as [Hlen _].
  assert (Hbound : 0 <= maxId - maxLen /\ maxId - maxLen <= i + 1 /\
    i + 1 <= Zlength s2_full_2 /\
    Zlength (NonHashChars (sublist (maxId - maxLen) (i + 1) s2_full_2)) <= maxLen).
  { repeat split; try lia. rewrite Hlen at 2.
    apply nonhash_sublist_length_mono; lia. }
  pose proof (output_copy_prefix_step_nonhash s2_full_2 out_prefix_2
    (maxId - maxLen) i j maxLen ltac:(lia) PreH22 Hbound PreH1) as [Hpref Hbound_j].
  Exists p_done_2. Exists s2_full_2.
  Exists (out_prefix_2 ++ Znth (i - 0) s2_full_2 0 :: nil).
  unfold store_string.
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_9_2 : longestPalindrom_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (CharArray.seg_Zlength &("s2") 0 (len + 1) s2_full_2).
  Intros_p Hs2.
  pose proof PreH23 as [Hlen _].
  assert (Hbound : 0 <= maxId - maxLen /\ maxId - maxLen <= i + 1 /\
    i + 1 <= Zlength s2_full_2 /\
    Zlength (NonHashChars (sublist (maxId - maxLen) (i + 1) s2_full_2)) <= maxLen).
  { repeat split; try lia. rewrite Hlen at 2.
    apply nonhash_sublist_length_mono; lia. }
  pose proof (output_copy_prefix_step_hash s2_full_2 out_prefix_2
    (maxId - maxLen) i j maxLen ltac:(lia) PreH22 Hbound PreH1) as Hpref.
  Exists p_done_2. Exists s2_full_2. Exists out_prefix_2.
  unfold store_string.
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_entail_wit_10 : longestPalindrom_entail_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = maxId + maxLen + 1) by lia. subst i.
  destruct PreH20 as [Hout Hj].
  assert (Hresult : LongestPalindromeResult str out_prefix_2 maxLen).
  { rewrite Hout. exact PreH21. }
  assert (Hj_done : j = maxLen) by (destruct Hresult as [Hlen _]; lia).
  Exists out_prefix_2.
  sep_apply (CharArray.seg_to_undef_seg &("s2") 0 (len + 1) s2_full).
  sep_apply (char_undef_seg0_merge_to_undef_full &("s2") (len + 1) 2003 ltac:(lia)).
  sep_apply (IntArray.seg_to_undef_seg &("p") 0 len p_done).
  sep_apply (int_undef_seg0_merge_to_undef_full &("p") len 2003 ltac:(lia)).
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_longestPalindrom_return_wit_1 : longestPalindrom_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst j. unfold store_string.
  Exists out_prefix.
  repeat (split_pure_spatial || split_pures);
    try solve [repeat cancel | dump_pre_spatial; auto; lia].
Qed.
