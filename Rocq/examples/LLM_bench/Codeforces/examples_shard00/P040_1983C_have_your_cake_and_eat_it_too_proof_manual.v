From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P040_1983C_have_your_cake_and_eat_it_too_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P040_1983C_have_your_cake_and_eat_it_too_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib.
Local Open Scope sac.

Lemma proof_of_try_order_safety_wit_11_split_goal_1 : try_order_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 who pos ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_try_order_safety_wit_11_split_goal_2 : try_order_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 who pos ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_try_order_safety_wit_11 : try_order_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_try_order_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_try_order_safety_wit_20_split_goal_1 : try_order_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH6 who i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_try_order_safety_wit_20_split_goal_2 : try_order_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH6 who i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_try_order_safety_wit_20 : try_order_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_try_order_safety_wit_20_split_goal_2.
Qed.

Lemma proof_of_try_order_entail_wit_1_split_goal_1 : try_order_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyRawState.
  repeat split; try assumption; try lia.
  - repeat rewrite Znth0_cons. lia.
Qed.

Lemma proof_of_try_order_entail_wit_1_split_goal_2 : try_order_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Pre in PreH6.
  destruct PreH6 as (_ & _ & _ & HFa & _).
  pose proof (cake_sum_bounds_from_forall__try_initialization a HFa) as [Hsumlo Hsum].
  change (ListLib.sum a <= Zlength a * 1000000) in Hsum.
  assert (Htotal : 0 <= ListLib.sum a).
  { change (0 <= CakeSum a). lia. }
  subst need_pre.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_le_upper_bound.
  - lia.
  - nia.
Qed.

Lemma proof_of_try_order_entail_wit_1_split_goal_3 : try_order_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Pre in PreH6.
  destruct PreH6 as (_ & _ & _ & HFa & _).
  pose proof (cake_sum_bounds_from_forall__try_initialization a HFa) as [Hsum _].
  change (Zlength a <= ListLib.sum a) in Hsum.
  assert (Htotal : 0 <= ListLib.sum a).
  { lia. }
  subst need_pre.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_le_lower_bound.
  all: lia.
Qed.

Lemma proof_of_try_order_entail_wit_1 : try_order_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_try_order_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_try_order_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_try_order_entail_wit_2 : try_order_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  remember (Znth part ord 0) as who.
  assert (Hwho : 0 <= who < 3).
  {
    assert (Hpart : part = 0 \/ part = 1) by lia.
    destruct Hpart as [-> | ->];
      unfold CakeOrder in PreH12;
      destruct PreH12 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      unfold Znth in Heqwho; simpl in Heqwho; lia.
  }
  clear Heqwho.
  assert (Hrowlen :
    Zlength (Znth who (a :: b :: c :: nil) nil) = n_pre).
  {
    destruct (Z.eq_dec who 0) as [-> | Hn0].
    - unfold Znth. simpl. lia.
    - destruct (Z.eq_dec who 1) as [-> | Hn1].
      + unfold Znth. simpl. lia.
      + assert (who = 2) by lia. subst who.
        unfold Znth. simpl. lia.
  }
  sep_apply (Int64PtrArray2.full_split_to_missing_i
    v_pre who 3 (a :: b :: c :: nil) Hwho).
  Intros row_ptr.
  Exists row_ptr lefts_2 rights_2.
  rewrite <- Hrowlen.
  split_pure_spatial.
  - cancel (Int64PtrArray2.missing_i v_pre 3 who row_ptr
      (a :: b :: c :: nil)).
    cancel ((v_pre + who * sizeof (PTR)) # Ptr |-> row_ptr).
    cancel (Int64Array.full row_ptr
      (Zlength (Znth who (a :: b :: c :: nil) nil))
      (Znth who (a :: b :: c :: nil) nil)).
    cancel (IntArray.full order_pre 3 ord).
    cancel (IntArray.full (&("left")) 3 lefts_2).
    cancel (IntArray.full (&("right")) 3 rights_2).
    cancel (IntArray.undef_full out_pre 6).
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_try_order_entail_wit_3_split_goal_1 : try_order_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyRawState in PreH20.
  destruct PreH20 as (_ & _ & _ & _ & Hpos & _).
  repeat rewrite Znth0_cons in Hpos.
  subst pos acc n_pre.
  unfold SearchPrefixState.
  assert (Hcases : who = 0 \/ who = 1 \/ who = 2) by lia.
  destruct Hcases as [-> | [-> | ->]];
    repeat rewrite Znth_cons by lia;
    repeat rewrite Znth0_cons;
    repeat split; try lia;
    try (rewrite Zsublist_nil by lia; reflexivity);
    intros q Hq; lia.
Qed.

Lemma proof_of_try_order_entail_wit_3_split_goal_2 : try_order_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyRawState in PreH20.
  destruct PreH20 as (_ & _ & _ & _ & Hpos & _).
  repeat rewrite Znth0_cons in Hpos.
  subst pos n_pre.
  lia.
Qed.

Lemma proof_of_try_order_entail_wit_3_split_goal_3 : try_order_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyRawState in PreH20.
  destruct PreH20 as (_ & _ & _ & _ & Hpos & _).
  repeat rewrite Znth0_cons in Hpos.
  subst pos.
  lia.
Qed.

Lemma proof_of_try_order_entail_wit_3_split_goal_4 : try_order_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyRawState in PreH20.
  destruct PreH20 as (_ & _ & _ & _ & Hpos & _).
  repeat rewrite Znth0_cons in Hpos.
  subst pos n_pre.
  lia.
Qed.

Lemma proof_of_try_order_entail_wit_3_split_goal_5 : try_order_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyRawState in PreH20.
  destruct PreH20 as (_ & _ & _ & _ & Hpos & _).
  repeat rewrite Znth0_cons in Hpos.
  subst pos.
  lia.
Qed.

Lemma proof_of_try_order_entail_wit_3 : try_order_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_try_order_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_try_order_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_try_order_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_try_order_entail_wit_3_split_goal_5.
Qed.

Lemma proof_of_try_order_entail_wit_4_split_goal_1 : try_order_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SearchPrefixState in *.
  destruct PreH27 as (Hstart & Hstartpos & Hposlen & Hacc & Hminimal).
  assert (Hwho : who = 0 \/ who = 1 \/ who = 2) by lia.
  assert (Hrowlen : Zlength (Znth who (a :: b :: c :: nil) nil) = n_pre).
  { destruct Hwho as [-> | [-> | ->]].
    - repeat rewrite Znth0_cons. lia.
    - rewrite Znth_cons by lia. repeat rewrite Znth0_cons. lia.
    - repeat rewrite Znth_cons by lia. repeat rewrite Znth0_cons. lia. }
  repeat split; try lia.
  - rewrite (sublist_split start (pos + 1) pos) by lia.
    rewrite (@sublist_single Z 0 pos (Znth who (a :: b :: c :: nil) nil)) by lia.
    unfold CakeSum in *.
    rewrite ListLib.sum_app.
    simpl.
    unfold ListLib.sum in *.
    lia.
  - intros q Hq.
    destruct (Z_lt_ge_dec q pos) as [Hlt | Hge].
    + apply Hminimal. lia.
    + assert (q = pos) by lia. subst q. lia.
Qed.

Lemma proof_of_try_order_entail_wit_4_split_goal_2 : try_order_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH7 who pos ltac:(lia)) as Hvalue.
  assert (Hsum : 0 <= ListLib.sum a < Z.of_nat (length a) * 1000001).
  { apply ListLib.sum_bound_lt.
    - intro Ha. rewrite Ha, Zlength_nil in PreH3. lia.
    - intros i Hi.
      specialize (PreH7 0 i ltac:(rewrite Zlength_correct; lia)).
      repeat rewrite Znth0_cons in PreH7.
      lia. }
  rewrite <- Zlength_correct in Hsum.
  assert (Hneedcap : need_pre <= 66666733334).
  { rewrite PreH10. apply Z.quot_le_upper_bound; nia. }
  lia.
Qed.

Lemma proof_of_try_order_entail_wit_4_split_goal_3 : try_order_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 who pos ltac:(lia)).
  lia.
Qed.

Lemma proof_of_try_order_entail_wit_4 : try_order_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_try_order_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_try_order_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_try_order_entail_wit_5_1_split_goal_1 : try_order_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_try_order_entail_wit_5_1_split_goal_spatial : try_order_entail_wit_5_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hwho : who = 0 \/ who = 1 \/ who = 2) by lia.
  assert (Hrowlen : Zlength (Znth who (a :: b :: c :: nil) nil) = n_pre).
  { destruct Hwho as [-> | [-> | ->]].
    - repeat rewrite Znth0_cons. lia.
    - rewrite Znth_cons by lia. repeat rewrite Znth0_cons. lia.
    - repeat rewrite Znth_cons by lia. repeat rewrite Znth0_cons. lia. }
  rewrite <- Hrowlen.
  rewrite <- (replace_Znth_Znth who (a :: b :: c :: nil) nil) at 4.
  sep_apply_r_atomic (Int64PtrArray2.missing_i_merge_to_full
    v_pre who 3 row_ptr (a :: b :: c :: nil)
    (Znth who (a :: b :: c :: nil) nil) ltac:(lia)).
  cancel.
  unfold StorePtrAsElement.storeA.
  cancel.
  unfold Int64Array.full, Int64PtrArray2.ElemArray.full.
  cancel.
Qed.

Lemma proof_of_try_order_entail_wit_5_1 : try_order_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_entail_wit_5_1_split_goal_spatial.
  - Goal_apply proof_of_try_order_entail_wit_5_1_split_goal_1.
Qed.

Lemma proof_of_try_order_entail_wit_5_2_split_goal_1 : try_order_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SearchPrefixState in PreH27.
  dump_pre_spatial.
  tauto.
Qed.

Lemma proof_of_try_order_entail_wit_5_2_split_goal_2 : try_order_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_try_order_entail_wit_5_2_split_goal_spatial : try_order_entail_wit_5_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hwho : who = 0 \/ who = 1 \/ who = 2) by lia.
  assert (Hrowlen : Zlength (Znth who (a :: b :: c :: nil) nil) = n_pre).
  { destruct Hwho as [-> | [-> | ->]].
    - repeat rewrite Znth0_cons. lia.
    - rewrite Znth_cons by lia. repeat rewrite Znth0_cons. lia.
    - repeat rewrite Znth_cons by lia. repeat rewrite Znth0_cons. lia. }
  rewrite <- Hrowlen.
  rewrite <- (replace_Znth_Znth who (a :: b :: c :: nil) nil) at 4.
  sep_apply_r_atomic (Int64PtrArray2.missing_i_merge_to_full
    v_pre who 3 row_ptr (a :: b :: c :: nil)
    (Znth who (a :: b :: c :: nil) nil) ltac:(lia)).
  cancel.
  unfold StorePtrAsElement.storeA.
  cancel.
  unfold Int64Array.full, Int64PtrArray2.ElemArray.full.
  cancel.
Qed.

Lemma proof_of_try_order_entail_wit_5_2 : try_order_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_entail_wit_5_2_split_goal_spatial.
  - Goal_apply proof_of_try_order_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_try_order_entail_wit_5_2_split_goal_2.
Qed.

Lemma proof_of_try_order_entail_wit_6_split_goal_1 : try_order_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SearchPrefixState in PreH22.
  unfold GreedyRawState in PreH21.
  destruct PreH22 as (Hs0 & Hspos & Hsend & Haccsum & Hsearchmin).
  destruct PreH21 as
    (Hcake & Hleftlen & Hrightlen & Hpart & Hrawpos & Hdone & Hstarteq).
  assert (Hposn : pos = n_pre) by lia.
  subst pos.
  assert (Hna : forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0).
  { intros k Hk. specialize (PreH6 0 k ltac:(lia)).
    repeat rewrite Znth0_cons in PreH6. lia. }
  assert (Hnb : forall k, 0 <= k < Zlength b -> 0 <= Znth k b 0).
  { intros k Hk. specialize (PreH6 1 k ltac:(lia)).
    rewrite Znth_cons in PreH6 by lia.
    repeat rewrite Znth0_cons in PreH6. lia. }
  assert (Hnc : forall k, 0 <= k < Zlength c -> 0 <= Znth k c 0).
  { intros k Hk. specialize (PreH6 2 k ltac:(lia)).
    repeat rewrite Znth_cons in PreH6 by lia.
    repeat rewrite Znth0_cons in PreH6. lia. }
  pose proof (sum_nonnegative_pointwise__try_terminal_semantics a Hna) as Htotalnon.
  assert (HneedDiv : need_pre = (ListLib.sum a + 2) / 3).
  { rewrite <- Z.quot_div_nonneg by lia. exact PreH9. }
  unfold TryOrderSpec.
  intros bounds Hvalid Hordered.
  unfold ValidCakeDivision in Hvalid.
  destruct Hvalid as
    (la & ra & lb & rb & lc & rc & total & Hboundseq & Htotal &
     Hla & Hra & Hlb & Hrb & Hlc & Hrc & Hab & Hac & Hbc &
     Hva & Hvb & Hvc).
  subst bounds. subst total.
  assert (HvaNeed : need_pre <= CakeSum (sublist la (ra + 1) a)).
  { apply (proj2 (ceil_third_threshold__try_terminal_semantics
      (ListLib.sum a) need_pre (CakeSum (sublist la (ra + 1) a))
      Htotalnon HneedDiv)).
    unfold CakeSum, ListLib.sum in *. lia. }
  assert (HvbNeed : need_pre <= CakeSum (sublist lb (rb + 1) b)).
  { apply (proj2 (ceil_third_threshold__try_terminal_semantics
      (ListLib.sum a) need_pre (CakeSum (sublist lb (rb + 1) b))
      Htotalnon HneedDiv)).
    unfold CakeSum, ListLib.sum in *. lia. }
  assert (HvcNeed : need_pre <= CakeSum (sublist lc (rc + 1) c)).
  { apply (proj2 (ceil_third_threshold__try_terminal_semantics
      (ListLib.sum a) need_pre (CakeSum (sublist lc (rc + 1) c))
      Htotalnon HneedDiv)).
    unfold CakeSum, ListLib.sum in *. lia. }
  unfold OrderedBy, BoundLeft, BoundRight in Hordered.
  destruct Hordered as (_ & Hord12 & Hord23).
  assert (Hpartcases : part = 0 \/ part = 1) by lia.
  destruct Hcake as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    destruct Hpartcases as [-> | ->];
    cbn [Znth CakeSumboolIf] in PreH14, Hstarteq, Haccsum, Hsearchmin,
      Hdone, Hord12, Hord23;
    subst who.
  all: unfold Znth, CakeSumboolIf in
    Hstarteq, Haccsum, Hsearchmin, Hsend, Hord12, Hord23;
    simpl in Hstarteq, Haccsum, Hsearchmin, Hsend, Hord12, Hord23.
  all: try (
    subst start;
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      a 0 la (ra + 1) n_pre Hna ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc;
    unfold CakeSum, ListLib.sum in *; lia).
  all: try (
    subst start;
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      b 0 lb (rb + 1) n_pre Hnb ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc;
    unfold CakeSum, ListLib.sum in *; lia).
  all: try (
    subst start;
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      c 0 lc (rc + 1) n_pre Hnc ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc;
    unfold CakeSum, ListLib.sum in *; lia).
  all: specialize (Hdone 0 ltac:(lia));
    unfold Znth, CakeSumboolIf in Hdone;
    simpl in Hdone;
    destruct Hdone as
      (Hdwho & Hdlo & Hdlr & Hdhi & Hdstart & Hdsum & Hdmin);
    cbn [Pos.to_nat] in Hdlo, Hdlr, Hdhi, Hdstart, Hdsum, Hdmin;
    subst start.
  - assert (Hcut : List.nth 0 rights_2 0 <= ra + 1).
    { destruct (Z_le_gt_dec (List.nth 0 rights_2 0) (ra + 1)) as [Hle | Hgt]; [lia|].
      change (List.nth 0 rights_2 0 > ra + 1) in Hgt.
      assert (Hrange : List.nth 0 lefts_2 0 - 1 <= ra + 1 <
                       List.nth 0 rights_2 0).
      { rewrite Hdstart. split; lia. }
      specialize (Hdmin (ra + 1) Hrange).
      rewrite Hdstart in Hdmin. simpl in Hdmin.
      pose proof (sum_sublist_inclusion__try_terminal_semantics
        a 0 la (ra + 1) (ra + 1) Hna ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
      unfold CakeSum, ListLib.sum in *. lia. }
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      b (List.nth 0 rights_2 0) lb (rb + 1) n_pre Hnb
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
    unfold CakeSum, ListLib.sum in *. lia.
  - assert (Hcut : List.nth 0 rights_2 0 <= ra + 1).
    { destruct (Z_le_gt_dec (List.nth 0 rights_2 0) (ra + 1)); [lia|].
      assert (Hrange : List.nth 0 lefts_2 0 - 1 <= ra + 1 <
                       List.nth 0 rights_2 0) by (rewrite Hdstart; lia).
      specialize (Hdmin (ra + 1) Hrange).
      rewrite Hdstart in Hdmin. simpl in Hdmin.
      pose proof (sum_sublist_inclusion__try_terminal_semantics
        a 0 la (ra + 1) (ra + 1) Hna ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
      unfold CakeSum, ListLib.sum in *. lia. }
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      c (List.nth 0 rights_2 0) lc (rc + 1) n_pre Hnc
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
    unfold CakeSum, ListLib.sum in *. lia.
  - assert (Hcut : List.nth (Pos.to_nat 1) rights_2 0 <= rb + 1).
    { destruct (Z_le_gt_dec (List.nth (Pos.to_nat 1) rights_2 0) (rb + 1)); [lia|].
      assert (Hrange : List.nth (Pos.to_nat 1) lefts_2 0 - 1 <= rb + 1 <
                       List.nth (Pos.to_nat 1) rights_2 0) by (rewrite Hdstart; lia).
      specialize (Hdmin (rb + 1) Hrange).
      rewrite Hdstart in Hdmin. simpl in Hdmin.
      pose proof (sum_sublist_inclusion__try_terminal_semantics
        b 0 lb (rb + 1) (rb + 1) Hnb ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
      unfold CakeSum, ListLib.sum in *. lia. }
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      a (List.nth (Pos.to_nat 1) rights_2 0) la (ra + 1) n_pre Hna
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
    unfold CakeSum, ListLib.sum in *. lia.
  - assert (Hcut : List.nth (Pos.to_nat 1) rights_2 0 <= rb + 1).
    { destruct (Z_le_gt_dec (List.nth (Pos.to_nat 1) rights_2 0) (rb + 1)); [lia|].
      assert (Hrange : List.nth (Pos.to_nat 1) lefts_2 0 - 1 <= rb + 1 <
                       List.nth (Pos.to_nat 1) rights_2 0) by (rewrite Hdstart; lia).
      specialize (Hdmin (rb + 1) Hrange).
      rewrite Hdstart in Hdmin. simpl in Hdmin.
      pose proof (sum_sublist_inclusion__try_terminal_semantics
        b 0 lb (rb + 1) (rb + 1) Hnb ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
      unfold CakeSum, ListLib.sum in *. lia. }
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      c (List.nth (Pos.to_nat 1) rights_2 0) lc (rc + 1) n_pre Hnc
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
    unfold CakeSum, ListLib.sum in *. lia.
  - assert (Hcut : List.nth (Pos.to_nat 2) rights_2 0 <= rc + 1).
    { destruct (Z_le_gt_dec (List.nth (Pos.to_nat 2) rights_2 0) (rc + 1)); [lia|].
      assert (Hrange : List.nth (Pos.to_nat 2) lefts_2 0 - 1 <= rc + 1 <
                       List.nth (Pos.to_nat 2) rights_2 0) by (rewrite Hdstart; lia).
      specialize (Hdmin (rc + 1) Hrange).
      rewrite Hdstart in Hdmin. simpl in Hdmin.
      pose proof (sum_sublist_inclusion__try_terminal_semantics
        c 0 lc (rc + 1) (rc + 1) Hnc ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
      unfold CakeSum, ListLib.sum in *. lia. }
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      a (List.nth (Pos.to_nat 2) rights_2 0) la (ra + 1) n_pre Hna
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
    unfold CakeSum, ListLib.sum in *. lia.
  - assert (Hcut : List.nth (Pos.to_nat 2) rights_2 0 <= rc + 1).
    { destruct (Z_le_gt_dec (List.nth (Pos.to_nat 2) rights_2 0) (rc + 1)); [lia|].
      assert (Hrange : List.nth (Pos.to_nat 2) lefts_2 0 - 1 <= rc + 1 <
                       List.nth (Pos.to_nat 2) rights_2 0) by (rewrite Hdstart; lia).
      specialize (Hdmin (rc + 1) Hrange).
      rewrite Hdstart in Hdmin. simpl in Hdmin.
      pose proof (sum_sublist_inclusion__try_terminal_semantics
        c 0 lc (rc + 1) (rc + 1) Hnc ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
      unfold CakeSum, ListLib.sum in *. lia. }
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      b (List.nth (Pos.to_nat 2) rights_2 0) lb (rb + 1) n_pre Hnb
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
    unfold CakeSum, ListLib.sum in *. lia.
Qed.

Lemma proof_of_try_order_entail_wit_6_split_goal_2 : try_order_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SearchPrefixState in PreH22.
  destruct PreH22 as (Hs0 & Hspos & Hsend & Haccsum & Hsearchmin).
  assert (Hrowlen :
      Zlength (Znth who (a :: b :: c :: nil) nil) = Zlength a).
  { assert (who = 0 \/ who = 1 \/ who = 2) as [-> | [-> | ->]] by lia;
      unfold Znth; simpl; lia. }
  assert (Hnonneg : forall k,
      0 <= k < Zlength (Znth who (a :: b :: c :: nil) nil) ->
      0 <= Znth k (Znth who (a :: b :: c :: nil) nil) 0).
  { intros k Hk. specialize (PreH6 who k ltac:(lia)). lia. }
  pose proof (sum_sublist_nonnegative__try_terminal_semantics
    (Znth who (a :: b :: c :: nil) nil) start pos Hnonneg
    ltac:(lia) ltac:(lia)) as Hsum.
  unfold CakeSum, ListLib.sum in *. lia.
Qed.

Lemma proof_of_try_order_entail_wit_6 : try_order_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_try_order_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_try_order_entail_wit_7_split_goal_1 : try_order_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyRawState in PreH21 |- *.
  unfold SearchPrefixState in PreH22.
  destruct PreH21 as
    (Hcake & Hleftlen & Hrightlen & Hpart & Hrawpos & Hdone & Hstarteq).
  destruct PreH22 as (Hs0 & Hspos & Hsend & Haccsum & Hsearchmin).
  assert (Hrowlen :
      Zlength (Znth who (a :: b :: c :: nil) nil) = Zlength a).
  { assert (who = 0 \/ who = 1 \/ who = 2) as [-> | [-> | ->]] by lia;
      unfold Znth; simpl; lia. }
  assert (Hna : forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0).
  { intros k Hk. specialize (PreH6 0 k ltac:(lia)).
    repeat rewrite Znth0_cons in PreH6. lia. }
  pose proof (sum_nonnegative_pointwise__try_terminal_semantics a Hna) as Htotalnon.
  assert (Htotalpos : 0 < ListLib.sum a).
  { pose proof (sum_sublist_inclusion__try_terminal_semantics
      a 0 0 1 (Zlength a) Hna ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
    pose proof (@sublist_app_exact1 Z a nil) as Hfull.
    rewrite app_nil_r in Hfull. rewrite Hfull in Hinc.
    rewrite (sublist_single 0 0) in Hinc by lia.
    specialize (PreH6 0 0 ltac:(lia)).
    repeat rewrite Znth0_cons in PreH6.
    unfold ListLib.sum in Hinc |- *. simpl in Hinc. lia. }
  assert (Hneedpos : 1 <= need_pre).
  { assert (HneedDiv : need_pre = (ListLib.sum a + 2) / 3).
    { rewrite <- Z.quot_div_nonneg by lia. exact PreH9. }
    rewrite HneedDiv. apply Z.div_le_lower_bound; lia. }
  assert (Hstartlt : start < pos).
  { destruct (Z.eq_dec start pos) as [-> | Hneq]; [|lia].
    rewrite Zsublist_nil in Haccsum by lia.
    unfold CakeSum, ListLib.sum in Haccsum. simpl in Haccsum. lia. }
  split; [exact Hcake|].
  split; [rewrite Zlength_replace_Znth; exact Hleftlen|].
  split; [rewrite Zlength_replace_Znth; exact Hrightlen|].
  split; [lia|].
  split.
  { unfold Znth. simpl. lia. }
  split.
  { intros k Hk.
    destruct (Z.eq_dec k part) as [-> | Hkp].
    - rewrite <- PreH14.
      repeat rewrite Znth_replace_Znth_Same by lia.
      repeat split; try lia; try exact Hsend.
      + assert (part = 0 \/ part = 1) as [-> | ->] by lia.
        * unfold CakeSumboolIf in Hstarteq |- *. simpl in *. lia.
        * assert (Hneqprev : Znth 0 ord 0 <> who).
          { rewrite PreH14.
            destruct Hcake as [-> | [-> | [-> | [-> | [-> | ->]]]]];
              unfold Znth; simpl; lia. }
          assert (Hprevbounds : 0 <= Znth 0 ord 0 < 3).
          { destruct Hcake as [-> | [-> | [-> | [-> | [-> | ->]]]]];
              unfold Znth; simpl; lia. }
          unfold CakeSumboolIf in Hstarteq |- *. simpl in *.
          rewrite Znth_replace_Znth_Diff by (try lia; congruence).
          lia.
      + replace (start + 1 - 1) with start by lia.
        unfold CakeSum, ListLib.sum in *; lia.
      + intros q Hq.
        replace (start + 1 - 1) with start in Hq |- * by lia.
        apply Hsearchmin. lia.
    - assert (Hklt : k < part) by lia.
      assert (Hpart1 : part = 1) by lia.
      assert (Hk0 : k = 0) by lia.
      subst part. subst k.
      specialize (Hdone 0 ltac:(lia)).
      pose proof (proj1 Hdone) as Hprevbounds.
      assert (Hneq : Znth 0 ord 0 <> who).
      { rewrite PreH14.
        destruct Hcake as [-> | [-> | [-> | [-> | [-> | ->]]]]];
          unfold Znth; simpl; lia. }
      repeat rewrite Znth_replace_Znth_Diff by (try lia; congruence).
      exact Hdone. }
  unfold CakeSumboolIf.
  destruct (Z.eq_dec (part + 1) 0); [lia|].
  replace (part + 1 - 1) with part by lia.
  rewrite <- PreH14.
  rewrite Znth_replace_Znth_Same by lia.
  reflexivity.
Qed.

Lemma proof_of_try_order_entail_wit_7_split_goal_2 : try_order_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Pre in PreH7.
  destruct PreH7 as
    (Halen & Hblen & Hclen & HFa & HFb & HFc & Hsumab & Hsumac).
  assert (Hsumupper : ListLib.sum a <= Zlength a * 1000000).
  { clear - HFa. induction HFa as [| x xs Hx HForall IH].
    - unfold ListLib.sum, Zlength. simpl. lia.
    - rewrite Zlength_cons. unfold ListLib.sum in *. simpl in *. lia. }
  assert (Hsumnon : 0 <= ListLib.sum a).
  { clear - HFa. induction HFa as [| x xs Hx HForall IH];
      unfold ListLib.sum in *; simpl in *; lia. }
  assert (HneedDiv : need_pre = (ListLib.sum a + 2) / 3).
  { rewrite <- Z.quot_div_nonneg by lia. exact PreH9. }
  rewrite HneedDiv.
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma proof_of_try_order_entail_wit_7_split_goal_3 : try_order_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Pre in PreH7.
  destruct PreH7 as
    (Halen & Hblen & Hclen & HFa & HFb & HFc & Hsumab & Hsumac).
  assert (Hsumlower : Zlength a <= ListLib.sum a).
  { clear - HFa. induction HFa as [| x xs Hx HForall IH].
    - unfold ListLib.sum, Zlength. simpl. lia.
    - rewrite Zlength_cons. unfold ListLib.sum in *. simpl in *. lia. }
  assert (HneedDiv : need_pre = (ListLib.sum a + 2) / 3).
  { rewrite <- Z.quot_div_nonneg by lia. exact PreH9. }
  rewrite HneedDiv.
  apply Z.div_le_lower_bound; lia.
Qed.

Lemma proof_of_try_order_entail_wit_7 : try_order_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_try_order_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_try_order_entail_wit_7_split_goal_3.
Qed.

Lemma proof_of_try_order_entail_wit_8 : try_order_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpart2 : part = 2) by lia. subst part.
  assert (Hwho : 0 <= Znth 2 ord 0 < 3).
  { destruct PreH12 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      unfold Znth; simpl; lia. }
  assert (Hrowlen :
      Zlength (Znth (Znth 2 ord 0) (a :: b :: c :: nil) nil) = Zlength a).
  { destruct PreH12 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      unfold Znth; simpl; lia. }
  pose proof PreH16 as Hraw.
  unfold GreedyRawState in Hraw.
  destruct Hraw as (_ & _ & _ & _ & Hpos & _ & _).
  unfold Znth in Hpos; simpl in Hpos.
  sep_apply_l_atomic (Int64PtrArray2.full_split_to_missing_i
    v_pre (Znth 2 ord 0) 3 (a :: b :: c :: nil)).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr lefts_2 rights_2.
    split_pure_spatial.
    + rewrite Hrowlen, <- PreH8.
      unfold StorePtrAsElement.storeA.
      change (Int64PtrArray2.ElemArray.full row_ptr n_pre
        (Znth (Znth 2 ord 0) (a :: b :: c :: nil) nil)) with
        (Int64Array.full row_ptr n_pre
          (Znth (Znth 2 ord 0) (a :: b :: c :: nil) nil)).
      normalize.
      cancel (Int64PtrArray2.missing_i v_pre 3 (Znth 2 ord 0) row_ptr
        (a :: b :: c :: nil)).
      cancel.
    + split_pures;
        dump_pre_spatial;
        try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_try_order_entail_wit_9_split_goal_1 : try_order_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply suffix_sum_empty__try_terminal_semantics; [lia |].
  destruct PreH11 as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  all: repeat rewrite Znth_cons in PreH13 by lia.
  all: repeat rewrite Znth0_cons in PreH13.
  all: subst who.
  - change (pos <= Zlength c). lia.
  - change (pos <= Zlength b). lia.
  - change (pos <= Zlength c). lia.
  - change (pos <= Zlength a). lia.
  - change (pos <= Zlength b). lia.
  - change (pos <= Zlength a). lia.
Qed.

Lemma proof_of_try_order_entail_wit_9 : try_order_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_try_order_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_try_order_entail_wit_10_split_goal_1 : try_order_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (selected_row_length__try_terminal_semantics
    a b c ord who PreH12 PreH14 PreH4 PreH5) as Hrowlen.
  apply suffix_sum_extend__try_terminal_semantics; [exact PreH23 |].
  rewrite Hrowlen. lia.
Qed.

Lemma proof_of_try_order_entail_wit_10_split_goal_2 : try_order_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (selected_row_length__try_terminal_semantics
    a b c ord who PreH12 PreH14 PreH4 PreH5) as Hrowlen.
  eapply suffix_sum_upper__try_terminal_semantics with
    (rows := a :: b :: c :: nil) (who := who) (start := pos) (i := i).
  - exact PreH23.
  - rewrite Hrowlen. lia.
  - intros k Hk.
    specialize (PreH6 who k ltac:(rewrite Hrowlen in Hk; lia)). lia.
  - rewrite Hrowlen. lia.
Qed.

Lemma proof_of_try_order_entail_wit_10_split_goal_3 : try_order_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH6 who i ltac:(lia)). lia.
Qed.

Lemma proof_of_try_order_entail_wit_10 : try_order_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_try_order_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_try_order_entail_wit_10_split_goal_3.
Qed.

Lemma proof_of_try_order_entail_wit_11_split_goal_1 : try_order_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with n_pre in PreH23 by lia.
  dump_pre_spatial.
  exact PreH23.
Qed.

Lemma proof_of_try_order_entail_wit_11_split_goal_2 : try_order_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_try_order_entail_wit_11_split_goal_spatial : try_order_entail_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (selected_row_length__try_terminal_semantics
    a b c ord who PreH12 PreH14 PreH4 PreH5) as Hrowlen.
  pose proof (Int64PtrArray2.missing_i_merge_to_full
    v_pre who 3 row_ptr (a :: b :: c :: nil)
    (Znth who (a :: b :: c :: nil) nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (Int64PtrArray2.ElemArray.full row_ptr
    (Zlength (Znth who (a :: b :: c :: nil) nil))
    (Znth who (a :: b :: c :: nil) nil)) with
    (Int64Array.full row_ptr
      (Zlength (Znth who (a :: b :: c :: nil) nil))
      (Znth who (a :: b :: c :: nil) nil)) in Hmerge.
  rewrite Hrowlen, <- PreH8 in Hmerge.
  assert (Hreorder :
    Int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: b :: c :: nil) **
    (((v_pre + who * sizeof ( PTR )) # Ptr |-> row_ptr) **
     Int64Array.full row_ptr n_pre (Znth who (a :: b :: c :: nil) nil))
    |--
    (((v_pre + who * sizeof ( PTR )) # Ptr |-> row_ptr) **
     Int64Array.full row_ptr n_pre (Znth who (a :: b :: c :: nil) nil)) **
    Int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: b :: c :: nil)).
  { cancel. }
  rewrite replace_Znth_Znth in Hmerge by lia.
  etransitivity.
  - exact Hreorder.
  - apply Hmerge. lia.
Qed.

Lemma proof_of_try_order_entail_wit_11 : try_order_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_try_order_entail_wit_11_split_goal_spatial.
  - Goal_apply proof_of_try_order_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_try_order_entail_wit_11_split_goal_2.
Qed.

Lemma proof_of_try_order_entail_wit_12_split_goal_1 : try_order_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnonneg : forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0).
  { intros k Hk. specialize (PreH6 0 k ltac:(lia)).
    repeat rewrite Znth0_cons in PreH6. lia. }
  pose proof (sum_nonnegative_pointwise__try_terminal_semantics a Hnonneg)
    as Htotal.
  assert (Hneeddiv : need_pre = (ListLib.sum a + 2) / 3).
  { rewrite <- Z.quot_div_nonneg; [exact PreH9 | lia | lia]. }
  pose proof (greedy_terminal_try_order__try_terminal_semantics
    a b c ord need_pre n_pre pos who acc lefts_2 rights_2
    PreH7 PreH6 PreH8 Hneeddiv PreH12 PreH16 PreH21 PreH22) as Hterminal.
  exact (proj1 Hterminal PreH1).
Qed.

Lemma proof_of_try_order_entail_wit_12 : try_order_entail_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_try_order_entail_wit_12_split_goal_1.
Qed.

Lemma proof_of_try_order_entail_wit_13_split_goal_1 : try_order_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnonneg : forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0).
  { intros k Hk. specialize (PreH6 0 k ltac:(lia)).
    repeat rewrite Znth0_cons in PreH6. lia. }
  pose proof (sum_nonnegative_pointwise__try_terminal_semantics a Hnonneg)
    as Htotal.
  assert (Hneeddiv : need_pre = (ListLib.sum a + 2) / 3).
  { rewrite <- Z.quot_div_nonneg; [exact PreH9 | lia | lia]. }
  pose proof (greedy_terminal_try_order__try_terminal_semantics
    a b c ord need_pre n_pre pos who acc lefts_2 rights_2
    PreH7 PreH6 PreH8 Hneeddiv PreH12 PreH16 PreH21 PreH22) as Hterminal.
  exact (proj2 Hterminal ltac:(lia)).
Qed.

Lemma proof_of_try_order_entail_wit_13 : try_order_entail_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_try_order_entail_wit_13_split_goal_1.
Qed.

Lemma proof_of_try_order_entail_wit_14 : try_order_entail_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists lefts_2 rights_2 (@nil Z).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg out_pre 6).
  repeat cancel.
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - replace (2 * 0) with 0 by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try (rewrite Zlength_nil; lia).
Qed.

Lemma proof_of_try_order_entail_wit_15 : try_order_entail_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists lefts_2 rights_2
    ((raw_prefix_2 ++ (Znth i lefts_2 0) :: nil) ++
      (Znth i rights_2 0) :: nil).
  replace (((2 * i) + 1) + 1) with (2 * (i + 1)) by lia.
  split_pure_spatial.
  - cancel. cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      repeat rewrite Zlength_app.
      repeat rewrite Zlength_cons.
      rewrite Zlength_nil.
      lia.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial.
      intros j Hj.
      destruct (Z_lt_ge_dec j (2 * i)) as [Hjold | Hjnew].
      * rewrite Znth_app_left__try_output_materialization by
          (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
        rewrite Znth_app_left__try_output_materialization by lia.
        apply PreH12. lia.
      * assert (j = 2 * i \/ j = 2 * i + 1) as [-> | ->] by lia.
        -- rewrite Znth_app_left__try_output_materialization by
             (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
           pose proof
             (Znth_app_last__try_output_materialization
                raw_prefix_2 0 (Znth i lefts_2 0)) as Hlast.
           rewrite PreH10 in Hlast.
           rewrite Hlast.
           unfold OutputBounds.
           assert (i = 0 \/ i = 1 \/ i = 2) as Hi by lia.
           destruct Hi as [-> | [-> | ->]].
           ++ replace (2 * 0) with 0 by lia.
              rewrite Znth0_cons. lia.
           ++ replace (2 * 1) with 2 by lia.
              repeat rewrite Znth_cons by lia.
              rewrite Znth0_cons. lia.
           ++ replace (2 * 2) with 4 by lia.
              repeat rewrite Znth_cons by lia.
              rewrite Znth0_cons. lia.
        -- pose proof
             (Znth_app_last__try_output_materialization
                (raw_prefix_2 ++ Znth i lefts_2 0 :: nil)
                0 (Znth i rights_2 0)) as Hlast.
           assert (Hinnerlen :
             Zlength (raw_prefix_2 ++ Znth i lefts_2 0 :: nil) = 2 * i + 1) by
             (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
           rewrite Hinnerlen in Hlast.
           rewrite Hlast.
           unfold OutputBounds.
           assert (i = 0 \/ i = 1 \/ i = 2) as Hi by lia.
           destruct Hi as [-> | [-> | ->]].
           ++ replace (2 * 0 + 1) with 1 by lia.
              rewrite Znth_cons by lia.
              rewrite Znth0_cons. lia.
           ++ replace (2 * 1 + 1) with 3 by lia.
              repeat rewrite Znth_cons by lia.
              rewrite Znth0_cons. lia.
           ++ replace (2 * 2 + 1) with 5 by lia.
              repeat rewrite Znth_cons by lia.
              rewrite Znth0_cons. lia.
Qed.

Lemma proof_of_try_order_entail_wit_16_split_goal_1 : try_order_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH12.
  lia.
Qed.

Lemma proof_of_try_order_entail_wit_16 : try_order_entail_wit_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_try_order_entail_wit_16_split_goal_1.
Qed.

Lemma proof_of_try_order_return_wit_1 : try_order_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists raw_result_2 (OutputBounds lefts rights).
  split_pure_spatial.
  - cancel. cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH6 0 i ltac:(lia)).
  repeat rewrite Znth0_cons in PreH6.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH6 0 i ltac:(lia)).
  repeat rewrite Znth0_cons in PreH6.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  sep_apply_l_atomic
    (Int64PtrArray2.full_split_to_missing_i v_pre 0 3 (a :: b :: c :: nil)).
  - dump_pre_spatial. lia.
  - Intros row0.
    Exists row0.
    replace (repeat_Z 0 1) with (0 :: nil) by reflexivity.
    repeat rewrite Znth0_cons.
    split_pure_spatial.
    + unfold StorePtrAsElement.storeA.
      change (Int64PtrArray2.ElemArray.full row0 (Zlength a) a)
        with (Int64Array.full row0 (Zlength a) a).
      normalize.
      cancel (Int64PtrArray2.missing_i v_pre 3 0 row0 (a :: b :: c :: nil)).
      cancel ((v_pre + 0 * sizeof (PTR)) # Ptr |-> row0).
      cancel (Int64Array.full row0 (Zlength a) a).
      cancel (IntArray.undef_full out_pre 6).
      cancel (IntArray.full &( "orders") 18
        (0 :: 1 :: 2 :: 0 :: 2 :: 1 :: 1 :: 0 :: 2 ::
         1 :: 2 :: 0 :: 2 :: 0 :: 1 :: 2 :: 1 :: 0 :: nil)).
    + split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnext :
    total + Znth i a 0 = ListLib.sum (sublist 0 (i + 1) a)).
  {
    rewrite (sublist_split 0 (i + 1) i a) by lia.
    rewrite (sublist_single 0 i a) by lia.
    rewrite ListLib.sum_app.
    simpl.
    lia.
  }
  rewrite Hnext.
  pose proof (ListLib.sum_bound 1000000 (sublist 0 (i + 1) a)) as Hsum.
  assert (Hpoint : forall j, 0 <= j ->
    0 <= Znth j (sublist 0 (i + 1) a) 0 <= 1000000).
  {
    intros j Hj.
    destruct (Z_lt_ge_dec j (i + 1)).
    - rewrite Znth_sublist0 by lia.
      specialize (PreH6 0 j ltac:(lia)).
      repeat rewrite Znth0_cons in PreH6.
      lia.
    - rewrite (@Znth_sublist_ge Z 0 0 (i + 1) a j) by lia.
      lia.
  }
  specialize (Hsum Hpoint).
  rewrite <- Zlength_correct in Hsum.
  rewrite Zlength_sublist in Hsum by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH6 0 i ltac:(lia)).
  repeat rewrite Znth0_cons in PreH6.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (sublist_split 0 (i + 1) i a) by lia.
  rewrite (sublist_single 0 i a) by lia.
  rewrite ListLib.sum_app.
  simpl.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH8 in PreH11.
  assert (Hfull : sublist 0 (Zlength a) a = a).
  {
    pose proof (@sublist_app_exact1 Z a nil) as H.
    rewrite app_nil_r in H.
    exact H.
  }
  rewrite Hfull in PreH11.
  dump_pre_spatial.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8.
  sep_apply_r_atomic
    (Int64PtrArray2.missing_i_merge_to_full
      v_pre 0 3 row0_addr (a :: b :: c :: nil) a ltac:(lia)).
  cancel.
  unfold StorePtrAsElement.storeA,
    Int64PtrArray2.ElemArray.full, Int64Array.full.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof. Abort.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof. Abort.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH6 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as
    (Hlen & Hlenb & Hlenc & HFa & HFb & HFc & Hsumab & Hsumac).
  pose proof (bounded_values_sum_lower__solver_order_setup a HFa) as Hsumlower.
  unfold CakeSum in Hsumlower.
  pose proof PreH8 as Htotal_sum.
  unfold ListLib.sum in Htotal_sum.
  pose proof (Z.div_mod (total + 2) 3 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (total + 2) 3 ltac:(lia)) as Hmod.
  Exists (0 :: 1 :: 2 :: 0 :: 2 :: 1 :: 1 :: 0 :: 2 ::
          1 :: 2 :: 0 :: 2 :: 0 :: 1 :: 2 :: 1 :: 0 :: nil).
  split_pure_spatial.
  - cancel (IntArray.full &("orders") 18
      (0 :: 1 :: 2 :: 0 :: 2 :: 1 :: 1 :: 0 :: 2 ::
       1 :: 2 :: 0 :: 2 :: 0 :: 1 :: 2 :: 1 :: 0 :: nil)).
    cancel (Int64PtrArray2.full v_pre 3 (a :: b :: c :: nil)).
    cancel (IntArray.undef_full out_pre 6).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try reflexivity.
    all: try (rewrite PreH8; reflexivity).
    all: try (unfold OrderTable; reflexivity).
    all: try (unfold FailedOrders; intros; lia).
    all: try (repeat rewrite Z.quot_div_nonneg by lia).
    all: try lia.
    all: try nia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (order_table_decomposition__solver_order_setup table_2 z PreH15
       ltac:(lia)) as
    (Hdecomp & Hbefore_len & Horder_len & Hafter_len &
     Horder_at & Hcake_order & Hslice & Hmiddle & Htail).
  Exists (sublist 0 (3 * z) table_2)
         (sublist (3 * (z + 1)) 18 table_2)
         table_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.full_split_to_seg &("orders") (3 * z) 18 table_2).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (IntArray.seg_split_to_seg &("orders") (3 * z)
          (3 * (z + 1)) 18 (sublist (3 * z) 18 table_2)).
      * dump_pre_spatial. lia.
      * rewrite Hmiddle, Htail.
        sep_apply_l_atomic
          (IntArray.seg_to_full &("orders") (3 * z) (3 * (z + 1))
            (OrderFor z)).
        replace (3 * (z + 1) - 3 * z) with 3 by lia.
        cancel (IntArray.full (&("orders") + 3 * z * sizeof(INT)) 3
          (OrderFor z)).
        cancel (IntArray.seg &("orders") 0 (3 * z)
          (sublist 0 (3 * z) table_2)).
        cancel (IntArray.seg &("orders") (3 * (z + 1)) 18
          (sublist (3 * (z + 1)) 18 table_2)).
        cancel (Int64PtrArray2.full v_pre 3 (a :: b :: c :: nil)).
        cancel (IntArray.undef_full out_pre 6).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try reflexivity.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hspec : Spec a b c (Some result_2)).
  { unfold Spec. left. exists result_2. split; [reflexivity |].
    unfold TryOrderSpec in PreH2. tauto. }
  subst ordp.
  sep_apply_l_atomic
    (IntArray.full_to_seg (&("orders") + 3 * z * sizeof(INT)) 3 (OrderFor z)).
  rewrite <- (IntArray.seg_shift (&("orders")) (3 * z) 0 3 (OrderFor z)).
  replace (3 * z + 0) with (3 * z) by lia.
  replace (3 * z + 3) with (3 * (z + 1)) by lia.
  sep_apply_l_atomic
    (IntArray.seg_merge_to_seg (&("orders")) 0 (3 * z) (3 * (z + 1))
       before_2 (OrderFor z) ltac:(lia)).
  sep_apply_l_atomic
    (IntArray.seg_merge_to_full (&("orders")) 0 (3 * (z + 1)) 18
       (before_2 ++ OrderFor z)%list after_2 ltac:(lia)).
  replace (&("orders") + 0 * sizeof(INT)) with (&("orders")) by lia.
  replace (18 - 0) with 18 by lia.
  rewrite <- app_assoc.
  Exists before_2 after_2 (before_2 ++ OrderFor z ++ after_2)%list
         raw_result_2 result_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity.
    rewrite <- PreH20. exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hfailed : FailedOrders a b c (z + 1)).
  { unfold FailedOrders in *.
    intros k Hk.
    destruct (Z.lt_ge_cases k z) as [Hlt | Hge].
    - apply PreH16. lia.
    - assert (k = z) by lia. subst k.
      exists (OrderFor z). split; assumption. }
  subst ordp.
  sep_apply_l_atomic
    (IntArray.full_to_seg (&("orders") + 3 * z * sizeof(INT)) 3 (OrderFor z)).
  rewrite <- (IntArray.seg_shift (&("orders")) (3 * z) 0 3 (OrderFor z)).
  replace (3 * z + 0) with (3 * z) by lia.
  replace (3 * z + 3) with (3 * (z + 1)) by lia.
  sep_apply_l_atomic
    (IntArray.seg_merge_to_seg (&("orders")) 0 (3 * z) (3 * (z + 1))
       before (OrderFor z) ltac:(lia)).
  sep_apply_l_atomic
    (IntArray.seg_merge_to_full (&("orders")) 0 (3 * (z + 1)) 18
       (before ++ OrderFor z)%list after ltac:(lia)).
  replace (&("orders") + 0 * sizeof(INT)) with (&("orders")) by lia.
  replace (18 - 0) with 18 by lia.
  rewrite <- app_assoc.
  Exists (before ++ OrderFor z ++ after)%list.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity.
    rewrite <- PreH19. exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Pre in PreH5.
  destruct PreH5 as (_ & _ & _ & HFa & HFb & HFc & _ & _).
  rewrite (Forall_Znth__solver_order_iteration
             (fun x => 1 <= x <= 1000000) 0 a) in HFa.
  rewrite (Forall_Znth__solver_order_iteration
             (fun x => 1 <= x <= 1000000) 0 b) in HFb.
  rewrite (Forall_Znth__solver_order_iteration
             (fun x => 1 <= x <= 1000000) 0 c) in HFc.
  destruct H as (((Hrowlo & Hrowhi) & Hcollo) & Hcolhi).
  assert (row = 0 \/ row = 1 \/ row = 2) as [-> | [-> | ->]] by lia.
  - repeat rewrite Znth0_cons. apply HFa. lia.
  - rewrite Znth_cons by lia. repeat rewrite Znth0_cons. apply HFb. lia.
  - repeat rewrite Znth_cons by lia. rewrite Znth0_cons. apply HFc. lia.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (z = 6) by lia.
  subst z.
  apply failed_six_orders_spec_none__solver_final_results.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (z = 6) by lia.
  subst z.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists raw_result_2 result_2.
  split_pure_spatial.
  - cancel (Int64PtrArray2.full v_pre 3 (a :: b :: c :: nil)).
    cancel (IntArray.full out_pre 6 raw_result_2).
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. assumption.
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
