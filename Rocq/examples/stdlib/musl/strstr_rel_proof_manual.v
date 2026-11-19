From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.stdlib.musl Require Import strstr_rel_goal.
From SimpleC.EE.stdlib.musl Require Import strstr_rel_proof_auto.
Import naive_C_Rules64.
Require Import SimpleC.EE.stdlib.musl.strstr_rel_lib.
Require Import SimpleC.EE.stdlib.musl.strstr_rel_legacy_bridge.
Require Import SimpleC.EE.stdlib.musl.two_way_list_lemmas.
From Coq Require Import Classical_Prop.
Require Import SimpleC.EE.stdlib.musl.monad.factorization_refinement.
Require Import SimpleC.EE.stdlib.musl.monad.factorization_result_bridge.
Require Import SimpleC.EE.stdlib.musl.monad.shift_table_refinement.
Require Import SimpleC.EE.stdlib.musl.monad.periodic_memory_refinement.
Require Import SimpleC.EE.stdlib.musl.monad.search_skip_refinement.
Require Import SimpleC.EE.stdlib.musl.monad.search_cursor_refinement.
Local Open Scope sac.

From SimpleC.EE.stdlib.musl.monad Require Import two_way_rel_lib two_way_critical_factorization_theorem two_way_match.
From SimpleC.EE.stdlib.musl.monad Require Import factorization_safeexec.
Import strstr_rel_lib.
Local Open Scope monad.
Local Open Scope sac.
Lemma cursor_before_valid_skip : forall text patn pos d,
  patn <> nil -> 0 <= pos -> 0 < d -> pos+d <= Zlength text ->
  no_match_before text patn (pos+d) -> SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.valid_skip text patn pos d.
Proof.
  intros text patn pos d Hn Hp Hd He Hb. split; [exact Hd|]. split; [exact He|].
  intros j Hj Hmatch. apply (Hb j ltac:(lia)).
  pose proof (strstr_result_bridge.nonempty_sublist_match_bounds text patn j Hn Hmatch).
  unfold substring_at; tauto.
Qed.

Lemma cursor_remaining_none : forall hs ns base pos end_ h z retval length cut p remembered memory,
  h = base + pos * sizeof(UCHAR) -> z = base + end_ * sizeof(UCHAR) ->
  length = Zlength ns -> 0 < length -> Zlength hs <= UINT64_MAX ->
  0 <= pos <= end_ -> end_ <= Zlength hs ->
  search_cursor hs ns cut p remembered pos memory ->
  memchr_zero_result (sublist end_ (Zlength hs) hs) z 0 (Z.lor length 63) retval ->
  retval <> 0 ->
  unsigned_last_nbits (Z.quot (retval-h) (sizeof(UCHAR))) 64 < length ->
  strstr_result hs ns base 0.
Proof.
  intros hs ns base pos end_ h z retval length cut p remembered memory
    Hh Hz Hlength Hpositive Hhslen Hpos Hend Hcursor Hmemchr Hretval Hoff.
  unfold memchr_zero_result in Hmemchr.
  destruct Hmemchr as [[Hshort [Hret Hnonnull]]|[Hcount Hzero]]; [|contradiction].
  assert (Hsuflen : Zlength (sublist end_ (Zlength hs) hs) = Zlength hs-end_)
    by (rewrite Zlength_sublist; lia).
  assert (Hret' : retval = base+Zlength hs).
  { rewrite Hret, Hz, Hsuflen, sizeof_uchar; lia. }
  assert (Hoff' : unsigned_last_nbits (Z.quot (retval-h) (sizeof(UCHAR))) 64 = Zlength hs-pos).
  { rewrite Hret', Hh, sizeof_uchar, Z.quot_1_r.
    unfold unsigned_last_nbits. rewrite Z.mod_small; lia. }
  eapply (search_cursor_result_none hs ns base cut p remembered pos memory); [|rewrite Hoff' in Hoff; lia|exact Hcursor].
  intro Hnil; rewrite Hnil, Zlength_nil in Hlength; lia.
Qed.

Lemma nonperiodic_small_branch_shift64 : forall l ms,
  0 <= ms < l /\ l <= 18446744073709551615 ->
  unsigned_last_nbits
    (unsigned_last_nbits (unsigned_last_nbits (l - ms) 64 - 1) 64 + 1) 64
  = l - ms.
Proof.
  intros l ms Hrange.
  unfold unsigned_last_nbits.
  change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small (l - ms) 18446744073709551616) by lia.
  rewrite (Z.mod_small (l - ms - 1) 18446744073709551616) by lia.
  rewrite (Z.mod_small (l - ms - 1 + 1) 18446744073709551616) by lia.
  lia.
Qed.

Lemma Forall_firstn_local {A} (P : A -> Prop) n (xs : list A) :
  Forall P xs -> Forall P (firstn n xs).
Proof.
  revert xs. induction n; intros xs H; simpl; [constructor|].
  destruct xs; simpl; [constructor|].
  inversion H; constructor; auto.
Qed.

Lemma Forall_skipn_local {A} (P : A -> Prop) n (xs : list A) :
  Forall P xs -> Forall P (skipn n xs).
Proof.
  revert xs. induction n; intros xs H; simpl; [assumption|].
  destruct xs; simpl; [constructor|].
  inversion H; auto.
Qed.

Lemma strstr_array_length64__cut_probe : forall p (s : list Z),
  UCharArray.full p (Zlength s + 1) (s ++ [0])
  |-- “ Zlength s <= UINT64_MAX ”.
Proof.
  intros p s.
  sep_apply (UCharArray.full_to_align p (Zlength s + 1) (s ++ [0])).
  rewrite sizeof_uchar, Z.mul_1_r.
  prop_apply (store_align_n_range (Zlength s + 1)).
  Intros_p Hrange.
  unfold sizeof_front_end_type in Hrange. cbn in Hrange.
  entailer!.
Qed.

(* A full NUL-terminated byte array is itself an owned 64-bit object, so its
   logical byte length is within the addressable range.  This is derived from
   the spatial resource, not added as a public precondition. *)
Lemma strstr_array_length64 : forall p (s : list Z),
  UCharArray.full p (Zlength s + 1) (s ++ [0])
  |-- “ Zlength s <= UINT64_MAX ”.
Proof.
  intros p s.
  sep_apply (UCharArray.full_to_align p (Zlength s + 1) (s ++ [0])).
  rewrite sizeof_uchar, Z.mul_1_r.
  prop_apply (store_align_n_range (Zlength s + 1)).
  Intros_p Hrange.
  unfold sizeof_front_end_type in Hrange. cbn in Hrange.
  entailer!.
Qed.

(* The 64-bit model owns the complete NUL-terminated needle and haystack as
   disjoint arrays.  Their combined byte count bounds every index below 2*l.
   This replaces the invalid 32-bit address-space shortcut in the old run. *)
Lemma strstr_pair_length64 : forall h n (hs ns : list Z),
  Zlength ns <= Zlength hs ->
  UCharArray.full h (Zlength hs + 1) (hs ++ [0]) **
  UCharArray.full n (Zlength ns + 1) (ns ++ [0])
  |-- “ 2 * Zlength ns < UINT64_MAX ”.
Proof.
  intros h n hs ns Hle.
  sep_apply (UCharArray.full_to_align h (Zlength hs + 1) (hs ++ [0])).
  sep_apply (UCharArray.full_to_align n (Zlength ns + 1) (ns ++ [0])).
  rewrite !sizeof_uchar.
  rewrite !Z.mul_1_r.
  sep_apply (store_align_merge (Zlength ns + 1) (Zlength hs + 1)).
  prop_apply (store_align_n_range (Zlength ns + 1 + (Zlength hs + 1))).
  Intros_p Hrange.
  unfold sizeof_front_end_type in Hrange.
  cbn in Hrange.
  pose proof (Zlength_nonneg hs).
  pose proof (Zlength_nonneg ns).
  entailer!.
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_1_split_goal_1 : twobyte_strstr_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 0 (hs ++ [0]) 0 * 2 ^ 8) 32 ltac:(lia)).
  dump_pre_spatial. simpl in *; lia.
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_1_split_goal_2 : twobyte_strstr_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 0 (hs ++ [0]) 0 * 2 ^ 8) 32 ltac:(lia)).
  dump_pre_spatial. simpl in *; lia.
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_1_split_goal_3 : twobyte_strstr_safety_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_1_split_goal_4 : twobyte_strstr_safety_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_1 : twobyte_strstr_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_1_split_goal_2.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_1_split_goal_3.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_1_split_goal_4.
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_5_split_goal_1 : twobyte_strstr_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 0 (ns ++ [0]) 0 * 2 ^ 8) 32 ltac:(lia)).
  dump_pre_spatial. simpl in *; lia.
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_5_split_goal_2 : twobyte_strstr_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 0 (ns ++ [0]) 0 * 2 ^ 8) 32 ltac:(lia)).
  dump_pre_spatial. simpl in *; lia.
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_5_split_goal_3 : twobyte_strstr_safety_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_5_split_goal_4 : twobyte_strstr_safety_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_5 : twobyte_strstr_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_5_split_goal_2.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_5_split_goal_3.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_5_split_goal_4.
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_11_split_goal_1 : twobyte_strstr_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (hw * 2 ^ 8) 32 ltac:(lia)).
  dump_pre_spatial. simpl in *; lia.
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_11_split_goal_2 : twobyte_strstr_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (hw * 2 ^ 8) 32 ltac:(lia)).
  dump_pre_spatial. simpl in *; lia.
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_11_split_goal_3 : twobyte_strstr_safety_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_11_split_goal_4 : twobyte_strstr_safety_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_twobyte_strstr_safety_wit_11 : twobyte_strstr_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_11_split_goal_2.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_11_split_goal_3.
  - Goal_apply proof_of_twobyte_strstr_safety_wit_11_split_goal_4.
Qed.


Lemma proof_of_twobyte_strstr_entail_wit_1 : twobyte_strstr_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists 1.
  split_pure_spatial.
  - sep_apply (UCharArray.full_split_to_full h_pre 1 (Zlength hs + 1) (hs ++ [0])); try lia.
    cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
    cancel (UCharArray.full h_pre 1 (sublist 0 1 (hs ++ [0]))).
    cancel (UCharArray.full (h_pre + 1 * sizeof(UCHAR)) (Zlength hs + 1 - 1) (sublist 1 (Zlength hs + 1) (hs ++ [0]))).
  - split_pures; dump_pre_spatial;
      try assumption;
      try (unfold no_match_before; intros; lia);
      try lia.
    1: (
      unfold rolling2; split; [lia|];
      destruct (first_two_bytes__proof_of_twobyte_1 hs PreH1 PreH4)
        as [Ha [Hb [H0 H1]]];
      rewrite Z.shiftl_mul_pow2 by lia;
      change (2 ^ 8) with 256;
      rewrite !unsigned_last_nbits_eq by lia;
      replace (Znth 0 (hs ++ [0]) 0 * 256)
        with (256 * Znth 0 (hs ++ [0]) 0) by lia;
      replace (1 - 1) with 0 by lia;
      rewrite (pack2_bytes__proof_of_twobyte_1 _ _ Ha Hb);
      replace 65535 with (Z.ones 16) by reflexivity;
      rewrite Z.land_ones by lia;
      symmetry; apply Z.mod_small; lia).
    1: (
      unfold needle2; split; [exact PreH3|];
      destruct (first_two_bytes__proof_of_twobyte_1 ns PreH2 ltac:(lia))
        as [Ha [Hb [H0 H1]]];
      rewrite Z.shiftl_mul_pow2 by lia;
      change (2 ^ 8) with 256;
      rewrite !unsigned_last_nbits_eq by lia;
      replace (Znth 0 (ns ++ [0]) 0 * 256)
        with (256 * Znth 0 (ns ++ [0]) 0) by lia;
      rewrite (pack2_bytes__proof_of_twobyte_1 _ _ Ha Hb);
      rewrite H0, H1; reflexivity).
Qed.


Lemma proof_of_twobyte_strstr_entail_wit_2 : twobyte_strstr_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i < Zlength hs).
  { rewrite Znth_sublist in PreH2 by
      (try rewrite Zlength_app; try rewrite Zlength_cons;
       try rewrite Zlength_nil; lia).
    destruct (Z.eq_dec i (Zlength hs)) as [Heq|Hneq]; [|lia].
    subst i. rewrite app_Znth2 in PreH2 by lia.
    unfold Znth in PreH2.
    exfalso. apply PreH2.
    replace (0 + Zlength hs - Zlength hs) with 0 by lia.
    reflexivity. }
  assert (Hno : no_match_before hs ns i).
  { unfold no_match_before in *.
    intros j Hj Hmatch.
    destruct (Z_lt_ge_dec j (i - 1)) as [Hold|Hlast].
    - apply (PreH10 j); [lia|exact Hmatch].
    - assert (j = i - 1) by lia. subst j.
      unfold substring_at in Hmatch.
      destruct Hmatch as [_ [_ Hsub]].
      destruct PreH8 as [_ Hword].
      destruct PreH9 as [Hlen Hneedle].
      assert (Ha : 0 <= Znth (i - 1) hs 0 < 256).
      { unfold nonzero_bytes in PreH6.
        assert (Hin : In (Znth (i - 1) hs 0) hs).
        { unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
          rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia. }
        pose proof ((proj1 (Forall_forall _ _)) PreH6 (Znth (i - 1) hs 0) Hin)
          as Hbyte. cbn in Hbyte. lia. }
      assert (Hb : 0 <= Znth i hs 0 < 256).
      { unfold nonzero_bytes in PreH6.
        assert (Hin : In (Znth i hs 0) hs).
        { unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
          rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia. }
        pose proof ((proj1 (Forall_forall _ _)) PreH6 (Znth i hs 0) Hin)
          as Hbyte. cbn in Hbyte. lia. }
      assert (Heq0 : Znth (i - 1) hs 0 = Znth 0 ns 0).
      { pose proof (f_equal (fun l => Znth 0 l 0) Hsub) as H.
        cbn beta in H.
        rewrite Znth_sublist in H by lia. exact H. }
      assert (Heq1 : Znth i hs 0 = Znth 1 ns 0).
      { pose proof (f_equal (fun l => Znth 1 l 0) Hsub) as H.
        cbn beta in H.
        rewrite Znth_sublist in H by lia.
        replace (1 + (i - 1)) with i in H by lia. exact H. }
      rewrite app_Znth1 in Hword by lia.
      rewrite app_Znth1 in Hword by lia.
      replace 65535 with (Z.ones 16) in Hword by reflexivity.
      rewrite Z.land_ones in Hword by lia.
      rewrite Z.mod_small in Hword by lia.
      rewrite Heq0, Heq1 in Hword.
      apply PreH1. congruence. }
  Exists (i + 1).
  split_pure_spatial.
  - subst h.
    sep_apply_l_atomic (UCharArray.full_split_to_full
      (h_pre + i * sizeof(UCHAR)) 1 (Zlength hs + 1 - i)
      (sublist i (Zlength hs + 1) (hs ++ [0]))).
    + dump_pre_spatial. lia.
    + rewrite !Zsublist_Zsublist by lia.
      replace (0 + i) with i by lia.
      replace (1 + i) with (i + 1) by lia.
      replace (Zlength hs + 1 - i + i) with (Zlength hs + 1) by lia.
      replace 1 with (i + 1 - i) at 1 by lia.
      sep_apply (UCharArray.full_merge_to_full
        h_pre i (i + 1)
        (sublist 0 i (hs ++ [0])) (sublist i (i + 1) (hs ++ [0]))).
      all: try lia.
      replace (sublist 0 i (hs ++ [0]) ++ sublist i (i + 1) (hs ++ [0]))
          with (sublist 0 (i + 1) (hs ++ [0]))
          by (apply sublist_split;
              try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia).
        replace (Zlength hs + 1 - i - 1) with
          (Zlength hs + 1 - (i + 1)) by lia.
        cancel (UCharArray.full h_pre (i + 1)
          (sublist 0 (i + 1) (hs ++ [0]))).
        cancel (UCharArray.full
          (h_pre + i * sizeof(UCHAR) + 1 * sizeof(UCHAR))
          (Zlength hs + 1 - (i + 1))
          (sublist (i + 1) (Zlength hs + 1) (hs ++ [0]))).
        cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
        Show.
  - split_pures; dump_pre_spatial; try lia; try assumption;
      replace (i + 1 - 1) with i by lia; assumption.
Qed.


Lemma proof_of_twobyte_strstr_entail_wit_3_split_goal_1 : twobyte_strstr_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rolling2 in PreH6 |- *.
  destruct PreH6 as [Hprev Hword].
  split; [lia|].
  rewrite Znth_sublist by lia.
  assert (Hbytes : Forall (fun c : Z => 0 <= c < 256) (hs ++ [0])).
  { apply Forall_forall; intros c Hc.
    apply in_app_or in Hc; destruct Hc as [Hc|Hc].
    - unfold nonzero_bytes in PreH4.
      pose proof ((proj1 (Forall_forall _ _)) PreH4 c Hc) as Hcb. cbn in Hcb. lia.
    - simpl in Hc. destruct Hc as [Hc|[]]. symmetry in Hc. subst c. cbn. lia. }
  assert (Hbound : forall k, 0 <= k < Zlength (hs ++ [0]) ->
      0 <= Znth k (hs ++ [0]) 0 < 256).
  { intros k Hk.
    apply ((proj1 (Forall_forall _ _)) Hbytes (Znth k (hs ++ [0]) 0)).
    unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. exact (proj2 Hk). }
  pose proof (Hbound (j - 2) ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia)) as Ha.
  pose proof (Hbound (j - 1) ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia)) as Hb.
  pose proof (Hbound j ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia)) as Hc.
  replace (j - 1 - 1) with (j - 2) in Hword by lia.
  replace 65535 with (Z.ones 16) in Hword by reflexivity.
  rewrite Z.land_ones in Hword by lia.
  rewrite Z.mod_small in Hword by lia.
  rewrite Hword.
  unfold unsigned_last_nbits.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 8) with 256.
  change (2 ^ 16) with 65536.
  replace ((256 * Znth (j - 2) (hs ++ [0]) 0 +
                    Znth (j - 1) (hs ++ [0]) 0) * 256)
    with (256 * Znth (j - 1) (hs ++ [0]) 0 +
          Znth (j - 2) (hs ++ [0]) 0 * 65536) by ring.
  rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia.
  replace (0 + j) with j by lia.
  rewrite Z.mod_small by lia.
  assert (Hland : Z.land (256 * Znth (j - 1) (hs ++ [0]) 0)
      (Znth j (hs ++ [0]) 0) = 0).
  { replace (Znth j (hs ++ [0]) 0)
      with (Z.land (Znth j (hs ++ [0]) 0) (Z.ones 8)).
    2:{ rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
    rewrite (Z.land_comm (Znth j (hs ++ [0]) 0) (Z.ones 8)).
    rewrite Z.land_assoc.
    rewrite Z.land_ones by lia.
    change (2 ^ 8) with 256.
    replace (256 * Znth (j - 1) (hs ++ [0]) 0)
      with (Znth (j - 1) (hs ++ [0]) 0 * 256) by ring.
    rewrite Z.mod_mul by lia.
    reflexivity. }
  pose proof (Z.add_lor_land (256 * Znth (j - 1) (hs ++ [0]) 0)
      (Znth j (hs ++ [0]) 0)) as Hsum.
  rewrite Hland in Hsum.
  replace 65535 with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  lia.
Qed.


Lemma proof_of_twobyte_strstr_entail_wit_3 : twobyte_strstr_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_twobyte_strstr_entail_wit_3_split_goal_1.
Qed.


Lemma proof_of_twobyte_strstr_return_wit_1_split_goal_1 : twobyte_strstr_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold strstr_result, first_substring, substring_at, no_match_before in *.
  assert (Hi : i < Zlength hs).
  { rewrite Znth_sublist in PreH3 by
      (try rewrite Zlength_app; try rewrite Zlength_cons;
       try rewrite Zlength_nil; lia).
    destruct (Z.eq_dec i (Zlength hs)) as [Heq|Hneq]; [|lia].
    subst i. rewrite app_Znth2 in PreH3 by lia.
    unfold Znth in PreH3.
    exfalso. apply PreH3.
    replace (0 + Zlength hs - Zlength hs) with 0 by lia.
    reflexivity. }
  destruct PreH9 as [_ Hword].
  destruct PreH10 as [Hlen Hneedle].
  assert (Hhay : Forall (fun c : Z => 0 <= c < 256) hs).
  { unfold nonzero_bytes in PreH7.
    apply Forall_forall; intros c Hc.
    pose proof ((proj1 (Forall_forall _ _)) PreH7 c Hc) as Hcb.
    cbn in Hcb. lia. }
  assert (Hnbytes : Forall (fun c : Z => 0 <= c < 256) ns).
  { unfold nonzero_bytes in PreH8.
    apply Forall_forall; intros c Hc.
    pose proof ((proj1 (Forall_forall _ _)) PreH8 c Hc) as Hcb.
    cbn in Hcb. lia. }
  assert (Hbound : forall l k, Forall (fun c : Z => 0 <= c < 256) l ->
      0 <= k < Zlength l -> 0 <= Znth k l 0 < 256).
  { intros l k HF Hk.
    apply ((proj1 (Forall_forall _ _)) HF (Znth k l 0)).
    unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. exact (proj2 Hk). }
  pose proof (Hbound hs (i - 1) Hhay ltac:(lia)) as Ha.
  pose proof (Hbound hs i Hhay ltac:(lia)) as Hb.
  pose proof (Hbound ns 0 Hnbytes ltac:(lia)) as Hc.
  pose proof (Hbound ns 1 Hnbytes ltac:(lia)) as Hd.
  rewrite app_Znth1 in Hword by lia.
  rewrite app_Znth1 in Hword by lia.
  replace 65535 with (Z.ones 16) in Hword by reflexivity.
  rewrite Z.land_ones in Hword by lia.
  rewrite Z.mod_small in Hword by lia.
  assert (Hbytes_eq : Znth (i - 1) hs 0 = Znth 0 ns 0 /\
      Znth i hs 0 = Znth 1 ns 0) by lia.
  assert (Hsub : sublist (i - 1) (i - 1 + Zlength ns) hs = ns).
  { rewrite Hlen.
    replace (i - 1 + 2) with (i + 1) by lia.
    rewrite sublist_split with (mid := i) by lia.
    replace (sublist (i - 1) i hs)
      with (sublist (i - 1) (i - 1 + 1) hs) by (f_equal; lia).
    rewrite (sublist_single 0 (i - 1) hs) by lia.
    rewrite (sublist_single 0 i hs) by lia.
    rewrite <- (sublist_self ns (Zlength ns)) by reflexivity.
    rewrite Hlen.
    rewrite sublist_split with (mid := 1) by lia.
    replace (sublist 0 1 ns) with (sublist 0 (0 + 1) ns)
      by (f_equal; lia).
    rewrite (sublist_single 0 0 ns) by lia.
    replace (sublist 1 2 ns) with (sublist 1 (1 + 1) ns)
      by (f_equal; lia).
    rewrite (sublist_single 0 1 ns) by lia.
    destruct Hbytes_eq as [Heq1 Heq2]. rewrite Heq1, Heq2.
    reflexivity. }
  right. exists (i - 1). split.
  - split.
    + split; [lia|split; [lia|exact Hsub]].
    + exact PreH11.
  - subst h.
    change (sizeof(UCHAR)) with 1.
    change (sizeof(CHAR)) with 1.
    lia.
Qed.


Lemma proof_of_twobyte_strstr_return_wit_1_split_goal_spatial : twobyte_strstr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst h.
  sep_apply_l_atomic (UCharArray.full_merge_to_full h_pre i (Zlength hs + 1)
    (sublist 0 i (hs ++ [0])) (sublist i (Zlength hs + 1) (hs ++ [0]))).
  - dump_pre_spatial. lia.
  - rewrite <- sublist_split by
      (try rewrite Zlength_app; try rewrite Zlength_cons;
       try rewrite Zlength_nil; lia).
    rewrite sublist_self by
      (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    cancel (UCharArray.full h_pre (Zlength hs + 1) (hs ++ [0])).
Qed.


Lemma proof_of_twobyte_strstr_return_wit_1 : twobyte_strstr_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twobyte_strstr_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_twobyte_strstr_return_wit_1_split_goal_1.
Qed.


Lemma proof_of_twobyte_strstr_return_wit_2_split_goal_1 : twobyte_strstr_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold strstr_result, substring_at, no_match_before in *.
  destruct PreH9 as [Hlen _].
  assert (Hi : i = Zlength hs).
  { rewrite Znth_sublist in PreH2 by
      (try rewrite Zlength_app; try rewrite Zlength_cons;
       try rewrite Zlength_nil; lia).
    destruct (Z.eq_dec i (Zlength hs)) as [Heq|Hneq]; [exact Heq|].
    assert (Hlt : i < Zlength hs) by lia.
    rewrite app_Znth1 in PreH2 by lia.
    replace (0 + i) with i in PreH2 by lia.
    assert (Hin : In (Znth i hs 0) hs).
    { unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. exact Hlt. }
    unfold nonzero_bytes in PreH6.
    pose proof ((proj1 (Forall_forall _ _)) PreH6 (Znth i hs 0) Hin) as Hbyte.
    cbn in Hbyte. lia. }
  left. split; [reflexivity|].
  intros j [Hj [Hrange Hsub]].
  destruct (Z_lt_ge_dec j (i - 1)) as [Hbefore|Hafter].
  - apply (PreH10 j). lia. split; [exact Hj|split; assumption].
  - lia.
Qed.


Lemma proof_of_twobyte_strstr_return_wit_2_split_goal_spatial : twobyte_strstr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst h.
  sep_apply_l_atomic (UCharArray.full_merge_to_full h_pre i (Zlength hs + 1)
    (sublist 0 i (hs ++ [0])) (sublist i (Zlength hs + 1) (hs ++ [0]))).
  - dump_pre_spatial. lia.
  - rewrite <- sublist_split by
      (try rewrite Zlength_app; try rewrite Zlength_cons;
       try rewrite Zlength_nil; lia).
    rewrite sublist_self by
      (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    cancel (UCharArray.full h_pre (Zlength hs + 1) (hs ++ [0])).
Qed.


Lemma proof_of_twobyte_strstr_return_wit_2 : twobyte_strstr_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twobyte_strstr_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_twobyte_strstr_return_wit_2_split_goal_1.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_1_split_goal_1 : threebyte_strstr_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range
    (Znth 2 (ns ++ [0]) 0 * 2 ^ 8) 32 ltac:(lia)) as Hrange.
  dump_pre_spatial.
  lia.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_1_split_goal_2 : threebyte_strstr_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 2 (ns ++ [0]) 0 * 2 ^ 8) 32 ltac:(lia)) as Hrange.
  dump_pre_spatial.
  lia.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_1_split_goal_3 : threebyte_strstr_safety_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_1_split_goal_4 : threebyte_strstr_safety_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_1 : threebyte_strstr_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_1_split_goal_2.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_1_split_goal_3.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_1_split_goal_4.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_2_split_goal_1 : threebyte_strstr_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 1 (ns ++ [0]) 0 * 2 ^ 16) 32 ltac:(lia)) as Hrange.
  dump_pre_spatial.
  lia.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_2_split_goal_2 : threebyte_strstr_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 1 (ns ++ [0]) 0 * 2 ^ 16) 32 ltac:(lia)) as Hrange.
  dump_pre_spatial.
  lia.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_2_split_goal_3 : threebyte_strstr_safety_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_2_split_goal_4 : threebyte_strstr_safety_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_2 : threebyte_strstr_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_2_split_goal_2.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_2_split_goal_3.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_2_split_goal_4.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_10_split_goal_1 : threebyte_strstr_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 2 (hs ++ [0]) 0 * 2 ^ 8) 32 ltac:(lia)) as Hrange.
  dump_pre_spatial.
  lia.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_10_split_goal_2 : threebyte_strstr_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 2 (hs ++ [0]) 0 * 2 ^ 8) 32 ltac:(lia)) as Hrange.
  dump_pre_spatial.
  lia.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_10_split_goal_3 : threebyte_strstr_safety_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_10_split_goal_4 : threebyte_strstr_safety_wit_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_10 : threebyte_strstr_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_10_split_goal_2.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_10_split_goal_3.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_10_split_goal_4.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_11_split_goal_1 : threebyte_strstr_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 1 (hs ++ [0]) 0 * 2 ^ 16) 32 ltac:(lia)) as Hrange.
  dump_pre_spatial.
  lia.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_11_split_goal_2 : threebyte_strstr_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (signed_Lastnbits_range (Znth 1 (hs ++ [0]) 0 * 2 ^ 16) 32 ltac:(lia)) as Hrange.
  dump_pre_spatial.
  lia.
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_11_split_goal_3 : threebyte_strstr_safety_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_11_split_goal_4 : threebyte_strstr_safety_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_threebyte_strstr_safety_wit_11 : threebyte_strstr_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_11_split_goal_2.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_11_split_goal_3.
  - Goal_apply proof_of_threebyte_strstr_safety_wit_11_split_goal_4.
Qed.


Lemma proof_of_threebyte_strstr_entail_wit_1 : threebyte_strstr_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists 2.
  split_pure_spatial.
  - sep_apply (UCharArray.full_split_to_full h_pre 2 (Zlength hs + 1) (hs ++ [0])).
    + cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
      cancel (UCharArray.full h_pre 2 (sublist 0 2 (hs ++ [0]))).
      cancel (UCharArray.full (h_pre + 2 * sizeof(UCHAR)) (Zlength hs + 1 - 2)
        (sublist 2 (Zlength hs + 1) (hs ++ [0]))).
    + lia.
  - split_pures; try (dump_pre_spatial; try tauto; try lia).
    + unfold rolling3. split; [lia|].
      assert (Ha : 0 <= Znth 0 (hs ++ [0]) 0 < 256).
      { rewrite nth_app_zero__proof_of_threebyte_2 by lia.
        apply nonzero_nth_bound__proof_of_threebyte_2; [exact PreH1|lia]. }
      assert (Hb : 0 <= Znth 1 (hs ++ [0]) 0 < 256).
      { rewrite nth_app_zero__proof_of_threebyte_2 by lia.
        apply nonzero_nth_bound__proof_of_threebyte_2; [exact PreH1|lia]. }
      assert (Hc : 0 <= Znth 2 (hs ++ [0]) 0 < 256).
      { rewrite nth_app_zero__proof_of_threebyte_2 by lia.
        apply nonzero_nth_bound__proof_of_threebyte_2; [exact PreH1|lia]. }
      unfold unsigned_last_nbits.
      rewrite packed3__proof_of_threebyte_2 by lia.
      change 4294967295 with (Z.ones 32).
      rewrite Z.land_ones by lia.
      replace (2 - 2) with 0 by lia.
      replace (2 - 1) with 1 by lia.
      symmetry.
      apply Z.mod_small.
      change (2 ^ 32) with 4294967296.
      lia.
    + unfold needle3. split; [lia|].
      assert (Ha : 0 <= Znth 0 ns 0 < 256).
      { apply nonzero_nth_bound__proof_of_threebyte_2; [exact PreH2|lia]. }
      assert (Hb : 0 <= Znth 1 ns 0 < 256).
      { apply nonzero_nth_bound__proof_of_threebyte_2; [exact PreH2|lia]. }
      assert (Hc : 0 <= Znth 2 ns 0 < 256).
      { apply nonzero_nth_bound__proof_of_threebyte_2; [exact PreH2|lia]. }
      rewrite (nth_app_zero__proof_of_threebyte_2 ns 0) by lia.
      rewrite (nth_app_zero__proof_of_threebyte_2 ns 1) by lia.
      rewrite (nth_app_zero__proof_of_threebyte_2 ns 2) by lia.
      unfold unsigned_last_nbits.
      rewrite packed3__proof_of_threebyte_2 by lia.
      ring.
    + unfold no_match_before. intros j Hj. lia.
Qed.


Lemma proof_of_threebyte_strstr_entail_wit_2 : threebyte_strstr_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i < Zlength hs).
  {
    rewrite Znth_sublist in PreH2 by
      (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    replace (0 + i) with i in PreH2 by lia.
    destruct (Z.eq_dec i (Zlength hs)) as [Heq | Hne].
    - subst i. rewrite terminator_index__proof_of_threebyte_2 in PreH2. contradiction.
    - lia.
  }
  assert (Hnm : no_match_before hs ns (i - 1)).
  {
    unfold no_match_before in *.
    intros k Hk.
    destruct (Z_lt_ge_dec k (i - 2)) as [Hbefore | Hlast].
    - apply PreH10; lia.
    - assert (k = i - 2) by lia. subst k.
      intro Hmatch. apply PreH1.
      exact (match_implies_packed3__proof_of_threebyte_2
        hs ns i hw nw PreH6 PreH8 PreH9 Hmatch).
  }
  Exists (i + 1).
  split_pure_spatial.
  - cancel (UCharArray.full n_pre (Zlength ns + 1) (ns +:: 0)).
    subst h.
    sep_apply_l_atomic (UCharArray.full_merge_to_full h_pre i (Zlength hs + 1)
      (sublist 0 i (hs +:: 0))
      (sublist i (Zlength hs + 1) (hs +:: 0))).
    + dump_pre_spatial. lia.
    + rewrite <- (sublist_split 0 (Zlength hs + 1) i (hs +:: 0)) by
        (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      rewrite sublist_self by
        (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      sep_apply_l_atomic (UCharArray.full_split_to_full h_pre
        (i + 1) (Zlength hs + 1) (hs +:: 0)).
      * dump_pre_spatial. lia.
      * replace (h_pre + (i + 1) * sizeof ( UCHAR ))
          with (h_pre + i * sizeof ( UCHAR ) + 1 * sizeof ( UCHAR )) by ring.
        cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: change (sizeof ( UCHAR )) with 1 in *.
    all: try lia.
    all: try assumption.
    all: try (replace (i + 1 - 1) with i by lia; exact PreH8).
    all: try (replace (i + 1 - 2) with (i - 1) by lia; exact Hnm).
Qed.


Lemma proof_of_threebyte_strstr_entail_wit_3_split_goal_1 : threebyte_strstr_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (rolling3_unmask__proof_of_threebyte_2 hs (j - 1) hw PreH4 PreH6) as Hw.
  pose proof (byte_or_nul_range__proof_of_threebyte_2 hs (j - 3) PreH4 ltac:(lia)) as Ha.
  pose proof (byte_or_nul_range__proof_of_threebyte_2 hs (j - 2) PreH4 ltac:(lia)) as Hb.
  pose proof (byte_or_nul_range__proof_of_threebyte_2 hs (j - 1) PreH4 ltac:(lia)) as Hc.
  pose proof (byte_or_nul_range__proof_of_threebyte_2 hs j PreH4 ltac:(lia)) as Hd.
  unfold rolling3. split; [lia |].
  rewrite Znth_sublist by (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  replace (0 + j) with j by lia.
  rewrite Hw.
  unfold unsigned_last_nbits.
  replace 4294967295 with (Z.ones 32) by reflexivity.
  rewrite Z.land_ones by lia.
  change (2 ^ 32) with 4294967296.
  rewrite (Z.mod_small
    (16777216 * Znth (j - 2) (hs +:: 0) 0 +
     65536 * Znth (j - 1) (hs +:: 0) 0 +
       256 * Znth j (hs +:: 0) 0) 4294967296) by lia.
  replace (j - 1 - 2) with (j - 3) by lia.
  replace (j - 1 - 1) with (j - 2) by lia.
  apply packed3_step__proof_of_threebyte_2; lia.
Qed.


Lemma proof_of_threebyte_strstr_entail_wit_3 : threebyte_strstr_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_threebyte_strstr_entail_wit_3_split_goal_1.
Qed.


Lemma proof_of_threebyte_strstr_return_wit_1_split_goal_1 : threebyte_strstr_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hi : i < Zlength hs).
  {
    rewrite Znth_sublist in PreH3 by
      (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    replace (0 + i) with i in PreH3 by lia.
    destruct (Z.eq_dec i (Zlength hs)) as [Heq | Hne].
    - subst i. rewrite terminator_index__proof_of_threebyte_2 in PreH3. contradiction.
    - lia.
  }
  unfold strstr_result.
  right. exists (i - 2).
  split.
  - unfold first_substring. split.
    + eapply packed3_implies_match__proof_of_threebyte_2; eauto; lia.
    + exact PreH11.
  - subst h.
    change (sizeof ( UCHAR )) with 1 in *.
    change (sizeof ( CHAR )) with 1 in *.
    lia.
Qed.


Lemma proof_of_threebyte_strstr_return_wit_1_split_goal_spatial : threebyte_strstr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst h.
  sep_apply_l_atomic (UCharArray.full_merge_to_full h_pre i (Zlength hs + 1)
      (sublist 0 i (hs +:: 0))
      (sublist i (Zlength hs + 1) (hs +:: 0))).
  - dump_pre_spatial. lia.
  - rewrite <- (sublist_split 0 (Zlength hs + 1) i (hs +:: 0)) by
      (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    rewrite sublist_self by (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    cancel.
Qed.


Lemma proof_of_threebyte_strstr_return_wit_1 : threebyte_strstr_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_threebyte_strstr_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_threebyte_strstr_return_wit_1_split_goal_1.
Qed.


Lemma proof_of_threebyte_strstr_return_wit_2_split_goal_1 : threebyte_strstr_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold strstr_result.
  left; split; [reflexivity |].
  assert (Hi : i = Zlength hs).
  {
    rewrite Znth_sublist in PreH2 by
      (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    destruct (Z.eq_dec i (Zlength hs)) as [Heq | Hne]; [exact Heq |].
    assert (Hlt : i < Zlength hs) by lia.
    unfold nonzero_bytes in PreH6.
    apply Forall_forall with (x := Znth i hs 0) in PreH6.
    2: { unfold Znth. apply nth_In. rewrite Zlength_correct in Hlt. lia. }
    unfold Znth in *.
    rewrite app_nth1 in PreH2 by (rewrite Zlength_correct in Hlt; lia).
    replace (0 + i) with i in PreH2 by lia.
    lia.
  }
  intros k Hmatch.
  apply (PreH10 k).
  - unfold substring_at in Hmatch.
    unfold needle3 in PreH9.
    destruct PreH9 as [Hn _].
    lia.
  - exact Hmatch.
Qed.


Lemma proof_of_threebyte_strstr_return_wit_2_split_goal_spatial : threebyte_strstr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst h.
  sep_apply_l_atomic (UCharArray.full_merge_to_full h_pre i (Zlength hs + 1)
      (sublist 0 i (hs +:: 0))
      (sublist i (Zlength hs + 1) (hs +:: 0))).
  - dump_pre_spatial. lia.
  - rewrite <- (sublist_split 0 (Zlength hs + 1) i (hs +:: 0)) by
      (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    rewrite sublist_self by (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    cancel.
Qed.


Lemma proof_of_threebyte_strstr_return_wit_2 : threebyte_strstr_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_threebyte_strstr_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_threebyte_strstr_return_wit_2_split_goal_1.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_1_split_goal_1 : fourbyte_strstr_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  all: match goal with |- context [signed_last_nbits ?x 32] =>
    pose proof (signed_Lastnbits_range x 32 ltac:(lia)) as Hrange end.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_1_split_goal_2 : fourbyte_strstr_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  all: match goal with |- context [signed_last_nbits ?x 32] =>
    pose proof (signed_Lastnbits_range x 32 ltac:(lia)) as Hrange end.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_1_split_goal_3 : fourbyte_strstr_safety_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_1_split_goal_4 : fourbyte_strstr_safety_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_1 : fourbyte_strstr_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_1_split_goal_2.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_1_split_goal_3.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_1_split_goal_4.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_2_split_goal_1 : fourbyte_strstr_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  all: match goal with |- context [signed_last_nbits ?x 32] =>
    pose proof (signed_Lastnbits_range x 32 ltac:(lia)) as Hrange end.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_2_split_goal_2 : fourbyte_strstr_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  all: match goal with |- context [signed_last_nbits ?x 32] =>
    pose proof (signed_Lastnbits_range x 32 ltac:(lia)) as Hrange end.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_2_split_goal_3 : fourbyte_strstr_safety_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_2_split_goal_4 : fourbyte_strstr_safety_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_2 : fourbyte_strstr_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_2_split_goal_2.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_2_split_goal_3.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_2_split_goal_4.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_11_split_goal_1 : fourbyte_strstr_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  all: match goal with |- context [signed_last_nbits ?x 32] =>
    pose proof (signed_Lastnbits_range x 32 ltac:(lia)) as Hrange end.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_11_split_goal_2 : fourbyte_strstr_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  all: match goal with |- context [signed_last_nbits ?x 32] =>
    pose proof (signed_Lastnbits_range x 32 ltac:(lia)) as Hrange end.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_11_split_goal_3 : fourbyte_strstr_safety_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_11_split_goal_4 : fourbyte_strstr_safety_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_11 : fourbyte_strstr_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_11_split_goal_2.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_11_split_goal_3.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_11_split_goal_4.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_12_split_goal_1 : fourbyte_strstr_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  all: match goal with |- context [signed_last_nbits ?x 32] =>
    pose proof (signed_Lastnbits_range x 32 ltac:(lia)) as Hrange end.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_12_split_goal_2 : fourbyte_strstr_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  all: match goal with |- context [signed_last_nbits ?x 32] =>
    pose proof (signed_Lastnbits_range x 32 ltac:(lia)) as Hrange end.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_12_split_goal_3 : fourbyte_strstr_safety_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_12_split_goal_4 : fourbyte_strstr_safety_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_fourbyte_strstr_safety_wit_12 : fourbyte_strstr_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_12_split_goal_2.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_12_split_goal_3.
  - Goal_apply proof_of_fourbyte_strstr_safety_wit_12_split_goal_4.
Qed.


Lemma proof_of_fourbyte_strstr_entail_wit_1 : fourbyte_strstr_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists 3.
  split_pure_spatial.
  - sep_apply (UCharArray.full_split_to_full h_pre 3 (Zlength hs + 1) (hs ++ [0])).
    cancel.
    all: lia.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
    + unfold rolling4. split; [lia|].
      pose proof (fourbyte_app_byte_bound__proof_of_fourbyte_2 hs 0 PreH1 ltac:(lia)) as B0.
      pose proof (fourbyte_app_byte_bound__proof_of_fourbyte_2 hs 1 PreH1 ltac:(lia)) as B1.
      pose proof (fourbyte_app_byte_bound__proof_of_fourbyte_2 hs 2 PreH1 ltac:(lia)) as B2.
      pose proof (fourbyte_app_byte_bound__proof_of_fourbyte_2 hs 3 PreH1 ltac:(lia)) as B3.
      unfold unsigned_last_nbits.
      rewrite fourbyte_pack_or__proof_of_fourbyte_2 by lia.
      replace 4294967295 with (Z.ones 32) by reflexivity.
      rewrite Z.land_ones by lia.
      change (2 ^ 32) with 4294967296.
      replace (3 - 3) with 0 by lia.
      replace (3 - 2) with 1 by lia.
      replace (3 - 1) with 2 by lia.
      rewrite Z.mod_small by lia.
      reflexivity.
    + unfold needle4. split; [assumption|].
      pose proof (fourbyte_app_byte_bound__proof_of_fourbyte_2 ns 0 PreH2 ltac:(lia)) as B0.
      pose proof (fourbyte_app_byte_bound__proof_of_fourbyte_2 ns 1 PreH2 ltac:(lia)) as B1.
      pose proof (fourbyte_app_byte_bound__proof_of_fourbyte_2 ns 2 PreH2 ltac:(lia)) as B2.
      pose proof (fourbyte_app_byte_bound__proof_of_fourbyte_2 ns 3 PreH2 ltac:(lia)) as B3.
      unfold unsigned_last_nbits.
      rewrite fourbyte_pack_or__proof_of_fourbyte_2 by lia.
      unfold Znth.
      simpl Z.to_nat.
      rewrite !app_nth1 by (rewrite Zlength_correct in PreH3; lia).
      reflexivity.
    + unfold no_match_before. intros j Hj. lia.
Qed.


Lemma proof_of_fourbyte_strstr_entail_wit_2 : fourbyte_strstr_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (i + 1).
  assert (Hi : i < Zlength hs).
  { destruct (Z.eq_dec i (Zlength hs)) as [Heq|Hne]; [subst i|lia].
    rewrite Znth_sublist in PreH2 by (try rewrite Zlength_app_cons; lia).
    unfold Znth in PreH2.
    rewrite app_nth2 in PreH2 by (rewrite Zlength_correct; lia).
    rewrite Zlength_correct in PreH2.
    replace (0 + Z.of_nat (Datatypes.length hs)) with
      (Z.of_nat (Datatypes.length hs)) in PreH2 by lia.
    rewrite Nat2Z.id in PreH2.
    rewrite Nat.sub_diag in PreH2.
    simpl in PreH2.
    contradiction. }
  split_pure_spatial.
  - replace h with (h_pre + i * sizeof (UCHAR)) by lia.
    sep_apply (UCharArray.full_merge_to_full h_pre i (Zlength hs + 1)).
    rewrite <- sublist_split by (try rewrite Zlength_app_cons; lia).
    rewrite sublist_self by (rewrite Zlength_app_cons; lia).
    sep_apply (UCharArray.full_split_to_full h_pre (i + 1) (Zlength hs + 1) (hs ++ [0])).
    replace (h_pre + i * sizeof (UCHAR) + 1 * sizeof (UCHAR)) with
      (h_pre + (i + 1) * sizeof (UCHAR)) by ring.
    cancel.
    all: lia.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
    all: try (replace (i + 1 - 1) with i by lia; assumption).
    unfold no_match_before in *.
    intros k Hk.
    assert (Hcase : k < i - 3 \/ k = i - 3) by lia.
    destruct Hcase as [Hbefore | Hat].
    + apply PreH10; lia.
    + subst k. intro Hsub. apply PreH1.
      eapply fourbyte_match_word__proof_of_fourbyte_2; eauto.
Qed.


Lemma proof_of_fourbyte_strstr_entail_wit_3_split_goal_1 : fourbyte_strstr_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold rolling4 in *.
  destruct PreH6 as [Hold_index Hword].
  split; [lia|].
  rewrite Znth_sublist by (try rewrite Zlength_app_cons; lia).
  replace (0 + j) with j by lia.
  replace (j - 1 - 3) with (j - 4) in Hword by lia.
  replace (j - 1 - 2) with (j - 3) in Hword by lia.
  replace (j - 1 - 1) with (j - 2) in Hword by lia.
  rewrite Hword.
  unfold unsigned_last_nbits.
  apply fourbyte_shift_word__proof_of_fourbyte_2.
  all: eapply fourbyte_app_byte_bound__proof_of_fourbyte_2; eauto; lia.
Qed.


Lemma proof_of_fourbyte_strstr_entail_wit_3 : fourbyte_strstr_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fourbyte_strstr_entail_wit_3_split_goal_1.
Qed.


Lemma proof_of_fourbyte_strstr_return_wit_1_split_goal_1 : fourbyte_strstr_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hi : i < Zlength hs).
  { eapply fourbyte_nonzero_read_lt__proof_of_fourbyte_2; eauto; lia. }
  assert (Hmatch : substring_at hs ns (i - 3)).
  { eapply fourbyte_word_substring__proof_of_fourbyte_2; eauto. }
  unfold strstr_result, first_substring.
  right. exists (i - 3).
  split; [split; [exact Hmatch | exact PreH11] |].
  rewrite PreH4.
  change (sizeof (CHAR)) with 1.
  change (sizeof (UCHAR)) with 1.
  lia.
Qed.


Lemma proof_of_fourbyte_strstr_return_wit_1_split_goal_spatial : fourbyte_strstr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace h with (h_pre + i * sizeof (UCHAR)) by lia.
  sep_apply (UCharArray.full_merge_to_full h_pre i (Zlength hs + 1)).
  rewrite <- sublist_split by (try rewrite Zlength_app_cons; lia).
  rewrite sublist_self by (rewrite Zlength_app_cons; lia).
  cancel.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_return_wit_1 : fourbyte_strstr_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_fourbyte_strstr_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_fourbyte_strstr_return_wit_1_split_goal_1.
Qed.


Lemma proof_of_fourbyte_strstr_return_wit_2_split_goal_1 : fourbyte_strstr_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hi : i = Zlength hs).
  { eapply fourbyte_zero_read_eq_len__proof_of_fourbyte_3; eauto; lia. }
  unfold strstr_result.
  left; split; [reflexivity|].
  intros j Hsub.
  assert (Hj : 0 <= j) by (destruct Hsub as [Hj _]; exact Hj).
  destruct (Z_lt_ge_dec j (i - 3)) as [Hbefore|Hafter].
  - unfold no_match_before in PreH10.
    apply (PreH10 j); [lia|exact Hsub].
  - unfold substring_at in Hsub.
    destruct Hsub as [_ [Hbound _]].
    destruct PreH9 as [Hneedle_len _].
    lia.
Qed.


Lemma proof_of_fourbyte_strstr_return_wit_2_split_goal_spatial : fourbyte_strstr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace h with (h_pre + i * sizeof (UCHAR)) by lia.
  sep_apply (UCharArray.full_merge_to_full h_pre i (Zlength hs + 1)).
  rewrite <- sublist_split by (try rewrite Zlength_app_cons; lia).
  rewrite sublist_self by (rewrite Zlength_app_cons; lia).
  cancel.
  all: lia.
Qed.


Lemma proof_of_fourbyte_strstr_return_wit_2 : fourbyte_strstr_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_fourbyte_strstr_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_fourbyte_strstr_return_wit_2_split_goal_1.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_6_split_goal_1 : twoway_strstr_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos_pos (Znth l (ns ++ [0]) 0) 64 ltac:(lia) ltac:(lia)) as Hmod.
  intro Hgt.
  apply Z.compare_gt_iff in Hgt.
  replace (8 * 8) with 64 in Hgt by lia.
  lia.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_6_split_goal_2 : twoway_strstr_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos_pos (Znth l (ns ++ [0]) 0) 64 ltac:(lia) ltac:(lia)) as Hmod.
  intro Hlt.
  apply Z.compare_gt_iff in Hlt.
  replace (8 * 8) with 64 in Hlt by lia.
  lia.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_6 : twoway_strstr_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_twoway_strstr_safety_wit_6_split_goal_2.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_104_split_goal_1 : twoway_strstr_safety_wit_104_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (8 * 8) with 64 by lia.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound
    (Znth (l - 1) (sublist pos end_ hs) 0) 64 ltac:(lia)).
  entailer!.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_104_split_goal_2 : twoway_strstr_safety_wit_104_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (8 * 8) with 64 by lia.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound
    (Znth (l - 1) (sublist pos end_ hs) 0) 64 ltac:(lia)).
  entailer!.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_104 : twoway_strstr_safety_wit_104.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_safety_wit_104_split_goal_1.
  - Goal_apply proof_of_twoway_strstr_safety_wit_104_split_goal_2.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_105_split_goal_1 : twoway_strstr_safety_wit_105_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos_pos
    (Znth (l - 1) (sublist pos end_ hs) 0) 64 ltac:(lia) PreH10).
  replace (8 * 8) with 64 by lia.
  lia.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_105_split_goal_2 : twoway_strstr_safety_wit_105_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos_pos
    (Znth (l - 1) (sublist pos end_ hs) 0) 64 ltac:(lia) PreH10).
  replace (8 * 8) with 64 by lia.
  lia.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_105 : twoway_strstr_safety_wit_105.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_safety_wit_105_split_goal_1.
  - Goal_apply proof_of_twoway_strstr_safety_wit_105_split_goal_2.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_106_split_goal_1 : twoway_strstr_safety_wit_106_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos_pos (Znth (l - 1) (sublist pos end_ hs) 0) 64 ltac:(lia) ltac:(lia)) as Hmod.
  intro Hgt.
  apply Z.compare_gt_iff in Hgt.
  replace (8 * 8) with 64 in Hgt by lia.
  lia.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_106_split_goal_2 : twoway_strstr_safety_wit_106_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos_pos (Znth (l - 1) (sublist pos end_ hs) 0) 64 ltac:(lia) ltac:(lia)) as Hmod.
  intro Hlt.
  apply Z.compare_gt_iff in Hlt.
  replace (8 * 8) with 64 in Hlt by lia.
  lia.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_106 : twoway_strstr_safety_wit_106.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_safety_wit_106_split_goal_1.
  - Goal_apply proof_of_twoway_strstr_safety_wit_106_split_goal_2.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_107_split_goal_1 : twoway_strstr_safety_wit_107_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos_pos (Znth (l - 1) (sublist pos end_ hs) 0) 64 ltac:(lia) ltac:(lia)) as Hmod.
  intro Hgt.
  apply Z.compare_gt_iff in Hgt.
  replace (8 * 8) with 64 in Hgt by lia.
  lia.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_107_split_goal_2 : twoway_strstr_safety_wit_107_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos_pos (Znth (l - 1) (sublist pos end_ hs) 0) 64 ltac:(lia) ltac:(lia)) as Hmod.
  intro Hlt.
  apply Z.compare_gt_iff in Hlt.
  replace (8 * 8) with 64 in Hlt by lia.
  lia.
Qed.


Lemma proof_of_twoway_strstr_safety_wit_107 : twoway_strstr_safety_wit_107.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_safety_wit_107_split_goal_1.
  - Goal_apply proof_of_twoway_strstr_safety_wit_107_split_goal_2.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_1 : twoway_strstr_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbyte : 0 < Znth 0 (ns ++ [0]) 0 < 256).
  { destruct ns as [|x xs].
    - rewrite Zlength_nil in PreH3. lia.
    - unfold nonzero_bytes in PreH2.
      inversion PreH2; subst.
      change (Znth 0 ((x :: xs) ++ [0]) 0) with x.
      assumption. }
  Exists (repeat_Z 0 256) (repeat_Z 0 4).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: try solve [dump_pre_spatial; simpl; lia].
    all: try solve [dump_pre_spatial; auto].
    all: try solve [dump_pre_spatial; vm_compute; reflexivity].
    all: try solve [dump_pre_spatial;
      rewrite Z.quot_div_nonneg by lia; apply Z.div_pos; lia].
    all: try solve [dump_pre_spatial;
      rewrite Z.quot_div_nonneg by lia; apply Z.div_lt_upper_bound; lia].
    all: try solve [dump_pre_spatial; unfold shift_prefix; intros; lia].
    dump_pre_spatial.
    unfold byteset_prefix.
    intros c Hc.
    split.
    + intro H.
      unfold repeat_Z in H.
      rewrite Znth_repeat in H.
      rewrite Z.testbit_0_l in H.
      discriminate.
    + intros [j [Hj _]]. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_1 : twoway_strstr_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 ns l (conj PreH5 PreH6) PreH2) as Hlt.
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  eapply (shift_prefix_step__twoway_table_1 ns l
    (Znth l (ns ++ [0]) 0) sh_2); try eassumption; try lia.
  rewrite app_Znth1 by lia. reflexivity.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_2 : twoway_strstr_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 ns l (conj PreH5 PreH6) PreH2) as Hlt.
  replace (unsigned_last_nbits (l + 1) 64) with (l + 1)
    by (symmetry; apply unsigned_last_nbits_eq; cbn; lia).
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.rem_mod_nonneg by lia.
  eapply (byteset_prefix_step__twoway_table_1 ns l
    (Znth l (ns ++ [0]) 0) bs_2); try eassumption; try lia.
  rewrite app_Znth1 by lia. reflexivity.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_3 : twoway_strstr_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_4 : twoway_strstr_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_5 : twoway_strstr_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 ns l (conj PreH5 PreH6) PreH2) as Hnlt.
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  pose proof (byte_at_or_terminator__twoway_table_1 ns (l + 1) PreH13 ltac:(lia)) as Hbyte.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_lt_upper_bound; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_6 : twoway_strstr_entail_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 ns l (conj PreH5 PreH6) PreH2) as Hnlt.
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  pose proof (byte_at_or_terminator__twoway_table_1 ns (l + 1) PreH13 ltac:(lia)) as Hbyte.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_7 : twoway_strstr_entail_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 ns l (conj PreH5 PreH6) PreH2) as Hnlt.
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  pose proof (byte_at_or_terminator__twoway_table_1 ns (l + 1) PreH13 ltac:(lia)) as Hbyte.
  lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_8 : twoway_strstr_entail_wit_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 ns l (conj PreH5 PreH6) PreH2) as Hnlt.
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  pose proof (byte_at_or_terminator__twoway_table_1 ns (l + 1) PreH13 ltac:(lia)) as Hbyte.
  lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_9 : twoway_strstr_entail_wit_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 hs l (conj PreH5 PreH7) PreH1) as Hlt.
  pose proof (nonzero_index_lt__twoway_table_1 ns l (conj PreH5 PreH6) PreH2) as Hnlt.
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_10 : twoway_strstr_entail_wit_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 ns l (conj PreH5 PreH6) PreH2) as Hnlt.
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2_split_goal_11 : twoway_strstr_entail_wit_2_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 ns l (conj PreH5 PreH6) PreH2) as Hnlt.
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_2 : twoway_strstr_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_5.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_6.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_7.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_8.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_9.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_10.
  - Goal_apply proof_of_twoway_strstr_entail_wit_2_split_goal_11.
Qed.








Lemma u64_max_add x : 1 <= x <= 18446744073709551616 ->
 unsigned_last_nbits (18446744073709551615+x) 64 = x-1.
Proof.
 intros H. unfold unsigned_last_nbits.
 change (2^64) with 18446744073709551616.
 replace (18446744073709551615+x) with ((x-1)+1*18446744073709551616) by lia.
 rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.
Lemma u64_sub_max x : 0 <= x < 18446744073709551615 ->
 unsigned_last_nbits (x-18446744073709551615) 64 = x+1.
Proof.
 intros H. unfold unsigned_last_nbits.
 change (2^64) with 18446744073709551616.
 replace (x-18446744073709551615) with ((x+1)+(-1)*18446744073709551616) by lia.
 rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Ltac cf_norm :=
 repeat first
 [ progress rewrite u64_max_add in * by lia
 | progress rewrite u64_sub_max in * by lia
 | progress rewrite unsigned_last_nbits_eq in * by lia ];
 try rewrite !app_Znth1 in * by lia;
 repeat match goal with
 | H : context [?x + 1 - 1] |- _ => replace (x+1-1) with x in * by lia
 | |- context [?x + 1 - 1] => replace (x+1-1) with x in * by lia
 end.

Ltac cf_step :=
  match goal with
  | H : safeExec ATrue (maxsuf_fwd_from_state ?ns ?i ?j ?k ?p) ?X |- _ =>
      let Hstep := fresh "Hstep" in
      pose proof (scan_safeExec_step ns 1 (i+1) j k p X) as Hstep;
      replace (i+1-1) with i in Hstep by lia;
      specialize (Hstep H ltac:(lia) ltac:(lia) ltac:(lia));
      unfold scan_cmp in Hstep; destruct (Z.eq_dec 1 1); [|lia];
      cf_choose Hstep i j k p
  | H : safeExec ATrue (maxsuf_rev_from_state ?ns ?i ?j ?k ?p) ?X |- _ =>
      let Hstep := fresh "Hstep" in
      pose proof (scan_safeExec_step ns 0 (i+1) j k p X) as Hstep;
      replace (i+1-1) with i in Hstep by lia;
      specialize (Hstep H ltac:(lia) ltac:(lia) ltac:(lia));
      unfold scan_cmp in Hstep; destruct (Z.eq_dec 0 1); [lia|];
      unfold Z_compare_rev in Hstep;
      cf_choose Hstep i j k p
  end
with cf_choose Hstep i j k p :=
  multimatch goal with
  | Hchar : ?rel (Znth ?a ?ns 0) (Znth ?b ?ns 0) |- _ =>
    first [replace (i+k) with a in Hstep by lia | replace (i+k) with b in Hstep by lia];
    first [replace (j+k) with a in Hstep by lia | replace (j+k) with b in Hstep by lia]
  end;
  match type of Hstep with
  | context [Z.compare ?a ?b] =>
    let Hcmp := fresh "Hcmp" in destruct (Z.compare a b) eqn:Hcmp;
    rewrite ?Z.compare_eq_iff, ?Z.compare_lt_iff, ?Z.compare_gt_iff in Hcmp
  end;
  try lia;
  try (destruct (Z.eq_dec k p); [|]); try lia.

Ltac cf_step_start h n hs ns :=
  prop_apply_p (strstr_pair_length64 h n hs ns ltac:(lia));
  let Hsmall := fresh "Hsmall" in Intros_p Hsmall;
  repeat match goal with H : ?i = UINT64_MAX |- _ => is_var i; subst i end;
  cf_norm; cf_step.
Ltac cf_spatial_choice finish :=
 first [solve [finish] | solve [Left; cf_spatial_choice finish] | solve [Right; cf_spatial_choice finish]].
Ltac cf_step_finish :=
  cf_norm;
  match goal with
  | |- context [UInt64Array.full _ 4 ?bs] =>
    match goal with
    | |- context [UInt64Array.full _ 256 ?sh] =>
      cf_spatial_choice ltac:(Exists sh bs; entailer!; try apply store_uint64_undef_store_uint64; try (rewrite Zlength_app, (Zlength_correct (0::nil)); cbn; lia))
    end
  end.


Ltac cf_prepare h n hs ns :=
  prop_apply_p (strstr_pair_length64 h n hs ns ltac:(lia));
  let Hsmall := fresh "Hsmall" in Intros_p Hsmall;
  repeat match goal with H : ?i = UINT64_MAX |- _ => is_var i; subst i end;
  try replace (unsigned_last_nbits (-1) 64) with 18446744073709551615 in * by (vm_compute; reflexivity);
  cf_norm.
Ltac cf_exit :=
  first [
  match goal with
  | H : safeExec ATrue (maxsuf_fwd_from_state ?ns ?i ?j ?k ?p) ?X |- _ =>
      let Hex := fresh "Hexit" in
      pose proof (scan_safeExec_exit ns 1 (i+1) j k p X) as Hex;
      replace (i+1-1) with i in Hex by lia;
      specialize (Hex H ltac:(lia))
  end |
  match goal with
  | H : safeExec ATrue (maxsuf_rev_from_state ?ns ?i ?j ?k ?p) ?X |- _ =>
      let Hex := fresh "Hexit" in
      pose proof (scan_safeExec_exit ns 0 (i+1) j k p X) as Hex;
      replace (i+1-1) with i in Hex by lia;
      specialize (Hex H ltac:(lia))
  end].
Ltac cf_select :=
  unfold maketuple in *;
  match goal with
  | Hf : safeExec ATrue (ret (?ms,?pf)) (result_state ATrue (maxsuf_fwd ?ns)),
    Hr : safeExec ATrue (ret (?mr,?pr)) (result_state ATrue (maxsuf_rev ?ns)) |- _ =>
    let Hne := fresh "Hnonempty" in
    assert (Hne : ns <> nil) by
      (let H := fresh in intro H; let Hb := fresh in assert (Hb : 0 < Zlength ns) by lia; rewrite H, Zlength_nil in Hb; lia);
    let Hres := fresh "Hselected" in
    pose proof (scans_safeExec_done ns (ms+1) pf (mr+1) pr Hne) as Hres;
    replace (ms+1-1) with ms in Hres by lia;
    replace (mr+1-1) with mr in Hres by lia;
    specialize (Hres Hf Hr);
    destruct (Z_lt_dec (ms+1) (mr+1)); try lia;
    first [rewrite Z.max_l in Hres by lia |rewrite Z.max_r in Hres by lia]
  end.


Lemma proof_of_twoway_strstr_entail_wit_5 : twoway_strstr_entail_wit_5.
Proof.
  unfold SimpleC.EE.stdlib.musl.strstr_rel_goal.twoway_strstr_entail_wit_5.
  right; intros.
  assert (Hl : l = Zlength ns)
    by (eapply nonzero_terminator_index__twoway_table_1; eauto; lia).
  subst l.
  replace (unsigned_last_nbits (-1) 64) with 18446744073709551615 by (vm_compute; reflexivity).
  replace (unsigned_last_nbits (18446744073709551615+1) 64) with 0 by (vm_compute; reflexivity).
  entailer!.
  change (safeExec ATrue (scan_initial ns 1) (result_state ATrue (scan_initial ns 1))).
  apply scan_safeExec_init.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_6_1 : twoway_strstr_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_pair_length64 h_pre n_pre hs ns ltac:(lia)).
  Intros_p Hsmall.
  subst ip. cf_norm.
  pose proof (scan_safeExec_step ns 1 0 jp k p _ PreH4 ltac:(lia) ltac:(lia) ltac:(lia)) as Hstep.
  unfold scan_cmp in Hstep; destruct (Z.eq_dec 1 1); [|lia].
  assert (Hcmp : Z.compare (Znth (jp+k) ns 0) (Znth (0-1+k) ns 0) = Eq).
  { apply Z.compare_eq_iff. replace (0-1+k) with (k-1) by lia. symmetry; exact PreH2. }
  rewrite Hcmp in Hstep. destruct (Z.eq_dec k p); [|lia].
  Left. Exists sh_2 bs_2. entailer!.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_6_2 : twoway_strstr_entail_wit_6_2.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_6_3 : twoway_strstr_entail_wit_6_3.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_6_4 : twoway_strstr_entail_wit_6_4.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_6_5 : twoway_strstr_entail_wit_6_5.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.



Lemma proof_of_twoway_strstr_entail_wit_6_6 : twoway_strstr_entail_wit_6_6.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.



Lemma proof_of_twoway_strstr_entail_wit_6_7 : twoway_strstr_entail_wit_6_7.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_6_8 : twoway_strstr_entail_wit_6_8.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.

Lemma proof_of_twoway_strstr_entail_wit_7_1 : twoway_strstr_entail_wit_7_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 cf_prepare h_pre n_pre hs ns. cf_exit.
 pose proof (scan_safeExec_init ns 0) as Hinit.
 cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_7_2 : twoway_strstr_entail_wit_7_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 cf_prepare h_pre n_pre hs ns. cf_exit.
 pose proof (scan_safeExec_init ns 0) as Hinit.
 cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_4 : twoway_strstr_entail_wit_8_4.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_3 : twoway_strstr_entail_wit_8_3.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_2 : twoway_strstr_entail_wit_8_2.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_1 : twoway_strstr_entail_wit_8_1.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_8 : twoway_strstr_entail_wit_8_8.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_7 : twoway_strstr_entail_wit_8_7.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_6 : twoway_strstr_entail_wit_8_6.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_5 : twoway_strstr_entail_wit_8_5.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_12 : twoway_strstr_entail_wit_8_12.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_11 : twoway_strstr_entail_wit_8_11.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_10 : twoway_strstr_entail_wit_8_10.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_9 : twoway_strstr_entail_wit_8_9.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_16 : twoway_strstr_entail_wit_8_16.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_15 : twoway_strstr_entail_wit_8_15.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_14 : twoway_strstr_entail_wit_8_14.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_8_13 : twoway_strstr_entail_wit_8_13.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_step_start h_pre n_pre hs ns. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_9_1 : twoway_strstr_entail_wit_9_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 cf_prepare h_pre n_pre hs ns. cf_exit. cf_select.
 all: unfold maxsuf_cut_index64.
 all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_9_2 : twoway_strstr_entail_wit_9_2.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_prepare h_pre n_pre hs ns. cf_exit. cf_select. all: unfold maxsuf_cut_index64. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_9_3 : twoway_strstr_entail_wit_9_3.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_prepare h_pre n_pre hs ns. cf_exit. cf_select. all: unfold maxsuf_cut_index64. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_9_4 : twoway_strstr_entail_wit_9_4.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_prepare h_pre n_pre hs ns. cf_exit. cf_select. all: unfold maxsuf_cut_index64. all: cf_step_finish.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_9_5 : twoway_strstr_entail_wit_9_5.
Proof. LLM_pre_process ltac:(lia || int_auto). cf_prepare h_pre n_pre hs ns. cf_exit. cf_select. all: unfold maxsuf_cut_index64. all: cf_step_finish.
Qed.


From SimpleC.EE.stdlib.musl Require Import strstr_rel_legacy_bridge.
Require Import SimpleC.EE.stdlib.musl.two_way_critical_factorization_theorem.


Lemma proof_of_twoway_strstr_entail_wit_10_1 : twoway_strstr_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hne : ns <> nil) by (intro He; assert (Hp : 0 < Zlength ns) by lia; rewrite He, Zlength_nil in Hp; lia).
  pose proof (factorization_safeExec_done ns (unsigned_last_nbits (ms+1) 64) p PreH6) as Hfactor.
  destruct (factorization_safeExec_bounds ns (unsigned_last_nbits (ms+1) 64) p Hne PreH6)
    as [Hsplitbound [Hpbound Hperiodbound]].
  assert (Hcfsearch : critical_search_split ns
    (unsigned_last_nbits (ms+1) 64) p).
  { eapply factorization_done_search_split.
    - let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia.
    - eassumption. }
  assert (Hsplitpos : 0 < unsigned_last_nbits (ms + 1) 64).
  { eapply memcmp_nonzero_count_positive; eauto. }
  assert (Hoff : off = p) by (rewrite sizeof_uchar in PreH2; lia).
  assert (Hnonrep : sublist 0 (unsigned_last_nbits (ms+1) 64) ns <>
    sublist p (unsigned_last_nbits (ms+1) 64+p) ns).
  { rewrite Hoff in PreH5. eapply memcmp_nonzero_needle_nonrep; eauto; lia. }
  assert (Hcursor : forall actual_p, search_cursor hs ns
    (unsigned_last_nbits (ms+1) 64) actual_p 0 0 0).
  { intros actual_p. eapply search_cursor_init_nonperiodic; eauto. }
  unfold maxsuf_cut_index64 in PreH21.
  destruct PreH21 as [Hms0 [Hsent | Hmslt]].
  - subst ms. vm_compute in Hsplitpos. exfalso. discriminate Hsplitpos.
  - assert (Hcritical : critical_split ns
      (unsigned_last_nbits (ms+1) 64) (unsigned_last_nbits (ms+1) 64)).
    { apply (proj1 (factorization_done_cut_search_split ns
        (unsigned_last_nbits (ms+1) 64) p
        ltac:(let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia) ltac:(eassumption) Hsplitpos)). }

    pose proof (proj2 Hcfsearch) as Hminimal.
    assert (Hsearch : critical_search_split ns
      (unsigned_last_nbits (ms + 1) 64) (unsigned_last_nbits (ms + 1) 64))
      by (split; assumption).
    prop_apply_p (strstr_array_length64__cut_probe h_pre hs).
    Intros_p Hlenhs.
    Exists sh_2 bs_2 0 0.
    split_pure_spatial.
    + cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
      cancel (UInt64Array.full &( "byteset" ) 4 bs_2).
      cancel (UInt64Array.full &( "shift" ) 256 sh_2).
      repeat rewrite Zsublist_nil by lia.
      rewrite sublist_self by reflexivity.
      repeat rewrite UCharArray.full_empty.
      entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [apply Hcursor | rewrite PreH7; exact Hcursor | rewrite <- Hsplit_eq; apply Hcursor |
        rewrite unsigned_last_nbits_eq by (cbn; lia); rewrite PreH7; exact Hcursor].
      all: try (unfold no_match_before; intros; lia).
      all: try (unfold strstr_rel_lib.matched_range; intros; lia).
      all: try (rewrite sublist_self by reflexivity; assumption).
      all: try (unfold periodic_memory_state; repeat split;
        try (left; reflexivity); intros; contradiction).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_10_2 : twoway_strstr_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hne : ns <> nil) by (intro He; assert (Hp : 0 < Zlength ns) by lia; rewrite He, Zlength_nil in Hp; lia).
  pose proof (factorization_safeExec_done ns (unsigned_last_nbits (ms+1) 64) p PreH6) as Hfactor.
  destruct (factorization_safeExec_bounds ns (unsigned_last_nbits (ms+1) 64) p Hne PreH6)
    as [Hsplitbound [Hpbound Hperiodbound]].
  assert (Hcfsearch : critical_search_split ns
    (unsigned_last_nbits (ms+1) 64) p).
  { eapply factorization_done_search_split.
    - let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia.
    - eassumption. }
  assert (Hoff : off = p) by (rewrite sizeof_uchar in PreH2; lia).
  assert (Hsplitpos : 0 < unsigned_last_nbits (ms + 1) 64).
  { eapply memcmp_nonzero_count_positive; eauto. }
  assert (Hnonrep :
    sublist 0 (unsigned_last_nbits (ms + 1) 64) ns <>
    sublist p (unsigned_last_nbits (ms + 1) 64 + p) ns).
  { rewrite Hoff in PreH5.
    eapply memcmp_nonzero_needle_nonrep; eauto; lia. }
  assert (Hcursor : forall actual_p, search_cursor hs ns
    (unsigned_last_nbits (ms+1) 64) actual_p 0 0 0).
  { intros actual_p. eapply search_cursor_init_nonperiodic; eauto. }
  assert (Hcritical : critical_split ns (unsigned_last_nbits (ms + 1) 64)
    (Z.max (unsigned_last_nbits (ms + 1) 64)
      (Zlength ns - unsigned_last_nbits (ms + 1) 64) + 1)).
  { apply (proj1 (factorization_done_nonrep_search_split ns
      (unsigned_last_nbits (ms+1) 64) p
      ltac:(let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia) ltac:(eassumption) Hnonrep)). }
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns).
  Intros_p Hlenns.
  prop_apply_p (strstr_array_length64__cut_probe h_pre hs).
  Intros_p Hlenhs.
  assert (Hmsrange : 0 <= ms < l).
  { unfold maxsuf_cut_index64 in PreH21.
    destruct PreH21 as [Hms0 [Hsent | Hmslt]]; [|lia].
    subst ms. vm_compute in Hsplitpos.
    exfalso. discriminate Hsplitpos. }
  assert (Hsplit_eq : unsigned_last_nbits (ms + 1) 64 = ms + 1).
  { unfold unsigned_last_nbits.
    rewrite Z.mod_small; [reflexivity |].
    change (2 ^ 64) with 18446744073709551616.
    lia. }
  assert (Hshift_eq :
    unsigned_last_nbits
      (unsigned_last_nbits (unsigned_last_nbits (l - ms) 64 - 1) 64 + 1) 64
    = l - ms).
  { apply nonperiodic_small_branch_shift64. lia. }
  assert (Hcritical_small : critical_split ns (ms + 1) (l - ms)).
  { rewrite Hsplit_eq in Hcritical.
    eapply critical_split_weaken_shift; [exact Hcritical |].
    rewrite <- PreH8. lia. }

  pose proof (proj2 Hcfsearch) as Hminimal.
  rewrite Hsplit_eq in Hminimal.
  assert (Hsearch_small : critical_search_split ns (ms + 1) (l - ms))
    by (split; assumption).
  Left.
  Exists sh_2 bs_2 0 0.
  split_pure_spatial.
  - cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
    cancel (UInt64Array.full &( "byteset" ) 4 bs_2).
    cancel (UInt64Array.full &( "shift" ) 256 sh_2).
    repeat rewrite Zsublist_nil by lia.
    rewrite sublist_self by reflexivity.
    repeat rewrite UCharArray.full_empty.
    entailer!.
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [apply Hcursor | rewrite PreH7; exact Hcursor | rewrite <- Hsplit_eq; apply Hcursor |
        rewrite unsigned_last_nbits_eq by (cbn; lia); rewrite PreH7; exact Hcursor].
    all: try (rewrite Hshift_eq; lia).
    all: try (rewrite Hsplit_eq, Hshift_eq; exact Hsearch_small).
    all: try (rewrite Hsplit_eq, Hshift_eq; exact Hcritical_small).
    all: try (unfold no_match_before; intros; lia).
    all: try (unfold strstr_rel_lib.matched_range; intros; lia).
    all: try (rewrite sublist_self by reflexivity; assumption).
    all: try (unfold periodic_memory_state; repeat split;
      try (left; reflexivity); intros; contradiction).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_10_3 : twoway_strstr_entail_wit_10_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hne : ns <> nil) by (intro He; assert (Hp : 0 < Zlength ns) by lia; rewrite He, Zlength_nil in Hp; lia).
  pose proof (factorization_safeExec_done ns (unsigned_last_nbits (ms+1) 64) p PreH6) as Hfactor.
  destruct (factorization_safeExec_bounds ns (unsigned_last_nbits (ms+1) 64) p Hne PreH6)
    as [Hsplitbound [Hpbound Hperiodbound]].
  assert (Hcfsearch : critical_search_split ns
    (unsigned_last_nbits (ms+1) 64) p).
  { eapply factorization_done_search_split.
    - let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia.
    - eassumption. }
  assert (Hsplitpos : 0 < unsigned_last_nbits (ms + 1) 64).
  { eapply memcmp_nonzero_count_positive; eauto. }
  assert (Hoff : off = p) by (rewrite sizeof_uchar in PreH2; lia).
  assert (Hnonrep : sublist 0 (unsigned_last_nbits (ms+1) 64) ns <>
    sublist p (unsigned_last_nbits (ms+1) 64+p) ns).
  { rewrite Hoff in PreH5. eapply memcmp_nonzero_needle_nonrep; eauto; lia. }
  assert (Hcursor : forall actual_p, search_cursor hs ns
    (unsigned_last_nbits (ms+1) 64) actual_p 0 0 0).
  { intros actual_p. eapply search_cursor_init_nonperiodic; eauto. }
  unfold maxsuf_cut_index64 in PreH21.
  destruct PreH21 as [Hms0 [Hsent | Hmslt]].
  - subst ms. vm_compute in Hsplitpos. exfalso. discriminate Hsplitpos.
  - assert (Hcritical : critical_split ns
      (unsigned_last_nbits (ms+1) 64) (unsigned_last_nbits (ms+1) 64)).
    { apply (proj1 (factorization_done_cut_search_split ns
        (unsigned_last_nbits (ms+1) 64) p
        ltac:(let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia) ltac:(eassumption) Hsplitpos)). }

    pose proof (proj2 Hcfsearch) as Hminimal.
    assert (Hsearch : critical_search_split ns
      (unsigned_last_nbits (ms + 1) 64) (unsigned_last_nbits (ms + 1) 64))
      by (split; assumption).
    prop_apply_p (strstr_array_length64__cut_probe h_pre hs).
    Intros_p Hlenhs.
    Exists sh_2 bs_2 0 0.
    split_pure_spatial.
    + cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
      cancel (UInt64Array.full &( "byteset" ) 4 bs_2).
      cancel (UInt64Array.full &( "shift" ) 256 sh_2).
      repeat rewrite Zsublist_nil by lia.
      rewrite sublist_self by reflexivity.
      repeat rewrite UCharArray.full_empty.
      entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [apply Hcursor | rewrite PreH7; exact Hcursor | rewrite <- Hsplit_eq; apply Hcursor |
        rewrite unsigned_last_nbits_eq by (cbn; lia); rewrite PreH7; exact Hcursor].
      all: try (unfold no_match_before; intros; lia).
      all: try (unfold strstr_rel_lib.matched_range; intros; lia).
      all: try (rewrite sublist_self by reflexivity; assumption).
      all: try (unfold periodic_memory_state; repeat split;
        try (left; reflexivity); intros; contradiction).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_10_4 : twoway_strstr_entail_wit_10_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hne : ns <> nil) by (intro He; assert (Hp : 0 < Zlength ns) by lia; rewrite He, Zlength_nil in Hp; lia).
  pose proof (factorization_safeExec_done ns (unsigned_last_nbits (ms+1) 64) p PreH6) as Hfactor.
  destruct (factorization_safeExec_bounds ns (unsigned_last_nbits (ms+1) 64) p Hne PreH6)
    as [Hsplitbound [Hpbound Hperiodbound]].
  assert (Hcfsearch : critical_search_split ns
    (unsigned_last_nbits (ms+1) 64) p).
  { eapply factorization_done_search_split.
    - let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia.
    - eassumption. }
  assert (Hoff : off = p) by (rewrite sizeof_uchar in PreH2; lia).
  assert (Hsplitpos : 0 < unsigned_last_nbits (ms + 1) 64).
  { eapply memcmp_nonzero_count_positive; eauto. }
  assert (Hnonrep :
    sublist 0 (unsigned_last_nbits (ms + 1) 64) ns <>
    sublist p (unsigned_last_nbits (ms + 1) 64 + p) ns).
  { rewrite Hoff in PreH5.
    eapply memcmp_nonzero_needle_nonrep; eauto; lia. }
  assert (Hcursor : forall actual_p, search_cursor hs ns
    (unsigned_last_nbits (ms+1) 64) actual_p 0 0 0).
  { intros actual_p. eapply search_cursor_init_nonperiodic; eauto. }
  assert (Hcritical : critical_split ns (unsigned_last_nbits (ms + 1) 64)
    (Z.max (unsigned_last_nbits (ms + 1) 64)
      (Zlength ns - unsigned_last_nbits (ms + 1) 64) + 1)).
  { apply (proj1 (factorization_done_nonrep_search_split ns
      (unsigned_last_nbits (ms+1) 64) p
      ltac:(let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia) ltac:(eassumption) Hnonrep)). }
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns).
  Intros_p Hlenns.
  prop_apply_p (strstr_array_length64__cut_probe h_pre hs).
  Intros_p Hlenhs.
  assert (Hmsrange : 0 <= ms < l).
  { unfold maxsuf_cut_index64 in PreH21.
    destruct PreH21 as [Hms0 [Hsent | Hmslt]]; [|lia].
    subst ms. vm_compute in Hsplitpos.
    exfalso. discriminate Hsplitpos. }
  assert (Hsplit_eq : unsigned_last_nbits (ms + 1) 64 = ms + 1).
  { unfold unsigned_last_nbits.
    rewrite Z.mod_small; [reflexivity |].
    change (2 ^ 64) with 18446744073709551616.
    lia. }
  assert (Hshift_eq :
    unsigned_last_nbits
      (unsigned_last_nbits (unsigned_last_nbits (l - ms) 64 - 1) 64 + 1) 64
    = l - ms).
  { apply nonperiodic_small_branch_shift64. lia. }
  assert (Hcritical_small : critical_split ns (ms + 1) (l - ms)).
  { rewrite Hsplit_eq in Hcritical.
    eapply critical_split_weaken_shift; [exact Hcritical |].
    rewrite <- PreH8. lia. }

  pose proof (proj2 Hcfsearch) as Hminimal.
  rewrite Hsplit_eq in Hminimal.
  assert (Hsearch_small : critical_search_split ns (ms + 1) (l - ms))
    by (split; assumption).
  Left.
  Exists sh_2 bs_2 0 0.
  split_pure_spatial.
  - cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
    cancel (UInt64Array.full &( "byteset" ) 4 bs_2).
    cancel (UInt64Array.full &( "shift" ) 256 sh_2).
    repeat rewrite Zsublist_nil by lia.
    rewrite sublist_self by reflexivity.
    repeat rewrite UCharArray.full_empty.
    entailer!.
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [apply Hcursor | rewrite PreH7; exact Hcursor | rewrite <- Hsplit_eq; apply Hcursor |
        rewrite unsigned_last_nbits_eq by (cbn; lia); rewrite PreH7; exact Hcursor].
    all: try (rewrite Hshift_eq; lia).
    all: try (rewrite Hsplit_eq, Hshift_eq; exact Hsearch_small).
    all: try (rewrite Hsplit_eq, Hshift_eq; exact Hcritical_small).
    all: try (unfold no_match_before; intros; lia).
    all: try (unfold strstr_rel_lib.matched_range; intros; lia).
    all: try (rewrite sublist_self by reflexivity; assumption).
    all: try (unfold periodic_memory_state; repeat split;
      try (left; reflexivity); intros; contradiction).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_10_5 : twoway_strstr_entail_wit_10_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hne : ns <> nil) by (intro He; assert (Hp : 0 < Zlength ns) by lia; rewrite He, Zlength_nil in Hp; lia).
  pose proof (factorization_safeExec_done ns (unsigned_last_nbits (ms+1) 64) p PreH5) as Hfactor.
  destruct (factorization_safeExec_bounds ns (unsigned_last_nbits (ms+1) 64) p Hne PreH5)
    as [Hsplitbound [Hpbound Hperiodbound]].
  assert (Hcfsearch : critical_search_split ns
    (unsigned_last_nbits (ms+1) 64) p).
  { eapply factorization_done_search_split.
    - let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia.
    - eassumption. }
  assert (Hoff : off = p) by (rewrite sizeof_uchar in PreH1; lia).
  subst off.
  unfold memcmp_zero in PreH4.
  destruct PreH4 as [_ Hcmp].
  pose proof (proj1 Hcfsearch) as Hcritical.

  pose proof (proj2 Hcfsearch) as Hminimal.
  assert (Hsearch : critical_search_split ns
    (unsigned_last_nbits (ms + 1) 64) p) by (split; assumption).
  assert (Hrep : SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.repetitive_split ns (unsigned_last_nbits (ms+1) 64) p).
  { pose proof (proj1 Hcmp PreH27) as Hcmp0.
    rewrite !sublist_split_app_l in Hcmp0 by lia.
    unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.repetitive_split.
    replace (unsigned_last_nbits (ms+1) 64+p) with
      (p+unsigned_last_nbits (ms+1) 64) by lia. exact Hcmp0. }
  assert (Hperiod : string_period ns p).
  { eapply SimpleC.EE.stdlib.musl.monad.two_way_match.repetitive_split_period.
    - exact Hne.
    - exact (proj1 (factorization_done_match_sound _ _ _ Hne Hfactor)).
    - exact Hrep. }
  pose proof (search_cursor_init_periodic hs ns
    (unsigned_last_nbits (ms+1) 64) p ltac:(eassumption) Hrep) as Hcursor.
  prop_apply_p (strstr_array_length64__cut_probe h_pre hs).
  Intros_p Hlenhs.
  unfold maxsuf_cut_index64 in PreH20.
  destruct PreH20 as [Hms0 [Hsent | Hmslt]].
  - Right. Exists sh_2 bs_2 0 0. split_pure_spatial.
    + cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
      cancel (UInt64Array.full &( "byteset" ) 4 bs_2).
      cancel (UInt64Array.full &( "shift" ) 256 sh_2).
      repeat rewrite Zsublist_nil by lia.
      rewrite sublist_self by reflexivity.
      repeat rewrite UCharArray.full_empty. entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [apply Hcursor | rewrite PreH7; exact Hcursor | rewrite <- Hsplit_eq; apply Hcursor |
        rewrite unsigned_last_nbits_eq by (cbn; lia); rewrite PreH7; exact Hcursor].
      all: try (unfold no_match_before; intros; lia).
      all: try (unfold strstr_rel_lib.matched_range; intros; lia).
      all: try (rewrite sublist_self by reflexivity; assumption).
      all: try (unfold periodic_memory_state; repeat split).
      all: first [left; reflexivity | right; lia |
                  exact (proj1 Hperiod) | exact (proj2 Hperiod)].
  - Left. Exists sh_2 bs_2 0 0. split_pure_spatial.
    + cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
      cancel (UInt64Array.full &( "byteset" ) 4 bs_2).
      cancel (UInt64Array.full &( "shift" ) 256 sh_2).
      repeat rewrite Zsublist_nil by lia.
      rewrite sublist_self by reflexivity.
      repeat rewrite UCharArray.full_empty. entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [apply Hcursor | rewrite PreH7; exact Hcursor | rewrite <- Hsplit_eq; apply Hcursor |
        rewrite unsigned_last_nbits_eq by (cbn; lia); rewrite PreH7; exact Hcursor].
      all: try (unfold no_match_before; intros; lia).
      all: try (unfold strstr_rel_lib.matched_range; intros; lia).
      all: try (rewrite sublist_self by reflexivity; assumption).
      all: try (unfold periodic_memory_state; repeat split).
      all: first [left; reflexivity | right; lia |
                  exact (proj1 Hperiod) | exact (proj2 Hperiod)].
Qed.


Lemma proof_of_twoway_strstr_entail_wit_10_6 : twoway_strstr_entail_wit_10_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hne : ns <> nil) by (intro He; assert (Hp : 0 < Zlength ns) by lia; rewrite He, Zlength_nil in Hp; lia).
  pose proof (factorization_safeExec_done ns (unsigned_last_nbits (ms+1) 64) p PreH5) as Hfactor.
  destruct (factorization_safeExec_bounds ns (unsigned_last_nbits (ms+1) 64) p Hne PreH5)
    as [Hsplitbound [Hpbound Hperiodbound]].
  assert (Hcfsearch : critical_search_split ns
    (unsigned_last_nbits (ms+1) 64) p).
  { eapply factorization_done_search_split.
    - let Hnil := fresh "Hnil" in let Hpositive := fresh "Hpositive" in intro Hnil; assert (Hpositive : 0 < Zlength ns) by lia; rewrite Hnil, Zlength_nil in Hpositive; lia.
    - eassumption. }
  assert (Hoff : off = p) by (rewrite sizeof_uchar in PreH1; lia).
  subst off.
  unfold memcmp_zero in PreH4.
  destruct PreH4 as [_ Hcmp].
  pose proof (proj1 Hcfsearch) as Hcritical.

  pose proof (proj2 Hcfsearch) as Hminimal.
  assert (Hsearch : critical_search_split ns
    (unsigned_last_nbits (ms + 1) 64) p) by (split; assumption).
  assert (Hrep : SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.repetitive_split ns (unsigned_last_nbits (ms+1) 64) p).
  { pose proof (proj1 Hcmp PreH27) as Hcmp0.
    rewrite !sublist_split_app_l in Hcmp0 by lia.
    unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.repetitive_split.
    replace (unsigned_last_nbits (ms+1) 64+p) with
      (p+unsigned_last_nbits (ms+1) 64) by lia. exact Hcmp0. }
  assert (Hperiod : string_period ns p).
  { eapply SimpleC.EE.stdlib.musl.monad.two_way_match.repetitive_split_period.
    - exact Hne.
    - exact (proj1 (factorization_done_match_sound _ _ _ Hne Hfactor)).
    - exact Hrep. }
  pose proof (search_cursor_init_periodic hs ns
    (unsigned_last_nbits (ms+1) 64) p ltac:(eassumption) Hrep) as Hcursor.
  prop_apply_p (strstr_array_length64__cut_probe h_pre hs).
  Intros_p Hlenhs.
  unfold maxsuf_cut_index64 in PreH20.
  destruct PreH20 as [Hms0 [Hsent | Hmslt]].
  - Right. Exists sh_2 bs_2 0 0. split_pure_spatial.
    + cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
      cancel (UInt64Array.full &( "byteset" ) 4 bs_2).
      cancel (UInt64Array.full &( "shift" ) 256 sh_2).
      repeat rewrite Zsublist_nil by lia.
      rewrite sublist_self by reflexivity.
      repeat rewrite UCharArray.full_empty. entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [apply Hcursor | rewrite PreH7; exact Hcursor | rewrite <- Hsplit_eq; apply Hcursor |
        rewrite unsigned_last_nbits_eq by (cbn; lia); rewrite PreH7; exact Hcursor].
      all: try (unfold no_match_before; intros; lia).
      all: try (unfold strstr_rel_lib.matched_range; intros; lia).
      all: try (rewrite sublist_self by reflexivity; assumption).
      all: try (unfold periodic_memory_state; repeat split).
      all: first [left; reflexivity | right; lia |
                  exact (proj1 Hperiod) | exact (proj2 Hperiod)].
  - Left. Exists sh_2 bs_2 0 0. split_pure_spatial.
    + cancel (UCharArray.full n_pre (Zlength ns + 1) (ns ++ [0])).
      cancel (UInt64Array.full &( "byteset" ) 4 bs_2).
      cancel (UInt64Array.full &( "shift" ) 256 sh_2).
      repeat rewrite Zsublist_nil by lia.
      rewrite sublist_self by reflexivity.
      repeat rewrite UCharArray.full_empty. entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [apply Hcursor | rewrite PreH7; exact Hcursor | rewrite <- Hsplit_eq; apply Hcursor |
        rewrite unsigned_last_nbits_eq by (cbn; lia); rewrite PreH7; exact Hcursor].
      all: try (unfold no_match_before; intros; lia).
      all: try (unfold strstr_rel_lib.matched_range; intros; lia).
      all: try (rewrite sublist_self by reflexivity; assumption).
      all: try (unfold periodic_memory_state; repeat split).
      all: first [left; reflexivity | right; lia |
                  exact (proj1 Hperiod) | exact (proj2 Hperiod)].
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_1 : twoway_strstr_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold memchr_zero_result in PreH2.
  destruct PreH2 as [[Hshort [Hret Hnonnull]] | [Hcount Hzero]].
  2: contradiction.
  rewrite sizeof_uchar in PreH1, PreH3, PreH4, PreH5.
  rewrite !Z.quot_1_r in PreH1, PreH3.
  assert (Hsuflen : Zlength (sublist end__2 (Zlength hs) hs) =
      Zlength hs - end__2).
  { rewrite Zlength_sublist; lia. }
  assert (Hretval : retval = h_pre + Zlength hs).
  { rewrite Hret, PreH5, Hsuflen. lia. }
  assert (Hoff : unsigned_last_nbits (retval - h) 64 =
      Zlength hs - pos_2).
  { rewrite Hretval, PreH4.
    unfold unsigned_last_nbits.
    rewrite Z.mod_small; lia. }
  assert (Hroom : l <= Zlength hs - pos_2) by (rewrite Hoff in PreH1; lia).
  assert (Hbyte : 0 <= Znth (l - 1) (sublist pos_2 (Zlength hs) hs) 0 < 256).
  { rewrite Znth_sublist by lia.
    apply nonzero_nth_bound__proof_of_threebyte_2; try assumption; lia. }
  Exists sh_2 bs_2 (Zlength hs) pos_2.
  split_pure_spatial.
  - rewrite PreH4, PreH5, Hretval, Hsuflen.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + end__2 * 1) with
      (h_pre + pos_2 + (end__2 - pos_2) * sizeof(UCHAR))
      by (rewrite sizeof_uchar; lia).
    replace (Zlength hs - end__2 + 1) with
      (Zlength hs + 1 - pos_2 - (end__2 - pos_2)) by lia.
    sep_apply (UCharArray.full_merge_to_full
      (h_pre + pos_2) (end__2 - pos_2) (Zlength hs + 1 - pos_2)
      (sublist pos_2 end__2 hs)
      (sublist end__2 (Zlength hs) hs ++ [0])).
    replace (sublist pos_2 end__2 hs ++
        (sublist end__2 (Zlength hs) hs ++ [0]))
      with (sublist pos_2 (Zlength hs) hs ++ [0]).
    2:{ rewrite app_assoc.
        rewrite <- (sublist_split pos_2 (Zlength hs) end__2 hs) by lia.
        reflexivity. }
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) (Zlength hs - pos_2)
      (Zlength hs + 1 - pos_2)
      (sublist pos_2 (Zlength hs) hs ++ [0])).
    assert (Htaillen : Zlength (sublist pos_2 (Zlength hs) hs) =
        Zlength hs - pos_2) by (rewrite Zlength_sublist; lia).
    rewrite <- Htaillen.
    rewrite sublist_app_exact1.
    rewrite sublist_split_app_r with
      (len := Zlength (sublist pos_2 (Zlength hs) hs)) by lia.
    replace (Zlength (sublist pos_2 (Zlength hs) hs) -
        Zlength (sublist pos_2 (Zlength hs) hs)) with 0 by lia.
    replace (Zlength hs + 1 - pos_2 -
        Zlength (sublist pos_2 (Zlength hs) hs)) with 1 by lia.
    rewrite sublist_cons1 by lia.
    replace (1 - 1) with 0 by lia.
    rewrite (Zsublist_nil [] 0 0) by lia.
    rewrite (Zsublist_nil hs (Zlength hs) (Zlength hs)) by lia.
    rewrite Zlength_sublist by lia.
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 + (Zlength hs - pos_2) * 1) with
      (h_pre + Zlength hs) by lia.
    cbn.
    cancel.
    all: try entailer!.
    all: repeat rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_sublist;
      try lia.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
      try (apply Z.quot_pos; lia);
      try (apply Z.quot_lt_upper_bound; lia);
      try (unfold nonzero_bytes; rewrite Zsublist_nil by lia; constructor).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_2 : twoway_strstr_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold memchr_zero_result in PreH2.
  destruct PreH2 as [[Hshort [Hret Hnonnull]] | [Hcount Hzero]].
  2: contradiction.
  rewrite sizeof_uchar in PreH1, PreH3, PreH4, PreH5.
  rewrite !Z.quot_1_r in PreH1, PreH3.
  assert (Hsuflen : Zlength (sublist end__2 (Zlength hs) hs) =
      Zlength hs - end__2).
  { rewrite Zlength_sublist; lia. }
  assert (Hretval : retval = h_pre + Zlength hs).
  { rewrite Hret, PreH5, Hsuflen. lia. }
  assert (Hoff : unsigned_last_nbits (retval - h) 64 =
      Zlength hs - pos_2).
  { rewrite Hretval, PreH4.
    unfold unsigned_last_nbits.
    rewrite Z.mod_small; lia. }
  assert (Hroom : l <= Zlength hs - pos_2) by (rewrite Hoff in PreH1; lia).
  assert (Hbyte : 0 <= Znth (l - 1) (sublist pos_2 (Zlength hs) hs) 0 < 256).
  { rewrite Znth_sublist by lia.
    apply nonzero_nth_bound__proof_of_threebyte_2; try assumption; lia. }
  Exists sh_2 bs_2 (Zlength hs) pos_2.
  split_pure_spatial.
  - rewrite PreH4, PreH5, Hretval, Hsuflen.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + end__2 * 1) with
      (h_pre + pos_2 + (end__2 - pos_2) * sizeof(UCHAR))
      by (rewrite sizeof_uchar; lia).
    replace (Zlength hs - end__2 + 1) with
      (Zlength hs + 1 - pos_2 - (end__2 - pos_2)) by lia.
    sep_apply (UCharArray.full_merge_to_full
      (h_pre + pos_2) (end__2 - pos_2) (Zlength hs + 1 - pos_2)
      (sublist pos_2 end__2 hs)
      (sublist end__2 (Zlength hs) hs ++ [0])).
    replace (sublist pos_2 end__2 hs ++
        (sublist end__2 (Zlength hs) hs ++ [0]))
      with (sublist pos_2 (Zlength hs) hs ++ [0]).
    2:{ rewrite app_assoc.
        rewrite <- (sublist_split pos_2 (Zlength hs) end__2 hs) by lia.
        reflexivity. }
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) (Zlength hs - pos_2)
      (Zlength hs + 1 - pos_2)
      (sublist pos_2 (Zlength hs) hs ++ [0])).
    assert (Htaillen : Zlength (sublist pos_2 (Zlength hs) hs) =
        Zlength hs - pos_2) by (rewrite Zlength_sublist; lia).
    rewrite <- Htaillen.
    rewrite sublist_app_exact1.
    rewrite sublist_split_app_r with
      (len := Zlength (sublist pos_2 (Zlength hs) hs)) by lia.
    replace (Zlength (sublist pos_2 (Zlength hs) hs) -
        Zlength (sublist pos_2 (Zlength hs) hs)) with 0 by lia.
    replace (Zlength hs + 1 - pos_2 -
        Zlength (sublist pos_2 (Zlength hs) hs)) with 1 by lia.
    rewrite sublist_cons1 by lia.
    replace (1 - 1) with 0 by lia.
    rewrite (Zsublist_nil [] 0 0) by lia.
    rewrite (Zsublist_nil hs (Zlength hs) (Zlength hs)) by lia.
    rewrite Zlength_sublist by lia.
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 + (Zlength hs - pos_2) * 1) with
      (h_pre + Zlength hs) by lia.
    cbn.
    cancel.
    all: try entailer!.
    all: repeat rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_sublist;
      try lia.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
      try (apply Z.quot_pos; lia);
      try (apply Z.quot_lt_upper_bound; lia);
      try (unfold nonzero_bytes; rewrite Zsublist_nil by lia; constructor).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_3 : twoway_strstr_entail_wit_11_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold memchr_zero_result in PreH2.
  destruct PreH2 as [[Hshort [Hret Hnonnull]] | [Hcount Hzero]].
  2: contradiction.
  rewrite sizeof_uchar in PreH1, PreH3, PreH4, PreH5.
  rewrite !Z.quot_1_r in PreH1, PreH3.
  assert (Hsuflen : Zlength (sublist end__2 (Zlength hs) hs) =
      Zlength hs - end__2).
  { rewrite Zlength_sublist; lia. }
  assert (Hretval : retval = h_pre + Zlength hs).
  { rewrite Hret, PreH5, Hsuflen. lia. }
  assert (Hoff : unsigned_last_nbits (retval - h) 64 =
      Zlength hs - pos_2).
  { rewrite Hretval, PreH4.
    unfold unsigned_last_nbits.
    rewrite Z.mod_small; lia. }
  assert (Hroom : l <= Zlength hs - pos_2) by (rewrite Hoff in PreH1; lia).
  assert (Hbyte : 0 <= Znth (l - 1) (sublist pos_2 (Zlength hs) hs) 0 < 256).
  { rewrite Znth_sublist by lia.
    apply nonzero_nth_bound__proof_of_threebyte_2; try assumption; lia. }
  Exists sh_2 bs_2 (Zlength hs) pos_2.
  split_pure_spatial.
  - rewrite PreH4, PreH5, Hretval, Hsuflen.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + end__2 * 1) with
      (h_pre + pos_2 + (end__2 - pos_2) * sizeof(UCHAR))
      by (rewrite sizeof_uchar; lia).
    replace (Zlength hs - end__2 + 1) with
      (Zlength hs + 1 - pos_2 - (end__2 - pos_2)) by lia.
    sep_apply (UCharArray.full_merge_to_full
      (h_pre + pos_2) (end__2 - pos_2) (Zlength hs + 1 - pos_2)
      (sublist pos_2 end__2 hs)
      (sublist end__2 (Zlength hs) hs ++ [0])).
    replace (sublist pos_2 end__2 hs ++
        (sublist end__2 (Zlength hs) hs ++ [0]))
      with (sublist pos_2 (Zlength hs) hs ++ [0]).
    2:{ rewrite app_assoc.
        rewrite <- (sublist_split pos_2 (Zlength hs) end__2 hs) by lia.
        reflexivity. }
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) (Zlength hs - pos_2)
      (Zlength hs + 1 - pos_2)
      (sublist pos_2 (Zlength hs) hs ++ [0])).
    assert (Htaillen : Zlength (sublist pos_2 (Zlength hs) hs) =
        Zlength hs - pos_2) by (rewrite Zlength_sublist; lia).
    rewrite <- Htaillen.
    rewrite sublist_app_exact1.
    rewrite sublist_split_app_r with
      (len := Zlength (sublist pos_2 (Zlength hs) hs)) by lia.
    replace (Zlength (sublist pos_2 (Zlength hs) hs) -
        Zlength (sublist pos_2 (Zlength hs) hs)) with 0 by lia.
    replace (Zlength hs + 1 - pos_2 -
        Zlength (sublist pos_2 (Zlength hs) hs)) with 1 by lia.
    rewrite sublist_cons1 by lia.
    replace (1 - 1) with 0 by lia.
    rewrite (Zsublist_nil [] 0 0) by lia.
    rewrite (Zsublist_nil hs (Zlength hs) (Zlength hs)) by lia.
    rewrite Zlength_sublist by lia.
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 + (Zlength hs - pos_2) * 1) with
      (h_pre + Zlength hs) by lia.
    cbn.
    cancel.
    all: try entailer!.
    all: repeat rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_sublist;
      try lia.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
      try (apply Z.quot_pos; lia);
      try (apply Z.quot_lt_upper_bound; lia);
      try (unfold nonzero_bytes; rewrite Zsublist_nil by lia; constructor).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_4 : twoway_strstr_entail_wit_11_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold memchr_zero_result in PreH2.
  destruct PreH2 as [[Hshort [Hret Hnonnull]] | [Hcount Hzero]].
  2: contradiction.
  rewrite sizeof_uchar in PreH1, PreH3, PreH4, PreH5.
  rewrite !Z.quot_1_r in PreH1, PreH3.
  assert (Hsuflen : Zlength (sublist end__2 (Zlength hs) hs) =
      Zlength hs - end__2).
  { rewrite Zlength_sublist; lia. }
  assert (Hretval : retval = h_pre + Zlength hs).
  { rewrite Hret, PreH5, Hsuflen. lia. }
  assert (Hoff : unsigned_last_nbits (retval - h) 64 =
      Zlength hs - pos_2).
  { rewrite Hretval, PreH4.
    unfold unsigned_last_nbits.
    rewrite Z.mod_small; lia. }
  assert (Hroom : l <= Zlength hs - pos_2) by (rewrite Hoff in PreH1; lia).
  assert (Hbyte : 0 <= Znth (l - 1) (sublist pos_2 (Zlength hs) hs) 0 < 256).
  { rewrite Znth_sublist by lia.
    apply nonzero_nth_bound__proof_of_threebyte_2; try assumption; lia. }
  Exists sh_2 bs_2 (Zlength hs) pos_2.
  split_pure_spatial.
  - rewrite PreH4, PreH5, Hretval, Hsuflen.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + end__2 * 1) with
      (h_pre + pos_2 + (end__2 - pos_2) * sizeof(UCHAR))
      by (rewrite sizeof_uchar; lia).
    replace (Zlength hs - end__2 + 1) with
      (Zlength hs + 1 - pos_2 - (end__2 - pos_2)) by lia.
    sep_apply (UCharArray.full_merge_to_full
      (h_pre + pos_2) (end__2 - pos_2) (Zlength hs + 1 - pos_2)
      (sublist pos_2 end__2 hs)
      (sublist end__2 (Zlength hs) hs ++ [0])).
    replace (sublist pos_2 end__2 hs ++
        (sublist end__2 (Zlength hs) hs ++ [0]))
      with (sublist pos_2 (Zlength hs) hs ++ [0]).
    2:{ rewrite app_assoc.
        rewrite <- (sublist_split pos_2 (Zlength hs) end__2 hs) by lia.
        reflexivity. }
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) (Zlength hs - pos_2)
      (Zlength hs + 1 - pos_2)
      (sublist pos_2 (Zlength hs) hs ++ [0])).
    assert (Htaillen : Zlength (sublist pos_2 (Zlength hs) hs) =
        Zlength hs - pos_2) by (rewrite Zlength_sublist; lia).
    rewrite <- Htaillen.
    rewrite sublist_app_exact1.
    rewrite sublist_split_app_r with
      (len := Zlength (sublist pos_2 (Zlength hs) hs)) by lia.
    replace (Zlength (sublist pos_2 (Zlength hs) hs) -
        Zlength (sublist pos_2 (Zlength hs) hs)) with 0 by lia.
    replace (Zlength hs + 1 - pos_2 -
        Zlength (sublist pos_2 (Zlength hs) hs)) with 1 by lia.
    rewrite sublist_cons1 by lia.
    replace (1 - 1) with 0 by lia.
    rewrite (Zsublist_nil [] 0 0) by lia.
    rewrite (Zsublist_nil hs (Zlength hs) (Zlength hs)) by lia.
    rewrite Zlength_sublist by lia.
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 + (Zlength hs - pos_2) * 1) with
      (h_pre + Zlength hs) by lia.
    cbn.
    cancel.
    all: try entailer!.
    all: repeat rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_sublist;
      try lia.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
      try (apply Z.quot_pos; lia);
      try (apply Z.quot_lt_upper_bound; lia);
      try (unfold nonzero_bytes; rewrite Zsublist_nil by lia; constructor).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_5 : twoway_strstr_entail_wit_11_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold memchr_zero_result in PreH1.
  destruct PreH1 as [[Hshort [Hret Hnonnull]] | [Hcount Hret]].
  - contradiction.
  - rewrite sizeof_uchar in PreH2, PreH3, PreH4.
    rewrite !Z.quot_1_r in PreH2.
    set (q := Z.lor l 63).
    assert (Hqnonneg : 0 <= q).
    { unfold q. apply Z.lor_nonneg. split; lia. }
    assert (Hql : l <= q).
    { unfold q.
      pose proof (Z.add_lor_land l 63).
      assert (Hland : Z.land l 63 = l mod 64).
      { change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia. reflexivity. }
      pose proof (Z.mod_pos_bound l 64 ltac:(lia)).
      lia. }
    assert (Hsuflen : Zlength (sublist end__2 (Zlength hs) hs) =
        Zlength hs - end__2) by (rewrite Zlength_sublist; lia).
    assert (Hend : end__2 + q <= Zlength hs) by (rewrite Hsuflen in Hcount; lia).
    assert (Hoff : unsigned_last_nbits (z - h) 64 = end__2 - pos_2).
    { rewrite PreH3, PreH4.
      unfold unsigned_last_nbits.
      rewrite Z.mod_small; lia. }
    assert (Hroom : l <= end__2 + q - pos_2) by lia.
    assert (Hbyte : 0 <= Znth (l - 1)
        (sublist pos_2 (end__2 + q) hs) 0 < 256).
    { rewrite Znth_sublist by lia.
      apply nonzero_nth_bound__proof_of_threebyte_2; try assumption; lia. }
    assert (Hnonzero_tail :
        nonzero_bytes (sublist (end__2 + q) (Zlength hs) hs)).
    { unfold nonzero_bytes in *.
      unfold sublist.
      apply Forall_skipn_local.
      apply Forall_firstn_local.
      exact PreH14. }
    Exists sh_2 bs_2 (end__2 + q) pos_2.
    split_pure_spatial.
    + rewrite PreH3, PreH4.
      rewrite sizeof_uchar.
      rewrite Hsuflen.
      replace (h_pre + end__2 * 1) with (h_pre + end__2) by lia.
      replace (Zlength hs - end__2 + 1) with
        (Zlength hs + 1 - end__2) by lia.
      replace (h_pre + end__2 + q) with
        (h_pre + end__2 + q * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
      sep_apply (UCharArray.full_split_to_full
        (h_pre + end__2) q (Zlength hs + 1 - end__2)
        (sublist end__2 (Zlength hs) hs ++ [0])).
      assert (Hprefix :
        sublist 0 q (sublist end__2 (Zlength hs) hs ++ [0]) =
        sublist end__2 (end__2 + q) hs).
      { rewrite sublist_split_app_l by (try rewrite Zlength_sublist; lia).
        rewrite Zsublist_Zsublist by lia.
        f_equal; lia. }
      assert (Hsuffix :
        sublist q (Zlength hs + 1 - end__2)
          (sublist end__2 (Zlength hs) hs ++ [0]) =
        sublist (end__2 + q) (Zlength hs) hs ++ [0]).
      { rewrite (sublist_split q (Zlength hs + 1 - end__2)
          (Zlength hs - end__2)) by
          (repeat rewrite Zlength_app, Zlength_cons, Zlength_nil,
            Zlength_sublist; lia).
        rewrite sublist_split_app_l by (try rewrite Zlength_sublist; lia).
        rewrite Zsublist_Zsublist by lia.
        rewrite sublist_split_app_r with
          (len := Zlength hs - end__2).
        2: rewrite Zlength_sublist; lia.
        2: lia.
        replace (Zlength hs - end__2 - (Zlength hs - end__2)) with 0 by lia.
        replace (Zlength hs + 1 - end__2 - (Zlength hs - end__2)) with 1 by lia.
        replace (q + end__2) with (end__2 + q) by lia.
        replace (Zlength hs - end__2 + end__2) with (Zlength hs) by lia.
        rewrite sublist_cons1 by lia.
        replace (1 - 1) with 0 by lia.
        cbn [sublist].
        reflexivity. }
      rewrite Hprefix, Hsuffix.
      replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
      replace (h_pre + end__2) with
        (h_pre + pos_2 + (end__2 - pos_2) * sizeof(UCHAR))
        by (rewrite sizeof_uchar; lia).
      replace q with
        (end__2 + q - pos_2 - (end__2 - pos_2)) at 1 by lia.
      sep_apply (UCharArray.full_merge_to_full
        (h_pre + pos_2) (end__2 - pos_2) (end__2 + q - pos_2)
        (sublist pos_2 end__2 hs)
        (sublist end__2 (end__2 + q) hs)).
      replace (sublist pos_2 end__2 hs ++ sublist end__2 (end__2 + q) hs)
        with (sublist pos_2 (end__2 + q) hs).
      2:{ rewrite <- sublist_split by lia. reflexivity. }
      rewrite sizeof_uchar.
      rewrite Zlength_sublist by lia.
      replace (Zlength hs + 1 - end__2 - q) with
        (Zlength hs - (end__2 + q) + 1) by lia.
      cancel.
      all: try entailer!.
    + split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
        try (apply Z.quot_pos; lia);
        try (apply Z.quot_lt_upper_bound; lia);
        try assumption.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_6 : twoway_strstr_entail_wit_11_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold memchr_zero_result in PreH1.
  destruct PreH1 as [[Hshort [Hret Hnonnull]] | [Hcount Hret]].
  - contradiction.
  - rewrite sizeof_uchar in PreH2, PreH3, PreH4.
    rewrite !Z.quot_1_r in PreH2.
    set (q := Z.lor l 63).
    assert (Hqnonneg : 0 <= q).
    { unfold q. apply Z.lor_nonneg. split; lia. }
    assert (Hql : l <= q).
    { unfold q.
      pose proof (Z.add_lor_land l 63).
      assert (Hland : Z.land l 63 = l mod 64).
      { change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia. reflexivity. }
      pose proof (Z.mod_pos_bound l 64 ltac:(lia)).
      lia. }
    assert (Hsuflen : Zlength (sublist end__2 (Zlength hs) hs) =
        Zlength hs - end__2) by (rewrite Zlength_sublist; lia).
    assert (Hend : end__2 + q <= Zlength hs) by (rewrite Hsuflen in Hcount; lia).
    assert (Hoff : unsigned_last_nbits (z - h) 64 = end__2 - pos_2).
    { rewrite PreH3, PreH4.
      unfold unsigned_last_nbits.
      rewrite Z.mod_small; lia. }
    assert (Hroom : l <= end__2 + q - pos_2) by lia.
    assert (Hbyte : 0 <= Znth (l - 1)
        (sublist pos_2 (end__2 + q) hs) 0 < 256).
    { rewrite Znth_sublist by lia.
      apply nonzero_nth_bound__proof_of_threebyte_2; try assumption; lia. }
    assert (Hnonzero_tail :
        nonzero_bytes (sublist (end__2 + q) (Zlength hs) hs)).
    { unfold nonzero_bytes in *.
      unfold sublist.
      apply Forall_skipn_local.
      apply Forall_firstn_local.
      exact PreH14. }
    Exists sh_2 bs_2 (end__2 + q) pos_2.
    split_pure_spatial.
    + rewrite PreH3, PreH4.
      rewrite sizeof_uchar.
      rewrite Hsuflen.
      replace (h_pre + end__2 * 1) with (h_pre + end__2) by lia.
      replace (Zlength hs - end__2 + 1) with
        (Zlength hs + 1 - end__2) by lia.
      replace (h_pre + end__2 + q) with
        (h_pre + end__2 + q * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
      sep_apply (UCharArray.full_split_to_full
        (h_pre + end__2) q (Zlength hs + 1 - end__2)
        (sublist end__2 (Zlength hs) hs ++ [0])).
      assert (Hprefix :
        sublist 0 q (sublist end__2 (Zlength hs) hs ++ [0]) =
        sublist end__2 (end__2 + q) hs).
      { rewrite sublist_split_app_l by (try rewrite Zlength_sublist; lia).
        rewrite Zsublist_Zsublist by lia.
        f_equal; lia. }
      assert (Hsuffix :
        sublist q (Zlength hs + 1 - end__2)
          (sublist end__2 (Zlength hs) hs ++ [0]) =
        sublist (end__2 + q) (Zlength hs) hs ++ [0]).
      { rewrite (sublist_split q (Zlength hs + 1 - end__2)
          (Zlength hs - end__2)) by
          (repeat rewrite Zlength_app, Zlength_cons, Zlength_nil,
            Zlength_sublist; lia).
        rewrite sublist_split_app_l by (try rewrite Zlength_sublist; lia).
        rewrite Zsublist_Zsublist by lia.
        rewrite sublist_split_app_r with
          (len := Zlength hs - end__2).
        2: rewrite Zlength_sublist; lia.
        2: lia.
        replace (Zlength hs - end__2 - (Zlength hs - end__2)) with 0 by lia.
        replace (Zlength hs + 1 - end__2 - (Zlength hs - end__2)) with 1 by lia.
        replace (q + end__2) with (end__2 + q) by lia.
        replace (Zlength hs - end__2 + end__2) with (Zlength hs) by lia.
        rewrite sublist_cons1 by lia.
        replace (1 - 1) with 0 by lia.
        cbn [sublist].
        reflexivity. }
      rewrite Hprefix, Hsuffix.
      replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
      replace (h_pre + end__2) with
        (h_pre + pos_2 + (end__2 - pos_2) * sizeof(UCHAR))
        by (rewrite sizeof_uchar; lia).
      replace q with
        (end__2 + q - pos_2 - (end__2 - pos_2)) at 1 by lia.
      sep_apply (UCharArray.full_merge_to_full
        (h_pre + pos_2) (end__2 - pos_2) (end__2 + q - pos_2)
        (sublist pos_2 end__2 hs)
        (sublist end__2 (end__2 + q) hs)).
      replace (sublist pos_2 end__2 hs ++ sublist end__2 (end__2 + q) hs)
        with (sublist pos_2 (end__2 + q) hs).
      2:{ rewrite <- sublist_split by lia. reflexivity. }
      rewrite sizeof_uchar.
      rewrite Zlength_sublist by lia.
      replace (Zlength hs + 1 - end__2 - q) with
        (Zlength hs - (end__2 + q) + 1) by lia.
      cancel.
      all: try entailer!.
    + split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
        try (apply Z.quot_pos; lia);
        try (apply Z.quot_lt_upper_bound; lia);
        try assumption.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_7 : twoway_strstr_entail_wit_11_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold memchr_zero_result in PreH1.
  destruct PreH1 as [[Hshort [Hret Hnonnull]] | [Hcount Hret]].
  - contradiction.
  - rewrite sizeof_uchar in PreH2, PreH3, PreH4.
    rewrite !Z.quot_1_r in PreH2.
    set (q := Z.lor l 63).
    assert (Hqnonneg : 0 <= q).
    { unfold q. apply Z.lor_nonneg. split; lia. }
    assert (Hql : l <= q).
    { unfold q.
      pose proof (Z.add_lor_land l 63).
      assert (Hland : Z.land l 63 = l mod 64).
      { change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia. reflexivity. }
      pose proof (Z.mod_pos_bound l 64 ltac:(lia)).
      lia. }
    assert (Hsuflen : Zlength (sublist end__2 (Zlength hs) hs) =
        Zlength hs - end__2) by (rewrite Zlength_sublist; lia).
    assert (Hend : end__2 + q <= Zlength hs) by (rewrite Hsuflen in Hcount; lia).
    assert (Hoff : unsigned_last_nbits (z - h) 64 = end__2 - pos_2).
    { rewrite PreH3, PreH4.
      unfold unsigned_last_nbits.
      rewrite Z.mod_small; lia. }
    assert (Hroom : l <= end__2 + q - pos_2) by lia.
    assert (Hbyte : 0 <= Znth (l - 1)
        (sublist pos_2 (end__2 + q) hs) 0 < 256).
    { rewrite Znth_sublist by lia.
      apply nonzero_nth_bound__proof_of_threebyte_2; try assumption; lia. }
    assert (Hnonzero_tail :
        nonzero_bytes (sublist (end__2 + q) (Zlength hs) hs)).
    { unfold nonzero_bytes in *.
      unfold sublist.
      apply Forall_skipn_local.
      apply Forall_firstn_local.
      exact PreH14. }
    Exists sh_2 bs_2 (end__2 + q) pos_2.
    split_pure_spatial.
    + rewrite PreH3, PreH4.
      rewrite sizeof_uchar.
      rewrite Hsuflen.
      replace (h_pre + end__2 * 1) with (h_pre + end__2) by lia.
      replace (Zlength hs - end__2 + 1) with
        (Zlength hs + 1 - end__2) by lia.
      replace (h_pre + end__2 + q) with
        (h_pre + end__2 + q * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
      sep_apply (UCharArray.full_split_to_full
        (h_pre + end__2) q (Zlength hs + 1 - end__2)
        (sublist end__2 (Zlength hs) hs ++ [0])).
      assert (Hprefix :
        sublist 0 q (sublist end__2 (Zlength hs) hs ++ [0]) =
        sublist end__2 (end__2 + q) hs).
      { rewrite sublist_split_app_l by (try rewrite Zlength_sublist; lia).
        rewrite Zsublist_Zsublist by lia.
        f_equal; lia. }
      assert (Hsuffix :
        sublist q (Zlength hs + 1 - end__2)
          (sublist end__2 (Zlength hs) hs ++ [0]) =
        sublist (end__2 + q) (Zlength hs) hs ++ [0]).
      { rewrite (sublist_split q (Zlength hs + 1 - end__2)
          (Zlength hs - end__2)) by
          (repeat rewrite Zlength_app, Zlength_cons, Zlength_nil,
            Zlength_sublist; lia).
        rewrite sublist_split_app_l by (try rewrite Zlength_sublist; lia).
        rewrite Zsublist_Zsublist by lia.
        rewrite sublist_split_app_r with
          (len := Zlength hs - end__2).
        2: rewrite Zlength_sublist; lia.
        2: lia.
        replace (Zlength hs - end__2 - (Zlength hs - end__2)) with 0 by lia.
        replace (Zlength hs + 1 - end__2 - (Zlength hs - end__2)) with 1 by lia.
        replace (q + end__2) with (end__2 + q) by lia.
        replace (Zlength hs - end__2 + end__2) with (Zlength hs) by lia.
        rewrite sublist_cons1 by lia.
        replace (1 - 1) with 0 by lia.
        cbn [sublist].
        reflexivity. }
      rewrite Hprefix, Hsuffix.
      replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
      replace (h_pre + end__2) with
        (h_pre + pos_2 + (end__2 - pos_2) * sizeof(UCHAR))
        by (rewrite sizeof_uchar; lia).
      replace q with
        (end__2 + q - pos_2 - (end__2 - pos_2)) at 1 by lia.
      sep_apply (UCharArray.full_merge_to_full
        (h_pre + pos_2) (end__2 - pos_2) (end__2 + q - pos_2)
        (sublist pos_2 end__2 hs)
        (sublist end__2 (end__2 + q) hs)).
      replace (sublist pos_2 end__2 hs ++ sublist end__2 (end__2 + q) hs)
        with (sublist pos_2 (end__2 + q) hs).
      2:{ rewrite <- sublist_split by lia. reflexivity. }
      rewrite sizeof_uchar.
      rewrite Zlength_sublist by lia.
      replace (Zlength hs + 1 - end__2 - q) with
        (Zlength hs - (end__2 + q) + 1) by lia.
      cancel.
      all: try entailer!.
    + split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
        try (apply Z.quot_pos; lia);
        try (apply Z.quot_lt_upper_bound; lia);
        try assumption.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_8 : twoway_strstr_entail_wit_11_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold memchr_zero_result in PreH1.
  destruct PreH1 as [[Hshort [Hret Hnonnull]] | [Hcount Hret]].
  - contradiction.
  - rewrite sizeof_uchar in PreH2, PreH3, PreH4.
    rewrite !Z.quot_1_r in PreH2.
    set (q := Z.lor l 63).
    assert (Hqnonneg : 0 <= q).
    { unfold q. apply Z.lor_nonneg. split; lia. }
    assert (Hql : l <= q).
    { unfold q.
      pose proof (Z.add_lor_land l 63).
      assert (Hland : Z.land l 63 = l mod 64).
      { change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia. reflexivity. }
      pose proof (Z.mod_pos_bound l 64 ltac:(lia)).
      lia. }
    assert (Hsuflen : Zlength (sublist end__2 (Zlength hs) hs) =
        Zlength hs - end__2) by (rewrite Zlength_sublist; lia).
    assert (Hend : end__2 + q <= Zlength hs) by (rewrite Hsuflen in Hcount; lia).
    assert (Hoff : unsigned_last_nbits (z - h) 64 = end__2 - pos_2).
    { rewrite PreH3, PreH4.
      unfold unsigned_last_nbits.
      rewrite Z.mod_small; lia. }
    assert (Hroom : l <= end__2 + q - pos_2) by lia.
    assert (Hbyte : 0 <= Znth (l - 1)
        (sublist pos_2 (end__2 + q) hs) 0 < 256).
    { rewrite Znth_sublist by lia.
      apply nonzero_nth_bound__proof_of_threebyte_2; try assumption; lia. }
    assert (Hnonzero_tail :
        nonzero_bytes (sublist (end__2 + q) (Zlength hs) hs)).
    { unfold nonzero_bytes in *.
      unfold sublist.
      apply Forall_skipn_local.
      apply Forall_firstn_local.
      exact PreH14. }
    Exists sh_2 bs_2 (end__2 + q) pos_2.
    split_pure_spatial.
    + rewrite PreH3, PreH4.
      rewrite sizeof_uchar.
      rewrite Hsuflen.
      replace (h_pre + end__2 * 1) with (h_pre + end__2) by lia.
      replace (Zlength hs - end__2 + 1) with
        (Zlength hs + 1 - end__2) by lia.
      replace (h_pre + end__2 + q) with
        (h_pre + end__2 + q * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
      sep_apply (UCharArray.full_split_to_full
        (h_pre + end__2) q (Zlength hs + 1 - end__2)
        (sublist end__2 (Zlength hs) hs ++ [0])).
      assert (Hprefix :
        sublist 0 q (sublist end__2 (Zlength hs) hs ++ [0]) =
        sublist end__2 (end__2 + q) hs).
      { rewrite sublist_split_app_l by (try rewrite Zlength_sublist; lia).
        rewrite Zsublist_Zsublist by lia.
        f_equal; lia. }
      assert (Hsuffix :
        sublist q (Zlength hs + 1 - end__2)
          (sublist end__2 (Zlength hs) hs ++ [0]) =
        sublist (end__2 + q) (Zlength hs) hs ++ [0]).
      { rewrite (sublist_split q (Zlength hs + 1 - end__2)
          (Zlength hs - end__2)) by
          (repeat rewrite Zlength_app, Zlength_cons, Zlength_nil,
            Zlength_sublist; lia).
        rewrite sublist_split_app_l by (try rewrite Zlength_sublist; lia).
        rewrite Zsublist_Zsublist by lia.
        rewrite sublist_split_app_r with
          (len := Zlength hs - end__2).
        2: rewrite Zlength_sublist; lia.
        2: lia.
        replace (Zlength hs - end__2 - (Zlength hs - end__2)) with 0 by lia.
        replace (Zlength hs + 1 - end__2 - (Zlength hs - end__2)) with 1 by lia.
        replace (q + end__2) with (end__2 + q) by lia.
        replace (Zlength hs - end__2 + end__2) with (Zlength hs) by lia.
        rewrite sublist_cons1 by lia.
        replace (1 - 1) with 0 by lia.
        cbn [sublist].
        reflexivity. }
      rewrite Hprefix, Hsuffix.
      replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
      replace (h_pre + end__2) with
        (h_pre + pos_2 + (end__2 - pos_2) * sizeof(UCHAR))
        by (rewrite sizeof_uchar; lia).
      replace q with
        (end__2 + q - pos_2 - (end__2 - pos_2)) at 1 by lia.
      sep_apply (UCharArray.full_merge_to_full
        (h_pre + pos_2) (end__2 - pos_2) (end__2 + q - pos_2)
        (sublist pos_2 end__2 hs)
        (sublist end__2 (end__2 + q) hs)).
      replace (sublist pos_2 end__2 hs ++ sublist end__2 (end__2 + q) hs)
        with (sublist pos_2 (end__2 + q) hs).
      2:{ rewrite <- sublist_split by lia. reflexivity. }
      rewrite sizeof_uchar.
      rewrite Zlength_sublist by lia.
      replace (Zlength hs + 1 - end__2 - q) with
        (Zlength hs - (end__2 + q) + 1) by lia.
      cancel.
      all: try entailer!.
    + split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
        try (apply Z.quot_pos; lia);
        try (apply Z.quot_lt_upper_bound; lia);
        try assumption.
Qed.


Ltac establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs :=
  rewrite sizeof_uchar in PreH1, PreH2, PreH3;
  rewrite Z.quot_1_r in PreH1;
  assert (Hoff : unsigned_last_nbits (z - h) 64 = end__2 - pos_2) by
    (rewrite PreH2, PreH3; unfold unsigned_last_nbits;
     rewrite Z.mod_small; lia);
  assert (Hroom : l <= end__2 - pos_2) by
    (rewrite Hoff in PreH1; lia);
  assert (Hbyte : 0 <= Znth (l - 1)
      (sublist pos_2 end__2 hs) 0 < 256) by
    (rewrite Znth_sublist by lia;
     apply nonzero_nth_bound__proof_of_threebyte_2; try assumption; lia).

Lemma proof_of_twoway_strstr_entail_wit_11_9_split_goal_1 :
  twoway_strstr_entail_wit_11_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  apply Z.quot_lt_upper_bound; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_9_split_goal_2 :
  twoway_strstr_entail_wit_11_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  apply Z.quot_pos; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_9_split_goal_3 :
  twoway_strstr_entail_wit_11_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_9_split_goal_4 :
  twoway_strstr_entail_wit_11_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_9_split_goal_5 :
  twoway_strstr_entail_wit_11_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_9 : twoway_strstr_entail_wit_11_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
      try (apply Z.quot_pos; lia);
      try (apply Z.quot_lt_upper_bound; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_10_split_goal_1 :
  twoway_strstr_entail_wit_11_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  apply Z.quot_lt_upper_bound; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_10_split_goal_2 :
  twoway_strstr_entail_wit_11_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  apply Z.quot_pos; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_10_split_goal_3 :
  twoway_strstr_entail_wit_11_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_10_split_goal_4 :
  twoway_strstr_entail_wit_11_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_10_split_goal_5 :
  twoway_strstr_entail_wit_11_10_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_10 : twoway_strstr_entail_wit_11_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
      try (apply Z.quot_pos; lia);
      try (apply Z.quot_lt_upper_bound; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_11_split_goal_1 :
  twoway_strstr_entail_wit_11_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  apply Z.quot_lt_upper_bound; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_11_split_goal_2 :
  twoway_strstr_entail_wit_11_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  apply Z.quot_pos; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_11_split_goal_3 :
  twoway_strstr_entail_wit_11_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_11_split_goal_4 :
  twoway_strstr_entail_wit_11_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_11_split_goal_5 :
  twoway_strstr_entail_wit_11_11_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_11 : twoway_strstr_entail_wit_11_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
      try (apply Z.quot_pos; lia);
      try (apply Z.quot_lt_upper_bound; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_12_split_goal_1 :
  twoway_strstr_entail_wit_11_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  apply Z.quot_lt_upper_bound; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_12_split_goal_2 :
  twoway_strstr_entail_wit_11_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  apply Z.quot_pos; lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_12_split_goal_3 :
  twoway_strstr_entail_wit_11_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_12_split_goal_4 :
  twoway_strstr_entail_wit_11_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_12_split_goal_5 :
  twoway_strstr_entail_wit_11_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_11_12 : twoway_strstr_entail_wit_11_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  establish_ready_window PreH1 PreH2 PreH3 z h end__2 pos_2 l hs.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption;
      try (apply Z.quot_pos; lia);
      try (apply Z.quot_lt_upper_bound; lia).
Qed.


Lemma bitop_hit_stage12 : forall word c,
  0 <= c < 256 ->
  Z.land word (unsigned_last_nbits (Z.shiftl 1 (c mod 64)) 64) <> 0 ->
  Z.testbit word (c mod 64) = true.
Proof.
  intros word c Hc Hland.
  assert (Hmod : 0 <= c mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  unfold unsigned_last_nbits in Hland.
  rewrite Z.shiftl_1_l in Hland by lia.
  rewrite Z.mod_small in Hland by
    (split; [pose proof (Z.pow_pos_nonneg 2 (c mod 64) ltac:(lia) ltac:(lia)); lia|];
     apply Z.pow_lt_mono_r; lia).
  destruct (Z.testbit word (c mod 64)) eqn:Hbit; auto.
  exfalso. apply Hland. apply Z.bits_inj. intro n.
  rewrite Z.land_spec. destruct (Z.eq_dec n (c mod 64)) as [-> | Hne].
  - rewrite Hbit. cbn. symmetry. apply Z.bits_0.
  - rewrite Z.pow2_bits_eqb by lia.
    replace (c mod 64 =? n)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Z.bits_0. destruct (Z.testbit word n); reflexivity.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_12_1 : twoway_strstr_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcut0 : 0 <= unsigned_last_nbits (ms+1) 64).
  { pose proof (unsigned_Lastnbits_range (ms+1) 64 ltac:(lia)); lia. }
  pose proof (search_cursor_right hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem Hcut0 ltac:(rewrite <- PreH4; lia) ltac:(eassumption)) as Hcursor.
  assert (Hmax : Z.max (unsigned_last_nbits (ms+1) 64) mem = (ms+1)).
  { destruct (Z.eq_dec ms UINT64_MAX) as [Heq|Hneq].
    - subst ms. replace (unsigned_last_nbits (UINT64_MAX+1) 64) with 0
        by (vm_compute; reflexivity). rewrite Z.max_r by lia; lia.
    - rewrite unsigned_last_nbits_eq by (cbn; lia).
      rewrite Z.max_l by lia; reflexivity. }
  rewrite Hmax in Hcursor.

  replace (8 * 8) with 64 in PreH39 by lia.
  rewrite Z.quot_div_nonneg in PreH39 by lia.
  rewrite Z.rem_mod_nonneg in PreH39 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage12; [lia | exact PreH39]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Hshift]]]].
  rewrite Hshift in PreH40.
  unfold unsigned_last_nbits in PreH40.
  rewrite Z.mod_small in PreH40 by (split; lia).
  assert (last = l - 1) by lia. subst last.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. rewrite PreH4. eapply terminated_nonzero_lt_stage12.
      * lia.
      * exact Hnz.
    + unfold right_half_matched. split.
      * unfold unsigned_last_nbits. rewrite Z.mod_small by (split; lia). lia.
      * unfold matched_range, unsigned_last_nbits.
        rewrite Z.mod_small by (split; lia). intros. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_12_2 : twoway_strstr_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcut0 : 0 <= unsigned_last_nbits (ms+1) 64).
  { pose proof (unsigned_Lastnbits_range (ms+1) 64 ltac:(lia)); lia. }
  pose proof (search_cursor_right hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem Hcut0 ltac:(rewrite <- PreH4; lia) ltac:(eassumption)) as Hcursor.
  assert (Hmax : Z.max (unsigned_last_nbits (ms+1) 64) mem = mem).
  { destruct (Z.eq_dec ms UINT64_MAX) as [Heq|Hneq].
    - subst ms. replace (unsigned_last_nbits (UINT64_MAX+1) 64) with 0
        by (vm_compute; reflexivity). rewrite Z.max_r by lia; lia.
    - rewrite unsigned_last_nbits_eq by (cbn; lia).
      rewrite Z.max_r by lia; reflexivity. }
  rewrite Hmax in Hcursor.

  replace (8 * 8) with 64 in PreH39 by lia.
  rewrite Z.quot_div_nonneg in PreH39 by lia.
  rewrite Z.rem_mod_nonneg in PreH39 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage12; [lia | exact PreH39]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Hshift]]]].
  rewrite Hshift in PreH40.
  unfold unsigned_last_nbits in PreH40.
  rewrite Z.mod_small in PreH40 by (split; lia).
  assert (last = l - 1) by lia. subst last.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. destruct (Z_lt_ge_dec mem l); [lia|].
      assert (mem = l) by lia. subst mem.
      rewrite PreH4 in Hnz. rewrite app_Znth2 in Hnz by lia.
      replace (Zlength ns - Zlength ns) with 0 in Hnz by lia.
      simpl in Hnz. contradiction.
    + unfold right_half_matched. split.
      * unfold unsigned_last_nbits. rewrite Z.mod_small by (split; lia).
        rewrite Z.max_r by lia. lia.
      * unfold matched_range. intros. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_12_3 : twoway_strstr_entail_wit_12_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcut0 : 0 <= unsigned_last_nbits (ms+1) 64).
  { pose proof (unsigned_Lastnbits_range (ms+1) 64 ltac:(lia)); lia. }
  pose proof (search_cursor_right hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem Hcut0 ltac:(rewrite <- PreH4; lia) ltac:(eassumption)) as Hcursor.
  assert (Hmax : Z.max (unsigned_last_nbits (ms+1) 64) mem = (ms+1)).
  { destruct (Z.eq_dec ms UINT64_MAX) as [Heq|Hneq].
    - subst ms. replace (unsigned_last_nbits (UINT64_MAX+1) 64) with 0
        by (vm_compute; reflexivity). rewrite Z.max_r by lia; lia.
    - rewrite unsigned_last_nbits_eq by (cbn; lia).
      rewrite Z.max_l by lia; reflexivity. }
  rewrite Hmax in Hcursor.

  replace (8 * 8) with 64 in PreH39 by lia.
  rewrite Z.quot_div_nonneg in PreH39 by lia.
  rewrite Z.rem_mod_nonneg in PreH39 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage12; [lia | exact PreH39]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Hshift]]]].
  rewrite Hshift in PreH40.
  unfold unsigned_last_nbits in PreH40.
  rewrite Z.mod_small in PreH40 by (split; lia).
  assert (last = l - 1) by lia. subst last.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. rewrite PreH4. eapply terminated_nonzero_lt_stage12.
      * lia.
      * exact Hnz.
    + unfold right_half_matched. split.
      * unfold unsigned_last_nbits. rewrite Z.mod_small by (split; lia). lia.
      * unfold matched_range, unsigned_last_nbits.
        rewrite Z.mod_small by (split; lia). intros. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_12_4 : twoway_strstr_entail_wit_12_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcut0 : 0 <= unsigned_last_nbits (ms+1) 64).
  { pose proof (unsigned_Lastnbits_range (ms+1) 64 ltac:(lia)); lia. }
  pose proof (search_cursor_right hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem Hcut0 ltac:(rewrite <- PreH4; lia) ltac:(eassumption)) as Hcursor.
  assert (Hmax : Z.max (unsigned_last_nbits (ms+1) 64) mem = mem).
  { destruct (Z.eq_dec ms UINT64_MAX) as [Heq|Hneq].
    - subst ms. replace (unsigned_last_nbits (UINT64_MAX+1) 64) with 0
        by (vm_compute; reflexivity). rewrite Z.max_r by lia; lia.
    - rewrite unsigned_last_nbits_eq by (cbn; lia).
      rewrite Z.max_r by lia; reflexivity. }
  rewrite Hmax in Hcursor.

  replace (8 * 8) with 64 in PreH39 by lia.
  rewrite Z.quot_div_nonneg in PreH39 by lia.
  rewrite Z.rem_mod_nonneg in PreH39 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage12; [lia | exact PreH39]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Hshift]]]].
  rewrite Hshift in PreH40.
  unfold unsigned_last_nbits in PreH40.
  rewrite Z.mod_small in PreH40 by (split; lia).
  assert (last = l - 1) by lia. subst last.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. destruct (Z_lt_ge_dec mem l); [lia|].
      assert (mem = l) by lia. subst mem.
      rewrite PreH4 in Hnz. rewrite app_Znth2 in Hnz by lia.
      replace (Zlength ns - Zlength ns) with 0 in Hnz by lia.
      simpl in Hnz. contradiction.
    + unfold right_half_matched. split.
      * unfold unsigned_last_nbits. rewrite Z.mod_small by (split; lia).
        rewrite Z.max_r by lia. lia.
      * unfold matched_range. intros. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_12_5 : twoway_strstr_entail_wit_12_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcut0 : 0 <= unsigned_last_nbits (ms+1) 64).
  { pose proof (unsigned_Lastnbits_range (ms+1) 64 ltac:(lia)); lia. }
  pose proof (search_cursor_right hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem Hcut0 ltac:(rewrite <- PreH4; lia) ltac:(eassumption)) as Hcursor.
  assert (Hmax : Z.max (unsigned_last_nbits (ms+1) 64) mem = mem).
  { destruct (Z.eq_dec ms UINT64_MAX) as [Heq|Hneq].
    - subst ms. replace (unsigned_last_nbits (UINT64_MAX+1) 64) with 0
        by (vm_compute; reflexivity). rewrite Z.max_r by lia; lia.
    - rewrite unsigned_last_nbits_eq by (cbn; lia).
      rewrite Z.max_r by lia; reflexivity. }
  rewrite Hmax in Hcursor.

  replace (8 * 8) with 64 in PreH38 by lia.
  rewrite Z.quot_div_nonneg in PreH38 by lia.
  rewrite Z.rem_mod_nonneg in PreH38 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage12; [lia | exact PreH38]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Hshift]]]].
  rewrite Hshift in PreH39.
  unfold unsigned_last_nbits in PreH39.
  rewrite Z.mod_small in PreH39 by (split; lia).
  assert (last = l - 1) by lia. subst last.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. destruct (Z_lt_ge_dec mem l); [lia|].
      assert (mem = l) by lia. subst mem.
      rewrite PreH4 in Hnz. rewrite app_Znth2 in Hnz by lia.
      replace (Zlength ns - Zlength ns) with 0 in Hnz by lia.
      simpl in Hnz. contradiction.
    + unfold right_half_matched. split; [lia|].
      unfold matched_range. intros. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_12_6 : twoway_strstr_entail_wit_12_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcut0 : 0 <= unsigned_last_nbits (ms+1) 64).
  { pose proof (unsigned_Lastnbits_range (ms+1) 64 ltac:(lia)); lia. }
  pose proof (search_cursor_right hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem Hcut0 ltac:(rewrite <- PreH4; lia) ltac:(eassumption)) as Hcursor.
  assert (Hmax : Z.max (unsigned_last_nbits (ms+1) 64) mem = mem).
  { destruct (Z.eq_dec ms UINT64_MAX) as [Heq|Hneq].
    - subst ms. replace (unsigned_last_nbits (UINT64_MAX+1) 64) with 0
        by (vm_compute; reflexivity). rewrite Z.max_r by lia; lia.
    - rewrite unsigned_last_nbits_eq by (cbn; lia).
      rewrite Z.max_r by lia; reflexivity. }
  rewrite Hmax in Hcursor.

  replace (8 * 8) with 64 in PreH38 by lia.
  rewrite Z.quot_div_nonneg in PreH38 by lia.
  rewrite Z.rem_mod_nonneg in PreH38 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage12; [lia | exact PreH38]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Hshift]]]].
  rewrite Hshift in PreH39.
  unfold unsigned_last_nbits in PreH39.
  rewrite Z.mod_small in PreH39 by (split; lia).
  assert (last = l - 1) by lia. subst last.
  Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. destruct (Z_lt_ge_dec mem l); [lia|].
      assert (mem = l) by lia. subst mem.
      rewrite PreH4 in Hnz. rewrite app_Znth2 in Hnz by lia.
      replace (Zlength ns - Zlength ns) with 0 in Hnz by lia.
      simpl in Hnz. contradiction.
    + unfold right_half_matched. split; [lia|].
      unfold matched_range. intros. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_13_1 : twoway_strstr_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcursor : search_right_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (k+1)).
  { eapply search_right_step; [rewrite <- PreH5; lia| |eassumption].
    unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond.
    rewrite app_Znth1 in PreH1 by lia.
    rewrite Znth_sublist in PreH1 by lia.
    replace (k+pos_2) with (pos_2+k) in PreH1 by lia. exact PreH1. }

  Left. Left. Left. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. rewrite PreH5. eapply terminated_nonzero_lt_stage12; [lia|exact Hnz].
    + unfold right_half_matched in *.
      destruct PreH17 as [Hbound PreH17]. split; [lia|].
      unfold matched_range in *.
      intros q Hq. destruct (Z_lt_ge_dec q k) as [Hlt|Hge].
      * apply PreH17. lia.
      * assert (q = k) by lia. subst q.
        rewrite app_Znth1 in PreH1 by lia.
        rewrite Znth_sublist in PreH1 by lia.
        symmetry. replace (pos_2 + k) with (k + pos_2) by lia. exact PreH1.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_13_2 : twoway_strstr_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcursor : search_right_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (k+1)).
  { eapply search_right_step; [rewrite <- PreH5; lia| |eassumption].
    unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond.
    rewrite app_Znth1 in PreH1 by lia.
    rewrite Znth_sublist in PreH1 by lia.
    replace (k+pos_2) with (pos_2+k) in PreH1 by lia. exact PreH1. }

  Left. Left. Right. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. rewrite PreH5. eapply terminated_nonzero_lt_stage12; [lia|exact Hnz].
    + unfold right_half_matched in *.
      destruct PreH17 as [Hbound PreH17]. split; [lia|].
      unfold matched_range in *.
      intros q Hq. destruct (Z_lt_ge_dec q k) as [Hlt|Hge].
      * apply PreH17. lia.
      * assert (q = k) by lia. subst q.
        rewrite app_Znth1 in PreH1 by lia.
        rewrite Znth_sublist in PreH1 by lia.
        symmetry. replace (pos_2 + k) with (k + pos_2) by lia. exact PreH1.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_13_3 : twoway_strstr_entail_wit_13_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcursor : search_right_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (k+1)).
  { eapply search_right_step; [rewrite <- PreH5; lia| |eassumption].
    unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond.
    rewrite app_Znth1 in PreH1 by lia.
    rewrite Znth_sublist in PreH1 by lia.
    replace (k+pos_2) with (pos_2+k) in PreH1 by lia. exact PreH1. }

  Left. Right. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. rewrite PreH5. eapply terminated_nonzero_lt_stage12; [lia|exact Hnz].
    + unfold right_half_matched in *.
      destruct PreH17 as [Hbound PreH17]. split; [lia|].
      unfold matched_range in *.
      intros q Hq. destruct (Z_lt_ge_dec q k) as [Hlt|Hge].
      * apply PreH17. lia.
      * assert (q = k) by lia. subst q.
        rewrite app_Znth1 in PreH1 by lia.
        rewrite Znth_sublist in PreH1 by lia.
        symmetry. replace (pos_2 + k) with (k + pos_2) by lia. exact PreH1.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_13_4 : twoway_strstr_entail_wit_13_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcursor : search_right_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (k+1)).
  { eapply search_right_step; [rewrite <- PreH5; lia| |eassumption].
    unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond.
    rewrite app_Znth1 in PreH1 by lia.
    rewrite Znth_sublist in PreH1 by lia.
    replace (k+pos_2) with (pos_2+k) in PreH1 by lia. exact PreH1. }

  Right. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + intros Hnz. rewrite PreH5. eapply terminated_nonzero_lt_stage12; [lia|exact Hnz].
    + unfold right_half_matched in *.
      destruct PreH17 as [Hbound PreH17]. split; [lia|].
      unfold matched_range in *.
      intros q Hq. destruct (Z_lt_ge_dec q k) as [Hlt|Hge].
      * apply PreH17. lia.
      * assert (q = k) by lia. subst q.
        rewrite app_Znth1 in PreH1 by lia.
        rewrite Znth_sublist in PreH1 by lia.
        symmetry. replace (pos_2 + k) with (k + pos_2) by lia. exact PreH1.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_16_1 : twoway_strstr_entail_wit_16_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hklen : k = Zlength ns).
  { assert (Hkl : k = l).
    { apply Z.le_antisymm; [lia|].
      destruct (Z_lt_ge_dec k l); [|lia].
      pose proof (nonzero_byte_range__proof_of_threebyte_2 ns k
        ltac:(eassumption) ltac:(lia)) as Hnz.
      match goal with Hzero : Znth k (ns ++ [0]) 0 = 0 |- _ =>
        rewrite app_Znth1 in Hzero by lia end. lia. }
    lia. }
  assert (Hcursor : search_left_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (unsigned_last_nbits (ms+1) 64)).
  { apply search_right_end. rewrite <- Hklen. assumption. }
  clear Hklen.

  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  assert (Hnowrap : unsigned_last_nbits (ms + 1) 64 = ms + 1).
  { unfold unsigned_last_nbits. change (2 ^ 64) with 18446744073709551616.
    apply Z.mod_small. lia. }
  rewrite Hnowrap in *.
  assert (Hsplit_bounds : 0 <= unsigned_last_nbits (ms + 1) 64 <= l).
  { pose proof (proj1 PreH36) as Hcritical.
    unfold critical_split in Hcritical.
    destruct Hcritical as [period [_ [_ [_ Hlocal]]]].
    unfold local_period in Hlocal. destruct Hlocal as [[Ha Hb] _].
    rewrite <- PreH4 in Hb. lia. }
  Right. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + assert (Hk : k = l).
      { apply Z.le_antisymm; [exact PreH11|].
        destruct (Z_lt_ge_dec k l) as [Hlt|Hge]; [|lia].
        exfalso.
        pose proof (nonzero_byte_range__proof_of_threebyte_2 ns k PreH18 ltac:(lia)) as Hnz.
        rewrite app_Znth1 in PreH38 by lia. lia. }
      subst k. unfold right_half_matched in PreH16.
      destruct PreH16 as [_ PreH16]. unfold matched_range in *.
      intros q [Hqlo Hqhi]. destruct (Z_lt_ge_dec q mem) as [Hlt|Hge].
      * apply PreH15. lia.
      * apply PreH16. destruct (Z_le_dec (unsigned_last_nbits (ms + 1) 64) mem) as [Hsm|Hms].
        -- rewrite Z.max_r by lia. split; [lia|exact Hqhi].
        -- rewrite Z.max_l by lia. split; [exact Hqlo|exact Hqhi].
Qed.


Lemma proof_of_twoway_strstr_entail_wit_16_2 : twoway_strstr_entail_wit_16_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hklen : k = Zlength ns).
  { assert (Hkl : k = l).
    { apply Z.le_antisymm; [lia|].
      destruct (Z_lt_ge_dec k l); [|lia].
      pose proof (nonzero_byte_range__proof_of_threebyte_2 ns k
        ltac:(eassumption) ltac:(lia)) as Hnz.
      match goal with Hzero : Znth k (ns ++ [0]) 0 = 0 |- _ =>
        rewrite app_Znth1 in Hzero by lia end. lia. }
    lia. }
  assert (Hcursor : search_left_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (unsigned_last_nbits (ms+1) 64)).
  { apply search_right_end. rewrite <- Hklen. assumption. }
  clear Hklen.

  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  assert (Hnowrap : unsigned_last_nbits (ms + 1) 64 = ms + 1).
  { unfold unsigned_last_nbits. change (2 ^ 64) with 18446744073709551616.
    apply Z.mod_small. lia. }
  rewrite Hnowrap in *.
  assert (Hsplit_bounds : 0 <= unsigned_last_nbits (ms + 1) 64 <= l).
  { pose proof (proj1 PreH36) as Hcritical.
    unfold critical_split in Hcritical.
    destruct Hcritical as [period [_ [_ [_ Hlocal]]]].
    unfold local_period in Hlocal. destruct Hlocal as [[Ha Hb] _].
    rewrite <- PreH4 in Hb. lia. }
  Left. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + assert (Hk : k = l).
      { apply Z.le_antisymm; [exact PreH11|].
        destruct (Z_lt_ge_dec k l) as [Hlt|Hge]; [|lia].
        exfalso.
        pose proof (nonzero_byte_range__proof_of_threebyte_2 ns k PreH18 ltac:(lia)) as Hnz.
        rewrite app_Znth1 in PreH38 by lia. lia. }
      subst k. unfold right_half_matched in PreH16.
      destruct PreH16 as [_ PreH16]. unfold matched_range in *.
      intros q [Hqlo Hqhi]. destruct (Z_lt_ge_dec q mem) as [Hlt|Hge].
      * apply PreH15. lia.
      * apply PreH16. destruct (Z_le_dec (unsigned_last_nbits (ms + 1) 64) mem) as [Hsm|Hms].
        -- rewrite Z.max_r by lia. split; [lia|exact Hqhi].
        -- rewrite Z.max_l by lia. split; [exact Hqlo|exact Hqhi].
Qed.


Lemma proof_of_twoway_strstr_entail_wit_16_3 : twoway_strstr_entail_wit_16_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hklen : k = Zlength ns).
  { assert (Hkl : k = l).
    { apply Z.le_antisymm; [lia|].
      destruct (Z_lt_ge_dec k l); [|lia].
      pose proof (nonzero_byte_range__proof_of_threebyte_2 ns k
        ltac:(eassumption) ltac:(lia)) as Hnz.
      match goal with Hzero : Znth k (ns ++ [0]) 0 = 0 |- _ =>
        rewrite app_Znth1 in Hzero by lia end. lia. }
    lia. }
  assert (Hcursor : search_left_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (unsigned_last_nbits (ms+1) 64)).
  { apply search_right_end. rewrite <- Hklen. assumption. }
  clear Hklen.

  assert (Hsplit : unsigned_last_nbits (ms + 1) 64 = 0)
    by (subst ms; vm_compute; reflexivity).
  rewrite Hsplit in *.
  Left. Left. Right. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + assert (Hk : k = l).
      { apply Z.le_antisymm; [exact PreH11|].
        destruct (Z_lt_ge_dec k l) as [Hlt|Hge]; [|lia].
        exfalso.
        pose proof (nonzero_byte_range__proof_of_threebyte_2 ns k PreH18 ltac:(lia)) as Hnz.
        rewrite app_Znth1 in PreH37 by lia. lia. }
      subst k. unfold right_half_matched in PreH16.
      destruct PreH16 as [_ PreH16]. unfold matched_range in *.
      intros q [Hqlo Hqhi]. destruct (Z_lt_ge_dec q mem) as [Hlt|Hge].
      * apply PreH15. lia.
      * apply PreH16. destruct (Z_le_dec (unsigned_last_nbits (ms + 1) 64) mem) as [Hsm|Hms].
        -- rewrite Z.max_r by lia. split; [lia|exact Hqhi].
        -- rewrite Z.max_l by lia. split; [exact Hqlo|exact Hqhi].
Qed.


Lemma proof_of_twoway_strstr_entail_wit_16_4 : twoway_strstr_entail_wit_16_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hklen : k = Zlength ns).
  { assert (Hkl : k = l).
    { apply Z.le_antisymm; [lia|].
      destruct (Z_lt_ge_dec k l); [|lia].
      pose proof (nonzero_byte_range__proof_of_threebyte_2 ns k
        ltac:(eassumption) ltac:(lia)) as Hnz.
      match goal with Hzero : Znth k (ns ++ [0]) 0 = 0 |- _ =>
        rewrite app_Znth1 in Hzero by lia end. lia. }
    lia. }
  assert (Hcursor : search_left_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (unsigned_last_nbits (ms+1) 64)).
  { apply search_right_end. rewrite <- Hklen. assumption. }
  clear Hklen.

  assert (Hsplit : unsigned_last_nbits (ms + 1) 64 = 0)
    by (subst ms; vm_compute; reflexivity).
  rewrite Hsplit in *.
  Left. Left. Left. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    + assert (Hk : k = l).
      { apply Z.le_antisymm; [exact PreH11|].
        destruct (Z_lt_ge_dec k l) as [Hlt|Hge]; [|lia].
        exfalso.
        pose proof (nonzero_byte_range__proof_of_threebyte_2 ns k PreH18 ltac:(lia)) as Hnz.
        rewrite app_Znth1 in PreH37 by lia. lia. }
      subst k. unfold right_half_matched in PreH16.
      destruct PreH16 as [_ PreH16]. unfold matched_range in *.
      intros q [Hqlo Hqhi]. destruct (Z_lt_ge_dec q mem) as [Hlt|Hge].
      * apply PreH15. lia.
      * apply PreH16. destruct (Z_le_dec (unsigned_last_nbits (ms + 1) 64) mem) as [Hsm|Hms].
        -- rewrite Z.max_r by lia. split; [lia|exact Hqhi].
        -- rewrite Z.max_l by lia. split; [exact Hqlo|exact Hqhi].
Qed.


Lemma proof_of_twoway_strstr_entail_wit_17_1 : twoway_strstr_entail_wit_17_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcursor : search_left_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (k-1)).
  { eapply search_left_step; [lia| |eassumption].
    unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond.
    match goal with Heq : Znth (k-1) (ns ++ [0]) 0 = _ |- _ =>
      rewrite app_Znth1 in Heq by lia;
      rewrite Znth_sublist in Heq by lia;
      replace (k-1+pos_2) with (pos_2+(k-1)) in Heq by lia; exact Heq end. }

  Left. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    unfold matched_range in *.
    intros q Hq. destruct (Z.eq_dec q (k - 1)) as [Heq|Hneq].
    + subst q. rewrite app_Znth1 in PreH1 by lia.
      rewrite Znth_sublist in PreH1 by lia.
      symmetry. replace (pos_2 + (k - 1)) with (k - 1 + pos_2) by lia. exact PreH1.
    + apply PreH18. lia.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_17_2 : twoway_strstr_entail_wit_17_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcursor : search_left_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 pos_2 mem (k-1)).
  { eapply search_left_step; [lia| |eassumption].
    unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond.
    match goal with Heq : Znth (k-1) (ns ++ [0]) 0 = _ |- _ =>
      rewrite app_Znth1 in Heq by lia;
      rewrite Znth_sublist in Heq by lia;
      replace (k-1+pos_2) with (pos_2+(k-1)) in Heq by lia; exact Heq end. }

  Right. Exists sh_2 bs_2 end__2 pos_2.
  split_pure_spatial.
  - cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar; try lia; try assumption.
    unfold matched_range in *.
    intros q Hq. destruct (Z.eq_dec q (k - 1)) as [Heq|Hneq].
    + subst q. rewrite app_Znth1 in PreH1 by lia.
      rewrite Znth_sublist in PreH1 by lia.
      symmetry. replace (pos_2 + (k - 1)) with (k - 1 + pos_2) by lia. exact PreH1.
    + apply PreH18. lia.
Qed.


Lemma local_period_multiple_of_least_stage18 :
  forall needle split w mp,
    least_string_period needle mp ->
    local_period needle split mp ->
    (forall q, local_period needle split q -> mp <= q) ->
    local_period needle split w ->
    split + w <= Zlength needle ->
    exists q, w = q * mp.
Proof.
  intros needle split w mp Hleast Hmp_local Hlocal_min Hlocal Hbound.
  destruct Hleast as [Hmp_period _].
  assert (Hmp_pos : 0 < mp) by exact (proj1 Hmp_period).
  destruct Hlocal as [Hsplit [Hw_pos Hlocal_body]].
  set (q := w / mp).
  set (r := w mod mp).
  assert (Hdiv : w = mp * q + r).
  { unfold q, r. apply Z.div_mod. destruct Hmp_period; lia. }
  assert (Hr : 0 <= r < mp).
  { unfold r. apply Z.mod_pos_bound. destruct Hmp_period; lia. }
  assert (Hq : 0 <= q).
  { unfold q. apply Z.div_pos; destruct Hmp_period; lia. }
  destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
  - exists q. nia.
  - assert (Hr_pos : 0 < r < mp) by lia.
    assert (Hseg :
      sublist split (split + r) needle =
      sublist (split + w - r) (split + w) needle).
    { rewrite Hdiv.
      replace (split + (mp * q + r) - r) with (split + q * mp) by lia.
      replace (split + (mp * q + r)) with (split + r + q * mp) by lia.
      eapply (periodic_segment' 0 needle mp q
        split (split + r) (split + q * mp) (split + r + q * mp));
        try exact Hmp_period; nia. }
    assert (Hr_local : local_period needle split r).
    { unfold local_period.
      split; [exact Hsplit | split; [lia |]].
      intros i Hi Hleft Hright.
      assert (Hfrom_w :
        Znth (split + (i + w - r) - w) needle 0 =
        Znth (split + (i + w - r)) needle 0).
      { exact (Hlocal_body (i + w - r) ltac:(lia) ltac:(lia) ltac:(lia)). }
      replace (split + (i + w - r) - w) with
        (split + i - r) in Hfrom_w by lia.
      apply (f_equal (fun xs => Znth i xs 0)) in Hseg.
      rewrite Znth_sublist in Hseg by lia.
      rewrite Znth_sublist in Hseg by lia.
      replace (i + split) with (split + i) in Hseg by lia.
      replace (i + (split + w - r)) with
        (split + (i + w - r)) in Hseg by lia.
      rewrite Hseg. exact Hfrom_w. }
    specialize (Hlocal_min r Hr_local). lia.
Qed.


Lemma split_hay_length64__cut_probe :
  forall h_pre h z hs pos end_,
    h = h_pre + pos * sizeof(UCHAR) ->
    z = h_pre + end_ * sizeof(UCHAR) ->
    0 <= pos <= end_ -> end_ <= Zlength hs ->
    UCharArray.full h (end_ - pos) (sublist pos end_ hs) **
    UCharArray.full h_pre pos (sublist 0 pos hs) **
    UCharArray.full z (Zlength (sublist end_ (Zlength hs) hs) + 1)
      (sublist end_ (Zlength hs) hs ++ [0])
    |-- “ Zlength hs <= UINT64_MAX ”.
Proof.
  intros h_pre h z hs pos end_ Hh Hz Hpos Hend.
  rewrite Hh, Hz, sizeof_uchar.
  assert (Hsuflen : Zlength (sublist end_ (Zlength hs) hs) =
      Zlength hs - end_) by (rewrite Zlength_sublist; lia).
  rewrite Hsuflen.
  replace (h_pre + end_ * 1) with
    (h_pre + pos * 1 + (end_ - pos) * sizeof(UCHAR))
    by (rewrite sizeof_uchar; lia).
  replace (Zlength hs - end_ + 1) with
    (Zlength hs + 1 - pos - (end_ - pos)) by lia.
  sep_apply (UCharArray.full_merge_to_full
    (h_pre + pos * 1) (end_ - pos) (Zlength hs + 1 - pos)
    (sublist pos end_ hs)
    (sublist end_ (Zlength hs) hs ++ [0])).
  all: try lia.
  replace (sublist pos end_ hs ++ (sublist end_ (Zlength hs) hs ++ [0]))
    with (sublist pos (Zlength hs) hs ++ [0]).
  2:{ rewrite app_assoc.
      rewrite <- (sublist_split pos (Zlength hs) end_ hs) by lia.
      reflexivity. }
  assert (Hmerge :
    UCharArray.full (h_pre + pos * 1)
      (Zlength hs + 1 - pos) (sublist pos (Zlength hs) hs ++ [0]) **
    UCharArray.full h_pre pos (sublist 0 pos hs)
    |-- UCharArray.full h_pre (Zlength hs + 1)
      (sublist 0 pos hs ++ (sublist pos (Zlength hs) hs ++ [0]))).
  { apply derivable1_trans with (y :=
      UCharArray.full h_pre pos (sublist 0 pos hs) **
      UCharArray.full (h_pre + pos * 1)
        (Zlength hs + 1 - pos) (sublist pos (Zlength hs) hs ++ [0])).
    - cancel.
    - exact (UCharArray.full_merge_to_full h_pre pos (Zlength hs + 1)
        (sublist 0 pos hs) (sublist pos (Zlength hs) hs ++ [0]) ltac:(lia)). }
  sep_apply Hmerge.
  replace (sublist 0 pos hs ++ (sublist pos (Zlength hs) hs ++ [0]))
    with (hs ++ [0]).
  2:{ rewrite app_assoc.
      rewrite <- (sublist_split 0 (Zlength hs) pos hs) by lia.
      rewrite sublist_self by lia. reflexivity. }
  apply strstr_array_length64__cut_probe.
Qed.

Lemma bitop_miss_stage18 : forall word c,
  0 <= c < 256 ->
  Z.land word (unsigned_last_nbits (Z.shiftl 1 (c mod 64)) 64) = 0 ->
  Z.testbit word (c mod 64) = false.
Proof.
  intros word c Hc Hland.
  assert (Hmod : 0 <= c mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  unfold unsigned_last_nbits in Hland.
  rewrite Z.shiftl_1_l in Hland by lia.
  rewrite Z.mod_small in Hland by
    (split; [pose proof (Z.pow_pos_nonneg 2 (c mod 64) ltac:(lia) ltac:(lia)); lia|];
     apply Z.pow_lt_mono_r; lia).
  destruct (Z.testbit word (c mod 64)) eqn:Hbit; auto.
  pose proof (f_equal (fun z => Z.testbit z (c mod 64)) Hland) as Heq.
  cbn beta in Heq.
  rewrite Z.land_spec, Hbit, Z.pow2_bits_eqb in Heq by lia.
  rewrite Z.eqb_refl, Z.bits_0 in Heq. discriminate.
Qed.





Lemma bitop_hit_stage18 : forall word c,
  0 <= c < 256 ->
  Z.land word (unsigned_last_nbits (Z.shiftl 1 (c mod 64)) 64) <> 0 ->
  Z.testbit word (c mod 64) = true.
Proof.
  intros word c Hc Hland.
  assert (Hmod : 0 <= c mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  unfold unsigned_last_nbits in Hland.
  rewrite Z.shiftl_1_l in Hland by lia.
  rewrite Z.mod_small in Hland by
    (split; [pose proof (Z.pow_pos_nonneg 2 (c mod 64) ltac:(lia) ltac:(lia)); lia|];
     apply Z.pow_lt_mono_r; lia).
  destruct (Z.testbit word (c mod 64)) eqn:Hbit; auto.
  exfalso. apply Hland. apply Z.bits_inj. intro n.
  rewrite Z.land_spec. destruct (Z.eq_dec n (c mod 64)) as [-> | Hne].
  - rewrite Hbit. cbn. symmetry. apply Z.bits_0.
  - rewrite Z.pow2_bits_eqb by lia.
    replace (c mod 64 =? n)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Z.bits_0. destruct (Z.testbit word n); reflexivity.
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_1 : twoway_strstr_entail_wit_18_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH4 PreH5 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  assert (Hmismatch :
      Znth (k - 1) ns 0 <> Znth (pos_2 + k - 1) hs 0).
  { rewrite app_Znth1 in PreH2 by lia.
    rewrite Znth_sublist in PreH2 by lia.
    replace (k - 1 + pos_2) with (pos_2 + k - 1) in PreH2 by lia.
    exact PreH2. }
  assert (Hmatched_tail : matched_range hs ns pos_2 k (Zlength ns)).
  { rewrite <- PreH6. exact PreH19. }
  pose proof (original_left_mismatch_skip hs ns pos_2
    (unsigned_last_nbits (ms + 1) 64) p mem k
    PreH17 ltac:(lia) ltac:(rewrite <- PreH6; lia)
    ltac:(lia) PreH16 ltac:(lia) Hmatched_tail Hmismatch PreH37) as Hskip.
  pose proof (periodic_memory_after_shift hs ns pos_2
    (unsigned_last_nbits (ms + 1) 64) p mem mem0 k
    PreH36 PreH37 PreH16 Hmatched_tail) as Hmatched.
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+p) mem0).
  { eapply search_left_mismatch with (memory:=mem) (k:=k); [lia| |rewrite <- PreH6; lia| |eassumption].
    - unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond. replace (pos_2+(k-1)) with (pos_2+k-1) by lia.
      exact Hmismatch.
    - eapply cursor_before_valid_skip; try lia; [|exact Hskip].
      intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
      rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p mem0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH36 as [_ [Hr Hp]].
    split; [right; reflexivity | split; assumption]. }
  Exists sh_2 bs_2 end__2 (pos_2 + p).
  split_pure_spatial.
  - rewrite PreH4, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + p * 1) with (h_pre + pos_2 + p) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) p (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 p (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + p) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist p (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + p) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) p
        (sublist pos_2 (pos_2 + p) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + p)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + p) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) p
          (sublist pos_2 (pos_2 + p) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + p)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + p) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + p - pos_2) with p in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + p) hs)
      with (sublist 0 (pos_2 + p) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + p * 1) with
      (h_pre + pos_2 * 1 + p) by lia.
    replace (end__2 - pos_2 - p) with (end__2 - (pos_2 + p)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH4, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_2 : twoway_strstr_entail_wit_18_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH4 PreH5 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  assert (Hmismatch :
      Znth (k - 1) ns 0 <> Znth (pos_2 + k - 1) hs 0).
  { rewrite app_Znth1 in PreH2 by lia.
    rewrite Znth_sublist in PreH2 by lia.
    replace (k - 1 + pos_2) with (pos_2 + k - 1) in PreH2 by lia.
    exact PreH2. }
  assert (Hmatched_tail : matched_range hs ns pos_2 k (Zlength ns)).
  { rewrite <- PreH6. exact PreH19. }
  pose proof (original_left_mismatch_skip hs ns pos_2
    (unsigned_last_nbits (ms + 1) 64) p mem k
    PreH17 ltac:(lia) ltac:(rewrite <- PreH6; lia)
    ltac:(lia) PreH16 ltac:(lia) Hmatched_tail Hmismatch PreH37) as Hskip.
  pose proof (periodic_memory_after_shift hs ns pos_2
    (unsigned_last_nbits (ms + 1) 64) p mem mem0 k
    PreH36 PreH37 PreH16 Hmatched_tail) as Hmatched.
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+p) mem0).
  { eapply search_left_mismatch with (memory:=mem) (k:=k); [lia| |rewrite <- PreH6; lia| |eassumption].
    - unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond. replace (pos_2+(k-1)) with (pos_2+k-1) by lia.
      exact Hmismatch.
    - eapply cursor_before_valid_skip; try lia; [|exact Hskip].
      intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
      rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p mem0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH36 as [_ [Hr Hp]].
    split; [right; reflexivity | split; assumption]. }
  Exists sh_2 bs_2 end__2 (pos_2 + p).
  split_pure_spatial.
  - rewrite PreH4, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + p * 1) with (h_pre + pos_2 + p) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) p (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 p (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + p) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist p (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + p) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) p
        (sublist pos_2 (pos_2 + p) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + p)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + p) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) p
          (sublist pos_2 (pos_2 + p) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + p)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + p) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + p - pos_2) with p in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + p) hs)
      with (sublist 0 (pos_2 + p) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + p * 1) with
      (h_pre + pos_2 * 1 + p) by lia.
    replace (end__2 - pos_2 - p) with (end__2 - (pos_2 + p)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH4, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_3 : twoway_strstr_entail_wit_18_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH2 PreH3 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  replace (8 * 8) with 64 in PreH39 by lia.
  rewrite Z.quot_div_nonneg in PreH39 by lia.
  rewrite Z.rem_mod_nonneg in PreH39 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage18; [lia | exact PreH39]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Htable]]]].
  rewrite Htable in PreH1, PreH40.
  unfold unsigned_last_nbits in PreH1, PreH40.
  rewrite Z.mod_small in PreH1 by (split; lia).
  rewrite Z.mod_small in PreH40 by (split; lia).
  assert (Hlast_value :
    Znth last ns 0 = Znth (pos_2 + Zlength ns - 1) hs 0).
  { rewrite <- PreH4.
    rewrite Znth_sublist in Hval by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hval by lia.
    exact Hval. }
  assert (Hlatest_value : forall t, last < t < Zlength ns ->
    Znth t ns 0 <> Znth (pos_2 + Zlength ns - 1) hs 0).
  { intros t Ht. rewrite <- PreH4 in Ht |- *.
    specialize (Hlatest t Ht).
    rewrite Znth_sublist in Hlatest by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hlatest by lia.
    exact Hlatest. }
  pose proof (musl_periodic_memory_skip_before hs ns bs_2 sh_2 pos_2 p mem mem0 last
    ltac:(assumption) ltac:(rewrite <- PreH4; lia)
    PreH6 ltac:(rewrite <- PreH4; lia) PreH16 PreH36
    ltac:(rewrite <- PreH4; exact PreH19)
    ltac:(rewrite <- PreH4; exact PreH20)
    ltac:(rewrite <- PreH4; exact Hlast) Hlast_value Hlatest_value
    ltac:(rewrite <- PreH4; lia) PreH15) as Hskip.
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+mem) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH36 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + mem) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + mem).
  split_pure_spatial.
  - rewrite PreH2, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + mem * 1) with (h_pre + pos_2 + mem) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) mem (end__2 - pos_2) (sublist pos_2 end__2 hs)).
    assert (Hprefix_part :
      sublist 0 mem (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + mem) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix_part :
      sublist mem (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + mem) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix_part, Hsuffix_part.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) mem
        (sublist pos_2 (pos_2 + mem) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + mem)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + mem) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) mem
          (sublist pos_2 (pos_2 + mem) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + mem)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + mem) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + mem - pos_2) with mem in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + mem) hs)
      with (sublist 0 (pos_2 + mem) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + mem * 1) with
      (h_pre + pos_2 * 1 + mem) by lia.
    replace (end__2 - pos_2 - mem) with
      (end__2 - (pos_2 + mem)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH2, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_4 : twoway_strstr_entail_wit_18_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH2 PreH3 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  replace (8 * 8) with 64 in PreH39 by lia.
  rewrite Z.quot_div_nonneg in PreH39 by lia.
  rewrite Z.rem_mod_nonneg in PreH39 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage18; [lia | exact PreH39]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Htable]]]].
  rewrite Htable in PreH1, PreH40.
  unfold unsigned_last_nbits in PreH1, PreH40.
  rewrite Z.mod_small in PreH1 by (split; lia).
  rewrite Z.mod_small in PreH40 by (split; lia).
  assert (Hlast_value :
    Znth last ns 0 = Znth (pos_2 + Zlength ns - 1) hs 0).
  { rewrite <- PreH4.
    rewrite Znth_sublist in Hval by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hval by lia.
    exact Hval. }
  assert (Hlatest_value : forall t, last < t < Zlength ns ->
    Znth t ns 0 <> Znth (pos_2 + Zlength ns - 1) hs 0).
  { intros t Ht. rewrite <- PreH4 in Ht |- *.
    specialize (Hlatest t Ht).
    rewrite Znth_sublist in Hlatest by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hlatest by lia.
    exact Hlatest. }
  pose proof (musl_periodic_memory_skip_before hs ns bs_2 sh_2 pos_2 p mem mem0 last
    ltac:(assumption) ltac:(rewrite <- PreH4; lia)
    PreH6 ltac:(rewrite <- PreH4; lia) PreH16 PreH36
    ltac:(rewrite <- PreH4; exact PreH19)
    ltac:(rewrite <- PreH4; exact PreH20)
    ltac:(rewrite <- PreH4; exact Hlast) Hlast_value Hlatest_value
    ltac:(rewrite <- PreH4; lia) PreH15) as Hskip.
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+mem) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH36 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + mem) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + mem).
  split_pure_spatial.
  - rewrite PreH2, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + mem * 1) with (h_pre + pos_2 + mem) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) mem (end__2 - pos_2) (sublist pos_2 end__2 hs)).
    assert (Hprefix_part :
      sublist 0 mem (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + mem) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix_part :
      sublist mem (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + mem) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix_part, Hsuffix_part.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) mem
        (sublist pos_2 (pos_2 + mem) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + mem)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + mem) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) mem
          (sublist pos_2 (pos_2 + mem) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + mem)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + mem) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + mem - pos_2) with mem in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + mem) hs)
      with (sublist 0 (pos_2 + mem) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + mem * 1) with
      (h_pre + pos_2 * 1 + mem) by lia.
    replace (end__2 - pos_2 - mem) with
      (end__2 - (pos_2 + mem)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH2, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_5 : twoway_strstr_entail_wit_18_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH2 PreH3 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  replace (8 * 8) with 64 in PreH38 by lia.
  rewrite Z.quot_div_nonneg in PreH38 by lia.
  rewrite Z.rem_mod_nonneg in PreH38 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage18; [lia | exact PreH38]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Htable]]]].
  rewrite Htable in PreH1, PreH39.
  unfold unsigned_last_nbits in PreH1, PreH39.
  rewrite Z.mod_small in PreH1 by (split; lia).
  rewrite Z.mod_small in PreH39 by (split; lia).
  assert (Hlast_value :
    Znth last ns 0 = Znth (pos_2 + Zlength ns - 1) hs 0).
  { rewrite <- PreH4.
    rewrite Znth_sublist in Hval by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hval by lia.
    exact Hval. }
  assert (Hlatest_value : forall t, last < t < Zlength ns ->
    Znth t ns 0 <> Znth (pos_2 + Zlength ns - 1) hs 0).
  { intros t Ht. rewrite <- PreH4 in Ht |- *.
    specialize (Hlatest t Ht).
    rewrite Znth_sublist in Hlatest by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hlatest by lia.
    exact Hlatest. }
  pose proof (musl_periodic_memory_skip_before hs ns bs_2 sh_2 pos_2 p mem mem0 last
    ltac:(assumption) ltac:(rewrite <- PreH4; lia)
    PreH6 ltac:(rewrite <- PreH4; lia) PreH16 PreH35
    ltac:(rewrite <- PreH4; exact PreH19)
    ltac:(rewrite <- PreH4; exact PreH20)
    ltac:(rewrite <- PreH4; exact Hlast) Hlast_value Hlatest_value
    ltac:(rewrite <- PreH4; lia) PreH15) as Hskip.
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+mem) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH35 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + mem) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + mem).
  split_pure_spatial.
  - rewrite PreH2, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + mem * 1) with (h_pre + pos_2 + mem) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) mem (end__2 - pos_2) (sublist pos_2 end__2 hs)).
    assert (Hprefix_part :
      sublist 0 mem (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + mem) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix_part :
      sublist mem (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + mem) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix_part, Hsuffix_part.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) mem
        (sublist pos_2 (pos_2 + mem) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + mem)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + mem) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) mem
          (sublist pos_2 (pos_2 + mem) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + mem)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + mem) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + mem - pos_2) with mem in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + mem) hs)
      with (sublist 0 (pos_2 + mem) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + mem * 1) with
      (h_pre + pos_2 * 1 + mem) by lia.
    replace (end__2 - pos_2 - mem) with
      (end__2 - (pos_2 + mem)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH2, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_6 : twoway_strstr_entail_wit_18_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH2 PreH3 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  replace (8 * 8) with 64 in PreH38 by lia.
  rewrite Z.quot_div_nonneg in PreH38 by lia.
  rewrite Z.rem_mod_nonneg in PreH38 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage18; [lia | exact PreH38]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Htable]]]].
  rewrite Htable in PreH1, PreH39.
  unfold unsigned_last_nbits in PreH1, PreH39.
  rewrite Z.mod_small in PreH1 by (split; lia).
  rewrite Z.mod_small in PreH39 by (split; lia).
  assert (Hlast_value :
    Znth last ns 0 = Znth (pos_2 + Zlength ns - 1) hs 0).
  { rewrite <- PreH4.
    rewrite Znth_sublist in Hval by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hval by lia.
    exact Hval. }
  assert (Hlatest_value : forall t, last < t < Zlength ns ->
    Znth t ns 0 <> Znth (pos_2 + Zlength ns - 1) hs 0).
  { intros t Ht. rewrite <- PreH4 in Ht |- *.
    specialize (Hlatest t Ht).
    rewrite Znth_sublist in Hlatest by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hlatest by lia.
    exact Hlatest. }
  pose proof (musl_periodic_memory_skip_before hs ns bs_2 sh_2 pos_2 p mem mem0 last
    ltac:(assumption) ltac:(rewrite <- PreH4; lia)
    PreH6 ltac:(rewrite <- PreH4; lia) PreH16 PreH35
    ltac:(rewrite <- PreH4; exact PreH19)
    ltac:(rewrite <- PreH4; exact PreH20)
    ltac:(rewrite <- PreH4; exact Hlast) Hlast_value Hlatest_value
    ltac:(rewrite <- PreH4; lia) PreH15) as Hskip.
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+mem) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH35 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + mem) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + mem).
  split_pure_spatial.
  - rewrite PreH2, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + mem * 1) with (h_pre + pos_2 + mem) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) mem (end__2 - pos_2) (sublist pos_2 end__2 hs)).
    assert (Hprefix_part :
      sublist 0 mem (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + mem) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix_part :
      sublist mem (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + mem) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix_part, Hsuffix_part.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) mem
        (sublist pos_2 (pos_2 + mem) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + mem)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + mem) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) mem
          (sublist pos_2 (pos_2 + mem) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + mem)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + mem) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + mem - pos_2) with mem in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + mem) hs)
      with (sublist 0 (pos_2 + mem) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + mem * 1) with
      (h_pre + pos_2 * 1 + mem) by lia.
    replace (end__2 - pos_2 - mem) with
      (end__2 - (pos_2 + mem)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH2, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_7 : twoway_strstr_entail_wit_18_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH2 PreH3 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  replace (8 * 8) with 64 in PreH39 by lia.
  rewrite Z.quot_div_nonneg in PreH39 by lia.
  rewrite Z.rem_mod_nonneg in PreH39 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage18; [lia | exact PreH39]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Htable]]]].
  rewrite Htable in PreH1, PreH40.
  unfold unsigned_last_nbits in PreH1, PreH40.
  rewrite Z.mod_small in PreH1 by (split; lia).
  rewrite Z.mod_small in PreH40 by (split; lia).
  assert (Hlast_value :
    Znth last ns 0 = Znth (pos_2 + Zlength ns - 1) hs 0).
  { rewrite <- PreH4.
    rewrite Znth_sublist in Hval by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hval by lia.
    exact Hval. }
  assert (Hlatest_value : forall t, last < t < Zlength ns ->
    Znth t ns 0 <> Znth (pos_2 + Zlength ns - 1) hs 0).
  { intros t Ht. rewrite <- PreH4 in Ht |- *.
    specialize (Hlatest t Ht).
    rewrite Znth_sublist in Hlatest by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hlatest by lia.
    exact Hlatest. }
  set (d := l - (last + 1)).
  assert (Hstep : unsigned_last_nbits
      (l - Znth (Znth (l - 1) (sublist pos_2 end__2 hs) 0) sh_2 0) 64 = d).
  { unfold d, unsigned_last_nbits. rewrite Htable.
    rewrite Z.mod_small by (split; lia). reflexivity. }
  assert (Hskip : no_match_before hs ns (pos_2 + d)).
  { eapply (musl_table_skip_before hs ns bs_2 sh_2 pos_2 d).
    - eassumption.
    - rewrite <- PreH4; lia.
    - rewrite <- PreH4; exact PreH19.
    - rewrite <- PreH4; exact PreH20.
    - lia.
    - rewrite <- PreH4; lia.
    - unfold musl_distance. rewrite <- PreH4.
      assert (Hc : Znth (pos_2 + l - 1) hs 0 =
        Znth (l - 1) (sublist pos_2 end__2 hs) 0).
      { rewrite Znth_sublist by lia. f_equal; lia. }
      rewrite Hc, Hhit, Htable. unfold d; reflexivity.
    - unfold d; lia.
    - exact PreH15. }
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+d) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH36 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + d) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + d).
  split_pure_spatial.
  - rewrite Hstep, PreH2, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + d * 1) with (h_pre + pos_2 + d) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) d (end__2 - pos_2) (sublist pos_2 end__2 hs)).
    assert (Hprefix_part :
      sublist 0 d (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + d) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix_part :
      sublist d (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + d) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix_part, Hsuffix_part.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) d
        (sublist pos_2 (pos_2 + d) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + d)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + d) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) d
          (sublist pos_2 (pos_2 + d) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + d)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + d) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + d - pos_2) with d in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + d) hs)
      with (sublist 0 (pos_2 + d) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + d * 1) with
      (h_pre + pos_2 * 1 + d) by lia.
    replace (end__2 - pos_2 - d) with
      (end__2 - (pos_2 + d)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar, ?Hstep;
      try lia; try assumption; try (rewrite PreH2, sizeof_uchar; lia).
Qed.



Lemma proof_of_twoway_strstr_entail_wit_18_8 : twoway_strstr_entail_wit_18_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH2 PreH3 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  replace (8 * 8) with 64 in PreH39 by lia.
  rewrite Z.quot_div_nonneg in PreH39 by lia.
  rewrite Z.rem_mod_nonneg in PreH39 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage18; [lia | exact PreH39]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Htable]]]].
  rewrite Htable in PreH1, PreH40.
  unfold unsigned_last_nbits in PreH1, PreH40.
  rewrite Z.mod_small in PreH1 by (split; lia).
  rewrite Z.mod_small in PreH40 by (split; lia).
  assert (Hlast_value :
    Znth last ns 0 = Znth (pos_2 + Zlength ns - 1) hs 0).
  { rewrite <- PreH4.
    rewrite Znth_sublist in Hval by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hval by lia.
    exact Hval. }
  assert (Hlatest_value : forall t, last < t < Zlength ns ->
    Znth t ns 0 <> Znth (pos_2 + Zlength ns - 1) hs 0).
  { intros t Ht. rewrite <- PreH4 in Ht |- *.
    specialize (Hlatest t Ht).
    rewrite Znth_sublist in Hlatest by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hlatest by lia.
    exact Hlatest. }
  set (d := l - (last + 1)).
  assert (Hstep : unsigned_last_nbits
      (l - Znth (Znth (l - 1) (sublist pos_2 end__2 hs) 0) sh_2 0) 64 = d).
  { unfold d, unsigned_last_nbits. rewrite Htable.
    rewrite Z.mod_small by (split; lia). reflexivity. }
  assert (Hskip : no_match_before hs ns (pos_2 + d)).
  { eapply (musl_table_skip_before hs ns bs_2 sh_2 pos_2 d).
    - eassumption.
    - rewrite <- PreH4; lia.
    - rewrite <- PreH4; exact PreH19.
    - rewrite <- PreH4; exact PreH20.
    - lia.
    - rewrite <- PreH4; lia.
    - unfold musl_distance. rewrite <- PreH4.
      assert (Hc : Znth (pos_2 + l - 1) hs 0 =
        Znth (l - 1) (sublist pos_2 end__2 hs) 0).
      { rewrite Znth_sublist by lia. f_equal; lia. }
      rewrite Hc, Hhit, Htable. unfold d; reflexivity.
    - unfold d; lia.
    - exact PreH15. }
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+d) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH36 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + d) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + d).
  split_pure_spatial.
  - rewrite Hstep, PreH2, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + d * 1) with (h_pre + pos_2 + d) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) d (end__2 - pos_2) (sublist pos_2 end__2 hs)).
    assert (Hprefix_part :
      sublist 0 d (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + d) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix_part :
      sublist d (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + d) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix_part, Hsuffix_part.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) d
        (sublist pos_2 (pos_2 + d) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + d)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + d) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) d
          (sublist pos_2 (pos_2 + d) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + d)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + d) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + d - pos_2) with d in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + d) hs)
      with (sublist 0 (pos_2 + d) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + d * 1) with
      (h_pre + pos_2 * 1 + d) by lia.
    replace (end__2 - pos_2 - d) with
      (end__2 - (pos_2 + d)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar, ?Hstep;
      try lia; try assumption; try (rewrite PreH2, sizeof_uchar; lia).
Qed.



Lemma proof_of_twoway_strstr_entail_wit_18_9 : twoway_strstr_entail_wit_18_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH2 PreH3 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  replace (8 * 8) with 64 in PreH38 by lia.
  rewrite Z.quot_div_nonneg in PreH38 by lia.
  rewrite Z.rem_mod_nonneg in PreH38 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage18; [lia | exact PreH38]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Htable]]]].
  rewrite Htable in PreH1, PreH39.
  unfold unsigned_last_nbits in PreH1, PreH39.
  rewrite Z.mod_small in PreH1 by (split; lia).
  rewrite Z.mod_small in PreH39 by (split; lia).
  assert (Hlast_value :
    Znth last ns 0 = Znth (pos_2 + Zlength ns - 1) hs 0).
  { rewrite <- PreH4.
    rewrite Znth_sublist in Hval by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hval by lia.
    exact Hval. }
  assert (Hlatest_value : forall t, last < t < Zlength ns ->
    Znth t ns 0 <> Znth (pos_2 + Zlength ns - 1) hs 0).
  { intros t Ht. rewrite <- PreH4 in Ht |- *.
    specialize (Hlatest t Ht).
    rewrite Znth_sublist in Hlatest by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hlatest by lia.
    exact Hlatest. }
  set (d := l - (last + 1)).
  assert (Hstep : unsigned_last_nbits
      (l - Znth (Znth (l - 1) (sublist pos_2 end__2 hs) 0) sh_2 0) 64 = d).
  { unfold d, unsigned_last_nbits. rewrite Htable.
    rewrite Z.mod_small by (split; lia). reflexivity. }
  assert (Hskip : no_match_before hs ns (pos_2 + d)).
  { eapply (musl_table_skip_before hs ns bs_2 sh_2 pos_2 d).
    - eassumption.
    - rewrite <- PreH4; lia.
    - rewrite <- PreH4; exact PreH19.
    - rewrite <- PreH4; exact PreH20.
    - lia.
    - rewrite <- PreH4; lia.
    - unfold musl_distance. rewrite <- PreH4.
      assert (Hc : Znth (pos_2 + l - 1) hs 0 =
        Znth (l - 1) (sublist pos_2 end__2 hs) 0).
      { rewrite Znth_sublist by lia. f_equal; lia. }
      rewrite Hc, Hhit, Htable. unfold d; reflexivity.
    - unfold d; lia.
    - exact PreH15. }
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+d) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH35 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + d) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + d).
  split_pure_spatial.
  - rewrite Hstep, PreH2, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + d * 1) with (h_pre + pos_2 + d) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) d (end__2 - pos_2) (sublist pos_2 end__2 hs)).
    assert (Hprefix_part :
      sublist 0 d (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + d) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix_part :
      sublist d (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + d) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix_part, Hsuffix_part.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) d
        (sublist pos_2 (pos_2 + d) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + d)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + d) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) d
          (sublist pos_2 (pos_2 + d) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + d)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + d) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + d - pos_2) with d in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + d) hs)
      with (sublist 0 (pos_2 + d) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + d * 1) with
      (h_pre + pos_2 * 1 + d) by lia.
    replace (end__2 - pos_2 - d) with
      (end__2 - (pos_2 + d)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar, ?Hstep;
      try lia; try assumption; try (rewrite PreH2, sizeof_uchar; lia).
Qed.



Lemma proof_of_twoway_strstr_entail_wit_18_10 : twoway_strstr_entail_wit_18_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH2 PreH3 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  replace (8 * 8) with 64 in PreH38 by lia.
  rewrite Z.quot_div_nonneg in PreH38 by lia.
  rewrite Z.rem_mod_nonneg in PreH38 by lia.
  let c := constr:(Znth (l - 1) (sublist pos_2 end__2 hs) 0) in
  assert (Hhit : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = true)
    by (apply bitop_hit_stage18; [lia | exact PreH38]);
  destruct (shift_hit_last_stage12 ns l bs_2 sh_2 c ltac:(lia) ltac:(lia)
    PreH19 PreH20 Hhit) as [last [Hlast [Hval [Hlatest Htable]]]].
  rewrite Htable in PreH1, PreH39.
  unfold unsigned_last_nbits in PreH1, PreH39.
  rewrite Z.mod_small in PreH1 by (split; lia).
  rewrite Z.mod_small in PreH39 by (split; lia).
  assert (Hlast_value :
    Znth last ns 0 = Znth (pos_2 + Zlength ns - 1) hs 0).
  { rewrite <- PreH4.
    rewrite Znth_sublist in Hval by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hval by lia.
    exact Hval. }
  assert (Hlatest_value : forall t, last < t < Zlength ns ->
    Znth t ns 0 <> Znth (pos_2 + Zlength ns - 1) hs 0).
  { intros t Ht. rewrite <- PreH4 in Ht |- *.
    specialize (Hlatest t Ht).
    rewrite Znth_sublist in Hlatest by lia.
    replace (l - 1 + pos_2) with (pos_2 + l - 1) in Hlatest by lia.
    exact Hlatest. }
  set (d := l - (last + 1)).
  assert (Hstep : unsigned_last_nbits
      (l - Znth (Znth (l - 1) (sublist pos_2 end__2 hs) 0) sh_2 0) 64 = d).
  { unfold d, unsigned_last_nbits. rewrite Htable.
    rewrite Z.mod_small by (split; lia). reflexivity. }
  assert (Hskip : no_match_before hs ns (pos_2 + d)).
  { eapply (musl_table_skip_before hs ns bs_2 sh_2 pos_2 d).
    - eassumption.
    - rewrite <- PreH4; lia.
    - rewrite <- PreH4; exact PreH19.
    - rewrite <- PreH4; exact PreH20.
    - lia.
    - rewrite <- PreH4; lia.
    - unfold musl_distance. rewrite <- PreH4.
      assert (Hc : Znth (pos_2 + l - 1) hs 0 =
        Znth (l - 1) (sublist pos_2 end__2 hs) 0).
      { rewrite Znth_sublist by lia. f_equal; lia. }
      rewrite Hc, Hhit, Htable. unfold d; reflexivity.
    - unfold d; lia.
    - exact PreH15. }
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+d) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH35 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + d) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + d).
  split_pure_spatial.
  - rewrite Hstep, PreH2, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + d * 1) with (h_pre + pos_2 + d) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) d (end__2 - pos_2) (sublist pos_2 end__2 hs)).
    assert (Hprefix_part :
      sublist 0 d (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + d) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix_part :
      sublist d (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + d) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix_part, Hsuffix_part.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) d
        (sublist pos_2 (pos_2 + d) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + d)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + d) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) d
          (sublist pos_2 (pos_2 + d) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + d)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + d) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + d - pos_2) with d in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + d) hs)
      with (sublist 0 (pos_2 + d) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + d * 1) with
      (h_pre + pos_2 * 1 + d) by lia.
    replace (end__2 - pos_2 - d) with
      (end__2 - (pos_2 + d)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar, ?Hstep;
      try lia; try assumption; try (rewrite PreH2, sizeof_uchar; lia).
Qed.



Lemma proof_of_twoway_strstr_entail_wit_18_11 : twoway_strstr_entail_wit_18_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (8 * 8) with 64 in PreH38 by lia.
  rewrite Z.quot_div_nonneg in PreH38 by lia.
  rewrite Z.rem_mod_nonneg in PreH38 by lia.
  set (c := Znth (l - 1) (sublist pos_2 end__2 hs) 0).
  assert (Hmiss : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = false)
    by (apply bitop_miss_stage18; [lia | exact PreH38]).
  assert (Hc : c = Znth (pos_2 + l - 1) hs 0).
  { unfold c. rewrite Znth_sublist by lia. f_equal. lia. }
  assert (Hskip : no_match_before hs ns (pos_2 + l)).
  { eapply (musl_table_skip_before hs ns bs_2 sh_2 pos_2 l).
    - eassumption.
    - rewrite <- PreH3; lia.
    - rewrite <- PreH3; exact PreH18.
    - rewrite <- PreH3; exact PreH19.
    - lia.
    - rewrite <- PreH3; lia.
    - unfold musl_distance. rewrite <- PreH3, <- Hc, Hmiss. reflexivity.
    - lia.
    - exact PreH14. }
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+l) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH35 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + l) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + l).
  split_pure_spatial.
  - rewrite PreH1, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + l * 1) with (h_pre + pos_2 + l) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) l (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 l (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + l) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist l (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + l) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) l
        (sublist pos_2 (pos_2 + l) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + l)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + l) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) l
          (sublist pos_2 (pos_2 + l) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + l)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + l) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + l - pos_2) with l in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + l) hs)
      with (sublist 0 (pos_2 + l) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + l * 1) with
      (h_pre + pos_2 * 1 + l) by lia.
    replace (end__2 - pos_2 - l) with (end__2 - (pos_2 + l)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH1, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_12 : twoway_strstr_entail_wit_18_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (8 * 8) with 64 in PreH38 by lia.
  rewrite Z.quot_div_nonneg in PreH38 by lia.
  rewrite Z.rem_mod_nonneg in PreH38 by lia.
  set (c := Znth (l - 1) (sublist pos_2 end__2 hs) 0).
  assert (Hmiss : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = false)
    by (apply bitop_miss_stage18; [lia | exact PreH38]).
  assert (Hc : c = Znth (pos_2 + l - 1) hs 0).
  { unfold c. rewrite Znth_sublist by lia. f_equal. lia. }
  assert (Hskip : no_match_before hs ns (pos_2 + l)).
  { eapply (musl_table_skip_before hs ns bs_2 sh_2 pos_2 l).
    - eassumption.
    - rewrite <- PreH3; lia.
    - rewrite <- PreH3; exact PreH18.
    - rewrite <- PreH3; exact PreH19.
    - lia.
    - rewrite <- PreH3; lia.
    - unfold musl_distance. rewrite <- PreH3, <- Hc, Hmiss. reflexivity.
    - lia.
    - exact PreH14. }
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+l) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH35 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + l) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + l).
  split_pure_spatial.
  - rewrite PreH1, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + l * 1) with (h_pre + pos_2 + l) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) l (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 l (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + l) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist l (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + l) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) l
        (sublist pos_2 (pos_2 + l) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + l)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + l) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) l
          (sublist pos_2 (pos_2 + l) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + l)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + l) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + l - pos_2) with l in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + l) hs)
      with (sublist 0 (pos_2 + l) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + l * 1) with
      (h_pre + pos_2 * 1 + l) by lia.
    replace (end__2 - pos_2 - l) with (end__2 - (pos_2 + l)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH1, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_13 : twoway_strstr_entail_wit_18_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (8 * 8) with 64 in PreH37 by lia.
  rewrite Z.quot_div_nonneg in PreH37 by lia.
  rewrite Z.rem_mod_nonneg in PreH37 by lia.
  set (c := Znth (l - 1) (sublist pos_2 end__2 hs) 0).
  assert (Hmiss : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = false)
    by (apply bitop_miss_stage18; [lia | exact PreH37]).
  assert (Hc : c = Znth (pos_2 + l - 1) hs 0).
  { unfold c. rewrite Znth_sublist by lia. f_equal. lia. }
  assert (Hskip : no_match_before hs ns (pos_2 + l)).
  { eapply (musl_table_skip_before hs ns bs_2 sh_2 pos_2 l).
    - eassumption.
    - rewrite <- PreH3; lia.
    - rewrite <- PreH3; exact PreH18.
    - rewrite <- PreH3; exact PreH19.
    - lia.
    - rewrite <- PreH3; lia.
    - unfold musl_distance. rewrite <- PreH3, <- Hc, Hmiss. reflexivity.
    - lia.
    - exact PreH14. }
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+l) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH34 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + l) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + l).
  split_pure_spatial.
  - rewrite PreH1, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + l * 1) with (h_pre + pos_2 + l) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) l (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 l (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + l) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist l (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + l) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) l
        (sublist pos_2 (pos_2 + l) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + l)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + l) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) l
          (sublist pos_2 (pos_2 + l) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + l)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + l) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + l - pos_2) with l in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + l) hs)
      with (sublist 0 (pos_2 + l) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + l * 1) with
      (h_pre + pos_2 * 1 + l) by lia.
    replace (end__2 - pos_2 - l) with (end__2 - (pos_2 + l)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH1, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_14 : twoway_strstr_entail_wit_18_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (8 * 8) with 64 in PreH37 by lia.
  rewrite Z.quot_div_nonneg in PreH37 by lia.
  rewrite Z.rem_mod_nonneg in PreH37 by lia.
  set (c := Znth (l - 1) (sublist pos_2 end__2 hs) 0).
  assert (Hmiss : Z.testbit (Znth (c / 64) bs_2 0) (c mod 64) = false)
    by (apply bitop_miss_stage18; [lia | exact PreH37]).
  assert (Hc : c = Znth (pos_2 + l - 1) hs 0).
  { unfold c. rewrite Znth_sublist by lia. f_equal. lia. }
  assert (Hskip : no_match_before hs ns (pos_2 + l)).
  { eapply (musl_table_skip_before hs ns bs_2 sh_2 pos_2 l).
    - eassumption.
    - rewrite <- PreH3; lia.
    - rewrite <- PreH3; exact PreH18.
    - rewrite <- PreH3; exact PreH19.
    - lia.
    - rewrite <- PreH3; lia.
    - unfold musl_distance. rewrite <- PreH3, <- Hc, Hmiss. reflexivity.
    - lia.
    - exact PreH14. }
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+l) 0).
  { eapply search_cursor_skip; [lia| |eassumption].
    eapply cursor_before_valid_skip; try (unfold d; lia); try lia; [|exact Hskip].
    intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
    rewrite Hnil, Zlength_nil in Hpositive; lia. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH34 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + l) 0 0).
  { unfold matched_range. intros. lia. }
  Exists sh_2 bs_2 end__2 (pos_2 + l).
  split_pure_spatial.
  - rewrite PreH1, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + l * 1) with (h_pre + pos_2 + l) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) l (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 l (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + l) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist l (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + l) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) l
        (sublist pos_2 (pos_2 + l) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + l)
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + l) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) l
          (sublist pos_2 (pos_2 + l) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + l)
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + l) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + l - pos_2) with l in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + l) hs)
      with (sublist 0 (pos_2 + l) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + l * 1) with
      (h_pre + pos_2 * 1 + l) by lia.
    replace (end__2 - pos_2 - l) with (end__2 - (pos_2 + l)) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar;
      try lia; try assumption; try (rewrite PreH1, sizeof_uchar; lia).
Qed.

Lemma proof_of_twoway_strstr_entail_wit_18_15 : twoway_strstr_entail_wit_18_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH3 PreH4 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  assert (Hsplit : unsigned_last_nbits (ms + 1) 64 = 0).
  { subst ms. vm_compute. reflexivity. }
  assert (Hklt : k < l) by (apply PreH14; exact PreH38).
  assert (Hbound : Z.max (unsigned_last_nbits (ms + 1) 64) mem <= k)
    by exact (proj1 PreH17).
  assert (Hstep : unsigned_last_nbits (k - ms) 64 = k + 1).
  { subst ms. unfold unsigned_last_nbits.
    change (2 ^ 64) with 18446744073709551616.
    symmetry. apply Z.mod_unique with (q := -1); [left; lia | ring]. }
  assert (Hmismatch : Znth k ns 0 <> Znth (pos_2 + k) hs 0).
  { rewrite app_Znth1 in PreH1 by lia.
    rewrite Znth_sublist in PreH1 by lia.
    replace (k + pos_2) with (pos_2 + k) in PreH1 by lia.
    exact PreH1. }
  pose proof (original_right_mismatch_skip hs ns pos_2
    (unsigned_last_nbits (ms + 1) 64) p mem k
    PreH15 PreH6 ltac:(rewrite <- PreH5; lia)
    ltac:(rewrite Hsplit; lia) ltac:(rewrite <- PreH5; lia)
    PreH31 PreH16 PreH17 Hmismatch PreH36) as Hskip.
  replace (pos_2 + k - unsigned_last_nbits (ms + 1) 64 + 1) with
    (pos_2 + (k + 1)) in Hskip by (rewrite Hsplit; lia).
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+(k+1)) 0).
  { replace (pos_2+(k+1)) with
      (pos_2+k-unsigned_last_nbits (ms+1) 64+1) by (rewrite Hsplit; lia).
    eapply search_right_mismatch; [lia|unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond; exact Hmismatch|eassumption]. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH35 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + (k + 1)) 0 0).
  { unfold matched_range. intros. lia. }
  assert (Hptr :
    h + unsigned_last_nbits (k - ms) 64 * sizeof(UCHAR) =
    h_pre + (pos_2 + (k + 1)) * sizeof(UCHAR)).
  { rewrite Hstep, PreH3, sizeof_uchar. lia. }
  rewrite Hstep, sizeof_uchar in Hptr.
  Exists sh_2 bs_2 end__2 (pos_2 + (k + 1)).
  split_pure_spatial.
  - rewrite PreH3, Hstep, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + (k + 1) * 1) with
      (h_pre + pos_2 + (k + 1)) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) (k + 1) (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 (k + 1) (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + (k + 1)) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist (k + 1) (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + (k + 1)) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) (k + 1)
        (sublist pos_2 (pos_2 + (k + 1)) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + (k + 1))
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + (k + 1)) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) (k + 1)
          (sublist pos_2 (pos_2 + (k + 1)) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + (k + 1))
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + (k + 1)) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + (k + 1) - pos_2) with (k + 1) in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + (k + 1)) hs)
      with (sublist 0 (pos_2 + (k + 1)) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + (k + 1) * 1) with
      (h_pre + pos_2 * 1 + (k + 1)) by lia.
    replace (end__2 - pos_2 - (k + 1)) with
      (end__2 - (pos_2 + (k + 1))) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar, ?Hstep;
      try lia; try assumption; try (rewrite PreH3, Hstep, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_16 : twoway_strstr_entail_wit_18_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH3 PreH4 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  assert (Hsplit : unsigned_last_nbits (ms + 1) 64 = 0).
  { subst ms. vm_compute. reflexivity. }
  assert (Hklt : k < l) by (apply PreH14; exact PreH38).
  assert (Hbound : Z.max (unsigned_last_nbits (ms + 1) 64) mem <= k)
    by exact (proj1 PreH17).
  assert (Hstep : unsigned_last_nbits (k - ms) 64 = k + 1).
  { subst ms. unfold unsigned_last_nbits.
    change (2 ^ 64) with 18446744073709551616.
    symmetry. apply Z.mod_unique with (q := -1); [left; lia | ring]. }
  assert (Hmismatch : Znth k ns 0 <> Znth (pos_2 + k) hs 0).
  { rewrite app_Znth1 in PreH1 by lia.
    rewrite Znth_sublist in PreH1 by lia.
    replace (k + pos_2) with (pos_2 + k) in PreH1 by lia.
    exact PreH1. }
  pose proof (original_right_mismatch_skip hs ns pos_2
    (unsigned_last_nbits (ms + 1) 64) p mem k
    PreH15 PreH6 ltac:(rewrite <- PreH5; lia)
    ltac:(rewrite Hsplit; lia) ltac:(rewrite <- PreH5; lia)
    PreH31 PreH16 PreH17 Hmismatch PreH36) as Hskip.
  replace (pos_2 + k - unsigned_last_nbits (ms + 1) 64 + 1) with
    (pos_2 + (k + 1)) in Hskip by (rewrite Hsplit; lia).
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+(k+1)) 0).
  { replace (pos_2+(k+1)) with
      (pos_2+k-unsigned_last_nbits (ms+1) 64+1) by (rewrite Hsplit; lia).
    eapply search_right_mismatch; [lia|unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond; exact Hmismatch|eassumption]. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH35 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + (k + 1)) 0 0).
  { unfold matched_range. intros. lia. }
  assert (Hptr :
    h + unsigned_last_nbits (k - ms) 64 * sizeof(UCHAR) =
    h_pre + (pos_2 + (k + 1)) * sizeof(UCHAR)).
  { rewrite Hstep, PreH3, sizeof_uchar. lia. }
  rewrite Hstep, sizeof_uchar in Hptr.
  Exists sh_2 bs_2 end__2 (pos_2 + (k + 1)).
  split_pure_spatial.
  - rewrite PreH3, Hstep, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + (k + 1) * 1) with
      (h_pre + pos_2 + (k + 1)) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) (k + 1) (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 (k + 1) (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + (k + 1)) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist (k + 1) (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + (k + 1)) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) (k + 1)
        (sublist pos_2 (pos_2 + (k + 1)) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + (k + 1))
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + (k + 1)) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) (k + 1)
          (sublist pos_2 (pos_2 + (k + 1)) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + (k + 1))
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + (k + 1)) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + (k + 1) - pos_2) with (k + 1) in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + (k + 1)) hs)
      with (sublist 0 (pos_2 + (k + 1)) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + (k + 1) * 1) with
      (h_pre + pos_2 * 1 + (k + 1)) by lia.
    replace (end__2 - pos_2 - (k + 1)) with
      (end__2 - (pos_2 + (k + 1))) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar, ?Hstep;
      try lia; try assumption; try (rewrite PreH3, Hstep, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_17 : twoway_strstr_entail_wit_18_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH3 PreH4 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  assert (Hsplit : unsigned_last_nbits (ms + 1) 64 = ms + 1).
  { unfold unsigned_last_nbits. change (2 ^ 64) with 18446744073709551616.
    apply Z.mod_small. lia. }
  assert (Hklt : k < l) by (apply PreH14; exact PreH39).
  assert (Hbound : Z.max (unsigned_last_nbits (ms + 1) 64) mem <= k)
    by exact (proj1 PreH17).
  assert (Hstep : unsigned_last_nbits (k - ms) 64 = k - ms).
  { unfold unsigned_last_nbits. change (2 ^ 64) with 18446744073709551616.
    apply Z.mod_small. split; lia. }
  assert (Hmismatch : Znth k ns 0 <> Znth (pos_2 + k) hs 0).
  { rewrite app_Znth1 in PreH1 by lia.
    rewrite Znth_sublist in PreH1 by lia.
    replace (k + pos_2) with (pos_2 + k) in PreH1 by lia.
    exact PreH1. }
  pose proof (original_right_mismatch_skip hs ns pos_2
    (unsigned_last_nbits (ms + 1) 64) p mem k
    PreH15 PreH6 ltac:(rewrite <- PreH5; lia)
    ltac:(rewrite Hsplit; lia) ltac:(rewrite <- PreH5; lia)
    PreH32 PreH16 PreH17 Hmismatch PreH37) as Hskip.
  replace (pos_2 + k - unsigned_last_nbits (ms + 1) 64 + 1) with
    (pos_2 + (k - ms)) in Hskip by (rewrite Hsplit; lia).
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+(k-ms)) 0).
  { replace (pos_2+(k-ms)) with
      (pos_2+k-unsigned_last_nbits (ms+1) 64+1) by (rewrite Hsplit; lia).
    eapply search_right_mismatch; [lia|unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond; exact Hmismatch|eassumption]. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH36 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + (k - ms)) 0 0).
  { unfold matched_range. intros. lia. }
  assert (Hptr :
    h + unsigned_last_nbits (k - ms) 64 * sizeof(UCHAR) =
    h_pre + (pos_2 + (k - ms)) * sizeof(UCHAR)).
  { rewrite Hstep, PreH3, sizeof_uchar. lia. }
  rewrite Hstep, sizeof_uchar in Hptr.
  Exists sh_2 bs_2 end__2 (pos_2 + (k - ms)).
  split_pure_spatial.
  - rewrite PreH3, Hstep, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + (k - ms) * 1) with
      (h_pre + pos_2 + (k - ms)) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) (k - ms) (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 (k - ms) (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + (k - ms)) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist (k - ms) (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + (k - ms)) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) (k - ms)
        (sublist pos_2 (pos_2 + (k - ms)) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + (k - ms))
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + (k - ms)) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) (k - ms)
          (sublist pos_2 (pos_2 + (k - ms)) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + (k - ms))
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + (k - ms)) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + (k - ms) - pos_2) with (k - ms) in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + (k - ms)) hs)
      with (sublist 0 (pos_2 + (k - ms)) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + (k - ms) * 1) with
      (h_pre + pos_2 * 1 + (k - ms)) by lia.
    replace (end__2 - pos_2 - (k - ms)) with
      (end__2 - (pos_2 + (k - ms))) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar, ?Hstep;
      try lia; try assumption; try (rewrite PreH3, Hstep, sizeof_uchar; lia).
Qed.


Lemma proof_of_twoway_strstr_entail_wit_18_18 : twoway_strstr_entail_wit_18_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (strstr_array_length64__cut_probe n_pre ns). Intros_p Hlenns.
  prop_apply_p (split_hay_length64__cut_probe
    h_pre h z hs pos_2 end__2 PreH3 PreH4 ltac:(lia) ltac:(lia)).
  Intros_p Hlenhs.
  assert (Hsplit : unsigned_last_nbits (ms + 1) 64 = ms + 1).
  { unfold unsigned_last_nbits. change (2 ^ 64) with 18446744073709551616.
    apply Z.mod_small. lia. }
  assert (Hklt : k < l) by (apply PreH14; exact PreH39).
  assert (Hbound : Z.max (unsigned_last_nbits (ms + 1) 64) mem <= k)
    by exact (proj1 PreH17).
  assert (Hstep : unsigned_last_nbits (k - ms) 64 = k - ms).
  { unfold unsigned_last_nbits. change (2 ^ 64) with 18446744073709551616.
    apply Z.mod_small. split; lia. }
  assert (Hmismatch : Znth k ns 0 <> Znth (pos_2 + k) hs 0).
  { rewrite app_Znth1 in PreH1 by lia.
    rewrite Znth_sublist in PreH1 by lia.
    replace (k + pos_2) with (pos_2 + k) in PreH1 by lia.
    exact PreH1. }
  pose proof (original_right_mismatch_skip hs ns pos_2
    (unsigned_last_nbits (ms + 1) 64) p mem k
    PreH15 PreH6 ltac:(rewrite <- PreH5; lia)
    ltac:(rewrite Hsplit; lia) ltac:(rewrite <- PreH5; lia)
    PreH32 PreH16 PreH17 Hmismatch PreH37) as Hskip.
  replace (pos_2 + k - unsigned_last_nbits (ms + 1) 64 + 1) with
    (pos_2 + (k - ms)) in Hskip by (rewrite Hsplit; lia).
  assert (Hcursor : search_cursor hs ns (unsigned_last_nbits (ms+1) 64)
    p mem0 (pos_2+(k-ms)) 0).
  { replace (pos_2+(k-ms)) with
      (pos_2+k-unsigned_last_nbits (ms+1) 64+1) by (rewrite Hsplit; lia).
    eapply search_right_mismatch; [lia|unfold SimpleC.EE.stdlib.musl.monad.two_way_rel_lib.match_cond; exact Hmismatch|eassumption]. }
  assert (Hmemory : periodic_memory_state ns p 0 mem0).
  { unfold periodic_memory_state in *.
    destruct PreH36 as [_ [Hr Hp]].
    split; [left; reflexivity | split; assumption]. }
  assert (Hmatched : matched_range hs ns (pos_2 + (k - ms)) 0 0).
  { unfold matched_range. intros. lia. }
  assert (Hptr :
    h + unsigned_last_nbits (k - ms) 64 * sizeof(UCHAR) =
    h_pre + (pos_2 + (k - ms)) * sizeof(UCHAR)).
  { rewrite Hstep, PreH3, sizeof_uchar. lia. }
  rewrite Hstep, sizeof_uchar in Hptr.
  Exists sh_2 bs_2 end__2 (pos_2 + (k - ms)).
  split_pure_spatial.
  - rewrite PreH3, Hstep, sizeof_uchar.
    replace (h_pre + pos_2 * 1) with (h_pre + pos_2) by lia.
    replace (h_pre + pos_2 + (k - ms) * 1) with
      (h_pre + pos_2 + (k - ms)) by lia.
    sep_apply (UCharArray.full_split_to_full
      (h_pre + pos_2) (k - ms) (end__2 - pos_2)
      (sublist pos_2 end__2 hs)).
    assert (Hprefix :
      sublist 0 (k - ms) (sublist pos_2 end__2 hs) =
      sublist pos_2 (pos_2 + (k - ms)) hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    assert (Hsuffix :
      sublist (k - ms) (end__2 - pos_2) (sublist pos_2 end__2 hs) =
      sublist (pos_2 + (k - ms)) end__2 hs).
    { rewrite Zsublist_Zsublist by lia. f_equal; lia. }
    rewrite Hprefix, Hsuffix.
    replace (h_pre + pos_2) with
      (h_pre + pos_2 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    assert (Hmerge :
      UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) (k - ms)
        (sublist pos_2 (pos_2 + (k - ms)) hs) **
      UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs)
      |-- UCharArray.full h_pre (pos_2 + (k - ms))
        (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + (k - ms)) hs)).
    { apply derivable1_trans with (y :=
        UCharArray.full h_pre pos_2 (sublist 0 pos_2 hs) **
        UCharArray.full (h_pre + pos_2 * sizeof(UCHAR)) (k - ms)
          (sublist pos_2 (pos_2 + (k - ms)) hs)).
      - cancel.
      - pose proof (UCharArray.full_merge_to_full
          h_pre pos_2 (pos_2 + (k - ms))
          (sublist 0 pos_2 hs) (sublist pos_2 (pos_2 + (k - ms)) hs)
          ltac:(lia)) as Hbase.
        replace (pos_2 + (k - ms) - pos_2) with (k - ms) in Hbase by lia.
        exact Hbase. }
    sep_apply Hmerge.
    replace (sublist 0 pos_2 hs ++ sublist pos_2 (pos_2 + (k - ms)) hs)
      with (sublist 0 (pos_2 + (k - ms)) hs).
    2:{ rewrite <- sublist_split by lia. reflexivity. }
    rewrite sizeof_uchar.
    replace (h_pre + pos_2 * 1 + (k - ms) * 1) with
      (h_pre + pos_2 * 1 + (k - ms)) by lia.
    replace (end__2 - pos_2 - (k - ms)) with
      (end__2 - (pos_2 + (k - ms))) by lia.
    cancel. all: try entailer!.
  - split_pures; dump_pre_spatial; rewrite ?sizeof_uchar, ?Hstep;
      try lia; try assumption; try (rewrite PreH3, Hstep, sizeof_uchar; lia).
Qed.




Lemma terminated_before_needle_no_result_stage19 :
  forall hs ns base l,
    Znth l (hs ++ [0]) 0 = 0 ->
    Znth l (ns ++ [0]) 0 <> 0 ->
    0 <= l -> l <= Zlength ns -> l <= Zlength hs ->
    nonzero_bytes hs ->
    strstr_result hs ns base 0.
Proof.
  intros hs ns base l Hhay Hneedle Hl Hlns Hlhs Hnonzero.
  assert (Hhaylen : l = Zlength hs).
  { destruct (Z.eq_dec l (Zlength hs)) as [Heq|Hne]; [exact Heq|].
    assert (Hlt : l < Zlength hs) by lia.
    rewrite app_Znth1 in Hhay by lia.
    unfold nonzero_bytes in Hnonzero.
    apply Forall_forall with (x := Znth l hs 0) in Hnonzero.
    2:{ unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
        rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. exact Hlt. }
    cbn in Hnonzero. lia. }
  assert (Hneedlelen : l < Zlength ns).
  { destruct (Z.eq_dec l (Zlength ns)) as [Heq|Hne]; [|lia].
    exfalso. apply Hneedle. subst l. rewrite Heq.
    rewrite app_Znth2 by lia.
    replace (Zlength ns - Zlength ns) with 0 by lia. reflexivity. }
  unfold strstr_result. left. split; [reflexivity|].
  intros i Hmatch. unfold substring_at in Hmatch.
  destruct Hmatch as [Hi [Hwindow Hsub]]. lia.
Qed.

Lemma merge_hay_stage19 :
  forall h_pre h z hs pos end_,
    h = h_pre + pos * sizeof(UCHAR) ->
    z = h_pre + end_ * sizeof(UCHAR) ->
    0 <= pos <= end_ -> end_ <= Zlength hs ->
    UCharArray.full h_pre pos (sublist 0 pos hs) **
    (UCharArray.full h (end_ - pos) (sublist pos end_ hs) **
     UCharArray.full z (Zlength (sublist end_ (Zlength hs) hs) + 1)
       (sublist end_ (Zlength hs) hs ++ [0]))
    |-- UCharArray.full h_pre (Zlength hs + 1) (hs ++ [0]).
Proof.
  intros h_pre h z hs pos end_ Hh Hz Hpos Hend.
  rewrite Hh, Hz, sizeof_uchar.
  assert (Hsuflen : Zlength (sublist end_ (Zlength hs) hs) =
      Zlength hs - end_) by (rewrite Zlength_sublist; lia).
  rewrite Hsuflen.
  replace (h_pre + end_ * 1) with
    (h_pre + pos * 1 + (end_ - pos) * sizeof(UCHAR))
    by (rewrite sizeof_uchar; lia).
  replace (Zlength hs - end_ + 1) with
    (Zlength hs + 1 - pos - (end_ - pos)) by lia.
  sep_apply (UCharArray.full_merge_to_full
    (h_pre + pos * 1) (end_ - pos) (Zlength hs + 1 - pos)
    (sublist pos end_ hs)
    (sublist end_ (Zlength hs) hs ++ [0])).
  all: try lia.
  replace (sublist pos end_ hs ++ (sublist end_ (Zlength hs) hs ++ [0]))
    with (sublist pos (Zlength hs) hs ++ [0]).
  2:{ rewrite app_assoc.
      rewrite <- (sublist_split pos (Zlength hs) end_ hs) by lia.
      reflexivity. }
  sep_apply (UCharArray.full_merge_to_full h_pre pos (Zlength hs + 1)
    (sublist 0 pos hs) (sublist pos (Zlength hs) hs ++ [0])).
  replace (sublist 0 pos hs ++ (sublist pos (Zlength hs) hs ++ [0]))
    with (hs ++ [0]).
  2:{ rewrite app_assoc.
      rewrite <- (sublist_split 0 (Zlength hs) pos hs) by lia.
      rewrite sublist_self by lia. reflexivity. }
  cancel. all: try entailer!.
Qed.

Lemma merge_hay_reordered_stage19 :
  forall h_pre h z hs pos end_,
    h = h_pre + pos * sizeof(UCHAR) ->
    z = h_pre + end_ * sizeof(UCHAR) ->
    0 <= pos <= end_ -> end_ <= Zlength hs ->
    UCharArray.full z (Zlength (sublist end_ (Zlength hs) hs) + 1)
      (sublist end_ (Zlength hs) hs ++ [0]) **
    (UCharArray.full h_pre pos (sublist 0 pos hs) **
     UCharArray.full h (end_ - pos) (sublist pos end_ hs))
    |-- UCharArray.full h_pre (Zlength hs + 1) (hs ++ [0]).
Proof.
  intros h_pre h z hs pos end_ Hh Hz Hpos Hend.
  apply derivable1_trans with (y :=
    UCharArray.full h_pre pos (sublist 0 pos hs) **
    (UCharArray.full h (end_ - pos) (sublist pos end_ hs) **
     UCharArray.full z (Zlength (sublist end_ (Zlength hs) hs) + 1)
       (sublist end_ (Zlength hs) hs ++ [0]))).
  - cancel.
  - apply merge_hay_stage19; assumption.
Qed.

Lemma proof_of_twoway_strstr_return_wit_1_split_goal_1 : twoway_strstr_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial.
  assert (Hh : h = h_pre+pos) by (rewrite sizeof_uchar in *; lia).
  rewrite Hh. eapply (search_left_result hs ns h_pre (unsigned_last_nbits (ms+1) 64) p mem0 pos mem k); [|lia|eassumption].
  intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
  rewrite Hnil, Zlength_nil in Hpositive; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_1_split_goal_spatial : twoway_strstr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_hay_stage19 h_pre h z hs pos end_); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_1 : twoway_strstr_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_twoway_strstr_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_twoway_strstr_return_wit_2_split_goal_1 : twoway_strstr_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial.
  assert (Hh : h = h_pre+pos) by (rewrite sizeof_uchar in *; lia).
  rewrite Hh. eapply (search_left_result hs ns h_pre (unsigned_last_nbits (ms+1) 64) p mem0 pos mem k); [|lia|eassumption].
  intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
  rewrite Hnil, Zlength_nil in Hpositive; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_2_split_goal_spatial : twoway_strstr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_hay_stage19 h_pre h z hs pos end_); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_2 : twoway_strstr_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_twoway_strstr_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_twoway_strstr_return_wit_3_split_goal_1 : twoway_strstr_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial.
  assert (Hh : h = h_pre+pos) by (rewrite sizeof_uchar in *; lia).
  rewrite Hh. eapply (search_left_result hs ns h_pre (unsigned_last_nbits (ms+1) 64) p mem0 pos mem k); [|lia|eassumption].
  intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
  rewrite Hnil, Zlength_nil in Hpositive; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_3_split_goal_spatial : twoway_strstr_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_hay_stage19 h_pre h z hs pos end_); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_3 : twoway_strstr_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_twoway_strstr_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_twoway_strstr_return_wit_4_split_goal_1 : twoway_strstr_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial.
  assert (Hh : h = h_pre+pos) by (rewrite sizeof_uchar in *; lia).
  rewrite Hh. eapply (search_left_result hs ns h_pre (unsigned_last_nbits (ms+1) 64) p mem0 pos mem k); [|lia|eassumption].
  intro Hnil. assert (Hpositive : 0 < Zlength ns) by lia.
  rewrite Hnil, Zlength_nil in Hpositive; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_4_split_goal_spatial : twoway_strstr_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_hay_stage19 h_pre h z hs pos end_); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_4 : twoway_strstr_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_twoway_strstr_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_twoway_strstr_return_wit_5_split_goal_1 : twoway_strstr_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial.
  eapply (cursor_remaining_none hs ns h_pre pos end_ h z retval l); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_5_split_goal_spatial : twoway_strstr_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_hay_reordered_stage19 h_pre h z hs pos end_); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_5 : twoway_strstr_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_return_wit_5_split_goal_spatial.
  - Goal_apply proof_of_twoway_strstr_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_twoway_strstr_return_wit_6_split_goal_1 : twoway_strstr_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial.
  eapply (cursor_remaining_none hs ns h_pre pos end_ h z retval l); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_6_split_goal_spatial : twoway_strstr_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_hay_reordered_stage19 h_pre h z hs pos end_); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_6 : twoway_strstr_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_return_wit_6_split_goal_spatial.
  - Goal_apply proof_of_twoway_strstr_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_twoway_strstr_return_wit_7_split_goal_1 : twoway_strstr_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial.
  eapply (cursor_remaining_none hs ns h_pre pos end_ h z retval l); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_7_split_goal_spatial : twoway_strstr_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_hay_reordered_stage19 h_pre h z hs pos end_); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_7 : twoway_strstr_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_return_wit_7_split_goal_spatial.
  - Goal_apply proof_of_twoway_strstr_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_twoway_strstr_return_wit_8_split_goal_1 : twoway_strstr_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial.
  eapply (cursor_remaining_none hs ns h_pre pos end_ h z retval l); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_8_split_goal_spatial : twoway_strstr_return_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_hay_reordered_stage19 h_pre h z hs pos end_); eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_8 : twoway_strstr_return_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_twoway_strstr_return_wit_8_split_goal_spatial.
  - Goal_apply proof_of_twoway_strstr_return_wit_8_split_goal_1.
Qed.

Lemma proof_of_twoway_strstr_return_wit_9_split_goal_1 : twoway_strstr_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (terminated_before_needle_no_result_stage19 hs ns h_pre l);
    eauto; lia.
Qed.

Lemma proof_of_twoway_strstr_return_wit_9 : twoway_strstr_return_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_twoway_strstr_return_wit_9_split_goal_1.
Qed.


Lemma proof_of_twoway_strstr_partial_solve_wit_36_pure : twoway_strstr_partial_solve_wit_36_pure.
Proof. pre_process. Exists p. entailer!.
Qed.


Lemma proof_of_twoway_strstr_partial_solve_wit_37_pure : twoway_strstr_partial_solve_wit_37_pure.
Proof. pre_process. Exists p. entailer!.
Qed.










Lemma substring_at_suffix_stage20 : forall hs ns i q,
  0 <= i <= Zlength hs -> 0 <= q ->
  (substring_at (sublist i (Zlength hs) hs) ns q <->
   substring_at hs ns (i + q)).
Proof.
  intros hs ns i q Hi Hq. pose proof (Zlength_nonneg ns). unfold substring_at.
  rewrite Zlength_sublist by lia.
  split; intros [Hq0 [Hbound Hsub]].
  - split; [lia|]. split; [lia|].
    rewrite (Zsublist_Zsublist (q + Zlength ns) (Zlength hs) q i hs)
      in Hsub by lia.
    replace (q + i) with (i + q) in Hsub by lia.
    replace (q + Zlength ns + i) with (i + q + Zlength ns) in Hsub by lia.
    exact Hsub.
  - split; [lia|]. split; [lia|].
    rewrite (Zsublist_Zsublist (q + Zlength ns) (Zlength hs) q i hs) by lia.
    replace (q + i) with (i + q) by lia.
    replace (q + Zlength ns + i) with (i + q + Zlength ns) by lia.
    exact Hsub.
Qed.

Lemma lift_suffix_result_stage20 : forall hs ns base suffix_base retval i,
  suffix_base = base + i ->
  0 <= i <= Zlength hs ->
  no_match_before hs ns i ->
  strstr_result (sublist i (Zlength hs) hs) ns suffix_base retval ->
  strstr_result hs ns base retval.
Proof.
  intros hs ns base suffix_base retval i Hbase Hi Hbefore Hresult.
  unfold strstr_result in Hresult |- *.
  destruct Hresult as [[Hzero Hnone] | [q [[Hmatch Hfirst] Hretval]]].
  - left. split; [exact Hzero|]. intros j Hjmatch.
    assert (Hj0 : 0 <= j) by (unfold substring_at in Hjmatch; lia).
    destruct (Z_lt_ge_dec j i) as [Hlt|Hge].
    + apply (Hbefore j); [lia|exact Hjmatch].
    + apply (Hnone (j - i)).
      apply (proj2 (substring_at_suffix_stage20 hs ns i (j - i) Hi ltac:(lia))).
      replace (i + (j - i)) with j by lia. exact Hjmatch.
  - right. exists (i + q). split.
    + unfold first_substring. split.
      * apply (proj1 (substring_at_suffix_stage20 hs ns i q Hi ltac:(
          unfold substring_at in Hmatch; lia))). exact Hmatch.
      * intros j Hj Hjmatch.
        destruct (Z_lt_ge_dec j i) as [Hlt|Hge].
        -- apply (Hbefore j); [lia|exact Hjmatch].
        -- apply (Hfirst (j - i)); [lia|].
           apply (proj2 (substring_at_suffix_stage20 hs ns i (j - i) Hi ltac:(lia))).
           replace (i + (j - i)) with j by lia. exact Hjmatch.
    + rewrite Hretval, Hbase. lia.
Qed.

Lemma merge_prefix_suffix_stage20 : forall hs base suffix_base i,
  suffix_base = base + i * sizeof(CHAR) ->
  0 <= i <= Zlength hs ->
  UCharArray.full suffix_base (Zlength (sublist i (Zlength hs) hs) + 1)
    (sublist i (Zlength hs) hs ++ [0]) **
  UCharArray.full base i (sublist 0 i (hs ++ [0]))
  |-- UCharArray.full base (Zlength hs + 1) (hs ++ [0]).
Proof.
  intros hs base suffix_base i Hbase Hi.
  rewrite Hbase, sizeof_char.
  rewrite Zlength_sublist by lia.
  replace (base + i * 1) with (base + i * sizeof(UCHAR)) by
    (rewrite sizeof_uchar; lia).
  replace (Zlength hs - i + 1) with (Zlength hs + 1 - i) by lia.
  replace (sublist 0 i (hs ++ [0])) with (sublist 0 i hs).
  2:{ rewrite sublist_split_app_l by lia. reflexivity. }
  sep_apply (UCharArray.full_merge_to_full base i (Zlength hs + 1)
    (sublist 0 i hs) (sublist i (Zlength hs) hs ++ [0])).
  replace (sublist 0 i hs ++ (sublist i (Zlength hs) hs ++ [0]))
    with (hs ++ [0]).
  2:{ rewrite app_assoc.
      rewrite <- (sublist_split 0 (Zlength hs) i hs) by lia.
      rewrite sublist_self by lia. reflexivity. }
  cancel. all: try entailer!.
Qed.

Lemma lift_suffix_result_sep_stage20 : forall hs ns base suffix_base retval i,
  suffix_base = base + i * sizeof(CHAR) ->
  0 <= i <= Zlength hs ->
  no_match_before hs ns i ->
  strstr_result (sublist i (Zlength hs) hs) ns suffix_base retval ->
  UCharArray.full suffix_base (Zlength (sublist i (Zlength hs) hs) + 1)
    (sublist i (Zlength hs) hs ++ [0]) **
  UCharArray.full base i (sublist 0 i (hs ++ [0]))
  |-- “ strstr_result hs ns base retval ”.
Proof.
  intros hs ns base suffix_base retval i Hbase Hi Hbefore Hresult.
  assert (Hbase' : suffix_base = base + i) by
    (rewrite Hbase, sizeof_char; lia).
  entailer!.
  eapply lift_suffix_result_stage20; eauto.
Qed.

Lemma suffix_terminated_result_stage20 : forall hay needle base t,
  Znth t (hay ++ [0]) 0 = 0 ->
  Znth t (needle ++ [0]) 0 <> 0 ->
  0 <= t -> t <= Zlength needle -> t <= Zlength hay ->
  nonzero_bytes hay ->
  strstr_result hay needle base 0.
Proof.
  intros hay needle base t Hhay Hneedle Ht Htn Hth Hnonzero.
  assert (Hhaylen : t = Zlength hay).
  { destruct (Z.eq_dec t (Zlength hay)) as [Heq|Hne]; [exact Heq|].
    assert (Hlt : t < Zlength hay) by lia.
    rewrite app_Znth1 in Hhay by lia.
    unfold nonzero_bytes in Hnonzero.
    apply Forall_forall with (x := Znth t hay 0) in Hnonzero.
    2:{ unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
        rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. exact Hlt. }
    cbn in Hnonzero. lia. }
  assert (Hneedlelen : t < Zlength needle).
  { destruct (Z.eq_dec t (Zlength needle)) as [Heq|Hne]; [|lia].
    exfalso. apply Hneedle. subst t. rewrite Heq.
    rewrite app_Znth2 by lia.
    replace (Zlength needle - Zlength needle) with 0 by lia. reflexivity. }
  unfold strstr_result. left. split; [reflexivity|].
  intros j Hmatch. unfold substring_at in Hmatch.
  destruct Hmatch as [Hj [Hwindow Hsub]]. lia.
Qed.

Lemma first_byte_exists_stage20 : forall hay c i,
  0 <= i < Zlength hay -> Znth i hay 0 = c ->
  exists j, first_byte_at hay c j.
Proof.
  intros hay c i Hi Hbyte.
  remember (Z.to_nat i) as n eqn:Hn.
  revert i Hi Hbyte Hn.
  induction n using lt_wf_ind; intros i Hi Hbyte Hn.
  destruct (classic (exists j, 0 <= j < i /\ Znth j hay 0 = c))
    as [[j [Hj Hjc]] | Hnone].
  - eapply H with (m := Z.to_nat j) (i := j).
    + rewrite Hn. apply Z2Nat.inj_lt; lia.
    + lia.
    + exact Hjc.
    + reflexivity.
  - exists i. unfold first_byte_at. split; [exact Hi|].
    split; [exact Hbyte|].
    intros j Hj Hjc. apply Hnone. exists j. auto.
Qed.

Lemma substring_first_byte_stage20 : forall hay needle i,
  1 <= Zlength needle -> substring_at hay needle i ->
  0 <= i < Zlength hay /\ Znth i hay 0 = Znth 0 needle 0.
Proof.
  intros hay needle i Hlen [Hi [Hwindow Hsub]]. split; [lia|].
  pose proof (f_equal (fun xs => Znth 0 xs 0) Hsub) as Hnth.
  cbn beta in Hnth. rewrite Znth_sublist in Hnth by lia.
  replace (0 + i) with i in Hnth by lia. exact Hnth.
Qed.

Lemma Forall_firstn_stage20 {A} (P : A -> Prop) n (xs : list A) :
  Forall P xs -> Forall P (firstn n xs).
Proof.
  revert xs. induction n; intros xs H; simpl; [constructor|].
  destruct xs; simpl; [constructor|]. inversion H; constructor; auto.
Qed.

Lemma Forall_skipn_stage20 {A} (P : A -> Prop) n (xs : list A) :
  Forall P xs -> Forall P (skipn n xs).
Proof.
  revert xs. induction n; intros xs H; simpl; [exact H|].
  destruct xs; simpl; [constructor|]. inversion H; auto.
Qed.

Lemma suffix_with_zero_stage20 : forall hs i,
  0 <= i <= Zlength hs ->
  sublist i (Zlength hs + 1) (hs ++ [0]) =
  sublist i (Zlength hs) hs ++ [0].
Proof.
  intros hs i Hi.
  rewrite (sublist_split i (Zlength hs + 1) (Zlength hs) (hs ++ [0])) by
    (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite sublist_split_app_l by lia.
  rewrite sublist_split_app_r with (len := Zlength hs) by lia.
  replace (Zlength hs - Zlength hs) with 0 by lia.
  replace (Zlength hs + 1 - Zlength hs) with 1 by lia.
  reflexivity.
Qed.

Lemma proof_of_strstr_return_wit_1_split_goal_1 : strstr_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (lift_suffix_result_sep_stage20 hs ns h_pre h retval i);
    eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_1_split_goal_spatial : strstr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_prefix_suffix_stage20 hs h_pre h i); eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_1 : strstr_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strstr_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_strstr_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_strstr_return_wit_2_split_goal_1 : strstr_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (lift_suffix_result_sep_stage20 hs ns h_pre h retval i);
    eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_2_split_goal_spatial : strstr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_prefix_suffix_stage20 hs h_pre h i); eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_2 : strstr_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strstr_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_strstr_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_strstr_return_wit_4_split_goal_1 : strstr_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (lift_suffix_result_sep_stage20 hs ns h_pre h retval i);
    eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_4_split_goal_spatial : strstr_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_prefix_suffix_stage20 hs h_pre h i); eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_4 : strstr_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strstr_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_strstr_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_strstr_return_wit_6_split_goal_1 : strstr_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (lift_suffix_result_sep_stage20 hs ns h_pre h retval i);
    eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_6_split_goal_spatial : strstr_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_prefix_suffix_stage20 hs h_pre h i); eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_6 : strstr_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strstr_return_wit_6_split_goal_spatial.
  - Goal_apply proof_of_strstr_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_strstr_return_wit_3_split_goal_1 : strstr_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). entailer!.
  eapply lift_suffix_result_stage20 with (suffix_base := h) (i := i).
  - rewrite PreH3, sizeof_char. lia.
  - rewrite Zlength_sublist in * by lia. lia.
  - exact PreH10.
  - eapply (suffix_terminated_result_stage20
      (sublist i (Zlength hs) hs) ns h 3); eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_3_split_goal_spatial : strstr_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_prefix_suffix_stage20 hs h_pre h i); eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_3 : strstr_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strstr_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_strstr_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_strstr_return_wit_5_split_goal_1 : strstr_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). entailer!.
  eapply lift_suffix_result_stage20 with (suffix_base := h) (i := i).
  - rewrite PreH3, sizeof_char. lia.
  - rewrite Zlength_sublist in * by lia. lia.
  - exact PreH10.
  - eapply (suffix_terminated_result_stage20
      (sublist i (Zlength hs) hs) ns h 2); eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_5_split_goal_spatial : strstr_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (merge_prefix_suffix_stage20 hs h_pre h i); eauto; lia.
Qed.

Lemma proof_of_strstr_return_wit_5 : strstr_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strstr_return_wit_5_split_goal_spatial.
  - Goal_apply proof_of_strstr_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_strstr_return_wit_7_split_goal_1 : strstr_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). entailer!.
  assert (Hend : i + 1 = Zlength hs).
  { rewrite Znth_sublist in PreH1 by lia.
    replace (1 + i) with (i + 1) in PreH1 by lia.
    destruct (Z.eq_dec (i + 1) (Zlength hs)) as [Heq|Hne]; [exact Heq|].
    assert (Hlt : i + 1 < Zlength hs) by lia.
    rewrite app_Znth1 in PreH1 by lia.
    unfold nonzero_bytes in PreH7.
    apply Forall_forall with (x := Znth (i + 1) hs 0) in PreH7.
    2:{ unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
        rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. exact Hlt. }
    cbn in PreH7. lia. }
  unfold strstr_result. left. split; [reflexivity|].
  intros j Hmatch.
  destruct (Z_lt_ge_dec j i) as [Hlt|Hge].
  - apply (PreH6 j).
    + unfold substring_at in Hmatch. lia.
    + exact Hmatch.
  - unfold substring_at in Hmatch.
    destruct Hmatch as [Hj [Hwindow Hsub]]. lia.
Qed.

Lemma proof_of_strstr_return_wit_7_split_goal_spatial : strstr_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst h.
  sep_apply_l_atomic (UCharArray.full_merge_to_full h_pre i (Zlength hs + 1)
    (sublist 0 i (hs ++ [0]))
    (sublist i (Zlength hs + 1) (hs ++ [0]))).
  - dump_pre_spatial. lia.
  - rewrite <- (sublist_split 0 (Zlength hs + 1) i (hs ++ [0])) by
      (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    rewrite sublist_self by
      (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    entailer!.
Qed.

Lemma proof_of_strstr_return_wit_7 : strstr_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strstr_return_wit_7_split_goal_spatial.
  - Goal_apply proof_of_strstr_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_strstr_return_wit_8_split_goal_1 : strstr_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval. unfold strchr_result in PreH2.
  destruct PreH2 as [[Hzero Hnone] | [j [Hfirst [Hret Hnonnull]]]].
  2: contradiction.
  unfold strstr_result. left. split; [reflexivity|].
  intros i Hmatch.
  destruct (substring_first_byte_stage20 hs ns i PreH3 Hmatch)
    as [Hi Hbyte].
  assert (Hnbyte : 0 <= Znth 0 ns 0 < 256).
  { eapply nonzero_nth_bound__proof_of_threebyte_2; eauto; lia. }
  assert (Hhead : Znth 0 (ns ++ [0]) 0 = Znth 0 ns 0).
  { rewrite app_Znth1 by lia. reflexivity. }
  assert (Hland : Z.land (Znth 0 (ns ++ [0]) 0) 255 = Znth 0 ns 0).
  { rewrite Hhead. change 255 with (Z.ones 8).
    rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  destruct (first_byte_exists_stage20 hs (Znth 0 ns 0) i Hi Hbyte)
    as [j Hj].
  apply (Hnone j). rewrite Hland. exact Hj.
Qed.

Lemma proof_of_strstr_return_wit_8 : strstr_return_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strstr_return_wit_8_split_goal_1.
Qed.

Lemma proof_of_strstr_return_wit_10_split_goal_1 : strstr_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength ns = 0).
  { destruct (Z.eq_dec (Zlength ns) 0) as [Heq|Hne]; [exact Heq|].
    assert (Hpos : 0 < Zlength ns) by (pose proof (Zlength_nonneg ns); lia).
    rewrite app_Znth1 in PreH1 by lia.
    unfold nonzero_bytes in PreH5.
    apply Forall_forall with (x := Znth 0 ns 0) in PreH5.
    2:{ unfold Znth. apply nth_In. rewrite Zlength_correct in Hpos. lia. }
    cbn in PreH5. lia. }
  assert (Hempty : ns = []) by (apply Zlength_zero_iff_nil; exact Hlen).
  subst ns. unfold strstr_result. right. exists 0. split.
  - unfold first_substring, substring_at. simpl. split.
    + repeat split; try lia.
    + intros j Hj. lia.
  - lia.
Qed.

Lemma proof_of_strstr_return_wit_10 : strstr_return_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strstr_return_wit_10_split_goal_1.
Qed.

Lemma proof_of_strstr_return_wit_9_split_goal_1 : strstr_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength ns = 1).
  { destruct (Z.eq_dec (Zlength ns) 1) as [Heq|Hne]; [exact Heq|].
    assert (Hgt : 1 < Zlength ns) by lia.
    rewrite app_Znth1 in PreH1 by lia.
    unfold nonzero_bytes in PreH6.
    apply Forall_forall with (x := Znth 1 ns 0) in PreH6.
    2:{ unfold Znth. apply nth_In. rewrite Zlength_correct in Hgt. lia. }
    cbn in PreH6. lia. }
  unfold strchr_result in PreH3.
  destruct PreH3 as [[Hzero Hnone] | [j [Hfirst [Hret Hnonnull]]]].
  - contradiction.
  - unfold first_byte_at in Hfirst.
    destruct Hfirst as [Hj [Hbyte Hbefore]].
    assert (Hnbyte : 0 <= Znth 0 ns 0 < 256).
    { eapply nonzero_nth_bound__proof_of_threebyte_2; eauto; lia. }
    assert (Hhead : Znth 0 (ns ++ [0]) 0 = Znth 0 ns 0).
    { rewrite app_Znth1 by lia. reflexivity. }
    assert (Hland : Z.land (Znth 0 (ns ++ [0]) 0) 255 = Znth 0 ns 0).
    { rewrite Hhead. change 255 with (Z.ones 8).
      rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
    rewrite Hland in Hbyte.
    unfold strstr_result. right. exists j. split.
    + unfold first_substring. split.
      * unfold substring_at. split; [lia|]. split; [lia|].
        apply (Zsublist_eq_ext 0).
        -- rewrite Zlength_sublist by lia. lia.
        -- intros t Ht. assert (Ht0 : t = 0) by
             (rewrite Zlength_sublist in Ht by lia; lia).
           subst t. rewrite Znth_sublist by lia.
           replace (0 + j) with j by lia. exact Hbyte.
      * intros x Hx Hmatch.
        destruct (substring_first_byte_stage20 hs ns x ltac:(lia) Hmatch)
          as [Hxrange Hxbyte].
        apply (Hbefore x Hx). rewrite Hland. exact Hxbyte.
    + exact Hret.
Qed.

Lemma proof_of_strstr_return_wit_9 : strstr_return_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strstr_return_wit_9_split_goal_1.
Qed.

Lemma proof_of_strstr_entail_wit_1_split_goal_1 : strstr_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct ns as [|a tail].
  - cbn [Znth] in PreH1. contradiction.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg tail). lia.
Qed.

Lemma proof_of_strstr_entail_wit_1 : strstr_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strstr_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_strstr_entail_wit_4_split_goal_1 : strstr_entail_wit_4_split_goal_1.
Proof.
  unfold strstr_entail_wit_4_split_goal_1.
  intros ns hs h_pre i h Htail2 Hns2 Hh Hi Hip2 Hnslen Htaillen
    Hz2 Hnz2 Hbefore Hhs Hns Htail Hnz3.
  assert (Hlen3 : 3 <= Zlength ns) by (apply Hnz2; exact Hns2).
  destruct (Z_lt_ge_dec 3 (Zlength ns)) as [Hlt|Hge]; [lia|].
  assert (Heq : Zlength ns = 3) by lia.
  rewrite app_Znth2 in Hnz3 by lia. rewrite Heq in Hnz3.
  cbn [Znth] in Hnz3. contradiction.
Qed.

Lemma proof_of_strstr_entail_wit_4_split_goal_2 : strstr_entail_wit_4_split_goal_2.
Proof.
  unfold strstr_entail_wit_4_split_goal_2.
  intros ns hs h_pre i h Htail2 Hns2 Hh Hi Hip2 Hnslen Htaillen
    Hz2 Hnz2 Hbefore Hhs Hns Htail Hzero.
  assert (Hlen3 : 3 <= Zlength ns) by (apply Hnz2; exact Hns2).
  destruct (Z.eq_dec (Zlength ns) 3) as [Heq|Hne]; [exact Heq|].
  assert (Hlt : 3 < Zlength ns) by lia.
  rewrite app_Znth1 in Hzero by lia.
  unfold nonzero_bytes in Hns.
  apply Forall_forall with (x := Znth 3 ns 0) in Hns.
  2:{ unfold Znth. apply nth_In. rewrite Zlength_correct in Hlt. lia. }
  cbn in Hns. lia.
Qed.

Lemma proof_of_strstr_entail_wit_4_split_goal_3 : strstr_entail_wit_4_split_goal_3.
Proof.
  unfold strstr_entail_wit_4_split_goal_3.
  intros ns hs h_pre i h Htail2 Hns2 Hh Hi Hip2 Hnslen Htaillen
    Hz2 Hnz2 Hbefore Hhs Hns Htail.
  set (tail := sublist i (Zlength hs) hs) in *.
  destruct (Z_lt_ge_dec 2 (Zlength tail)) as [Hlt|Hge]; [lia|].
  assert (Heq : Zlength tail = 2) by lia.
  rewrite app_Znth2 in Htail2 by lia. rewrite Heq in Htail2.
  cbn [Znth] in Htail2. contradiction.
Qed.

Lemma proof_of_strstr_entail_wit_4_split_goal_4 : strstr_entail_wit_4_split_goal_4.
Proof.
  unfold strstr_entail_wit_4_split_goal_4.
  intros ns hs h_pre i h Htail2 Hns2 Hh Hi Hip2 Hnslen Htaillen
    Hz2 Hnz2 Hbefore Hhs Hns Htail.
  assert (Htail3 : 3 <= Zlength (sublist i (Zlength hs) hs)).
  { eapply proof_of_strstr_entail_wit_4_split_goal_3; eauto. }
  rewrite Zlength_sublist in Htail3 by lia. lia.
Qed.

Lemma proof_of_strstr_entail_wit_4 : strstr_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strstr_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_strstr_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_strstr_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_strstr_entail_wit_4_split_goal_4.
Qed.

Lemma proof_of_strstr_entail_wit_2 : strstr_entail_wit_2.
Proof.
  unfold strstr_entail_wit_2. left.
  intros ns hs h_pre n_pre retval Hn1 Hretval Hstrchr Hnlen Hhs Hns.
  unfold strchr_result in Hstrchr.
  destruct Hstrchr as [[Hzero Hnone] | [i [Hfirst [Hret Hnonnull]]]].
  - contradiction.
  - unfold first_byte_at in Hfirst.
    destruct Hfirst as [Hi [Hbyte Hbefore]].
    assert (Hlen2 : 2 <= Zlength ns).
    { destruct (Z_lt_ge_dec 1 (Zlength ns)) as [Hlt|Hge]; [lia|].
      assert (Heq : Zlength ns = 1) by lia.
      rewrite app_Znth2 in Hn1 by lia. rewrite Heq in Hn1.
      cbn [Znth] in Hn1. contradiction. }
    assert (Hnbyte : 0 <= Znth 0 ns 0 < 256).
    { eapply nonzero_nth_bound__proof_of_threebyte_2; eauto; lia. }
    assert (Hhead : Znth 0 (ns ++ [0]) 0 = Znth 0 ns 0).
    { rewrite app_Znth1 by lia. reflexivity. }
    assert (Hland : Z.land (Znth 0 (ns ++ [0]) 0) 255 = Znth 0 ns 0).
    { rewrite Hhead. change 255 with (Z.ones 8).
      rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
    rewrite Hland in Hbyte, Hbefore.
    assert (Hnomatch : no_match_before hs ns i).
    { unfold no_match_before. intros j Hj Hmatch.
      destruct (substring_first_byte_stage20 hs ns j ltac:(lia) Hmatch)
        as [Hjrange Hjbyte].
      apply (Hbefore j Hj). exact Hjbyte. }
    Exists i. split_pure_spatial.
    + sep_apply (UCharArray.full_split_to_full h_pre i (Zlength hs + 1)
        (hs ++ [0])); try lia.
      rewrite Hret.
      replace (h_pre + i) with (h_pre + i * sizeof(UCHAR)) by
        (rewrite sizeof_uchar; lia).
      cancel.
    + split_pures; dump_pre_spatial; try assumption; try lia.
      rewrite Hret, sizeof_char. lia.
Qed.

Lemma proof_of_strstr_entail_wit_3 : strstr_entail_wit_3.
Proof.
  unfold strstr_entail_wit_3. left.
  intros ns hs h_pre n_pre i h Htail1 Hh Hi Hilt Hnlen Hbefore Hhs Hns.
  assert (Hi2 : i + 2 <= Zlength hs).
  { rewrite Znth_sublist in Htail1 by lia.
    replace (1 + i) with (i + 1) in Htail1 by lia.
    destruct (Z.eq_dec (i + 1) (Zlength hs)) as [Heq|Hne].
    - rewrite app_Znth2 in Htail1 by lia.
      replace (i + 1 - Zlength hs) with 0 in Htail1 by lia.
      exfalso. apply Htail1. reflexivity.
    - lia. }
  assert (Htail_len : 2 <= Zlength (sublist i (Zlength hs) hs)).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hneedle_zero :
      Znth 2 (ns ++ [0]) 0 = 0 -> Zlength ns = 2).
  { intro Hzero.
    destruct (Z.eq_dec (Zlength ns) 2) as [Heq|Hne]; [exact Heq|].
    assert (Hlt : 2 < Zlength ns) by lia.
    rewrite app_Znth1 in Hzero by lia.
    unfold nonzero_bytes in Hns.
    apply Forall_forall with (x := Znth 2 ns 0) in Hns.
    2:{ unfold Znth. apply nth_In. rewrite Zlength_correct in Hlt. lia. }
    cbn in Hns. lia. }
  assert (Hneedle_nonzero :
      Znth 2 (ns ++ [0]) 0 <> 0 -> 3 <= Zlength ns).
  { intro Hnz.
    destruct (Z_lt_ge_dec 2 (Zlength ns)) as [Hlt|Hge]; [lia|].
    assert (Heq : Zlength ns = 2) by lia.
    rewrite app_Znth2 in Hnz by lia. rewrite Heq in Hnz.
    cbn [Znth] in Hnz. contradiction. }
  assert (Htail_nonzero : nonzero_bytes (sublist i (Zlength hs) hs)).
  { unfold nonzero_bytes in *; unfold sublist.
    apply Forall_skipn_stage20. apply Forall_firstn_stage20. exact Hhs. }
  Exists i. split_pure_spatial.
  - rewrite (suffix_with_zero_stage20 hs i) by lia.
    rewrite Zlength_sublist by lia.
    replace (Zlength hs + 1 - i) with (Zlength hs - i + 1) by lia.
    entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_strstr_partial_solve_wit_3_pure_split_goal_1 : strstr_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 by lia.
  entailer!.
  unfold nonzero_bytes in PreH3.
  apply Forall_forall with (x := Znth 0 ns 0) in PreH3.
  - lia.
  - unfold Znth. apply nth_In. rewrite Zlength_correct in PreH1. lia.
Qed.


Lemma proof_of_strstr_partial_solve_wit_3_pure : strstr_partial_solve_wit_3_pure.
Proof.
  right. LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 by lia.
  assert (Hbyte : 0 < Znth 0 ns 0 < 256).
  { unfold nonzero_bytes in PreH3.
    apply Forall_forall with (x := Znth 0 ns 0) in PreH3.
    - exact PreH3.
    - unfold Znth. apply nth_In. rewrite Zlength_correct in PreH1. lia. }
  entailer!.
Qed.


Lemma proof_of_strstr_partial_solve_wit_13_pure_split_goal_1 : strstr_partial_solve_wit_13_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : 4 <= Zlength ns) by (apply PreH10; exact PreH3).
  pose proof (nonzero_terminator_index__twoway_table_1 ns 4 PreH13 ltac:(lia) PreH1) as Heq.
  entailer!.
Qed.


Lemma proof_of_strstr_partial_solve_wit_13_pure_split_goal_2 : strstr_partial_solve_wit_13_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (nonzero_index_lt__twoway_table_1 (sublist i (Zlength hs) hs) 3 ltac:(lia) PreH2) as Hlen.
  entailer!.
Qed.


Lemma proof_of_strstr_partial_solve_wit_13_pure : strstr_partial_solve_wit_13_pure.
Proof.
  right. intros.
  assert (Hnlen : 4 <= Zlength ns) by (apply PreH10; exact PreH3).
  pose proof (nonzero_terminator_index__twoway_table_1 ns 4 PreH13 ltac:(lia) PreH1) as Heq.
  pose proof (nonzero_index_lt__twoway_table_1 (sublist i (Zlength hs) hs) 3 ltac:(lia) PreH2) as Hhlen.
  entailer!.
Qed.


Lemma proof_of_strstr_partial_solve_wit_14_pure : strstr_partial_solve_wit_14_pure.
Proof.
  right. intros.
  assert (Hnlen : 5 <= Zlength ns).
  { pose proof (nonzero_index_lt__twoway_table_1 ns 4 ltac:(lia) PreH1).
    lia. }
  assert (Hhlen : 4 <= Zlength (sublist i (Zlength hs) hs)).
  { pose proof (nonzero_index_lt__twoway_table_1
      (sublist i (Zlength hs) hs) 3 ltac:(lia) PreH2).
    lia. }
  prop_apply_p (strstr_array_length64 n_pre ns).
  Intros_p Hnb.
  prop_apply_p (strstr_array_length64 h (sublist i (Zlength hs) hs)).
  Intros_p Hhb.
  entailer!.
Qed.
