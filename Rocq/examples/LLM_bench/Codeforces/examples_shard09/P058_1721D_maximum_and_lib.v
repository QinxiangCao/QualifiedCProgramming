Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition AndList30 (xs : list Z) : Z := fold_right Z.land (Z.pow 2 30 - 1) xs.
Definition AndCandidate (a b : list Z) (v : Z) : Prop :=
  exists p, Permutation p b /\ v = AndList30 (map (fun q => Z.lxor (fst q) (snd q)) (combine a p)).
Definition Pre (a b : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P058 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength a <= 100000 /\
       Zlength b = Zlength a /\
       Forall (fun x => 0 <= x < Z.pow 2 30) a /\
       Forall (fun x => 0 <= x < Z.pow 2 30) b. *)
  True.

Definition Spec (a b : list Z) (out : Z) : Prop := max_value_of_subset Z.le (AndCandidate a b) (fun x => x) out.

Definition MaskedLeft (a : list Z) (mask : Z) : list Z :=
  map (fun x => Z.land x mask) a.

Definition MaskedComplementRight (b : list Z) (mask : Z) : list Z :=
  map (fun x => Z.land (Z.lnot x) mask) b.

Definition MaskFeasible (a b : list Z) (mask : Z) : Prop :=
  Permutation (MaskedLeft a mask) (MaskedComplementRight b mask).

Definition MaskedBuffersPrefix
    (a b : list Z) (mask : Z)
    (ka kb : list Z) (upto : Z) : Prop :=
  ka = MaskedLeft (sublist 0 upto a) mask /\
  kb = MaskedComplementRight (sublist 0 upto b) mask.

Definition GreedyMaskPrefixOptimal
    (a b : list Z) (bit ans : Z) : Prop :=
  MaskFeasible a b ans /\
  ans = Z.shiftl (Z.shiftr ans (bit + 1)) (bit + 1) /\
  forall v,
    AndCandidate a b v ->
    Z.shiftr v (bit + 1) <= Z.shiftr ans (bit + 1).

Require Import Coq.micromega.Lia.
Lemma masked_buffers_prefix_snoc__feasible_buffers :
  forall (a b : list Z) mask ka kb i,
    0 <= i < Zlength a ->
    Zlength b = Zlength a ->
    MaskedBuffersPrefix a b mask ka kb i ->
    MaskedBuffersPrefix a b mask
      (ka ++ [Z.land (Znth i a 0) mask])
      (kb ++ [Z.land (Z.lnot (Znth i b 0)) mask])
      (i + 1).
Proof.
  intros a b mask ka kb i Hi Hlen Hprefix.
  unfold MaskedBuffersPrefix, MaskedLeft, MaskedComplementRight in *.
  destruct Hprefix as [Hka Hkb].
  subst ka kb.
  split.
  - rewrite (sublist_split 0 (i + 1) i a) by lia.
    rewrite (sublist_single 0 i a) by lia.
    rewrite map_app. reflexivity.
  - rewrite (sublist_split 0 (i + 1) i b) by lia.
    rewrite (sublist_single 0 i b) by lia.
    rewrite map_app. reflexivity.
Qed.
Lemma masked_buffers_prefix_at_length__feasible_buffers :
  forall (a b : list Z) mask ka kb,
    Zlength b = Zlength a ->
    MaskedBuffersPrefix a b mask ka kb (Zlength a) ->
    ka = MaskedLeft a mask /\ kb = MaskedComplementRight b mask.
Proof.
  intros a b mask ka kb Hlen Hprefix.
  unfold MaskedBuffersPrefix, MaskedLeft, MaskedComplementRight in *.
  destruct Hprefix as [Hka Hkb].
  rewrite (sublist_self a (Zlength a)) in Hka by reflexivity.
  rewrite (sublist_self b (Zlength a)) in Hkb by lia.
  auto.
Qed.
Lemma sublist_prefix_snoc_from_znth_eq__feasible_sort_compare :
  forall (l1 l2 : list Z) i,
    0 <= i < Zlength l1 ->
    i < Zlength l2 ->
    sublist 0 i l1 = sublist 0 i l2 ->
    Znth i l1 0 = Znth i l2 0 ->
    sublist 0 (i + 1) l1 = sublist 0 (i + 1) l2.
Proof.
  intros l1 l2 i Hi1 Hi2 Hprefix Hnth.
  rewrite (sublist_split 0 (i + 1) i l1) by lia.
  rewrite (sublist_split 0 (i + 1) i l2) by lia.
  rewrite (sublist_single 0 i l1) by lia.
  rewrite (sublist_single 0 i l2) by lia.
  now rewrite Hprefix, Hnth.
Qed.
Lemma monotone_permutation_unique__feasible_sort_compare :
  forall (l1 l2 : list Z),
    ListLib.increasing l1 ->
    ListLib.increasing l2 ->
    Permutation l1 l2 ->
    l1 = l2.
Proof.
  induction l1 as [| a l1 IH]; intros l2 Hinc1 Hinc2 Hperm.
  - apply Permutation_nil in Hperm. symmetry. exact Hperm.
  - destruct l2 as [| b l2].
    + apply Permutation_length in Hperm. simpl in Hperm. discriminate.
    + simpl in Hinc1, Hinc2.
      assert (Hab : a <= b).
      { destruct (Z.eq_dec a b) as [-> | Hneq]; [lia |].
        assert (Hin : In b (a :: l1)).
        { eapply Permutation_in.
          - symmetry. exact Hperm.
          - simpl. auto. }
        simpl in Hin. destruct Hin as [Heq | Hin]; [contradiction |].
        eapply ListLib.increasing_aux_head_le_all_In; eauto. }
      assert (Hba : b <= a).
      { destruct (Z.eq_dec b a) as [-> | Hneq]; [lia |].
        assert (Hin : In a (b :: l2)).
        { eapply Permutation_in.
          - exact Hperm.
          - simpl. auto. }
        simpl in Hin. destruct Hin as [Heq | Hin]; [contradiction |].
        eapply ListLib.increasing_aux_head_le_all_In; eauto. }
      assert (a = b) by lia. subst b.
      f_equal.
      apply IH.
      * eapply ListLib.increasing_aux_tail_increasing; eauto.
      * eapply ListLib.increasing_aux_tail_increasing; eauto.
      * now apply Permutation_cons_inv in Hperm.
Qed.
Lemma masked_buffers_sorted_lengths__feasible_sort_compare :
  forall left right mask ka kb sorted_ka sorted_kb n,
    n = Zlength left ->
    Zlength right = n ->
    MaskedBuffersPrefix left right mask ka kb n ->
    Permutation ka sorted_ka ->
    Permutation kb sorted_kb ->
    Zlength sorted_ka = n /\ Zlength sorted_kb = n.
Proof.
  intros left right mask ka kb sorted_ka sorted_kb n
    Hleft Hright [Hka_def Hkb_def] Hka Hkb.
  split.
  - assert (Hperm_len : Zlength ka = Zlength sorted_ka).
    { pose proof (Permutation_length Hka) as Hlen.
      rewrite !Zlength_correct. now rewrite Hlen. }
    rewrite <- Hperm_len, Hka_def.
    unfold MaskedLeft.
    rewrite Zlength_correct, length_map, <- Zlength_correct.
    apply Zlength_sublist0. pose proof (Zlength_nonneg left). lia.
  - assert (Hperm_len : Zlength kb = Zlength sorted_kb).
    { pose proof (Permutation_length Hkb) as Hlen.
      rewrite !Zlength_correct. now rewrite Hlen. }
    rewrite <- Hperm_len, Hkb_def.
    unfold MaskedComplementRight.
    rewrite Zlength_correct, length_map, <- Zlength_correct.
    apply Zlength_sublist0. pose proof (Zlength_nonneg right). lia.
Qed.
Lemma mask_feasible_from_complete_sorted_prefix__feasible_sort_compare :
  forall left right mask ka kb sorted_ka sorted_kb n,
    n = Zlength left ->
    Zlength right = n ->
    MaskedBuffersPrefix left right mask ka kb n ->
    Permutation ka sorted_ka ->
    Permutation kb sorted_kb ->
    sublist 0 n sorted_ka = sublist 0 n sorted_kb ->
    MaskFeasible left right mask.
Proof.
  intros left right mask ka kb sorted_ka sorted_kb n
    Hleft Hright Hbuffers Hka Hkb Hprefix.
  unfold MaskedBuffersPrefix in Hbuffers.
  destruct Hbuffers as [Hka_def Hkb_def].
  assert (Hbuffers_copy :
      MaskedBuffersPrefix left right mask ka kb n).
  { split; assumption. }
  pose proof
    (masked_buffers_sorted_lengths__feasible_sort_compare
       left right mask ka kb sorted_ka sorted_kb n Hleft Hright
       Hbuffers_copy Hka Hkb) as [Hlen_ka Hlen_kb].
  assert (Hsorted : sorted_ka = sorted_kb).
  { rewrite <- (sublist_self sorted_ka n) by lia.
    rewrite <- (sublist_self sorted_kb n) by lia.
    exact Hprefix. }
  unfold MaskFeasible.
  rewrite (sublist_self left n Hleft) in Hka_def.
  rewrite (sublist_self right n ltac:(lia)) in Hkb_def.
  rewrite <- Hka_def, <- Hkb_def.
  eapply Permutation_trans; [exact Hka |].
  rewrite Hsorted.
  symmetry. exact Hkb.
Qed.
Lemma sorted_first_mismatch_refutes_mask_feasible__feasible_sort_compare :
  forall left right mask ka kb sorted_ka sorted_kb n i,
    n = Zlength left ->
    Zlength right = n ->
    MaskedBuffersPrefix left right mask ka kb n ->
    Permutation ka sorted_ka ->
    Permutation kb sorted_kb ->
    ListLib.increasing sorted_ka ->
    ListLib.increasing sorted_kb ->
    Znth i sorted_ka 0 <> Znth i sorted_kb 0 ->
    ~ MaskFeasible left right mask.
Proof.
  intros left right mask ka kb sorted_ka sorted_kb n i
    Hleft Hright Hbuffers Hka Hkb Hmono_ka Hmono_kb Hneq Hfeasible.
  unfold MaskedBuffersPrefix in Hbuffers.
  destruct Hbuffers as [Hka_def Hkb_def].
  unfold MaskFeasible in Hfeasible.
  rewrite (sublist_self left n Hleft) in Hka_def.
  rewrite (sublist_self right n ltac:(lia)) in Hkb_def.
  rewrite <- Hka_def, <- Hkb_def in Hfeasible.
  assert (Hsorted_perm : Permutation sorted_ka sorted_kb).
  { eapply Permutation_trans.
    - symmetry. exact Hka.
    - eapply Permutation_trans; eauto. }
  pose proof
    (monotone_permutation_unique__feasible_sort_compare
       sorted_ka sorted_kb Hmono_ka Hmono_kb Hsorted_perm) as Heq.
  apply Hneq. now rewrite Heq.
Qed.
Lemma mask_feasible_zero__solver_init_bounds :
  forall a b,
    Zlength a = Zlength b ->
    MaskFeasible a b 0.
Proof.
  intros a b Hlen.
  assert (Hzero : forall (f : Z -> Z) (xs : list Z),
      map (fun x => Z.land (f x) 0) xs = repeat 0 (length xs)).
  {
    intros f xs. induction xs as [|x xs IH]; simpl; [reflexivity|].
    rewrite Z.land_0_r, IH. reflexivity.
  }
  unfold MaskFeasible, MaskedLeft, MaskedComplementRight.
  rewrite (Hzero (fun x => x) a), (Hzero Z.lnot b).
  assert (Hnatlen : length a = length b).
  {
    apply Nat2Z.inj.
    rewrite <- !Zlength_correct.
    exact Hlen.
  }
  rewrite Hnatlen.
  apply Permutation_refl.
Qed.
Lemma and_list30_range__solver_init_bounds :
  forall xs,
    0 <= AndList30 xs < Z.pow 2 30.
Proof.
  assert (Hbounded : forall x,
      Z.land x (Z.pow 2 30 - 1) = x ->
      0 <= x < Z.pow 2 30).
  {
    intros x Hmask.
    change (Z.land x (Z.ones 30) = x) in Hmask.
    rewrite Z.land_ones in Hmask by lia.
    pose proof (Z.mod_pos_bound x (Z.pow 2 30) ltac:(lia)).
    lia.
  }
  induction xs as [|x xs IH]; unfold AndList30 in *; simpl.
  - change (0 <= 1073741823 < 1073741824). lia.
  - apply Hbounded.
    assert (Htail : Z.land (fold_right Z.land (Z.pow 2 30 - 1) xs)
        (Z.pow 2 30 - 1) = fold_right Z.land (Z.pow 2 30 - 1) xs).
    {
      change (Z.land (fold_right Z.land (Z.pow 2 30 - 1) xs)
          (Z.ones 30) = fold_right Z.land (Z.pow 2 30 - 1) xs).
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small; lia.
    }
    rewrite <- Htail at 2.
    symmetry. apply Z.land_assoc.
Qed.
Lemma and_candidate_range30__solver_init_bounds :
  forall a b v,
    AndCandidate a b v ->
    0 <= v < Z.pow 2 30.
Proof.
  intros a b v (p & Hperm & Hv).
  subst v.
  apply and_list30_range__solver_init_bounds.
Qed.
Lemma lor_single_bit_range30__solver_init_bounds :
  forall ans bit,
    0 <= ans < Z.pow 2 30 ->
    0 <= bit <= 29 ->
    0 <= Z.lor ans (Z.shiftl 1 bit) < Z.pow 2 30.
Proof.
  intros ans bit Hans Hbit.
  assert (Hpow : 0 <= Z.shiftl 1 bit < Z.pow 2 30).
  {
    rewrite Z.shiftl_1_l.
    split.
    - pose proof (Z.pow_pos_nonneg 2 bit ltac:(lia) ltac:(lia)). lia.
    - apply Z.pow_lt_mono_r; lia.
  }
  split.
  - apply Z.lor_nonneg. lia.
  - assert (Hansmask : Z.land ans (Z.pow 2 30 - 1) = ans).
    {
      change (Z.land ans (Z.ones 30) = ans).
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small; lia.
    }
    assert (Hpowmask :
        Z.land (Z.shiftl 1 bit) (Z.pow 2 30 - 1) = Z.shiftl 1 bit).
    {
      change (Z.land (Z.shiftl 1 bit) (Z.ones 30) = Z.shiftl 1 bit).
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small; lia.
    }
    assert (Hmask :
        Z.land (Z.lor ans (Z.shiftl 1 bit)) (Z.pow 2 30 - 1) =
        Z.lor ans (Z.shiftl 1 bit)).
    {
      rewrite Z.land_lor_distr_l, Hansmask, Hpowmask.
      reflexivity.
    }
    change (Z.land (Z.lor ans (Z.shiftl 1 bit)) (Z.ones 30) =
        Z.lor ans (Z.shiftl 1 bit)) in Hmask.
    rewrite Z.land_ones in Hmask by lia.
    pose proof (Z.mod_pos_bound (Z.lor ans (Z.shiftl 1 bit))
        (Z.pow 2 30) ltac:(lia)).
    lia.
Qed.
Lemma land_nested_left__solver_transitions :
  forall x y mask,
    Z.land (Z.land x y) mask = mask ->
    Z.land x mask = mask.
Proof.
  intros x y mask H.
  apply Z.bits_inj'.
  intros i Hi.
  assert (Hb :
    Z.testbit (Z.land (Z.land x y) mask) i = Z.testbit mask i)
    by now rewrite H.
  rewrite !Z.land_spec in Hb |- *.
  destruct (Z.testbit mask i) eqn:Hm.
  - rewrite !Bool.andb_true_r in Hb |- *.
    rewrite Z.land_spec in Hb.
    apply Bool.andb_true_iff in Hb.
    tauto.
  - apply Bool.andb_false_r.
Qed.
Lemma land_nested_right__solver_transitions :
  forall x y mask,
    Z.land (Z.land x y) mask = mask ->
    Z.land y mask = mask.
Proof.
  intros x y mask H.
  apply Z.bits_inj'.
  intros i Hi.
  assert (Hb :
    Z.testbit (Z.land (Z.land x y) mask) i = Z.testbit mask i)
    by now rewrite H.
  rewrite !Z.land_spec in Hb |- *.
  destruct (Z.testbit mask i) eqn:Hm.
  - rewrite !Bool.andb_true_r in Hb |- *.
    rewrite Z.land_spec in Hb.
    apply Bool.andb_true_iff in Hb.
    tauto.
  - apply Bool.andb_false_r.
Qed.
Lemma andlist_mask_each__solver_transitions :
  forall xs mask,
    Z.land (AndList30 xs) mask = mask ->
    Forall (fun x => Z.land x mask = mask) xs.
Proof.
  induction xs as [|x xs IH]; intros mask Hmask.
  - constructor.
  - change (Z.land (Z.land x (AndList30 xs)) mask = mask) in Hmask.
    constructor.
    + eapply land_nested_left__solver_transitions; eauto.
    + apply IH.
      eapply land_nested_right__solver_transitions; eauto.
Qed.
Lemma xor_mask_opposites__solver_transitions :
  forall x y mask,
    Z.land (Z.lxor x y) mask = mask ->
    Z.land x mask = Z.land (Z.lnot y) mask.
Proof.
  intros x y mask Hmask.
  apply Z.bits_inj'.
  intros i Hi.
  assert (Hb :
    Z.testbit (Z.land (Z.lxor x y) mask) i = Z.testbit mask i)
    by now rewrite Hmask.
  rewrite Z.land_spec, Z.lxor_spec in Hb.
  rewrite !Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.testbit mask i) eqn:Hm.
  - rewrite !Bool.andb_true_r in Hb |- *.
    destruct (Z.testbit x i), (Z.testbit y i);
      simpl in Hb |- *; try reflexivity; discriminate.
  - rewrite !Bool.andb_false_r.
    reflexivity.
Qed.
Lemma masked_pairs_equal__solver_transitions :
  forall a p mask,
    length a = length p ->
    Forall
      (fun q => Z.land (Z.lxor (fst q) (snd q)) mask = mask)
      (combine a p) ->
    MaskedLeft a mask = MaskedComplementRight p mask.
Proof.
  induction a as [|x a IH]; intros p mask Hlen Hall;
    destruct p as [|y p]; simpl in Hlen, Hall |- *; try discriminate.
  - reflexivity.
  - inversion Hlen as [Hlen'].
    inversion Hall as [|q qs Hhead Htail]; subst q qs.
    f_equal.
    + eapply xor_mask_opposites__solver_transitions; exact Hhead.
    + eapply IH; eauto.
Qed.
Lemma zlength_natlength__solver_transitions :
  forall (xs : list Z), Zlength xs = Z.of_nat (length xs).
Proof.
  apply Zlength_correct.
Qed.
Lemma andcandidate_mask_feasible__solver_transitions :
  forall a b v mask,
    Zlength a = Zlength b ->
    AndCandidate a b v ->
    Z.land v mask = mask ->
    MaskFeasible a b mask.
Proof.
  intros a b v mask Hlen (p & Hperm & ->) Hmask.
  assert (Hlen_nat : length a = length p).
  {
    rewrite !Zlength_correct in Hlen.
    apply Nat2Z.inj in Hlen.
    transitivity (length b); [exact Hlen |].
    symmetry. now apply Permutation_length in Hperm.
  }
  pose proof
    (andlist_mask_each__solver_transitions
      (map (fun q : Z * Z => Z.lxor (fst q) (snd q)) (combine a p))
      mask Hmask) as Hall.
  rewrite Forall_map in Hall.
  pose proof
    (masked_pairs_equal__solver_transitions a p mask Hlen_nat Hall) as Heq.
  unfold MaskFeasible.
  rewrite Heq.
  unfold MaskedComplementRight.
  now apply Permutation_map.
Qed.
Lemma shiftr_adjacent_bounds__solver_transitions :
  forall x k,
    2 * Z.shiftr x (k + 1) <= Z.shiftr x k <=
      2 * Z.shiftr x (k + 1) + 1.
Proof.
  intros x k.
  replace (Z.shiftr x (k + 1)) with
    (Z.shiftr (Z.shiftr x k) 1).
  2: {
    apply Z.shiftr_shiftr.
    lia.
  }
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  set (u := Z.shiftr x k).
  pose proof (Z.div_mod u 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound u 2 ltac:(lia)) as Hmod.
  lia.
Qed.
Lemma lor_shiftl_one__solver_transitions :
  forall q,
    Z.lor (Z.shiftl q 1) 1 = 2 * q + 1.
Proof.
  intro q.
  assert (Hland : Z.land (Z.shiftl q 1) 1 = 0).
  {
    replace 1 with (Z.ones 1) by
      (rewrite Z.ones_equiv; reflexivity).
    rewrite Z.land_ones by lia.
    rewrite Z.shiftl_mul_pow2 by easy.
    change (2 ^ 1) with 2.
    rewrite Z.mod_mul by lia.
    reflexivity.
  }
  pose proof (Z.add_lor_land (Z.shiftl q 1) 1) as Hsum.
  rewrite Hland, Z.shiftl_mul_pow2 in Hsum by easy.
  change (2 ^ 1) with 2 in Hsum.
  rewrite Z.add_0_r in Hsum.
  rewrite Z.mul_comm in Hsum.
  exact Hsum.
Qed.
Lemma normalized_take_properties__solver_transitions :
  forall ans k,
    0 <= k ->
    ans = Z.shiftl (Z.shiftr ans (k + 1)) (k + 1) ->
    let trial := Z.lor ans (Z.shiftl 1 k) in
    trial = Z.shiftl (Z.shiftr trial k) k /\
    Z.shiftr trial k = 2 * Z.shiftr ans (k + 1) + 1.
Proof.
  intros ans k Hk Hnorm.
  cbn.
  set (q := Z.shiftr ans (k + 1)).
  fold q in Hnorm.
  rewrite Hnorm.
  assert (Hfactor :
    Z.shiftl q (k + 1) = Z.shiftl (Z.shiftl q 1) k).
  {
    rewrite Z.shiftl_shiftl by lia.
    f_equal. lia.
  }
  rewrite Hfactor.
  rewrite <- Z.shiftl_lor.
  split.
  - rewrite Z.shiftr_shiftl_l by lia.
    replace (k - k) with 0 by lia.
    rewrite Z.shiftl_0_r.
    reflexivity.
  - rewrite Z.shiftr_shiftl_l by lia.
    replace (k - k) with 0 by lia.
    rewrite Z.shiftl_0_r.
    apply lor_shiftl_one__solver_transitions.
Qed.
Lemma normalized_skip_properties__solver_transitions :
  forall ans k,
    0 <= k ->
    ans = Z.shiftl (Z.shiftr ans (k + 1)) (k + 1) ->
    ans = Z.shiftl (Z.shiftr ans k) k /\
    Z.shiftr ans k = 2 * Z.shiftr ans (k + 1).
Proof.
  intros ans k Hk Hnorm.
  set (q := Z.shiftr ans (k + 1)).
  fold q in Hnorm.
  rewrite Hnorm.
  assert (Hfactor :
    Z.shiftl q (k + 1) = Z.shiftl (Z.shiftl q 1) k).
  {
    rewrite Z.shiftl_shiftl by lia.
    f_equal. lia.
  }
  rewrite Hfactor.
  split.
  - rewrite Z.shiftr_shiftl_l by lia.
    replace (k - k) with 0 by lia.
    rewrite Z.shiftl_0_r.
    reflexivity.
  - rewrite Z.shiftr_shiftl_l by lia.
    replace (k - k) with 0 by lia.
    rewrite Z.shiftl_0_r.
    rewrite Z.shiftl_mul_pow2 by lia.
    change (2 ^ 1) with 2.
    lia.
Qed.
Lemma normalized_mask_in_value__solver_transitions :
  forall v mask k,
    0 <= k ->
    mask = Z.shiftl (Z.shiftr mask k) k ->
    Z.shiftr v k = Z.shiftr mask k ->
    Z.land v mask = mask.
Proof.
  intros v mask k Hk Hnorm Hprefix.
  apply Z.bits_inj'.
  intros i Hi.
  destruct (Z_lt_ge_dec i k) as [Hlow | Hhigh].
  - assert (Hbit : Z.testbit mask i = false).
    {
      rewrite Hnorm, Z.shiftl_spec by lia.
      rewrite Z.testbit_neg_r by lia.
      reflexivity.
    }
    rewrite Z.land_spec, Hbit.
    apply Bool.andb_false_r.
  - assert (Hb :
      Z.testbit (Z.shiftr v k) (i - k) =
      Z.testbit (Z.shiftr mask k) (i - k))
      by now rewrite Hprefix.
    rewrite Z.shiftr_spec in Hb by lia.
    rewrite Z.shiftr_spec in Hb by lia.
    replace (i - k + k) with i in Hb by lia.
    rewrite Z.land_spec, Hb.
    apply Bool.andb_diag.
Qed.
Lemma greedy_mask_take_feasible_bit__solver_transitions :
  forall a b k ans,
    0 <= k ->
    GreedyMaskPrefixOptimal a b k ans ->
    MaskFeasible a b (Z.lor ans (Z.shiftl 1 k)) ->
    GreedyMaskPrefixOptimal a b (k - 1)
      (Z.lor ans (Z.shiftl 1 k)).
Proof.
  intros a b k ans Hk (Hans_feasible & Hnorm & Hbest) Htrial_feasible.
  pose proof
    (normalized_take_properties__solver_transitions ans k Hk Hnorm)
    as (Htrial_norm & Htrial_prefix).
  unfold GreedyMaskPrefixOptimal.
  split; [exact Htrial_feasible |].
  split.
  - replace (k - 1 + 1) with k by lia.
    exact Htrial_norm.
  - intros v Hv.
    replace (k - 1 + 1) with k by lia.
    specialize (Hbest v Hv).
    pose proof (shiftr_adjacent_bounds__solver_transitions v k) as Hvbound.
    lia.
Qed.
Lemma greedy_mask_skip_infeasible_bit__solver_transitions :
  forall a b k ans,
    0 <= k ->
    Zlength a = Zlength b ->
    GreedyMaskPrefixOptimal a b k ans ->
    ~ MaskFeasible a b (Z.lor ans (Z.shiftl 1 k)) ->
    GreedyMaskPrefixOptimal a b (k - 1) ans.
Proof.
  intros a b k ans Hk Hlen (Hans_feasible & Hnorm & Hbest) Htrial_bad.
  pose proof
    (normalized_skip_properties__solver_transitions ans k Hk Hnorm)
    as (Hans_norm & Hans_prefix).
  pose proof
    (normalized_take_properties__solver_transitions ans k Hk Hnorm)
    as (Htrial_norm & Htrial_prefix).
  unfold GreedyMaskPrefixOptimal.
  split; [exact Hans_feasible |].
  split.
  - replace (k - 1 + 1) with k by lia.
    exact Hans_norm.
  - intros v Hv.
    replace (k - 1 + 1) with k by lia.
    specialize (Hbest v Hv).
    pose proof (shiftr_adjacent_bounds__solver_transitions v k) as Hvbound.
    destruct (Z_lt_ge_dec (Z.shiftr v (k + 1))
      (Z.shiftr ans (k + 1))) as [Hless | Heq].
    + lia.
    + assert (Hhigh :
        Z.shiftr v (k + 1) = Z.shiftr ans (k + 1)) by lia.
      destruct (Z_le_gt_dec (Z.shiftr v k) (Z.shiftr ans k)) as [Hle | Hgt].
      * exact Hle.
      * exfalso.
        assert (Htrial_eq :
          Z.shiftr v k = Z.shiftr (Z.lor ans (Z.shiftl 1 k)) k)
          by lia.
        assert (Hland :
          Z.land v (Z.lor ans (Z.shiftl 1 k)) =
            Z.lor ans (Z.shiftl 1 k)).
        {
          eapply normalized_mask_in_value__solver_transitions; eauto.
        }
        apply Htrial_bad.
        eapply andcandidate_mask_feasible__solver_transitions; eauto.
Qed.
Lemma map_eq_Forall2__solver_final :
  forall (A B C : Type) (f : A -> C) (g : B -> C)
         (xs : list A) (ys : list B),
    map f xs = map g ys ->
    Forall2 (fun x y => f x = g y) xs ys.
Proof.
  intros A B C f g xs.
  induction xs as [|x xs IH]; intros ys Heq;
    destruct ys as [|y ys]; simpl in Heq; try discriminate.
  - constructor.
  - inversion Heq. constructor; auto.
Qed.
Lemma mask_permutation_pairing__solver_final :
  forall (a b : list Z) (mask : Z),
    Permutation (map (fun x => Z.land x mask) a)
                (map (fun y => Z.land (Z.lnot y) mask) b) ->
    exists p,
      Permutation p b /\
      Forall2
        (fun x y => Z.land x mask = Z.land (Z.lnot y) mask) a p.
Proof.
  intros a b mask Hperm.
  destruct (@Permutation_map_inv Z Z
    (fun y => Z.land (Z.lnot y) mask)
    (map (fun x => Z.land x mask) a) b Hperm)
    as (p & Hmap & Hp).
  exists p. split; [apply Permutation_sym; exact Hp|].
  eapply map_eq_Forall2__solver_final. exact Hmap.
Qed.
Lemma paired_mask_xor__solver_final :
  forall x y mask,
    Z.land x mask = Z.land (Z.lnot y) mask ->
    Z.land mask (Z.lxor x y) = mask.
Proof.
  intros x y mask Heq.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.lxor_spec by exact Hn.
  destruct (Z.testbit mask n) eqn:Hmask; simpl.
  - apply (f_equal (fun z => Z.testbit z n)) in Heq.
    rewrite !Z.land_spec in Heq by exact Hn.
    rewrite Z.lnot_spec in Heq by exact Hn.
    rewrite Hmask in Heq.
    repeat rewrite Bool.andb_true_r in Heq.
    rewrite Heq. destruct (Z.testbit y n); reflexivity.
  - reflexivity.
Qed.
Lemma mask_andlist_of_pairs__solver_final :
  forall (a p : list Z) mask,
    0 <= mask < Z.pow 2 30 ->
    Forall2
      (fun x y => Z.land x mask = Z.land (Z.lnot y) mask) a p ->
    Z.land mask
      (AndList30
        (map (fun q => Z.lxor (fst q) (snd q)) (combine a p))) = mask.
Proof.
  intros a p mask Hmask Hpairs.
  induction Hpairs as [|x y a p Hxy Hpairs IH].
  - simpl. change (Z.land mask (Z.ones 30) = mask).
    rewrite Z.land_ones by lia.
    rewrite Z.mod_small; lia.
  - simpl. rewrite Z.land_assoc.
    rewrite paired_mask_xor__solver_final by exact Hxy.
    exact IH.
Qed.
Lemma andlist30_nonnegative__solver_final :
  forall xs, 0 <= AndList30 xs.
Proof.
  induction xs as [|x xs IH]; simpl.
  - lia.
  - apply Z.land_nonneg. right. exact IH.
Qed.
Lemma land_le_right_nonnegative__solver_final :
  forall x y, 0 <= x -> 0 <= y -> Z.land x y <= y.
Proof.
  intros x y Hx Hy.
  destruct x as [|px|px], y as [|py|py]; simpl in *; try lia.
  change (Z.of_N (N.land (N.pos px) (N.pos py)) <= Z.of_N (N.pos py)).
  apply (proj1 (N2Z.inj_le _ _)). apply N.land_le_r.
Qed.
Lemma mask_feasible_candidate_extension__solver_final :
  forall (a b : list Z) mask,
    0 <= mask < Z.pow 2 30 ->
    MaskFeasible a b mask ->
    exists v, AndCandidate a b v /\ mask <= v.
Proof.
  intros a b mask Hmask Hfeasible.
  unfold MaskFeasible, MaskedLeft, MaskedComplementRight in Hfeasible.
  destruct (mask_permutation_pairing__solver_final a b mask Hfeasible)
    as (p & Hp & Hpairs).
  set (v := AndList30
    (map (fun q => Z.lxor (fst q) (snd q)) (combine a p))).
  exists v. split.
  - unfold AndCandidate. exists p. split; [exact Hp|reflexivity].
  - assert (Hvnonneg : 0 <= v).
    { unfold v. apply andlist30_nonnegative__solver_final. }
    assert (Hland : Z.land mask v = mask).
    { unfold v. apply mask_andlist_of_pairs__solver_final; assumption. }
    rewrite <- Hland.
    apply land_le_right_nonnegative__solver_final; lia.
Qed.
Lemma greedy_mask_at_minus_one_spec__solver_final :
  forall (a b : list Z) bit ans,
    0 <= ans < Z.pow 2 30 ->
    bit = -1 ->
    GreedyMaskPrefixOptimal a b bit ans ->
    Spec a b ans.
Proof.
  intros a b bit ans Hans Hbit Hgreedy. subst bit.
  destruct Hgreedy as (Hfeasible & _ & Hoptimal).
  destruct (mask_feasible_candidate_extension__solver_final
    a b ans Hans Hfeasible) as (v & Hcandidate & Hansv).
  assert (Hvans : v <= ans).
  { specialize (Hoptimal v Hcandidate).
    replace (-1 + 1) with 0 in Hoptimal by lia.
    repeat rewrite Z.shiftr_0_r in Hoptimal. exact Hoptimal. }
  assert (Heq : v = ans) by lia. subst v.
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists ans. split; [|reflexivity]. split; [exact Hcandidate|].
  intros v Hv.
  specialize (Hoptimal v Hv).
  replace (-1 + 1) with 0 in Hoptimal by lia.
  repeat rewrite Z.shiftr_0_r in Hoptimal. exact Hoptimal.
Qed.
