Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition LuckyTriple (n : Z) (triple : list Z * list Z * list Z) : Prop :=
  let '(a, b, c) := triple in
  Permutation a (Zrange 0 n) /\ Permutation b (Zrange 0 n) /\
  Permutation c (Zrange 0 n) /\
  forall i, 0 <= i < n -> (Znth i a 0 + Znth i b 0) mod n = Znth i c 0.

Definition Pre (n : Z) : Prop := 1 <= n <= 100000.

Definition Spec (n : Z) (out : option (list Z * list Z * list Z)) : Prop :=
  (exists triple, out = Some triple /\ LuckyTriple n triple) \/
  (out = None /\ forall triple, ~ LuckyTriple n triple).

Definition IdentityRange (len : Z) (xs : list Z) : Prop :=
  Zlength xs = len /\
  forall i, 0 <= i < len -> Znth i xs 0 = i.

Definition TwiceModRange (n len : Z) (xs : list Z) : Prop :=
  Zlength xs = len /\
  forall i, 0 <= i < len -> Znth i xs 0 = (2 * i) mod n.

Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Logic.FinFun.
Lemma identity_range_nil__identity_prefix :
  IdentityRange 0 (@nil Z).
Proof.
  unfold IdentityRange.
  split.
  - reflexivity.
  - intros j Hj.
    lia.
Qed.
Lemma identity_range_snoc__identity_prefix :
  forall (len : Z) (xs : list Z),
    IdentityRange len xs ->
    IdentityRange (len + 1) (xs ++ len :: nil).
Proof.
  intros len xs [Hlen Hpoint].
  unfold IdentityRange.
  split.
  - rewrite Zlength_app_cons, Hlen.
    lia.
  - intros j Hj.
    destruct (Z_lt_dec j len) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      apply Hpoint.
      lia.
    + assert (j = len) by lia.
      subst j.
      rewrite app_Znth2 by lia.
      rewrite Hlen, Z.sub_diag.
      apply Znth0_cons.
Qed.
Lemma land_odd_mod_two__identity_prefix :
  forall n : Z,
    0 < n ->
    Z.land n 1 <> 0 ->
    Z.rem n 2 = 1.
Proof.
  intros n Hpos Hland.
  assert (Hbit : Z.land n 1 = n mod 2).
  {
    change (Z.land n (Z.ones 1) = n mod 2).
    rewrite Z.land_ones by lia.
    reflexivity.
  }
  rewrite Hbit in Hland.
  assert (Hrem : Z.rem n 2 = n mod 2) by
    (apply Z.rem_mod_nonneg; lia).
  pose proof (Z.mod_pos_bound n 2 ltac:(lia)).
  rewrite Hrem.
  lia.
Qed.
Lemma twice_mod_range_nil__twice_mod_prefix :
  forall n, TwiceModRange n 0 nil.
Proof.
  intros n.
  unfold TwiceModRange.
  split.
  - reflexivity.
  - intros i Hi.
    lia.
Qed.
Lemma twice_mod_range_snoc__twice_mod_prefix :
  forall n len xs,
    0 <= len < n ->
    TwiceModRange n len xs ->
    TwiceModRange n (len + 1) (xs ++ ((2 * len) mod n :: nil)).
Proof.
  intros n len xs Hlen Hrange.
  unfold TwiceModRange in *.
  destruct Hrange as [Hzlen Hvalues].
  split.
  - rewrite Zlength_app_cons, Hzlen.
    lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j len) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      apply Hvalues.
      lia.
    + assert (j = len) by lia.
      subst j.
      rewrite app_Znth2 by lia.
      rewrite Hzlen.
      replace (len - len) with 0 by lia.
      reflexivity.
Qed.
Lemma Zlength_map__lucky_spec : forall {A B : Type} (f : A -> B) xs,
  Zlength (map f xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__lucky_spec : forall {A B : Type} (f : A -> B) xs
    (da : A) (db : B) i,
  0 <= i < Zlength xs ->
  Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_Zrange_aux__lucky_spec : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__lucky_spec : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__lucky_spec. lia.
Qed.
Lemma Znth_Zrange_aux__lucky_spec : forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__lucky_spec : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__lucky_spec by lia. lia.
Qed.
Lemma identity_range_permutation__lucky_spec : forall n xs,
  0 <= n -> IdentityRange n xs -> Permutation xs (Zrange 0 n).
Proof.
  intros n xs Hn [Hlen Hpoint].
  assert (Heq : xs = Zrange 0 n).
  {
    apply (proj2 (list_eq_ext xs (Zrange 0 n) 0)). split.
    - rewrite Zlength_Zrange__lucky_spec by lia. lia.
    - intros i Hi. rewrite Znth_Zrange__lucky_spec by lia.
      rewrite Hpoint by lia. lia.
  }
  subst xs. apply Permutation_refl.
Qed.
Lemma double_mod_injective_odd__lucky_spec : forall n x y,
  0 < n -> n mod 2 = 1 ->
  0 <= x < n -> 0 <= y < n ->
  (2 * x) mod n = (2 * y) mod n -> x = y.
Proof.
  intros n x y Hn Hodd Hx Hy Heq.
  assert (Hmod : (2 * x - 2 * y) mod n = 0).
  {
    rewrite Zminus_mod. rewrite Heq. rewrite Z.sub_diag, Zmod_0_l; lia.
  }
  apply Z.mod_divide in Hmod; [|lia].
  destruct Hmod as [k Hk].
  assert (-2 < k < 2) by nia.
  assert (Hcases : k = -1 \/ k = 0 \/ k = 1) by lia.
  destruct Hcases as [-> | [-> | ->]].
  - assert (Hpar : (2 * x - 2 * y) mod 2 = 0).
    { apply Z.mod_divide; [lia |]. exists (x - y). ring. }
    replace (2 * x - 2 * y) with (-n) in Hpar by nia.
    rewrite Z.mod_opp_l_nz, Hodd in Hpar by lia. discriminate.
  - nia.
  - assert (Hpar : (2 * x - 2 * y) mod 2 = 0).
    { apply Z.mod_divide; [lia |]. exists (x - y). ring. }
    replace (2 * x - 2 * y) with n in Hpar by nia.
    rewrite Hodd in Hpar. discriminate.
Qed.
Lemma NoDup_map_on__lucky_spec : forall {A B : Type} (f : A -> B) xs,
  NoDup xs ->
  (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
  NoDup (map f xs).
Proof.
  intros A B f xs Hnd. induction Hnd as [|x xs Hnot Hnd IH]; intros Hinj.
  - constructor.
  - simpl. constructor.
    + intro Hmap. apply in_map_iff in Hmap.
      destruct Hmap as [y [Heq Hy]].
      assert (x = y) by (eapply Hinj; simpl; eauto).
      subst y. contradiction.
    + apply IH. intros u v Hu Hv Heq.
      eapply Hinj; simpl; eauto.
Qed.
Lemma twice_mod_range_permutation_odd__lucky_spec : forall n xs,
  0 < n -> n mod 2 = 1 ->
  TwiceModRange n n xs -> Permutation xs (Zrange 0 n).
Proof.
  intros n xs Hn Hodd [Hlen Hpoint].
  set (f := fun i : Z => (2 * i) mod n).
  assert (Heq : xs = map f (Zrange 0 n)).
  {
    apply (proj2 (list_eq_ext xs (map f (Zrange 0 n)) 0)). split.
    - rewrite Zlength_map__lucky_spec, Zlength_Zrange__lucky_spec by lia.
      lia.
    - intros i Hi.
      rewrite (@Znth_map__lucky_spec Z Z f (Zrange 0 n) 0 0 i) by
        (rewrite Zlength_Zrange__lucky_spec by lia; lia).
      rewrite Znth_Zrange__lucky_spec by lia.
      unfold f. rewrite Hpoint by lia. f_equal.
  }
  subst xs. apply NoDup_Permutation_bis.
  - apply NoDup_map_on__lucky_spec.
    + apply NoDup_Zrange.
    + intros x y Hxin Hyin Hxy.
      apply double_mod_injective_odd__lucky_spec with n; auto;
        apply In_Zrange; assumption.
  - rewrite length_map. lia.
  - intros z Hz. apply in_map_iff in Hz.
    destruct Hz as [x [Hfx Hxin]]. rewrite <- Hfx. apply In_Zrange.
    apply In_Zrange in Hxin.
    apply Z.mod_pos_bound. lia.
Qed.
Lemma sum_permutation__lucky_spec : forall xs ys : list Z,
  Permutation xs ys -> ListLib.sum xs = ListLib.sum ys.
Proof.
  intros xs ys Hperm. induction Hperm; simpl; lia.
Qed.
Lemma twice_sum_Zrange_aux__lucky_spec : forall low m,
  ListLib.sum (Zrange_aux low m) + ListLib.sum (Zrange_aux low m) =
  Z.of_nat m * (2 * low + Z.of_nat m - 1).
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low.
  - simpl. ring.
  - rewrite Nat2Z.inj_succ.
    simpl Zrange_aux. simpl ListLib.sum.
    replace (low + ListLib.sum (Zrange_aux (low + 1) m) +
             (low + ListLib.sum (Zrange_aux (low + 1) m)))
      with (2 * low +
            (ListLib.sum (Zrange_aux (low + 1) m) +
             ListLib.sum (Zrange_aux (low + 1) m))) by ring.
    rewrite IH.
    ring.
Qed.
Lemma twice_sum_Zrange_zero__lucky_spec : forall n,
  0 <= n ->
  2 * ListLib.sum (Zrange 0 n) = n * (n - 1).
Proof.
  intros n Hn. unfold Zrange.
  replace (2 * ListLib.sum (Zrange_aux 0 (Z.to_nat (n - 0))))
    with (ListLib.sum (Zrange_aux 0 (Z.to_nat (n - 0))) +
          ListLib.sum (Zrange_aux 0 (Z.to_nat (n - 0)))) by ring.
  rewrite twice_sum_Zrange_aux__lucky_spec. rewrite Z2Nat.id by lia. ring.
Qed.
Lemma pointwise_mod_sum__lucky_spec : forall n a b c,
  n <> 0 ->
  Zlength a = Zlength b -> Zlength a = Zlength c ->
  (forall i, 0 <= i < Zlength a ->
    (Znth i a 0 + Znth i b 0) mod n = Znth i c 0) ->
  (ListLib.sum a + ListLib.sum b) mod n = ListLib.sum c mod n.
Proof.
  intros n a. induction a as [|x xs IH]; intros b c Hn Hab Hac Hpoint.
  - destruct b as [|y ys], c as [|z zs].
    + reflexivity.
    + rewrite Zlength_nil, Zlength_cons in Hac.
      pose proof (Zlength_nonneg zs). lia.
    + rewrite Zlength_nil, Zlength_cons in Hab.
      pose proof (Zlength_nonneg ys). lia.
    + rewrite Zlength_nil, Zlength_cons in Hab.
      pose proof (Zlength_nonneg ys). lia.
  - destruct b as [|y ys].
    { rewrite Zlength_cons, Zlength_nil in Hab.
      pose proof (Zlength_nonneg xs). lia. }
    destruct c as [|z zs].
    { rewrite Zlength_cons, Zlength_nil in Hac.
      pose proof (Zlength_nonneg xs). lia. }
    simpl ListLib.sum.
    pose proof (Zlength_nonneg xs) as Hxs_nonneg.
    rewrite !Zlength_cons in Hab, Hac.
    assert (Hhead : (x + y) mod n = z).
    {
      specialize (Hpoint 0).
      rewrite !Znth0_cons in Hpoint. apply Hpoint.
      rewrite Zlength_cons. lia.
    }
    assert (Htail : (ListLib.sum xs + ListLib.sum ys) mod n =
                    ListLib.sum zs mod n).
    {
      apply IH; try lia. intros i Hi.
      specialize (Hpoint (i + 1)). simpl in Hpoint.
      rewrite !Znth_cons in Hpoint by lia.
      replace (i + 1 - 1) with i in Hpoint by lia.
      apply Hpoint. rewrite Zlength_cons. lia.
    }
    replace (x + ListLib.sum xs + (y + ListLib.sum ys))
      with ((x + y) + (ListLib.sum xs + ListLib.sum ys)) by ring.
    rewrite Z.add_mod by assumption.
    rewrite Hhead, Htail.
    rewrite Z.add_mod by assumption.
    rewrite <- Hhead, Z.mod_mod by assumption.
    repeat rewrite Z.mod_mod by assumption.
    rewrite <- Z.add_mod by assumption.
    symmetry. apply Z.add_mod_idemp_l. assumption.
Qed.
Lemma lucky_triple_odd__lucky_spec : forall n triple,
  0 < n -> LuckyTriple n triple -> n mod 2 = 1.
Proof.
  intros n [[a b] c] Hn.
  unfold LuckyTriple. intros [Hpa [Hpb [Hpc Hpoint]]].
  assert (Hrange_len : Zlength (Zrange 0 n) = n) by
    (rewrite Zlength_Zrange__lucky_spec; lia).
  assert (Ha_len : Zlength a = n).
  { rewrite <- Hrange_len. rewrite !Zlength_correct. f_equal.
    apply Permutation_length. exact Hpa. }
  assert (Hb_len : Zlength b = n).
  { rewrite <- Hrange_len. rewrite !Zlength_correct. f_equal.
    apply Permutation_length. exact Hpb. }
  assert (Hc_len : Zlength c = n).
  { rewrite <- Hrange_len. rewrite !Zlength_correct. f_equal.
    apply Permutation_length. exact Hpc. }
  pose proof (sum_permutation__lucky_spec _ _ Hpa) as Hsa.
  pose proof (sum_permutation__lucky_spec _ _ Hpb) as Hsb.
  pose proof (sum_permutation__lucky_spec _ _ Hpc) as Hsc.
  assert (Hsum :
    (ListLib.sum a + ListLib.sum b) mod n = ListLib.sum c mod n).
  {
    apply pointwise_mod_sum__lucky_spec.
    - lia.
    - lia.
    - lia.
    - intros i Hi. apply Hpoint. lia.
  }
  assert (Hmod_bounds : 0 <= n mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  assert (Hcases : n mod 2 = 0 \/ n mod 2 = 1) by lia.
  destruct Hcases as [Heven | Hodd]; [|exact Hodd].
  exfalso.
  set (s := ListLib.sum (Zrange 0 n)) in *.
  assert (Htwice : 2 * s = n * (n - 1)).
  { unfold s. apply twice_sum_Zrange_zero__lucky_spec. lia. }
  assert (Hex : exists k, n = 2 * k).
  {
    apply Z.mod_divide in Heven; [|lia].
    destruct Heven as [k Hk]. exists k. nia.
  }
  destruct Hex as [k Hn2k].
  assert (Hk_bounds : 0 < k < n) by nia.
  assert (Hs : s = n * (k - 1) + k) by nia.
  assert (Hsmod : s mod n = k).
  { symmetry. apply Z.mod_unique_pos with (q := k - 1); lia. }
  assert (Htwmod : (2 * s) mod n = 0).
  { rewrite Htwice. apply Z.mod_divide; [lia |]. exists (n - 1). ring. }
  rewrite Hsa, Hsb, Hsc in Hsum.
  replace (s + s) with (2 * s) in Hsum by ring.
  rewrite Htwmod, Hsmod in Hsum. lia.
Qed.
Lemma land_even_mod_two__lucky_spec : forall n,
  0 < n -> Z.land n 1 = 0 -> n mod 2 = 0.
Proof.
  intros n Hn Hland.
  replace 1 with (Z.ones 1) in Hland by reflexivity.
  rewrite Z.land_ones in Hland by lia.
  simpl in Hland. exact Hland.
Qed.
Lemma rem_one_mod_two__lucky_spec : forall n,
  0 <= n -> Z.rem n 2 = 1 -> n mod 2 = 1.
Proof.
  intros n Hn Hrem. rewrite <- Zrem_Zmod_pos by lia. exact Hrem.
Qed.
