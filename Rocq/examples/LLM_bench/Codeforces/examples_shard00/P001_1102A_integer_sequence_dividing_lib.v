Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition DivisionDifference (n : Z) (left : Z -> Prop) (d : Z) : Prop :=
  d = Z.abs
        (sum (fun x : Z => 1 <= x < n + 1 /\ left x) (fun x => x) -
         sum (fun x : Z => 1 <= x < n + 1 /\ ~ left x) (fun x => x)).

Definition Pre (n : Z) : Prop :=
  1 <= n <= 2000000000.

Definition Spec (n out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      DivisionDifference n (fst candidate) (snd candidate))
    snd out.

Require Import Coq.micromega.Lia.
Lemma land_one_mod__partition_parity :
  forall z : Z, Z.land z 1 = z mod 2.
Proof.
  intros z.
  change (Z.land z (Z.ones 1) = z mod 2).
  rewrite Z.land_ones by lia.
  reflexivity.
Qed.
Lemma subset_sum_as_indicator__partition_parity :
  forall (low high : Z) (P : Z -> Prop) (f : Z -> Z),
    sum (fun x : Z => low <= x < high /\ P x) f =
    sum (fun x : Z => low <= x < high)
      (fun x => if prop_dec (P x) then f x else 0).
Proof.
  intros low high P f.
  unfold sum.
  cbn.
  induction (Zrange low high) as [|x xs IH]; cbn.
  - reflexivity.
  - destruct (prop_dec (P x)); cbn; rewrite ?IH; lia.
Qed.
Lemma range_sum_partition__partition_parity :
  forall (low high : Z) (P : Z -> Prop) (f : Z -> Z),
    sum (fun x : Z => low <= x < high) f =
    sum (fun x : Z => low <= x < high /\ P x) f +
    sum (fun x : Z => low <= x < high /\ ~ P x) f.
Proof.
  intros low high P f.
  rewrite !subset_sum_as_indicator__partition_parity.
  rewrite <- sum_Z_range_add.
  apply sum_Z_range_ext.
  intros x Hx.
  destruct (prop_dec (P x)); destruct (prop_dec (~ P x)); cbn; tauto || lia.
Qed.
Lemma consecutive_sum_formula__partition_parity :
  forall n : Z, 0 <= n ->
    sum (fun x : Z => 1 <= x < n + 1) (fun x => x) =
    n * (n + 1) / 2.
Proof.
  intros n Hn.
  assert (Hnat : forall k : nat,
    sum (fun x : Z => 1 <= x < Z.of_nat k + 1) (fun x => x) =
    Z.of_nat k * (Z.of_nat k + 1) / 2).
  {
    induction k as [|k IH].
    - rewrite sum_Z_range_empty by lia. reflexivity.
    - rewrite Nat2Z.inj_succ.
      replace (Z.succ (Z.of_nat k) + 1)
        with ((Z.of_nat k + 1) + 1) by lia.
      rewrite sum_Z_range_extend_right by lia.
      rewrite IH.
      replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) by lia.
      replace (Z.of_nat k + 1 + 1) with (Z.of_nat k + 2) by ring.
      replace ((Z.of_nat k + 1) * (Z.of_nat k + 2))
        with ((Z.of_nat k + 1) * 2 +
              Z.of_nat k * (Z.of_nat k + 1)) by ring.
      rewrite Z.div_add_l by lia.
      ring.
  }
  specialize (Hnat (Z.to_nat n)).
  rewrite Z2Nat.id in Hnat by lia.
  exact Hnat.
Qed.
Lemma subset_sum_extend_exclude__partition_parity :
  forall (high : Z) (P : Z -> Prop), 1 <= high ->
    sum (fun x : Z => 1 <= x < high + 1 /\ x < high /\ P x) (fun x => x) =
    sum (fun x : Z => 1 <= x < high /\ P x) (fun x => x).
Proof.
  intros high P Hhigh.
  rewrite !subset_sum_as_indicator__partition_parity.
  rewrite sum_Z_range_extend_right by lia.
  rewrite (sum_Z_range_ext 1 high
    (fun x => if prop_dec (x < high /\ P x) then x else 0)
    (fun x => if prop_dec (P x) then x else 0)).
  - destruct (prop_dec (high < high /\ P high)); cbn; [lia | ring].
  - intros x Hx.
    destruct (prop_dec (x < high /\ P x)); destruct (prop_dec (P x)); cbn; tauto.
Qed.
Lemma subset_sum_extend_include__partition_parity :
  forall (high : Z) (P : Z -> Prop), 1 <= high ->
    sum (fun x : Z => 1 <= x < high + 1 /\
      (x = high \/ (x < high /\ P x))) (fun x => x) =
    sum (fun x : Z => 1 <= x < high /\ P x) (fun x => x) + high.
Proof.
  intros high P Hhigh.
  rewrite !subset_sum_as_indicator__partition_parity.
  rewrite sum_Z_range_extend_right by lia.
  rewrite (sum_Z_range_ext 1 high
    (fun x => if prop_dec (x = high \/ (x < high /\ P x)) then x else 0)
    (fun x => if prop_dec (P x) then x else 0)).
  - destruct (prop_dec (high = high \/ (high < high /\ P high))); cbn; [ring | tauto].
  - intros x Hx.
    destruct (prop_dec (x = high \/ (x < high /\ P x))) as [HQ | HnQ];
      destruct (prop_dec (P x)) as [HP | HnP]; cbn.
    + reflexivity.
    + exfalso. destruct HQ as [Heq | [_ HP']]; [lia | tauto].
    + exfalso. apply HnQ. right. split; [lia | exact HP].
    + reflexivity.
Qed.
Lemma consecutive_subset_sum_representable__partition_parity :
  forall (k : nat) (s : Z),
    0 <= s <=
      sum (fun x : Z => 1 <= x < Z.of_nat k + 1) (fun x => x) ->
    exists P : Z -> Prop,
      sum (fun x : Z => 1 <= x < Z.of_nat k + 1 /\ P x)
        (fun x => x) = s.
Proof.
  induction k as [|k IH]; intros s Hs.
  - rewrite sum_Z_range_empty in Hs by lia.
    assert (s = 0) by lia. subst s.
    exists (fun _ => False).
    rewrite subset_sum_as_indicator__partition_parity.
    apply sum_Z_range_eq_zero.
    intros x Hx. destruct (prop_dec False); tauto.
  - rewrite Nat2Z.inj_succ.
    set (high := Z.of_nat k + 1).
    replace (Z.succ (Z.of_nat k) + 1) with (high + 1) in Hs |- * by (unfold high; lia).
    rewrite sum_Z_range_extend_right in Hs by (unfold high; lia).
    rewrite Nat2Z.inj_succ in Hs.
    replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) in Hs by lia.
    assert (Htotal_lower : high - 1 <=
      sum (fun x : Z => 1 <= x < high) (fun x => x)).
    {
      apply Z.le_trans with ((high - 1) * 1); [ring_simplify; lia |].
      apply sum_Z_range_lower_bound.
      - unfold high. lia.
      - intros x Hx. lia.
    }
    unfold high in *.
    destruct (Z_lt_ge_dec s (Z.of_nat k + 1)) as [Hsmall | Hlarge].
    + assert (Hs_old : 0 <= s <=
        sum (fun x : Z => 1 <= x < Z.of_nat k + 1) (fun x => x)) by lia.
      specialize (IH s Hs_old) as [P HP].
      exists (fun x => x < Z.of_nat k + 1 /\ P x).
      rewrite subset_sum_extend_exclude__partition_parity by lia.
      exact HP.
    + assert (Hs_old : 0 <= s - (Z.of_nat k + 1) <=
        sum (fun x : Z => 1 <= x < Z.of_nat k + 1) (fun x => x)).
      {
        split.
        - lia.
        - lia.
      }
      specialize (IH (s - (Z.of_nat k + 1)) Hs_old) as [P HP].
      exists (fun x => x = Z.of_nat k + 1 \/
        (x < Z.of_nat k + 1 /\ P x)).
      rewrite subset_sum_extend_include__partition_parity by lia.
      rewrite HP. ring.
Qed.
Lemma balanced_consecutive_partition__partition_parity :
  forall n : Z, 1 <= n ->
    exists left : Z -> Prop,
      DivisionDifference n left (Z.land (n * (n + 1) / 2) 1).
Proof.
  intros n Hn.
  assert (Hnat : n = Z.of_nat (Z.to_nat n)) by lia.
  pose proof (consecutive_sum_formula__partition_parity n ltac:(lia)) as Htotal.
  assert (HTnonneg : 0 <= n * (n + 1) / 2).
  {
    rewrite <- Htotal.
    apply sum_nonneg. intros x Hx. lia.
  }
  pose proof (Z.div_mod (n * (n + 1) / 2) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (n * (n + 1) / 2) 2 ltac:(lia)) as Hmodbound.
  assert (Hhalf : 0 <= (n * (n + 1) / 2) / 2 <= n * (n + 1) / 2) by nia.
  assert (Htotal_nat :
    sum (fun x : Z => 1 <= x < Z.of_nat (Z.to_nat n) + 1)
      (fun x => x) = n * (n + 1) / 2).
  {
    rewrite <- Hnat.
    exact Htotal.
  }
  assert (Hhalf_repr : 0 <= (n * (n + 1) / 2) / 2 <=
    sum (fun x : Z => 1 <= x < Z.of_nat (Z.to_nat n) + 1)
      (fun x => x)).
  {
    rewrite Htotal_nat.
    exact Hhalf.
  }
  destruct (consecutive_subset_sum_representable__partition_parity
    (Z.to_nat n) ((n * (n + 1) / 2) / 2) Hhalf_repr) as [left Hleft].
  assert (Hleft_n :
    sum (fun x : Z => 1 <= x < n + 1 /\ left x) (fun x => x) =
    (n * (n + 1) / 2) / 2).
  {
    rewrite <- Hnat in Hleft.
    exact Hleft.
  }
  exists left.
  unfold DivisionDifference.
  pose proof (range_sum_partition__partition_parity 1 (n + 1) left
    (fun x => x)) as Hpartition.
  rewrite Htotal in Hpartition.
  rewrite Hleft_n in Hpartition.
  rewrite land_one_mod__partition_parity.
  nia.
Qed.
Lemma partition_difference_parity_lower_bound__partition_parity :
  forall (n : Z) (left : Z -> Prop) (d : Z),
    0 <= n -> DivisionDifference n left d ->
    Z.land (n * (n + 1) / 2) 1 <= d.
Proof.
  intros n left d Hn Hd.
  unfold DivisionDifference in Hd.
  subst d.
  pose proof (consecutive_sum_formula__partition_parity n Hn) as Htotal.
  pose proof (range_sum_partition__partition_parity 1 (n + 1) left
    (fun x => x)) as Hpartition.
  rewrite Htotal in Hpartition.
  rewrite land_one_mod__partition_parity.
  pose proof (Z.mod_pos_bound (n * (n + 1) / 2) 2 ltac:(lia)) as Hmodbound.
  pose proof (Z.abs_nonneg
    (sum (fun x : Z => 1 <= x < n + 1 /\ left x) (fun x => x) -
     sum (fun x : Z => 1 <= x < n + 1 /\ ~ left x) (fun x => x))) as Habs.
  assert (Hparity :
    n * (n + 1) / 2 mod 2 = 0 \/
    n * (n + 1) / 2 mod 2 = 1) by lia.
  destruct Hparity as [Hparity | Hparity].
  - lia.
  - destruct (Z.eq_dec
      (Z.abs
        (sum (fun x : Z => 1 <= x < n + 1 /\ left x) (fun x => x) -
         sum (fun x : Z => 1 <= x < n + 1 /\ ~ left x) (fun x => x))) 0)
      as [Habszero | Habsnonzero].
    + assert (Hzero :
        sum (fun x : Z => 1 <= x < n + 1 /\ left x) (fun x => x) -
        sum (fun x : Z => 1 <= x < n + 1 /\ ~ left x) (fun x => x) = 0).
      {
        apply (proj1 (Z.abs_0_iff _)).
        exact Habszero.
      }
      assert (Heven : n * (n + 1) / 2 mod 2 = 0).
      {
        replace (n * (n + 1) / 2) with
          (sum (fun x : Z => 1 <= x < n + 1 /\ left x)
            (fun x => x) * 2) by lia.
        apply Z.mod_mul. lia.
      }
      lia.
    + lia.
Qed.
Lemma spec_parity_optimal__partition_parity :
  forall n : Z, 1 <= n ->
    Spec n (Z.land (n * (n + 1) / 2) 1).
Proof.
  intros n Hn.
  destruct (balanced_consecutive_partition__partition_parity n Hn)
    as [left Hleft].
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (left, Z.land (n * (n + 1) / 2) 1).
  split.
  - split.
    + exact Hleft.
    + intros [other difference] Hother.
      simpl in *.
      eapply partition_difference_parity_lower_bound__partition_parity.
      * lia.
      * exact Hother.
  - reflexivity.
Qed.
