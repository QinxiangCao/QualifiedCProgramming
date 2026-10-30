Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(k:Z,a:list Z)->Z. Output is the minimum number of
   positions changed to obtain a {1,2}-valued array of period k. *)
Definition KPeriodic (k : Z) (a : list Z) : Prop :=
  (k | Zlength a) /\ forall i, 0 <= i < Zlength a - k -> Znth i a 0 = Znth (i + k) a 0.
Definition DifferenceCount (a b : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength a /\ Znth i a 0 <> Znth i b 0).
Definition Pre (k : Z) (a : list Z) : Prop :=
  (* 1 <= k <= Zlength a /\ *)
  (* Zlength a <= 100 /\  *)
  (k | Zlength a) 
  (* /\ Forall (fun x => x = 1 \/ x = 2) a *)
  .
Definition Spec (k : Z) (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (fun d => exists b, Zlength b = Zlength a /\
 Forall (fun x => x = 1 \/ x = 2) b /\ KPeriodic k b /\ d = DifferenceCount a b) (fun x => x) out.

(* Mathematical cost of making one residue class constant. *)
Definition ResidueValueCount
    (k r upto value : Z) (a : list Z) : Z :=
  #(fun i : Z =>
      0 <= i < Zlength a /\
      i < upto /\
      Z.modulo i k = r /\
      Znth i a 0 = value).

Definition ResidueChangeCost (k r : Z) (a : list Z) : Z :=
  Z.min (ResidueValueCount k r (Zlength a) 1 a)
        (ResidueValueCount k r (Zlength a) 2 a).

Definition ProcessedChangeCost (k r : Z) (a : list Z) : Z :=
  fold_right Z.add 0
    (map
       (fun rn => ResidueChangeCost k (Z.of_nat rn) a)
       (seq 0 (Z.to_nat r))).

Definition PrefixCost
    (k r : Z) (a : list Z) (changes : Z) : Prop :=
  changes = ProcessedChangeCost k r a.

Definition ResidueScan
    (k r upto : Z) (a : list Z) (ones twos : Z) : Prop :=
  ones = ResidueValueCount k r upto 1 a /\
  twos = ResidueValueCount k r upto 2 a.

From Coq Require Import Lia.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.setoid_ring.Ring.
Lemma set_card_empty__initialization :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma residue_value_count_initial_zero__initialization :
  forall k r value a,
    1 <= k -> 0 <= r < k ->
    ResidueValueCount k r r value a = 0.
Proof.
  intros k r value a Hk Hr.
  unfold ResidueValueCount.
  apply set_card_empty__initialization.
  intros i (Hi & Hupto & Hmod & Hvalue).
  rewrite Z.mod_small in Hmod by lia.
  lia.
Qed.
Lemma set_card_ext__residue_accounting :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intro x.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv.
  }
  induction Hperm; simpl; try reflexivity.
  - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
            1 + fold_right (fun _ acc => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma set_card_Z_as_sum__residue_accounting :
  forall (low high : Z) (P : Z -> Prop),
    #(fun x : Z => low <= x < high /\ P x) =
    SumLib.Sum.sum (fun x : Z => low <= x < high)
      (fun x => if prop_dec (P x) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun x => if prop_dec (P x) then true else false) xs) =
    fold_right (fun x acc : Z =>
      (if prop_dec (P x) then 1 else 0) + acc) 0 xs).
  {
    induction xs as [|x xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P x)); simpl.
    - exact (f_equal (fun z : Z => 1 + z) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__residue_accounting :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun x : Z => low <= x < high + 1 /\ P x) =
    #(fun x : Z => low <= x < high /\ P x) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__residue_accounting.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__residue_accounting :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun x : Z => low <= x < high + 1 /\ P x) =
    #(fun x : Z => low <= x < high /\ P x).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__residue_accounting.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction | lia].
Qed.
Lemma fold_sum_zero__residue_accounting :
  forall {A : Type} (xs : list A),
    fold_right (fun _ acc => 0 + acc) 0 xs = 0.
Proof.
  intros A xs. induction xs; simpl; auto.
Qed.
Lemma fold_sum_add__residue_accounting :
  forall {A : Type} (xs : list A) (f g : A -> Z),
    fold_right (fun x acc => (f x + g x) + acc) 0 xs =
    fold_right (fun x acc => f x + acc) 0 xs +
    fold_right (fun x acc => g x + acc) 0 xs.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros f g; simpl; [lia |].
  rewrite IH. lia.
Qed.
Lemma fold_sum_nested_swap__residue_accounting :
  forall {A B : Type} (xs : list A) (ys : list B) (f : A -> B -> Z),
    fold_right
      (fun x acc => fold_right (fun y acc' => f x y + acc') 0 ys + acc)
      0 xs =
    fold_right
      (fun y acc => fold_right (fun x acc' => f x y + acc') 0 xs + acc)
      0 ys.
Proof.
  intros A B xs.
  induction xs as [|x xs IH]; intros ys f; simpl.
  - rewrite fold_sum_zero__residue_accounting. reflexivity.
  - rewrite IH.
    rewrite <- fold_sum_add__residue_accounting.
    reflexivity.
Qed.
Lemma sum_Z_range_swap__residue_accounting :
  forall (xlow xhigh ylow yhigh : Z) (f : Z -> Z -> Z),
    SumLib.Sum.sum (fun x => xlow <= x < xhigh)
      (fun x => SumLib.Sum.sum (fun y => ylow <= y < yhigh) (fun y => f x y)) =
    SumLib.Sum.sum (fun y => ylow <= y < yhigh)
      (fun y => SumLib.Sum.sum (fun x => xlow <= x < xhigh) (fun x => f x y)).
Proof.
  intros.
  unfold SumLib.Sum.sum.
  apply fold_sum_nested_swap__residue_accounting.
Qed.
Lemma sum_indicator_eq_le_one__residue_accounting :
  forall low high z,
    low <= high ->
    SumLib.Sum.sum (fun x : Z => low <= x < high)
      (fun x => if prop_dec (z = x) then 1 else 0) <= 1.
Proof.
  intros low high z Hrange.
  destruct (Z_lt_le_dec z low) as [Hzlow | Hlowz].
  - rewrite SumLib.ZRange.sum_Z_range_eq_zero.
    + lia.
    + intros x Hx. destruct (prop_dec (z = x)); [lia | reflexivity].
  - destruct (Z_lt_ge_dec z high) as [Hzhigh | Hhighz].
    + rewrite (SumLib.ZRange.sum_Z_range_split low z high) by lia.
      rewrite (SumLib.ZRange.sum_Z_range_split z (z + 1) high) by lia.
      rewrite (SumLib.ZRange.sum_Z_range_eq_zero low z).
      2:{ intros x Hx. destruct (prop_dec (z = x)); [lia | reflexivity]. }
      rewrite SumLib.ZRange.sum_Z_range_single.
      rewrite (SumLib.ZRange.sum_Z_range_eq_zero (z + 1) high).
      2:{ intros x Hx. destruct (prop_dec (z = x)); [lia | reflexivity]. }
      destruct (prop_dec (z = z)); lia.
    + rewrite SumLib.ZRange.sum_Z_range_eq_zero.
      * lia.
      * intros x Hx. destruct (prop_dec (z = x)); [lia | reflexivity].
Qed.
Lemma map_Z_of_nat_seq__residue_accounting :
  forall start len,
    map Z.of_nat (seq start len) = Zrange_aux (Z.of_nat start) len.
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intro start; simpl; [reflexivity |].
  rewrite IH.
  replace (Z.of_nat (S start)) with (Z.of_nat start + 1) by lia.
  reflexivity.
Qed.
Lemma processed_change_cost_as_sum__residue_accounting :
  forall k r a,
    0 <= r ->
    ProcessedChangeCost k r a =
    SumLib.Sum.sum (fun s : Z => 0 <= s < r)
      (fun s => ResidueChangeCost k s a).
Proof.
  intros k r a Hr.
  unfold ProcessedChangeCost.
  rewrite <- (@map_map nat Z Z Z.of_nat
    (fun s => ResidueChangeCost k s a) (seq 0 (Z.to_nat r))).
  rewrite map_Z_of_nat_seq__residue_accounting.
  rewrite SumLib.ZRange.sum_range_unfold.
  unfold Zrange.
  replace (r - 0) with r by lia.
  change
    (fold_right Z.add 0
       (map (fun s => ResidueChangeCost k s a)
          (Zrange_aux 0 (Z.to_nat r))) =
     fold_right (fun s acc => ResidueChangeCost k s a + acc) 0
       (Zrange_aux 0 (Z.to_nat r))).
  generalize (Zrange_aux 0 (Z.to_nat r)) as xs.
  intro xs. induction xs as [|x xs IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.
Lemma processed_change_cost_succ__residue_accounting :
  forall k r a,
    0 <= r ->
    ProcessedChangeCost k (r + 1) a =
    ProcessedChangeCost k r a + ResidueChangeCost k r a.
Proof.
  intros k r a Hr.
  rewrite !processed_change_cost_as_sum__residue_accounting by lia.
  apply SumLib.ZRange.sum_Z_range_extend_right.
  lia.
Qed.
Lemma residue_value_count_canonical_step__residue_accounting :
  forall k r i q value a,
    1 <= k -> 0 <= r < k -> i = r + q * k -> 0 <= q ->
    i < Zlength a ->
    ResidueValueCount k r (i + k) value a =
    #(fun x : Z =>
        0 <= x < i + 1 /\
        x < Zlength a /\ Z.modulo x k = r /\ Znth x a 0 = value).
Proof.
  intros k r i q value a Hk Hr Hi Hq Hin.
  unfold ResidueValueCount.
  apply set_card_ext__residue_accounting.
  intro x.
  split.
  - intros ((Hx0 & Hxn) & Hxu & Hmod & Hval).
    repeat split; try assumption.
    assert (Himod : Z.modulo i k = r).
    {
      apply Zdivide_mod_minus.
      - exact Hr.
      - exists q. subst i. lia.
    }
    assert (Hxle : x <= i).
    {
      destruct (Z_le_gt_dec x i); [assumption |].
      assert (Hdmod : Z.modulo (x - i) k = 0).
      {
        rewrite Zminus_mod by lia.
        rewrite Hmod, Himod, Z.sub_diag.
        apply Z.mod_0_l. lia.
      }
      rewrite Z.mod_small in Hdmod by lia.
      lia.
    }
    lia.
  - intros ((Hx0 & Hxhi) & Hxn & Hmod & Hval).
    repeat split; try assumption; lia.
Qed.
Lemma residue_value_count_canonical_old__residue_accounting :
  forall k r i value a,
    i < Zlength a ->
    ResidueValueCount k r i value a =
    #(fun x : Z =>
        0 <= x < i /\
        x < Zlength a /\ Z.modulo x k = r /\ Znth x a 0 = value).
Proof.
  intros k r i value a Hin.
  unfold ResidueValueCount.
  apply set_card_ext__residue_accounting.
  intro x. intuition lia.
Qed.
Lemma residue_value_count_step_eq__residue_accounting :
  forall k r i q value a,
    1 <= k -> 0 <= r < k -> i = r + q * k -> 0 <= q ->
    i < Zlength a -> Znth i a 0 = value ->
    ResidueValueCount k r (i + k) value a =
    ResidueValueCount k r i value a + 1.
Proof.
  intros k r i q value a Hk Hr Hi Hq Hin Hval.
  rewrite residue_value_count_canonical_step__residue_accounting
    with (q := q) by assumption.
  rewrite residue_value_count_canonical_old__residue_accounting by assumption.
  apply set_card_Z_extend_true__residue_accounting.
  - assert (Hi0 : 0 <= i) by (subst i; nia). lia.
  - repeat split; try assumption.
    apply Zdivide_mod_minus.
    + exact Hr.
    + exists q. subst i. lia.
Qed.
Lemma residue_value_count_step_neq__residue_accounting :
  forall k r i q value a,
    1 <= k -> 0 <= r < k -> i = r + q * k -> 0 <= q ->
    i < Zlength a -> Znth i a 0 <> value ->
    ResidueValueCount k r (i + k) value a =
    ResidueValueCount k r i value a.
Proof.
  intros k r i q value a Hk Hr Hi Hq Hin Hval.
  rewrite residue_value_count_canonical_step__residue_accounting
    with (q := q) by assumption.
  rewrite residue_value_count_canonical_old__residue_accounting by assumption.
  apply set_card_Z_extend_false__residue_accounting.
  - assert (Hi0 : 0 <= i) by (subst i; nia). lia.
  - intros (_ & _ & Heq). contradiction.
Qed.
Lemma residue_scan_step__residue_accounting :
  forall k r i q a ones twos,
    1 <= k -> 0 <= r < k -> i = r + q * k -> 0 <= q ->
    i < Zlength a -> ResidueScan k r i a ones twos ->
    (Znth i a 0 = 1 ->
       ResidueScan k r (i + k) a (ones + 1) twos) /\
    (Znth i a 0 = 2 ->
       ResidueScan k r (i + k) a ones (twos + 1)).
Proof.
  intros k r i q a ones twos Hk Hr Hi Hq Hin [Hones Htwos].
  split; intro Hvalue; unfold ResidueScan.
  - split.
    + rewrite Hones.
      symmetry.
      apply residue_value_count_step_eq__residue_accounting with (q := q);
        assumption.
    + rewrite Htwos.
      symmetry.
      apply residue_value_count_step_neq__residue_accounting with (q := q);
        try assumption; lia.
  - split.
    + rewrite Hones.
      symmetry.
      apply residue_value_count_step_neq__residue_accounting with (q := q);
        try assumption; lia.
    + rewrite Htwos.
      symmetry.
      apply residue_value_count_step_eq__residue_accounting with (q := q);
        assumption.
Qed.
Lemma residue_value_count_as_sum__residue_accounting :
  forall k r upto value a,
    ResidueValueCount k r upto value a =
    SumLib.Sum.sum (fun x : Z => 0 <= x < Zlength a)
      (fun x =>
         if prop_dec (x < upto /\ Z.modulo x k = r /\ Znth x a 0 = value)
         then 1 else 0).
Proof.
  intros k r upto value a.
  unfold ResidueValueCount.
  rewrite set_card_Z_as_sum__residue_accounting.
  apply SumLib.ZRange.sum_Z_range_ext.
  intros x Hx.
  destruct (prop_dec (x < Zlength a /\
             x < upto /\ Z.modulo x k = r /\ Znth x a 0 = value)) as [HP | HnP];
  destruct (prop_dec (x < upto /\ Z.modulo x k = r /\ Znth x a 0 = value)) as [HQ | HnQ];
  try reflexivity; exfalso; intuition (auto with *).
Qed.
Lemma two_disjoint_indicators_le_one__residue_accounting :
  forall (P Q : Prop),
    ~ (P /\ Q) ->
    (if prop_dec P then 1 else 0) + (if prop_dec Q then 1 else 0) <= 1.
Proof.
  intros P Q Hdisjoint.
  destruct (prop_dec P); destruct (prop_dec Q); simpl; intuition lia.
Qed.
Lemma indicator_imp_le__residue_accounting :
  forall (P Q : Prop),
    (P -> Q) ->
    (if prop_dec P then 1 else 0) <= (if prop_dec Q then 1 else 0).
Proof.
  intros P Q Himp.
  destruct (prop_dec P); destruct (prop_dec Q); simpl; intuition lia.
Qed.
Lemma residue_scan_bounds__residue_accounting :
  forall k r upto a ones twos,
    ResidueScan k r upto a ones twos ->
    0 <= ones /\ 0 <= twos /\ ones + twos <= Zlength a.
Proof.
  intros k r upto a ones twos [Hones Htwos].
  rewrite Hones, Htwos.
  rewrite !residue_value_count_as_sum__residue_accounting.
  assert (Hlen : 0 <= Zlength a) by apply Zlength_nonneg.
  repeat split.
  - apply SumLib.Sum.sum_nonneg.
    intros x Hx. destruct prop_dec; lia.
  - apply SumLib.Sum.sum_nonneg.
    intros x Hx. destruct prop_dec; lia.
  - rewrite <- SumLib.ZRange.sum_Z_range_add.
    eapply Z.le_trans.
    + apply SumLib.ZRange.sum_Z_range_le.
      intros x Hx.
      apply two_disjoint_indicators_le_one__residue_accounting.
      intros [Hone Htwo].
      pose proof (proj2 (proj2 Hone)) as Hone_value.
      pose proof (proj2 (proj2 Htwo)) as Htwo_value.
      lia.
    + rewrite SumLib.ZRange.sum_Z_range_const by exact Hlen.
      lia.
Qed.
Lemma residue_scan_complete__residue_accounting :
  forall k r i a ones twos,
    Zlength a <= i -> ResidueScan k r i a ones twos ->
    ones = ResidueValueCount k r (Zlength a) 1 a /\
    twos = ResidueValueCount k r (Zlength a) 2 a.
Proof.
  intros k r i a ones twos Hi [Hones Htwos].
  split.
  - rewrite Hones. unfold ResidueValueCount.
    apply set_card_ext__residue_accounting.
    intro x. intuition lia.
  - rewrite Htwos. unfold ResidueValueCount.
    apply set_card_ext__residue_accounting.
    intro x. intuition lia.
Qed.
Lemma residue_value_count_full_as_sum__residue_accounting :
  forall k r value a,
    ResidueValueCount k r (Zlength a) value a =
    SumLib.Sum.sum (fun x : Z => 0 <= x < Zlength a)
      (fun x => if prop_dec (Z.modulo x k = r /\ Znth x a 0 = value)
                then 1 else 0).
Proof.
  intros k r value a.
  rewrite residue_value_count_as_sum__residue_accounting.
  apply SumLib.ZRange.sum_Z_range_ext.
  intros x Hx.
  destruct prop_dec; destruct prop_dec; try reflexivity; exfalso;
    intuition (auto with *).
Qed.
Lemma processed_change_cost_partial_bound__residue_accounting :
  forall k r i a changes ones twos,
    Pre k a -> 0 <= r < k -> PrefixCost k r a changes ->
    Zlength a <= i -> ResidueScan k r i a ones twos ->
    changes + Z.min ones twos <= Zlength a.
Proof.
  intros k r i a changes ones twos Hpre Hr Hprefix Hi Hscan.
  unfold PrefixCost in Hprefix.
  subst changes.
  destruct (residue_scan_complete__residue_accounting
    k r i a ones twos Hi Hscan) as [Hones Htwos].
  rewrite Hones, Htwos.
  change (ProcessedChangeCost k r a + ResidueChangeCost k r a <= Zlength a).
  rewrite processed_change_cost_as_sum__residue_accounting by lia.
  rewrite <- SumLib.ZRange.sum_Z_range_extend_right by lia.
  eapply Z.le_trans.
  - apply SumLib.ZRange.sum_Z_range_le.
    intros s Hs.
    unfold ResidueChangeCost.
    apply Z.le_min_l.
  - assert (Heq :
      SumLib.Sum.sum (fun s : Z => 0 <= s < r + 1)
        (fun s => ResidueValueCount k s (Zlength a) 1 a) =
      SumLib.Sum.sum (fun x : Z => 0 <= x < Zlength a)
        (fun x => SumLib.Sum.sum (fun s : Z => 0 <= s < r + 1)
          (fun s => if prop_dec (Z.modulo x k = s /\ Znth x a 0 = 1)
                    then 1 else 0))).
    {
      transitivity
        (SumLib.Sum.sum (fun s : Z => 0 <= s < r + 1)
          (fun s => SumLib.Sum.sum (fun x : Z => 0 <= x < Zlength a)
            (fun x => if prop_dec (Z.modulo x k = s /\ Znth x a 0 = 1)
                      then 1 else 0))).
      - apply SumLib.ZRange.sum_Z_range_ext.
        intros s Hs.
        apply residue_value_count_full_as_sum__residue_accounting.
      - apply sum_Z_range_swap__residue_accounting.
    }
    rewrite Heq.
    eapply Z.le_trans.
    + apply SumLib.ZRange.sum_Z_range_le.
      intros x Hx.
      eapply Z.le_trans.
      * apply SumLib.ZRange.sum_Z_range_le.
        intros s Hs.
        apply indicator_imp_le__residue_accounting.
        intros [Hmod Hvalue]. exact Hmod.
      * apply sum_indicator_eq_le_one__residue_accounting. lia.
    + rewrite SumLib.ZRange.sum_Z_range_const by apply Zlength_nonneg.
      lia.
Qed.
Lemma set_card_extensional__final_result :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros x.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
            1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma set_card_Z_as_sum__final_result :
  forall (low high : Z) (P : Z -> Prop),
    #(fun x : Z => low <= x < high /\ P x) =
    SumLib.Sum.sum (fun x : Z => low <= x < high)
      (fun x => if prop_dec (P x) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun x => if prop_dec (P x) then true else false) xs) =
    fold_right (fun x acc : Z =>
      (if prop_dec (P x) then 1 else 0) + acc) 0 xs).
  {
    induction xs as [|x xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P x)); simpl.
    - exact (f_equal (fun z : Z => 1 + z) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_bounded_extensional__final_result :
  forall (low high : Z) (P Q : Z -> Prop),
    (forall x, low <= x < high -> (P x <-> Q x)) ->
    #(fun x : Z => low <= x < high /\ P x) =
    #(fun x : Z => low <= x < high /\ Q x).
Proof.
  intros low high P Q Heq.
  apply set_card_extensional__final_result.
  intros x. split; intros [Hx HP]; split; auto.
  - apply (proj1 (Heq x Hx)); exact HP.
  - apply (proj2 (Heq x Hx)); exact HP.
Qed.
Lemma set_card_Z_bounded_subset__final_result :
  forall (low high : Z) (P Q : Z -> Prop),
    (forall x, low <= x < high -> P x -> Q x) ->
    #(fun x : Z => low <= x < high /\ P x) <=
    #(fun x : Z => low <= x < high /\ Q x).
Proof.
  intros low high P Q Hsub.
  rewrite !set_card_Z_as_sum__final_result.
  apply SumLib.ZRange.sum_Z_range_le.
  intros x Hx.
  destruct (prop_dec (P x)); destruct (prop_dec (Q x)); try lia.
  exfalso; eauto.
Qed.
Lemma set_card_Z_bounded_disjoint_or__final_result :
  forall (low high : Z) (P Q : Z -> Prop),
    (forall x, low <= x < high -> ~ (P x /\ Q x)) ->
    #(fun x : Z => low <= x < high /\ (P x \/ Q x)) =
    #(fun x : Z => low <= x < high /\ P x) +
    #(fun x : Z => low <= x < high /\ Q x).
Proof.
  intros low high P Q Hdisj.
  rewrite !set_card_Z_as_sum__final_result.
  rewrite <- SumLib.Sum.sum_add.
  apply SumLib.Sum.sum_ext.
  intros x Hx.
  destruct (prop_dec (P x)); destruct (prop_dec (Q x));
    destruct (prop_dec (P x \/ Q x)); try lia; try tauto.
  exfalso. apply (Hdisj x Hx). tauto.
Qed.
Lemma seq_snoc__final_result :
  forall start len : nat,
    seq start (S len) = seq start len ++ [(start + len)%nat].
Proof.
  intros start len.
  change (seq start (S len) =
    seq start len ++ seq (start + len)%nat 1).
  rewrite <- seq_app.
  f_equal. lia.
Qed.
Lemma fold_right_add_map_le__final_result :
  forall {A : Type} (f g : A -> Z) (xs : list A),
    (forall x, In x xs -> f x <= g x) ->
    fold_right Z.add 0 (map f xs) <= fold_right Z.add 0 (map g xs).
Proof.
  intros A f g xs. induction xs as [|x xs IH]; intros Hle; simpl.
  - lia.
  - assert (Hhead := Hle x (or_introl eq_refl)).
    assert (Htail : forall y, In y xs -> f y <= g y).
    { intros y Hy. apply Hle. now right. }
    specialize (IH Htail). lia.
Qed.
Lemma fold_right_Zadd_app__final_result :
  forall xs ys : list Z,
    fold_right Z.add 0 (xs ++ ys) =
    fold_right Z.add 0 xs + fold_right Z.add 0 ys.
Proof.
  intros xs ys. induction xs as [|x xs IH]; simpl; [lia |].
  rewrite IH. lia.
Qed.
Lemma fold_residue_cards_partial__final_result :
  forall (m : nat) (k n : Z) (P : Z -> Prop),
    0 < k ->
    fold_right Z.add 0
      (map (fun rn =>
        #(fun i : Z => 0 <= i < n /\
          Z.modulo i k = Z.of_nat rn /\ P i))
        (seq 0 m)) =
    #(fun i : Z => 0 <= i < n /\
      Z.modulo i k < Z.of_nat m /\ P i).
Proof.
  induction m as [|m IH]; intros k n P Hk.
  - simpl.
    rewrite set_card_Z_as_sum__final_result.
    transitivity (SumLib.Sum.sum (fun i : Z => 0 <= i < n)
      (fun _ => 0)).
    + symmetry. apply SumLib.Sum.sum_zero.
    + apply SumLib.Sum.sum_ext. intros i Hi.
      destruct (prop_dec (Z.modulo i k < 0 /\ P i)) as [[Hbad _] | _].
      * pose proof (Z.mod_pos_bound i k Hk). lia.
      * reflexivity.
  - rewrite seq_snoc__final_result, map_app,
      fold_right_Zadd_app__final_result. simpl.
    rewrite (IH k n P Hk).
    rewrite Z.add_0_r.
    rewrite <- set_card_Z_bounded_disjoint_or__final_result.
    + apply set_card_Z_bounded_extensional__final_result.
      intros i Hi.
      assert (Hmod0 : 0 <= Z.modulo i k) by (apply Z.mod_pos_bound; lia).
      split.
      * intros [[Hlt HP] | [Heq HP]].
        -- split; [lia | exact HP].
        -- split; [lia | exact HP].
      * intros [Hlt HP].
        destruct (Z.lt_trichotomy (Z.modulo i k) (Z.of_nat m))
          as [Hsmall | [Heq | Hlarge]].
        -- left. split; assumption.
        -- right. split; assumption.
        -- exfalso. lia.
    + intros i Hi [[Hlt _] [Heq _]]. lia.
Qed.
Lemma set_card_partition_residues__final_result :
  forall (k n : Z) (P : Z -> Prop),
    0 < k ->
    #(fun i : Z => 0 <= i < n /\ P i) =
    fold_right Z.add 0
      (map (fun rn =>
        #(fun i : Z => 0 <= i < n /\
          Z.modulo i k = Z.of_nat rn /\ P i))
        (seq 0 (Z.to_nat k))).
Proof.
  intros k n P Hk.
  rewrite fold_residue_cards_partial__final_result by exact Hk.
  apply set_card_Z_bounded_extensional__final_result.
  intros i Hi.
  replace (Z.of_nat (Z.to_nat k)) with k by lia.
  split.
  - intros HP. split; [apply Z.mod_pos_bound; lia | exact HP].
  - tauto.
Qed.
Lemma Zlength_Zrange_aux__final_result :
  forall low m, Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low.
  induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange_0__final_result :
  forall n, 0 <= n -> Zlength (Zrange 0 n) = n.
Proof.
  intros n Hn. unfold Zrange.
  rewrite Zlength_Zrange_aux__final_result.
  lia.
Qed.
Lemma Znth_Zrange_aux__final_result :
  forall m low i,
    0 <= i < Z.of_nat m ->
    Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl.
  destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia).
    lia.
Qed.
Lemma Znth_Zrange_0__final_result :
  forall n i,
    0 <= n -> 0 <= i < n ->
    Znth i (Zrange 0 n) 0 = i.
Proof.
  intros n i Hn Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__final_result by lia.
  lia.
Qed.
Lemma Zlength_map__final_result :
  forall {A B : Type} (f : A -> B) (l : list A),
    Zlength (map f l) = Zlength l.
Proof.
  intros A B f l. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__final_result :
  forall {A B : Type} (f : A -> B) (l : list A)
         (da : A) (db : B) i,
    0 <= i < Zlength l ->
    Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l. induction l as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma residue_choice_value__final_result :
  forall k r a,
    {v : Z |
      v = if Z.leb (ResidueValueCount k r (Zlength a) 1 a)
                   (ResidueValueCount k r (Zlength a) 2 a)
          then 2 else 1}.
Proof.
  intros k r a. eexists. reflexivity.
Defined.
Lemma periodic_candidate_value__final_result :
  forall k a,
    {b : list Z |
      b = map
        (fun i =>
          proj1_sig
            (residue_choice_value__final_result k (Z.modulo i k) a))
        (Zrange 0 (Zlength a))}.
Proof.
  intros k a. eexists. reflexivity.
Defined.
Lemma periodic_candidate_length__final_result :
  forall k a,
    Zlength (proj1_sig (periodic_candidate_value__final_result k a)) =
    Zlength a.
Proof.
  intros k a. rewrite (proj2_sig (periodic_candidate_value__final_result k a)).
  rewrite Zlength_map__final_result, Zlength_Zrange_0__final_result;
    [reflexivity | apply Zlength_nonneg].
Qed.
Lemma periodic_candidate_Znth__final_result :
  forall k a i,
    0 <= i < Zlength a ->
    Znth i (proj1_sig (periodic_candidate_value__final_result k a)) 0 =
    proj1_sig
      (residue_choice_value__final_result k (Z.modulo i k) a).
Proof.
  intros k a i Hi.
  rewrite (proj2_sig (periodic_candidate_value__final_result k a)).
  rewrite (@Znth_map__final_result Z Z
    (fun i =>
      proj1_sig
        (residue_choice_value__final_result k (Z.modulo i k) a))
    (Zrange 0 (Zlength a)) 0 0 i) by
    (rewrite Zlength_Zrange_0__final_result; [exact Hi | apply Zlength_nonneg]).
  rewrite Znth_Zrange_0__final_result;
    [reflexivity | apply Zlength_nonneg | exact Hi].
Qed.
Lemma residue_choice_binary__final_result :
  forall k r a,
    proj1_sig (residue_choice_value__final_result k r a) = 1 \/
    proj1_sig (residue_choice_value__final_result k r a) = 2.
Proof.
  intros k r a. rewrite (proj2_sig (residue_choice_value__final_result k r a)).
  destruct Z.leb; auto.
Qed.
Lemma periodic_candidate_binary__final_result :
  forall k a,
    Forall (fun x => x = 1 \/ x = 2)
      (proj1_sig (periodic_candidate_value__final_result k a)).
Proof.
  intros k a. apply Forall_forall. intros x Hx.
  rewrite (proj2_sig (periodic_candidate_value__final_result k a)) in Hx.
  apply in_map_iff in Hx as [i [<- _]].
  apply residue_choice_binary__final_result.
Qed.
Lemma periodic_candidate_periodic__final_result :
  forall k a,
    0 < k -> (k | Zlength a) ->
    KPeriodic k (proj1_sig (periodic_candidate_value__final_result k a)).
Proof.
  intros k a Hk Hdiv. unfold KPeriodic.
  rewrite periodic_candidate_length__final_result.
  split; [exact Hdiv |].
  intros i Hi.
  rewrite !periodic_candidate_Znth__final_result by lia.
  f_equal.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_same by lia.
  rewrite Z.add_0_r, Z.mod_mod by lia.
  reflexivity.
Qed.
Lemma residue_value_count_full__final_result :
  forall k r value a,
    ResidueValueCount k r (Zlength a) value a =
    #(fun i : Z => 0 <= i < Zlength a /\
      Z.modulo i k = r /\ Znth i a 0 = value).
Proof.
  intros k r value a. unfold ResidueValueCount.
  apply set_card_extensional__final_result.
  intros i. tauto.
Qed.
Lemma candidate_residue_difference__final_result :
  forall k r a,
    0 < k -> 0 <= r < k ->
    (forall i, 0 <= i < Zlength a ->
      Znth i a 0 = 1 \/ Znth i a 0 = 2) ->
    #(fun i : Z => 0 <= i < Zlength a /\
      Z.modulo i k = r /\
      Znth i a 0 <>
        Znth i (proj1_sig (periodic_candidate_value__final_result k a)) 0) =
    ResidueChangeCost k r a.
Proof.
  intros k r a Hk Hr Hbinary.
  unfold ResidueChangeCost.
  destruct (Z.leb
    (ResidueValueCount k r (Zlength a) 1 a)
    (ResidueValueCount k r (Zlength a) 2 a)) eqn:Hle.
  - assert (HleZ :
      ResidueValueCount k r (Zlength a) 1 a <=
      ResidueValueCount k r (Zlength a) 2 a).
    { apply Z.leb_le. exact Hle. }
    rewrite Z.min_l by exact HleZ.
    rewrite residue_value_count_full__final_result.
    apply set_card_Z_bounded_extensional__final_result.
    intros i Hi. split.
    + intros [Hmod Hneq]. split; [exact Hmod |].
      rewrite periodic_candidate_Znth__final_result in Hneq by exact Hi.
      rewrite Hmod in Hneq.
      rewrite (proj2_sig (residue_choice_value__final_result k r a)) in Hneq.
      rewrite Hle in Hneq.
      destruct (Hbinary i Hi); congruence.
    + intros [Hmod Hone]. split; [exact Hmod |].
      rewrite periodic_candidate_Znth__final_result by exact Hi.
      rewrite Hmod.
      rewrite (proj2_sig (residue_choice_value__final_result k r a)).
      rewrite Hle.
      congruence.
  - assert (HgtZ :
      ResidueValueCount k r (Zlength a) 2 a <
      ResidueValueCount k r (Zlength a) 1 a).
    { apply Z.leb_gt. exact Hle. }
    rewrite Z.min_r by lia.
    rewrite residue_value_count_full__final_result.
    apply set_card_Z_bounded_extensional__final_result.
    intros i Hi. split.
    + intros [Hmod Hneq]. split; [exact Hmod |].
      rewrite periodic_candidate_Znth__final_result in Hneq by exact Hi.
      rewrite Hmod in Hneq.
      rewrite (proj2_sig (residue_choice_value__final_result k r a)) in Hneq.
      rewrite Hle in Hneq.
      destruct (Hbinary i Hi); congruence.
    + intros [Hmod Htwo]. split; [exact Hmod |].
      rewrite periodic_candidate_Znth__final_result by exact Hi.
      rewrite Hmod.
      rewrite (proj2_sig (residue_choice_value__final_result k r a)).
      rewrite Hle.
      congruence.
Qed.
Lemma candidate_difference_cost__final_result :
  forall k a,
    0 < k ->
    (forall i, 0 <= i < Zlength a ->
      Znth i a 0 = 1 \/ Znth i a 0 = 2) ->
    DifferenceCount a
      (proj1_sig (periodic_candidate_value__final_result k a)) =
    ProcessedChangeCost k k a.
Proof.
  intros k a Hk Hbinary.
  unfold DifferenceCount, ProcessedChangeCost.
  rewrite (set_card_partition_residues__final_result k (Zlength a)
    (fun i => Znth i a 0 <>
      Znth i (proj1_sig (periodic_candidate_value__final_result k a)) 0))
    by exact Hk.
  f_equal. apply map_ext_in. intros rn Hrn.
  apply candidate_residue_difference__final_result; try exact Hk.
  - apply in_seq in Hrn. lia.
  - exact Hbinary.
Qed.
Lemma Znth_in__final_result :
  forall {A : Type} (l : list A) (d : A) i,
    0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l d i Hi. unfold Znth.
  apply nth_In. rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Forall_Znth__final_result :
  forall {A : Type} (P : A -> Prop) l d i,
    Forall P l -> 0 <= i < Zlength l -> P (Znth i l d).
Proof.
  intros A P l d i Hall Hi.
  rewrite Forall_forall in Hall. apply Hall.
  apply Znth_in__final_result. exact Hi.
Qed.
Lemma kperiodic_offset_nat__final_result :
  forall k b r (q : nat),
    0 < k -> 0 <= r < k ->
    r + Z.of_nat q * k < Zlength b ->
    KPeriodic k b ->
    Znth (r + Z.of_nat q * k) b 0 = Znth r b 0.
Proof.
  intros k b r q. revert r.
  induction q as [|q IH]; intros r Hk Hr Hbound Hperiodic.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - destruct Hperiodic as [Hdiv Hstep].
    rewrite Nat2Z.inj_succ in Hbound |- *.
    assert (Eindex : r + Z.succ (Z.of_nat q) * k =
      (r + Z.of_nat q * k) + k) by ring.
    rewrite Eindex in Hbound |- *.
    assert (Hprev :
      Znth (r + Z.of_nat q * k) b 0 =
      Znth ((r + Z.of_nat q * k) + k) b 0).
    { apply Hstep. split; nia. }
    rewrite <- Hprev.
    apply IH.
    + exact Hk.
    + exact Hr.
    + nia.
    + split; assumption.
Qed.
Lemma kperiodic_same_residue__final_result :
  forall k b r i,
    0 < k -> 0 <= r < k -> 0 <= i < Zlength b ->
    Z.modulo i k = r -> KPeriodic k b ->
    Znth i b 0 = Znth r b 0.
Proof.
  intros k b r i Hk Hr Hi Hmod Hperiodic.
  assert (Hdivnonneg : 0 <= i / k) by (apply Z_div_pos; lia).
  pose proof (Z.div_mod i k ltac:(lia)) as Hdecomp.
  rewrite Hmod in Hdecomp.
  replace i with (r + Z.of_nat (Z.to_nat (i / k)) * k).
  - apply kperiodic_offset_nat__final_result; try assumption.
    lia.
  - replace (Z.of_nat (Z.to_nat (i / k))) with (i / k) by lia.
    lia.
Qed.
Lemma competitor_residue_lower_bound__final_result :
  forall k a b r,
    0 < k -> 0 <= r < k -> Zlength b = Zlength a -> k <= Zlength b ->
    Forall (fun x => x = 1 \/ x = 2) b ->
    KPeriodic k b ->
    ResidueChangeCost k r a <=
    #(fun i : Z => 0 <= i < Zlength a /\
      Z.modulo i k = r /\ Znth i a 0 <> Znth i b 0).
Proof.
  intros k a b r Hk Hr Hlen Hklen Hbinary Hperiodic.
  assert (Hrlen : 0 <= r < Zlength b) by lia.
  pose proof (Forall_Znth__final_result
    (fun x : Z => x = 1 \/ x = 2) b 0 r Hbinary Hrlen) as Hchoice.
  destruct Hchoice as [Hone | Htwo].
  - unfold ResidueChangeCost.
    eapply Z.le_trans; [apply Z.le_min_r |].
    rewrite residue_value_count_full__final_result.
    apply set_card_Z_bounded_subset__final_result.
    intros i Hi [Hmod Hai]. split; [exact Hmod |].
    assert (Hsame : Znth i b 0 = Znth r b 0).
    {
      apply kperiodic_same_residue__final_result with (k := k);
        try assumption.
      rewrite Hlen. exact Hi.
    }
    rewrite Hsame, Hone, Hai. congruence.
  - unfold ResidueChangeCost.
    eapply Z.le_trans; [apply Z.le_min_l |].
    rewrite residue_value_count_full__final_result.
    apply set_card_Z_bounded_subset__final_result.
    intros i Hi [Hmod Hai]. split; [exact Hmod |].
    assert (Hsame : Znth i b 0 = Znth r b 0).
    {
      apply kperiodic_same_residue__final_result with (k := k);
        try assumption.
      rewrite Hlen. exact Hi.
    }
    rewrite Hsame, Htwo, Hai. congruence.
Qed.
Lemma processed_cost_competitor_lower_bound__final_result :
  forall k a b,
    0 < k -> Zlength b = Zlength a -> k <= Zlength a ->
    Forall (fun x => x = 1 \/ x = 2) b ->
    KPeriodic k b ->
    ProcessedChangeCost k k a <= DifferenceCount a b.
Proof.
  intros k a b Hk Hlen Hklen Hbinary Hperiodic.
  unfold ProcessedChangeCost, DifferenceCount.
  rewrite (set_card_partition_residues__final_result k (Zlength a)
    (fun i => Znth i a 0 <> Znth i b 0)) by exact Hk.
  apply fold_right_add_map_le__final_result.
  intros rn Hrn.
  apply competitor_residue_lower_bound__final_result; try assumption.
  - apply in_seq in Hrn. lia.
  - lia.
Qed.
Lemma pointwise_binary_Forall__final_result :
  forall a,
    (forall i, 0 <= i < Zlength a ->
      Znth i a 0 = 1 \/ Znth i a 0 = 2) ->
    Forall (fun x => x = 1 \/ x = 2) a.
Proof.
  intros a Hpoint. apply Forall_forall. intros x Hx.
  apply In_nth with (d := 0) in Hx as [n [Hn <-]].
  specialize (Hpoint (Z.of_nat n)).
  unfold Znth in Hpoint. rewrite Nat2Z.id in Hpoint.
  apply Hpoint. rewrite Zlength_correct. lia.
Qed.
Lemma prefix_cost_implies_spec__final_result :
  forall k a changes,
    1 <= k -> k <= Zlength a -> (k | Zlength a) ->
    (forall i, 0 <= i < Zlength a ->
      Znth i a 0 = 1 \/ Znth i a 0 = 2) ->
    changes = ProcessedChangeCost k k a ->
    Spec k a changes.
Proof.
  intros k a changes Hk Hklen Hdiv Hbinary Hchanges.
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists changes. split.
  - split.
    + exists (proj1_sig (periodic_candidate_value__final_result k a)).
      split.
      * apply periodic_candidate_length__final_result.
      * split.
        -- apply periodic_candidate_binary__final_result.
        -- split.
           ++ apply periodic_candidate_periodic__final_result;
                [lia | exact Hdiv].
           ++ rewrite candidate_difference_cost__final_result by
                (try lia; exact Hbinary).
              exact Hchanges.
    + intros d [b [Hblen [Hbbinary [Hbperiodic Hd]]]].
      subst d. rewrite Hchanges.
      apply processed_cost_competitor_lower_bound__final_result; try assumption;
        lia.
  - reflexivity.
Qed.
