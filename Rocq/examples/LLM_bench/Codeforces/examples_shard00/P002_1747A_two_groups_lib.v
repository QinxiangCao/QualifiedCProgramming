Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition TwoGroupValue (a : list Z) (first : Z -> Prop) (value : Z) : Prop :=
  value =
    Z.abs (sum (fun i : Z => 0 <= i < Zlength a /\ first i)
               (fun i => Znth i a 0)) -
    Z.abs (sum (fun i : Z => 0 <= i < Zlength a /\ ~ first i)
               (fun i => Znth i a 0)).

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 100000 /\
  Forall (fun x => -1000000000 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      TwoGroupValue a (fst candidate) (snd candidate))
    snd out.

Require Import Coq.micromega.Lia.
Lemma partition_indexed_sum__final_result :
  forall low high (first : Z -> Prop) (f : Z -> Z),
    sum (fun i => low <= i < high /\ first i) f +
    sum (fun i => low <= i < high /\ ~ first i) f =
    sum (fun i => low <= i < high) f.
Proof.
  intros low high first f.
  unfold sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfold : forall xs,
    fold_right (fun x acc => f x + acc) 0
      (filter (fun x => if prop_dec (first x) then true else false) xs) +
    fold_right (fun x acc => f x + acc) 0
      (filter (fun x => if prop_dec (~ first x) then true else false) xs) =
    fold_right (fun x acc => f x + acc) 0 xs).
  {
    induction xs as [|x xs IH]; simpl.
    - reflexivity.
    - destruct (prop_dec (first x)) as [Hx | Hx];
        destruct (prop_dec (~ first x)) as [Hnx | Hnx];
        simpl; try contradiction; specialize IH; lia.
  }
  apply Hfold.
Qed.
Lemma indexed_sum_all__final_result :
  forall low high (f : Z -> Z),
    sum (fun i => low <= i < high /\ True) f =
    sum (fun i => low <= i < high) f.
Proof.
  intros low high f.
  unfold sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfold : forall xs,
    fold_right (fun x acc => f x + acc) 0
      (filter (fun _ => if prop_dec True then true else false) xs) =
    fold_right (fun x acc => f x + acc) 0 xs).
  {
    induction xs as [|x xs IH]; simpl.
    - reflexivity.
    - destruct (prop_dec True) as [_ | H]; [|contradiction].
      simpl. rewrite IH. reflexivity.
  }
  apply Hfold.
Qed.
Lemma indexed_sum_none__final_result :
  forall low high (f : Z -> Z),
    sum (fun i => low <= i < high /\ ~ True) f = 0.
Proof.
  intros low high f.
  unfold sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfold : forall xs,
    fold_right (fun x acc => f x + acc) 0
      (filter (fun _ => if prop_dec (~ True) then true else false) xs) = 0).
  {
    induction xs as [|x xs IH]; simpl.
    - reflexivity.
    - destruct (prop_dec (~ True)) as [H | _]; [contradiction |].
      simpl. exact IH.
  }
  apply Hfold.
Qed.
Lemma two_group_value_upper_bound__final_result :
  forall a first value,
    TwoGroupValue a first value ->
    value <= Z.abs (ListLib.sum a).
Proof.
  intros a first value Hvalue.
  unfold TwoGroupValue in Hvalue.
  set (x := sum (fun i : Z => 0 <= i < Zlength a /\ first i)
                (fun i => Znth i a 0)) in *.
  set (y := sum (fun i : Z => 0 <= i < Zlength a /\ ~ first i)
                (fun i => Znth i a 0)) in *.
  assert (Hpartition : x + y = ListLib.sum a).
  {
    unfold x, y.
    rewrite partition_indexed_sum__final_result.
    rewrite <- list_sum_as_Z_range_sum.
    reflexivity.
  }
  pose proof (Z.abs_triangle (x + y) (- y)) as Htriangle.
  rewrite Z.abs_opp in Htriangle.
  replace (x + y + - y) with x in Htriangle by lia.
  rewrite Hpartition in Htriangle.
  lia.
Qed.
Lemma spec_abs_total__final_result :
  forall a, Spec a (Z.abs (ListLib.sum a)).
Proof.
  intros a.
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists ((fun _ : Z => True), Z.abs (ListLib.sum a)).
  split.
  - split.
    + change (TwoGroupValue a (fun _ : Z => True)
                (Z.abs (ListLib.sum a))).
      unfold TwoGroupValue. simpl.
      rewrite indexed_sum_all__final_result.
      rewrite indexed_sum_none__final_result.
      rewrite Z.abs_0.
      rewrite <- list_sum_as_Z_range_sum.
      lia.
    + intros [first value] Hvalue. simpl in *.
      change (TwoGroupValue a first value) in Hvalue.
      eapply two_group_value_upper_bound__final_result.
      exact Hvalue.
  - reflexivity.
Qed.
