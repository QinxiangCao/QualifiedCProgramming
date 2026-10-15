Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition OneMagneticTransfer (before after : list Z) : Prop :=
  after = before \/
  exists i j x,
    0 <= i < Zlength before /\ 0 <= j < Zlength before /\ i <> j /\
    x > 0 /\ (x | Znth i before 0) /\
    Zlength after = Zlength before /\
    forall k, 0 <= k < Zlength before ->
      Znth k after 0 =
        if Z.eqb k i then Znth k before 0 / x
        else if Z.eqb k j then Znth k before 0 * x
        else Znth k before 0.

Definition TotalPower (a : list Z) : Z := fold_right Z.add 0 a.

Definition Pre (a : list Z) : Prop :=
  2 <= Zlength a <= 50000 /\
  Forall (fun power => 1 <= power <= 100) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (OneMagneticTransfer a) TotalPower out.

Definition PrefixSummary
    (a : list Z) (i total least : Z) : Prop :=
  0 <= i <= Zlength a /\
  total = TotalPower (sublist 0 i a) /\
  ((i = 0 /\ least = 101) \/
   (0 < i /\
    exists least_index,
      0 <= least_index < i /\
      least = Znth least_index a 0 /\
      forall k, 0 <= k < i -> least <= Znth k a 0)).

Definition EnumeratedCost
    (a : list Z) (total least i x cost : Z) : Prop :=
  cost = total \/
  exists source factor,
    0 <= source < Zlength a /\
    2 <= factor <= Znth source a 0 /\
    (factor | Znth source a 0) /\
    (source < i \/ (source = i /\ factor < x)) /\
    cost = total - Znth source a 0 - least +
           Znth source a 0 / factor + least * factor.

Definition SearchMinimum
    (a : list Z) (total least i x answer : Z) : Prop :=
  min_value_of_subset Z.le
    (EnumeratedCost a total least i x) (fun cost => cost) answer.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma total_power_nonnegative__arithmetic_safety :
  forall a,
    (forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0) ->
    0 <= TotalPower a.
Proof.
  induction a as [| head tail IH]; intros Hnonnegative.
  - unfold TotalPower. simpl. lia.
  - pose proof (Zlength_nonneg tail) as Htail_len.
    assert (Hhead : 0 <= head).
    {
      specialize (Hnonnegative 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hnonnegative. exact Hnonnegative.
    }
    assert (Htail : forall k, 0 <= k < Zlength tail -> 0 <= Znth k tail 0).
    {
      intros k Hk.
      specialize (Hnonnegative (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hnonnegative by lia.
      replace (k + 1 - 1) with k in Hnonnegative by lia.
      exact Hnonnegative.
    }
    unfold TotalPower in *. simpl. specialize (IH Htail). lia.
Qed.
Lemma total_power_dominates_selected__arithmetic_safety :
  forall a i,
    (forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0) ->
    0 <= i < Zlength a ->
    Znth i a 0 <= TotalPower a.
Proof.
  induction a as [| head tail IH]; intros i Hnonnegative Hi.
  - rewrite Zlength_nil in Hi. lia.
  - pose proof (Zlength_nonneg tail) as Htail_len.
    assert (Hhead : 0 <= head).
    {
      specialize (Hnonnegative 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hnonnegative. exact Hnonnegative.
    }
    assert (Htail : forall k, 0 <= k < Zlength tail -> 0 <= Znth k tail 0).
    {
      intros k Hk.
      specialize (Hnonnegative (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hnonnegative by lia.
      replace (k + 1 - 1) with k in Hnonnegative by lia.
      exact Hnonnegative.
    }
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons.
      pose proof
        (total_power_nonnegative__arithmetic_safety tail Htail) as Htail_sum.
      unfold TotalPower in *. simpl. lia.
    + rewrite Znth_cons by lia.
      pose proof
        (IH (i - 1) Htail ltac:(rewrite Zlength_cons in Hi; lia)) as Hselected.
      unfold TotalPower in *. simpl. lia.
Qed.
Lemma total_power_dominates_selected_and_lower_bound__arithmetic_safety :
  forall a least i,
    2 <= Zlength a ->
    (forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0) ->
    (forall k, 0 <= k < Zlength a -> least <= Znth k a 0) ->
    0 <= i < Zlength a ->
    Znth i a 0 + least <= TotalPower a.
Proof.
  intros a least i Hlen Hnonnegative Hleast Hi.
  destruct a as [| head tail].
  - rewrite Zlength_nil in Hlen. lia.
  - pose proof (Zlength_nonneg tail) as Htail_len.
    assert (Hhead_nonnegative : 0 <= head).
    {
      specialize (Hnonnegative 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hnonnegative. exact Hnonnegative.
    }
    assert (Hleast_head : least <= head).
    {
      specialize (Hleast 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hleast. exact Hleast.
    }
    assert (Htail_nonnegative :
      forall k, 0 <= k < Zlength tail -> 0 <= Znth k tail 0).
    {
      intros k Hk.
      specialize (Hnonnegative (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hnonnegative by lia.
      replace (k + 1 - 1) with k in Hnonnegative by lia.
      exact Hnonnegative.
    }
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons.
      assert (Htail_index : 0 <= 0 < Zlength tail).
      { rewrite Zlength_cons in Hlen. lia. }
      assert (Hleast_first : least <= Znth 0 tail 0).
      {
        specialize (Hleast 1 ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth_cons in Hleast by lia.
        replace (1 - 1) with 0 in Hleast by lia.
        exact Hleast.
      }
      pose proof
        (total_power_dominates_selected__arithmetic_safety
           tail 0 Htail_nonnegative Htail_index) as Htail_sum.
      unfold TotalPower in *. simpl. lia.
    + rewrite Znth_cons by lia.
      assert (Htail_index : 0 <= i - 1 < Zlength tail).
      { rewrite Zlength_cons in Hi. lia. }
      pose proof
        (total_power_dominates_selected__arithmetic_safety
           tail (i - 1) Htail_nonnegative Htail_index) as Htail_sum.
      unfold TotalPower in *. simpl. lia.
Qed.
Lemma prefix_summary_total_dominates_source_and_least__arithmetic_safety :
  forall a n total least i,
    2 <= Zlength a ->
    n = Zlength a ->
    (forall k, 0 <= k < Zlength a -> 1 <= Znth k a 0) ->
    PrefixSummary a n total least ->
    0 <= i < Zlength a ->
    Znth i a 0 + least <= total.
Proof.
  intros a n total least i Hlen Hn Hpositive Hsummary Hi.
  subst n.
  unfold PrefixSummary in Hsummary.
  destruct Hsummary as [_ [Htotal Hleast]].
  assert (Hsublist : sublist 0 (Zlength a) a = a).
  {
    pose proof (sublist_app_exact1 a (@nil Z)) as Hsublist.
    rewrite app_nil_r in Hsublist.
    exact Hsublist.
  }
  rewrite Hsublist in Htotal.
  destruct Hleast as [[Hempty _] | [_ [least_index [_ [_ Hleast_all]]]]].
  - lia.
  - assert (Hnonnegative_bound :
      forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0).
    { intros k Hk. specialize (Hpositive k Hk). lia. }
    rewrite Htotal.
    apply total_power_dominates_selected_and_lower_bound__arithmetic_safety;
      assumption.
Qed.
Lemma total_power_sublist_snoc__prefix_summary :
  forall (a : list Z) (i : Z),
    0 <= i < Zlength a ->
    TotalPower (sublist 0 (i + 1) a) =
    TotalPower (sublist 0 i a) + Znth i a 0.
Proof.
  intros a i Hi.
  rewrite (sublist_split 0 (i + 1) i a) by lia.
  rewrite (sublist_single 0) by lia.
  unfold TotalPower.
  induction (sublist 0 i a) as [|x xs IH]; simpl in *; lia.
Qed.
Lemma prefix_summary_step_lt__prefix_summary :
  forall (a : list Z) (i total least : Z),
    0 <= i < Zlength a ->
    PrefixSummary a i total least ->
    Znth i a 0 < least ->
    PrefixSummary a (i + 1) (total + Znth i a 0) (Znth i a 0).
Proof.
  intros a i total least Hi Hsummary Hlt.
  unfold PrefixSummary in *.
  destruct Hsummary as [Hbounds [Htotal Hleast]].
  split; [lia |].
  split.
  - rewrite total_power_sublist_snoc__prefix_summary by lia.
    rewrite <- Htotal.
    reflexivity.
  - right.
    split; [lia |].
    exists i.
    split; [lia |].
    split; [reflexivity |].
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + destruct Hleast as [[Hzero _] | [Hpositive Hleast]].
      * lia.
      * destruct Hleast as [least_index [Hleast_index [Hleast_value Hminimum]]].
        specialize (Hminimum k).
        lia.
    + assert (k = i) by lia.
      subst k.
      lia.
Qed.
Lemma prefix_summary_step_ge__prefix_summary :
  forall (a : list Z) (i total least : Z),
    0 < i < Zlength a ->
    PrefixSummary a i total least ->
    least <= Znth i a 0 ->
    PrefixSummary a (i + 1) (total + Znth i a 0) least.
Proof.
  intros a i total least Hi Hsummary Hge.
  unfold PrefixSummary in *.
  destruct Hsummary as [Hbounds [Htotal Hleast]].
  split; [lia |].
  split.
  - rewrite total_power_sublist_snoc__prefix_summary by lia.
    rewrite <- Htotal.
    reflexivity.
  - right.
    split; [lia |].
    destruct Hleast as [[Hzero _] | [Hpositive Hleast]]; [lia |].
    destruct Hleast as [least_index [Hleast_index [Hleast_value Hminimum]]].
    exists least_index.
    split; [lia |].
    split; [exact Hleast_value |].
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + apply Hminimum.
      lia.
    + assert (k = i) by lia.
      subst k.
      exact Hge.
Qed.
Lemma enumerated_cost_extend_factor__search_transitions :
  forall a total least i x cost,
    0 <= i < Zlength a ->
    2 <= x <= Znth i a 0 ->
    Z.rem (Znth i a 0) x = 0 ->
    (EnumeratedCost a total least i (x + 1) cost <->
     EnumeratedCost a total least i x cost \/
     cost = total - Znth i a 0 - least +
            Znth i a 0 / x + least * x).
Proof.
  intros a total least i x cost Hi Hx Hmod.
  unfold EnumeratedCost.
  split.
  - intros [Htotal | Hfactor_case].
    + left. left. exact Htotal.
    + destruct Hfactor_case as
        (source & factor & Hsource & Hfactor & Hdiv & Hseen & Hcost).
      destruct Hseen as [Hsource_lt | [Hsource_eq Hfactor_lt]].
      * left. right. exists source, factor.
        split; [exact Hsource |].
        split; [exact Hfactor |].
        split; [exact Hdiv |].
        split; [left; exact Hsource_lt | exact Hcost].
      * subst source.
        destruct (Z.lt_trichotomy factor x) as [Hlt | [Heq | Hgt]].
        -- left. right. exists i, factor.
           split; [exact Hi |].
           split; [exact Hfactor |].
           split; [exact Hdiv |].
           split; [right; split; lia | exact Hcost].
        -- right. subst factor. exact Hcost.
        -- lia.
  - intros [Hold | Hcost].
    + destruct Hold as [Htotal | Hfactor_case].
      * left. exact Htotal.
      * destruct Hfactor_case as
          (source & factor & Hsource & Hfactor & Hdiv & Hseen & Heq).
        right. exists source, factor.
        split; [exact Hsource |].
        split; [exact Hfactor |].
        split; [exact Hdiv |].
        split.
        -- destruct Hseen as [Hsource_lt | [Hsource_eq Hfactor_lt]].
           ++ left. exact Hsource_lt.
           ++ right. split; lia.
        -- exact Heq.
    + right. exists i, x.
      split; [exact Hi |].
      split; [exact Hx |].
      split.
      * apply Z.rem_divide; [lia | exact Hmod].
      * split; [right; split; lia | exact Hcost].
Qed.
Lemma search_minimum_extend_factor__search_transitions :
  forall a total least i x answer,
    0 <= i < Zlength a ->
    2 <= x <= Znth i a 0 ->
    Z.rem (Znth i a 0) x = 0 ->
    SearchMinimum a total least i x answer ->
    SearchMinimum a total least i (x + 1)
      (le_min Z.le answer
        (total - Znth i a 0 - least + Znth i a 0 / x + least * x)).
Proof.
  intros a total least i x answer Hi Hx Hmod Hminimum.
  unfold SearchMinimum in *.
  eapply min_union_1_right
    with (a := total - Znth i a 0 - least +
               Znth i a 0 / x + least * x)
         (P := EnumeratedCost a total least i x).
  - exact Hminimum.
  - reflexivity.
  - intros cost.
    rewrite enumerated_cost_extend_factor__search_transitions by auto.
    split.
    + intros [Hold | Heq].
      * left. exact Hold.
      * right. symmetry. exact Heq.
    + intros [Hold | Heq].
      * left. exact Hold.
      * right. symmetry. exact Heq.
Qed.
Lemma search_minimum_extend_factor_lower__search_transitions :
  forall a total least i x answer,
    0 <= i < Zlength a ->
    2 <= x <= Znth i a 0 ->
    Z.rem (Znth i a 0) x = 0 ->
    total - Znth i a 0 - least + Znth i a 0 / x + least * x < answer ->
    SearchMinimum a total least i x answer ->
    SearchMinimum a total least i (x + 1)
      (total - Znth i a 0 - least + Znth i a 0 / x + least * x).
Proof.
  intros a total least i x answer Hi Hx Hmod Hlower Hminimum.
  pose proof (search_minimum_extend_factor__search_transitions
                a total least i x answer Hi Hx Hmod Hminimum) as Hextended.
  rewrite (min_l Z.le answer
             (total - Znth i a 0 - least + Znth i a 0 / x + least * x))
    in Hextended by lia.
  exact Hextended.
Qed.
Lemma search_minimum_extend_factor_upper__search_transitions :
  forall a total least i x answer,
    0 <= i < Zlength a ->
    2 <= x <= Znth i a 0 ->
    Z.rem (Znth i a 0) x = 0 ->
    answer <= total - Znth i a 0 - least + Znth i a 0 / x + least * x ->
    SearchMinimum a total least i x answer ->
    SearchMinimum a total least i (x + 1) answer.
Proof.
  intros a total least i x answer Hi Hx Hmod Hupper Hminimum.
  pose proof (search_minimum_extend_factor__search_transitions
                a total least i x answer Hi Hx Hmod Hminimum) as Hextended.
  rewrite (min_r Z.le answer
             (total - Znth i a 0 - least + Znth i a 0 / x + least * x))
    in Hextended by lia.
  exact Hextended.
Qed.
Lemma enumerated_cost_skip_nondivisor__search_transitions :
  forall a total least i x cost,
    0 <= i < Zlength a ->
    2 <= x <= Znth i a 0 ->
    Z.rem (Znth i a 0) x <> 0 ->
    (EnumeratedCost a total least i (x + 1) cost <->
     EnumeratedCost a total least i x cost).
Proof.
  intros a total least i x cost Hi Hx Hmod.
  unfold EnumeratedCost.
  split.
  - intros [Htotal | Hfactor_case].
    + left. exact Htotal.
    + destruct Hfactor_case as
        (source & factor & Hsource & Hfactor & Hdiv & Hseen & Hcost).
      right. exists source, factor.
      split; [exact Hsource |].
      split; [exact Hfactor |].
      split; [exact Hdiv |].
      split.
      * destruct Hseen as [Hsource_lt | [Hsource_eq Hfactor_lt]].
        -- left. exact Hsource_lt.
        -- subst source.
           right. split; [reflexivity |].
           destruct (Z.lt_trichotomy factor x) as [Hlt | [Heq | Hgt]].
           ++ exact Hlt.
           ++ subst factor. exfalso. apply Hmod.
              apply Z.rem_divide; [lia | exact Hdiv].
           ++ lia.
      * exact Hcost.
  - intros [Htotal | Hfactor_case].
    + left. exact Htotal.
    + destruct Hfactor_case as
        (source & factor & Hsource & Hfactor & Hdiv & Hseen & Hcost).
      right. exists source, factor.
      split; [exact Hsource |].
      split; [exact Hfactor |].
      split; [exact Hdiv |].
      split.
      * destruct Hseen as [Hsource_lt | [Hsource_eq Hfactor_lt]].
        -- left. exact Hsource_lt.
        -- right. split; lia.
      * exact Hcost.
Qed.
Lemma search_minimum_skip_nondivisor__search_transitions :
  forall a total least i x answer,
    0 <= i < Zlength a ->
    2 <= x <= Znth i a 0 ->
    Z.rem (Znth i a 0) x <> 0 ->
    SearchMinimum a total least i x answer ->
    SearchMinimum a total least i (x + 1) answer.
Proof.
  intros a total least i x answer Hi Hx Hmod Hminimum.
  unfold SearchMinimum in *.
  eapply min_eq_forward with
      (P1 := EnumeratedCost a total least i x)
      (f1 := fun cost => cost).
  - typeclasses eauto.
  - exact Hminimum.
  - intros cost Hcost. exists cost. split; [| lia].
    apply (proj2 (enumerated_cost_skip_nondivisor__search_transitions
                    a total least i x cost Hi Hx Hmod)).
    exact Hcost.
  - intros cost Hcost. exists cost. split; [| lia].
    apply (proj1 (enumerated_cost_skip_nondivisor__search_transitions
                    a total least i x cost Hi Hx Hmod)).
    exact Hcost.
Qed.
Lemma enumerated_cost_advance_source__search_transitions :
  forall a total least i x cost,
    0 <= i < Zlength a ->
    2 <= x ->
    Znth i a 0 < x <= Znth i a 0 + 1 ->
    (EnumeratedCost a total least i x cost <->
     EnumeratedCost a total least (i + 1) 2 cost).
Proof.
  intros a total least i x cost Hi Hx Hdone.
  assert (Hx_eq : x = Znth i a 0 + 1) by lia.
  unfold EnumeratedCost.
  split.
  - intros [Htotal | Hfactor_case].
    + left. exact Htotal.
    + destruct Hfactor_case as
        (source & factor & Hsource & Hfactor & Hdiv & Hseen & Hcost).
      right. exists source, factor.
      split; [exact Hsource |].
      split; [exact Hfactor |].
      split; [exact Hdiv |].
      split.
      * destruct Hseen as [Hsource_lt | [Hsource_eq Hfactor_lt]].
        -- left. lia.
        -- left. subst source. lia.
      * exact Hcost.
  - intros [Htotal | Hfactor_case].
    + left. exact Htotal.
    + destruct Hfactor_case as
        (source & factor & Hsource & Hfactor & Hdiv & Hseen & Hcost).
      right. exists source, factor.
      split; [exact Hsource |].
      split; [exact Hfactor |].
      split; [exact Hdiv |].
      split.
      * destruct Hseen as [Hsource_lt | [Hsource_eq Hfactor_lt]].
        -- destruct (Z.lt_trichotomy source i) as [Hlt | [Heq | Hgt]].
           ++ left. exact Hlt.
           ++ right. subst source. split; lia.
           ++ lia.
        -- lia.
      * exact Hcost.
Qed.
Lemma search_minimum_advance_source__search_transitions :
  forall a total least i x answer,
    0 <= i < Zlength a ->
    2 <= x ->
    Znth i a 0 < x <= Znth i a 0 + 1 ->
    SearchMinimum a total least i x answer ->
    SearchMinimum a total least (i + 1) 2 answer.
Proof.
  intros a total least i x answer Hi Hx Hdone Hminimum.
  unfold SearchMinimum in *.
  eapply min_eq_forward with
      (P1 := EnumeratedCost a total least i x)
      (f1 := fun cost => cost).
  - typeclasses eauto.
  - exact Hminimum.
  - intros cost Hcost. exists cost. split; [| lia].
    apply (proj1 (enumerated_cost_advance_source__search_transitions
                    a total least i x cost Hi Hx Hdone)).
    exact Hcost.
  - intros cost Hcost. exists cost. split; [| lia].
    apply (proj2 (enumerated_cost_advance_source__search_transitions
                    a total least i x cost Hi Hx Hdone)).
    exact Hcost.
Qed.
Lemma total_power_nonnegative__search_transitions :
  forall a,
    (forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0) ->
    0 <= TotalPower a.
Proof.
  induction a as [|head tail IH]; intros Hpoint.
  - reflexivity.
  - pose proof (Zlength_nonneg tail) as Htail_length.
    assert (Hhead : 0 <= head).
    { specialize (Hpoint 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hpoint. exact Hpoint. }
    assert (Htail : forall k, 0 <= k < Zlength tail -> 0 <= Znth k tail 0).
    { intros k Hk.
      specialize (Hpoint (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hpoint by lia.
      replace (k + 1 - 1) with k in Hpoint by lia.
      exact Hpoint. }
    unfold TotalPower in *. simpl. specialize (IH Htail). lia.
Qed.
Lemma total_power_ge_entry__search_transitions :
  forall a i,
    (forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0) ->
    0 <= i < Zlength a ->
    Znth i a 0 <= TotalPower a.
Proof.
  induction a as [|head tail IH]; intros i Hpoint Hi.
  - rewrite Zlength_nil in Hi. lia.
  - pose proof (Zlength_nonneg tail) as Htail_length.
    assert (Hhead : 0 <= head).
    { specialize (Hpoint 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hpoint. exact Hpoint. }
    assert (Htail : forall k, 0 <= k < Zlength tail -> 0 <= Znth k tail 0).
    { intros k Hk.
      specialize (Hpoint (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hpoint by lia.
      replace (k + 1 - 1) with k in Hpoint by lia.
      exact Hpoint. }
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons.
      unfold TotalPower. simpl.
      pose proof (total_power_nonnegative__search_transitions tail Htail) as Htail_total.
      unfold TotalPower in Htail_total.
      lia.
    + rewrite Znth_cons by lia.
      unfold TotalPower. simpl.
      pose proof (IH (i - 1) Htail ltac:(rewrite Zlength_cons in Hi; lia))
        as Htail_sum.
      unfold TotalPower in Htail_sum.
      lia.
Qed.
Lemma total_power_ge_entry_plus_lower__search_transitions :
  forall a i least,
    (forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0) ->
    (forall k, 0 <= k < Zlength a -> least <= Znth k a 0) ->
    0 <= least ->
    2 <= Zlength a ->
    0 <= i < Zlength a ->
    Znth i a 0 + least <= TotalPower a.
Proof.
  intros a i least Hnonnegative Hleast Hleast_nonnegative Hlength Hi.
  destruct a as [|head tail].
  - rewrite Zlength_nil in Hlength. lia.
  - pose proof (Zlength_nonneg tail) as Htail_length_nonnegative.
    assert (Hhead_nonnegative : 0 <= head).
    { specialize (Hnonnegative 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hnonnegative. exact Hnonnegative. }
    assert (Hleast_head : least <= head).
    { specialize (Hleast 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hleast. exact Hleast. }
    assert (Htail_nonnegative :
              forall k, 0 <= k < Zlength tail -> 0 <= Znth k tail 0).
    { intros k Hk.
      specialize (Hnonnegative (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hnonnegative by lia.
      replace (k + 1 - 1) with k in Hnonnegative by lia.
      exact Hnonnegative. }
    assert (Hleast_tail :
              forall k, 0 <= k < Zlength tail -> least <= Znth k tail 0).
    { intros k Hk.
      specialize (Hleast (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hleast by lia.
      replace (k + 1 - 1) with k in Hleast by lia.
      exact Hleast. }
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons.
      unfold TotalPower. simpl.
      assert (Htail_length : 0 < Zlength tail).
      { rewrite Zlength_cons in Hlength. lia. }
      pose proof (Hleast_tail 0 ltac:(lia)) as Htail_first.
      pose proof (total_power_ge_entry__search_transitions
                    tail 0 Htail_nonnegative ltac:(lia)) as Htail_sum.
      unfold TotalPower in Htail_sum.
      lia.
    + rewrite Znth_cons by lia.
      unfold TotalPower. simpl.
      pose proof (total_power_ge_entry__search_transitions
                    tail (i - 1) Htail_nonnegative ltac:(rewrite Zlength_cons in Hi; lia))
        as Htail_sum.
      unfold TotalPower in Htail_sum.
      lia.
Qed.
Lemma sublist_full__search_transitions :
  forall {A : Type} (a : list A),
    sublist 0 (Zlength a) a = a.
Proof.
  intros A a.
  unfold sublist.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  simpl.
  apply firstn_all.
Qed.
Lemma enumerated_candidate_nonnegative__search_transitions :
  forall a total least i x,
    2 <= Zlength a ->
    0 <= i < Zlength a ->
    2 <= x ->
    (forall k, 0 <= k < Zlength a -> 1 <= Znth k a 0) ->
    PrefixSummary a (Zlength a) total least ->
    0 <= total - Znth i a 0 - least +
         Znth i a 0 / x + least * x.
Proof.
  intros a total least i x Hlength Hi Hvalues Hpoint Hprefix.
  unfold PrefixSummary in Hprefix.
  destruct Hprefix as [_ [Htotal Hleast]].
  rewrite sublist_full__search_transitions in Htotal.
  destruct Hleast as [[Hzero _] | [Hpositive [least_index [Hleast_index [Hleast_value Hleast_all]]]]].
  - lia.
  - assert (Hlower0 : forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0).
    { intros k Hk. specialize (Hpoint k Hk). lia. }
    assert (Hlowerleast : forall k, 0 <= k < Zlength a -> least <= Znth k a 0).
    { intros k Hk. apply Hleast_all. exact Hk. }
    assert (Hleast_nonnegative : 0 <= least).
    { specialize (Hpoint least_index Hleast_index). lia. }
    pose proof (total_power_ge_entry_plus_lower__search_transitions
                  a i least Hlower0 Hlowerleast Hleast_nonnegative Hlength Hi)
      as Htotal_lower.
    assert (Hdivision : 0 <= Znth i a 0 / x).
    { apply Z.div_pos; specialize (Hpoint i Hi); lia. }
    rewrite Htotal.
    nia.
Qed.
Lemma Zlength_replace_Znth__final_spec :
  forall {A : Type} (l : list A) i (v : A),
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros A l. induction l as [|a l IH]; intros i v; simpl; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat i) as [|n].
  - simpl. repeat rewrite Zlength_cons. lia.
  - simpl. repeat rewrite Zlength_cons.
    specialize (IH (Z.of_nat n) v).
    replace (Z.to_nat (Z.of_nat n)) with n in IH by lia.
    rewrite IH. lia.
Qed.
Lemma total_power_replace_Znth__final_spec :
  forall a i v,
    0 <= i < Zlength a ->
    TotalPower (replace_Znth i v a) =
      TotalPower a - Znth i a 0 + v.
Proof.
  induction a as [|head tail IH]; intros i v Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + unfold TotalPower, replace_Znth, Znth. simpl. ring.
    + assert (0 < i) by lia.
      unfold TotalPower in *.
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons by lia.
      simpl.
      rewrite IH by lia.
      ring.
Qed.
Lemma total_power_two_index_update__final_spec :
  forall a source recipient factor,
    0 <= source < Zlength a ->
    0 <= recipient < Zlength a ->
    source <> recipient ->
    let after :=
      replace_Znth recipient (Znth recipient a 0 * factor)
        (replace_Znth source (Znth source a 0 / factor) a) in
    Zlength after = Zlength a /\
    (forall k, 0 <= k < Zlength a ->
       Znth k after 0 =
         if Z.eqb k source then Znth k a 0 / factor
         else if Z.eqb k recipient then Znth k a 0 * factor
         else Znth k a 0) /\
    TotalPower after =
      TotalPower a - Znth source a 0 - Znth recipient a 0 +
      Znth source a 0 / factor + Znth recipient a 0 * factor.
Proof.
  intros a source recipient factor Hsource Hrecipient Hdistinct after.
  assert (Hinner_length :
    Zlength (replace_Znth source (Znth source a 0 / factor) a) =
    Zlength a) by apply Zlength_replace_Znth__final_spec.
  split.
  - unfold after. repeat rewrite Zlength_replace_Znth__final_spec.
    reflexivity.
  - split.
    + intros k Hk.
      unfold after.
      destruct (Z.eqb_spec k source) as [-> | Hksource].
      * rewrite Znth_replace_Znth_Diff by
          (try rewrite Hinner_length; try lia).
        rewrite Znth_replace_Znth_Same by exact Hsource.
        reflexivity.
      * destruct (Z.eqb_spec k recipient) as [-> | Hkrecipient].
        -- rewrite Znth_replace_Znth_Same by (rewrite Hinner_length; lia).
           reflexivity.
        -- rewrite Znth_replace_Znth_Diff by
             (try rewrite Hinner_length; try lia).
           rewrite Znth_replace_Znth_Diff by lia.
           reflexivity.
    + unfold after.
      rewrite total_power_replace_Znth__final_spec by
        (rewrite Hinner_length; exact Hrecipient).
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite total_power_replace_Znth__final_spec by exact Hsource.
      ring.
Qed.
Lemma least_recipient_minimizes_transfer_cost__final_spec :
  forall total source_power least recipient_power factor,
    1 <= factor ->
    least <= recipient_power ->
    total - source_power - least + source_power / factor + least * factor <=
    total - source_power - recipient_power +
      source_power / factor + recipient_power * factor.
Proof.
  intros. nia.
Qed.
Lemma enumerated_cost_realizable_or_no_better__final_spec :
  forall a total least cost least_index,
    total = TotalPower a ->
    0 <= least_index < Zlength a ->
    least = Znth least_index a 0 ->
    EnumeratedCost a total least (Zlength a) 2 cost ->
    exists after,
      OneMagneticTransfer a after /\ TotalPower after <= cost.
Proof.
  intros a total least cost least_index Htotal Hleast_index Hleast Henumerated.
  unfold EnumeratedCost in Henumerated.
  destruct Henumerated as [Hunchanged |
    (source & factor & Hsource & Hfactor & Hdivide & Hcompleted & Hcost)].
  - exists a. split.
    + unfold OneMagneticTransfer. left. reflexivity.
    + subst cost. rewrite Htotal. lia.
  - destruct Hcompleted as [Hcompleted | [Hsource_end _]]; [|lia].
    destruct (Z.eq_dec source least_index) as [Hsame | Hdifferent].
    + exists a. split.
      * unfold OneMagneticTransfer. left. reflexivity.
      * subst source least cost.
        assert (Hdiv_nonneg : 0 <= Znth least_index a 0 / factor).
        { apply Z_div_nonneg_nonneg; lia. }
        rewrite Htotal. nia.
    + set (after :=
        replace_Znth least_index (Znth least_index a 0 * factor)
          (replace_Znth source (Znth source a 0 / factor) a)).
      pose proof
        (total_power_two_index_update__final_spec
          a source least_index factor Hsource Hleast_index Hdifferent)
        as [Hafter_length [Hafter_values Hafter_total]].
      exists after. split.
      * unfold OneMagneticTransfer. right.
        exists source, least_index, factor.
        repeat split; try assumption; try lia.
      * subst least cost. unfold after.
        rewrite Hafter_total, <- Htotal. lia.
Qed.
Lemma magnetic_transfer_dominated_by_enumeration__final_spec :
  forall a total least least_index after,
    total = TotalPower a ->
    0 <= least_index < Zlength a ->
    least = Znth least_index a 0 ->
    (forall k, 0 <= k < Zlength a -> 1 <= Znth k a 0) ->
    (forall k, 0 <= k < Zlength a -> least <= Znth k a 0) ->
    OneMagneticTransfer a after ->
    exists cost,
      EnumeratedCost a total least (Zlength a) 2 cost /\
      cost <= TotalPower after.
Proof.
  intros a total least least_index after Htotal Hleast_index Hleast
    Hpositive Hleast_bound Htransfer.
  unfold OneMagneticTransfer in Htransfer.
  destruct Htransfer as [-> |
    (source & recipient & factor & Hsource & Hrecipient & Hdistinct &
     Hfactor & Hdivide & Hafter_length & Hafter_values)].
  - exists total. split.
    + unfold EnumeratedCost. left. reflexivity.
    + rewrite Htotal. lia.
  - set (constructed :=
      replace_Znth recipient (Znth recipient a 0 * factor)
        (replace_Znth source (Znth source a 0 / factor) a)).
    pose proof
      (total_power_two_index_update__final_spec
        a source recipient factor Hsource Hrecipient Hdistinct)
      as [Hconstructed_length [Hconstructed_values Hconstructed_total]].
    assert (Hafter_eq : after = constructed).
    {
      apply nth_ext with (d := 0) (d' := 0).
      - apply Nat2Z.inj. rewrite <- !Zlength_correct.
        rewrite Hafter_length. unfold constructed.
        rewrite Hconstructed_length. reflexivity.
      - intros index Hindex.
        assert (HindexZ : 0 <= Z.of_nat index < Zlength a).
        { assert (Hindex_after : Z.of_nat index < Zlength after).
          { rewrite Zlength_correct. lia. }
          rewrite Hafter_length in Hindex_after. lia. }
        assert (Hraw :
          Znth (Z.of_nat index) after 0 =
          Znth (Z.of_nat index)
            (replace_Znth recipient (Znth recipient a 0 * factor)
              (replace_Znth source (Znth source a 0 / factor) a)) 0).
        { rewrite Hafter_values by exact HindexZ.
          rewrite Hconstructed_values by exact HindexZ.
          reflexivity. }
        unfold Znth in Hraw. rewrite Nat2Z.id in Hraw.
        unfold constructed, Znth. exact Hraw.
    }
    subst after.
    destruct (Z.eq_dec factor 1) as [-> | Hfactor_not_one].
    + exists total. split.
      * unfold EnumeratedCost. left. reflexivity.
      * unfold constructed.
        rewrite Hconstructed_total, Htotal, Z.div_1_r. lia.
    + assert (Hfactor_two : 2 <= factor) by lia.
      assert (Hsource_positive : 0 < Znth source a 0).
      { specialize (Hpositive source Hsource). lia. }
      assert (Hfactor_upper : factor <= Znth source a 0).
      { apply Z.divide_pos_le; assumption. }
      exists (total - Znth source a 0 - least +
        Znth source a 0 / factor + least * factor).
      split.
      * unfold EnumeratedCost. right.
        exists source, factor.
        repeat split; try assumption; try lia.
      * unfold constructed. rewrite Hconstructed_total, Htotal.
        apply least_recipient_minimizes_transfer_cost__final_spec;
          [lia | apply Hleast_bound; exact Hrecipient].
Qed.
