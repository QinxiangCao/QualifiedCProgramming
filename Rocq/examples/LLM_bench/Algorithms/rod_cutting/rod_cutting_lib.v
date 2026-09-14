From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition RodCutPlan (rod_len : Z) (pieces : list Z) : Prop :=
  0 <= rod_len /\
  Forall (fun piece => 1 <= piece <= rod_len) pieces /\
  sum pieces = rod_len.

Definition RodCutPlanRevenue (price pieces : list Z) : Z :=
  sum (map (fun piece => Znth piece price 0) pieces).

Definition RodCutOptimalRevenue
    (price : list Z) (rod_len answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun pieces : list Z => RodCutPlan rod_len pieces)
    (fun pieces => RodCutPlanRevenue price pieces)
    answer.

Definition RodCutRevenueTable
    (price revenue : list Z) (upto : Z) : Prop :=
  forall rod_len,
    0 <= rod_len < upto ->
    RodCutOptimalRevenue price rod_len (Znth rod_len revenue 0).

Definition RodCutScanBest
    (price revenue : list Z)
    (rod_len next_piece best : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun piece : Z => 1 <= piece < next_piece)
    (fun piece =>
       Znth piece price 0 + Znth (rod_len - piece) revenue 0)
    0
    best.

From Coq Require Import Lia.
Lemma rod_cut_scan_best_step__scan_transitions :
  forall (f : Z -> Z) i best next_best,
    1 <= i ->
    max_value_of_subset_with_default Z.le
      (fun piece : Z => 1 <= piece < i) f 0 best ->
    ((best <= f i /\ next_best = f i) \/
     (f i <= best /\ next_best = best)) ->
    max_value_of_subset_with_default Z.le
      (fun piece : Z => 1 <= piece < i + 1) f 0 next_best.
Proof.
  intros f i best next_best Hi Hold Hnext.
  unfold max_value_of_subset_with_default in *.
  destruct Hnext as [[Hbestle Hnext] | [Hile Hnext]]; subst next_best.
  - assert (Hdefault : 0 <= f i).
    { destruct Hold as [[_ Hzero] | [_ Hzero]]; lia. }
    left; split; [| exact Hdefault].
    exists i; split; [| reflexivity].
    split.
    + change (1 <= i < i + 1); lia.
    + intros b Hb.
      change (1 <= b < i + 1) in Hb.
      assert (b < i \/ b = i) as [Hbi | ->] by lia; [| lia].
      destruct Hold as [[[a [[Ha Hupper] Heq]] Hzero] | [Hupper Hzero]].
      * specialize (Hupper b ltac:(change (1 <= b < i); lia)).
        lia.
      * specialize (Hupper b ltac:(change (1 <= b < i); lia)).
        lia.
  - destruct Hold as [[[a [[Ha Hupper] Heq]] Hzero] | [Hupper Hzero]].
    + left; split; [| exact Hzero].
      exists a; split; [| exact Heq].
      split.
      * change (1 <= a < i) in Ha.
        change (1 <= a < i + 1); lia.
      * intros b Hb.
        change (1 <= b < i + 1) in Hb.
        assert (b < i \/ b = i) as [Hbi | Hbi] by lia.
        { apply Hupper; change (1 <= b < i); lia. }
        { subst b; lia. }
    + right; split; [| exact Hzero].
      intros b Hb.
      change (1 <= b < i + 1) in Hb.
      assert (b < i \/ b = i) as [Hbi | Hbi] by lia.
      { apply Hupper; change (1 <= b < i); lia. }
      { subst b; lia. }
Qed.
Lemma rod_cut_positive_sum_nonnegative__table_extension :
  forall parts,
    Forall (fun piece => 1 <= piece) parts ->
    0 <= sum parts.
Proof.
  intros parts Hparts.
  induction Hparts; simpl; lia.
Qed.
Lemma rod_cut_positive_sum_member_bound__table_extension :
  forall parts piece,
    Forall (fun p => 1 <= p) parts ->
    In piece parts ->
    piece <= sum parts.
Proof.
  intros parts piece Hparts.
  induction Hparts as [|p parts Hp Hparts IH]; intros Hin.
  - inversion Hin.
  - simpl in Hin |- *.
    destruct Hin as [Heq | Hin].
    + subst piece.
      pose proof
        (rod_cut_positive_sum_nonnegative__table_extension parts Hparts).
      lia.
    + specialize (IH Hin).
      lia.
Qed.
Lemma rod_cut_plan_tail__table_extension :
  forall rod_len piece tail,
    RodCutPlan rod_len (piece :: tail) ->
    RodCutPlan (rod_len - piece) tail.
Proof.
  intros rod_len piece tail Hplan.
  unfold RodCutPlan in *.
  destruct Hplan as [Hlen [Hparts Hsum]].
  inversion Hparts as [|? ? Hpiece Htail].
  split.
  - simpl in Hsum. lia.
  - split.
    + apply Forall_forall.
      intros q Hinq.
      pose proof Htail as Htail_positive.
      eapply Forall_impl in Htail_positive;
        [| intros z Hz; exact (proj1 Hz)].
      rewrite Forall_forall in Htail.
      specialize (Htail q Hinq).
      pose proof
        (rod_cut_positive_sum_member_bound__table_extension
           tail q Htail_positive Hinq).
      simpl in Hsum.
      lia.
    + simpl in Hsum. lia.
Qed.
Lemma rod_cut_optimal_revenue_step__table_extension :
  forall price revenue rod_len best,
    1 <= rod_len ->
    0 <= Znth rod_len price 0 ->
    RodCutRevenueTable price revenue rod_len ->
    RodCutScanBest price revenue rod_len (rod_len + 1) best ->
    RodCutOptimalRevenue price rod_len best.
Proof.
  intros price revenue rod_len best Hlen Hprice Htable Hscan.
  assert (Hrevenue0 : Znth 0 revenue 0 = 0).
  {
    pose proof (Htable 0 ltac:(lia)) as Hzero.
    unfold RodCutOptimalRevenue, max_value_of_subset,
      max_object_of_subset in Hzero.
    destruct Hzero as [pieces [[Hplan _] Heq]].
    assert (pieces = nil) as Hnil.
    {
      unfold RodCutPlan in Hplan.
      destruct Hplan as [_ [Hparts _]].
      destruct pieces as [|p pieces]; [reflexivity |].
      inversion Hparts; lia.
    }
    subst pieces.
    unfold RodCutPlanRevenue in Heq.
    simpl in Heq.
    lia.
  }
  unfold RodCutScanBest, max_value_of_subset_with_default in Hscan.
  unfold RodCutOptimalRevenue, max_value_of_subset, max_object_of_subset.
  destruct Hscan as [Hscan | Hscan].
  - destruct Hscan as [Hscan _].
    unfold max_value_of_subset, max_object_of_subset in Hscan.
    destruct Hscan as
      [piece [[Hpiece_domain Hpiece_max] Hpiece_value]].
    destruct Hpiece_domain as [Hpiece_lo Hpiece_hi].
    pose proof (Htable (rod_len - piece) ltac:(lia)) as Htail_opt.
    unfold RodCutOptimalRevenue, max_value_of_subset,
      max_object_of_subset in Htail_opt.
    destruct Htail_opt as [tail [[Htail_plan Htail_max] Htail_value]].
    exists (piece :: tail).
    split.
    + split.
      * unfold RodCutPlan in *.
        destruct Htail_plan as [Htail_len [Htail_parts Htail_sum]].
        split; [lia |].
        split.
        -- constructor; [lia |].
           apply Forall_forall.
           intros q Hinq.
           rewrite Forall_forall in Htail_parts.
           specialize (Htail_parts q Hinq).
           lia.
        -- simpl. lia.
      * intros pieces Hpieces_plan.
        destruct pieces as [|first rest].
        -- unfold RodCutPlan in Hpieces_plan.
           destruct Hpieces_plan as [_ [_ Hempty_sum]].
           simpl in Hempty_sum.
           lia.
        -- pose proof
             (rod_cut_plan_tail__table_extension
                rod_len first rest Hpieces_plan) as Hrest_plan.
           unfold RodCutPlan in Hpieces_plan.
           destruct Hpieces_plan as [_ [Hpieces_bounds _]].
           inversion Hpieces_bounds as [|? ? Hfirst_bounds _]; subst.
           pose proof (Htable (rod_len - first) ltac:(lia)) as Hrest_opt.
           unfold RodCutOptimalRevenue, max_value_of_subset,
             max_object_of_subset in Hrest_opt.
           destruct Hrest_opt as
             [optimal_rest [[_ Hrest_max] Hrest_value]].
           specialize (Hrest_max rest Hrest_plan).
           assert (Hfirst_domain : 1 <= first < rod_len + 1) by lia.
           specialize (Hpiece_max first Hfirst_domain).
           unfold RodCutPlanRevenue in *.
           simpl in *.
           lia.
    + unfold RodCutPlanRevenue in *.
      simpl in *.
      lia.
  - destruct Hscan as [Hscan Hbest].
    assert (Hcandidate :
      Znth rod_len price 0 + Znth (rod_len - rod_len) revenue 0 <= 0).
    {
      apply Hscan.
      change (1 <= rod_len < rod_len + 1).
      lia.
    }
    assert (Hsingle_revenue : RodCutPlanRevenue price [rod_len] = 0).
    {
      unfold RodCutPlanRevenue.
      simpl.
      replace (rod_len - rod_len) with 0 in Hcandidate by lia.
      rewrite Hrevenue0 in Hcandidate.
      lia.
    }
    exists [rod_len].
    split.
    + split.
      * unfold RodCutPlan.
        split; [lia |].
        split.
        -- constructor; [lia | constructor].
        -- simpl. lia.
      * intros pieces Hpieces_plan.
        destruct pieces as [|first rest].
        -- unfold RodCutPlan in Hpieces_plan.
           destruct Hpieces_plan as [_ [_ Hempty_sum]].
           simpl in Hempty_sum.
           lia.
        -- pose proof
             (rod_cut_plan_tail__table_extension
                rod_len first rest Hpieces_plan) as Hrest_plan.
           unfold RodCutPlan in Hpieces_plan.
           destruct Hpieces_plan as [_ [Hpieces_bounds _]].
           inversion Hpieces_bounds as [|? ? Hfirst_bounds _]; subst.
           pose proof (Htable (rod_len - first) ltac:(lia)) as Hrest_opt.
           unfold RodCutOptimalRevenue, max_value_of_subset,
             max_object_of_subset in Hrest_opt.
           destruct Hrest_opt as
             [optimal_rest [[_ Hrest_max] Hrest_value]].
           specialize (Hrest_max rest Hrest_plan).
           assert (Hfirst_domain : 1 <= first < rod_len + 1) by lia.
           specialize (Hscan first Hfirst_domain).
           unfold RodCutPlanRevenue in *.
           simpl in *.
           lia.
    + lia.
Qed.
Lemma rod_cut_revenue_table_snoc__table_extension :
  forall price revenue rod_len best,
    1 <= rod_len ->
    Zlength revenue = rod_len ->
    0 <= Znth rod_len price 0 ->
    RodCutRevenueTable price revenue rod_len ->
    RodCutScanBest price revenue rod_len (rod_len + 1) best ->
    RodCutRevenueTable price (revenue ++ [best]) (rod_len + 1).
Proof.
  intros price revenue rod_len best Hlen Hrevenue_len Hprice
    Htable Hscan queried_len Hqueried_len.
  destruct (Z_lt_ge_dec queried_len rod_len) as [Hlt | Hge].
  - rewrite app_Znth1 by lia.
    apply Htable. lia.
  - assert (queried_len = rod_len) by lia.
    subst queried_len.
    rewrite app_Znth2 by lia.
    rewrite Hrevenue_len.
    replace (rod_len - rod_len) with 0 by lia.
    rewrite Znth0_cons.
    apply (rod_cut_optimal_revenue_step__table_extension
      price revenue rod_len best); auto.
Qed.
Lemma rod_cut_optimal_revenue_zero__boundary_states :
  forall price, RodCutOptimalRevenue price 0 0.
Proof.
  intros price.
  unfold RodCutOptimalRevenue, max_value_of_subset, max_object_of_subset.
  exists nil.
  split.
  - split.
    + unfold RodCutPlan.
      simpl.
      repeat split; try lia.
      constructor.
    + intros pieces Hplan.
      unfold RodCutPlanRevenue.
      destruct Hplan as [_ [Hpieces _]].
      destruct pieces as [| piece pieces].
      * simpl. lia.
      * inversion Hpieces. lia.
  - reflexivity.
Qed.
