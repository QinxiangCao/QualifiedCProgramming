Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Safety and C-data representation: these declarations deliberately do not
   state the knapsack optimum. *)
Definition KnapsackInputsBounded
    (weights values : list Z) (item_count capacity : Z) : Prop :=
  Zlength weights = item_count /\
  Zlength values = item_count /\
  (forall k, 0 <= k < item_count ->
     1 <= Znth k weights 0 <= capacity + 1) /\
  (forall k, 0 <= k < item_count ->
     0 <= Znth k values 0 <= 10000).

Definition KnapsackTableValuesBounded (dp : list Z) : Prop :=
  forall k, 0 <= k < Zlength dp -> 0 <= Znth k dp 0 <= 4000000.

Definition KnapsackTablePrefixShape
    (dp : list Z) (written : Z) : Prop :=
  0 <= written /\ Zlength dp = written.

(* The following annotation-facing states compose, rather than redefine, the
   separate safety/representation and mathematical predicates. *)
Definition KnapsackStaticSafety
    (weights values : list Z) (item_count capacity width : Z) : Prop :=
  0 <= item_count <= 300 /\
  0 <= capacity <= 300 /\
  width = capacity + 1 /\
  1 <= width <= 301 /\
  KnapsackInputsBounded weights values item_count capacity.

Definition KnapsackPlanWeight (weights picks : list Z) (weight : Z) : Prop :=
  weight = sum (map (fun i => Znth i weights 0) picks).

Definition KnapsackPlanValue
    (weights values picks : list Z) (value : Z) : Prop :=
  Zlength weights = Zlength values /\
  value = sum (map (fun i => Znth i values 0) picks).

Definition KnapsackPlan
    (weights values : list Z) (item_count cap value : Z) : Prop :=
  0 <= item_count <= Zlength weights /\
  Zlength weights = Zlength values /\
  0 <= cap /\
  exists picks weight,
    NoDup picks /\
    Forall (fun i => 0 <= i < item_count) picks /\
    KnapsackPlanWeight weights picks weight /\
    weight <= cap /\
    KnapsackPlanValue weights values picks value.

Definition KnapsackMaxValue
    (weights values : list Z) (item_count cap answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun value => KnapsackPlan weights values item_count cap value)
    (fun value => value)
    answer.

Definition KnapsackCellCorrect
    (weights values : list Z) (row col value : Z) : Prop :=
  KnapsackMaxValue weights values row col value.

Definition KnapsackCellIndex (capacity row col : Z) : Z :=
  row * (capacity + 1) + col.

Definition KnapsackTablePrefix
    (weights values : list Z) (capacity : Z) (dp : list Z)
    (written : Z) : Prop :=
  forall row col,
    0 <= row ->
    0 <= col <= capacity ->
    0 <= KnapsackCellIndex capacity row col < written ->
    KnapsackCellCorrect weights values row col
      (Znth (KnapsackCellIndex capacity row col) dp 0).

Definition KnapsackRowsDone
    (weights values : list Z) (capacity : Z) (dp : list Z)
    (rows_done : Z) : Prop :=
  KnapsackTablePrefix weights values capacity dp
    (rows_done * (capacity + 1)).

Definition KnapsackRowProgress
    (weights values : list Z) (capacity : Z) (dp : list Z)
    (row col : Z) : Prop :=
  KnapsackTablePrefix weights values capacity dp
    (row * (capacity + 1) + col).

Definition KnapsackRowsAnnotationState
    (weights values : list Z) (item_count capacity width : Z)
    (dp : list Z) (rows_done : Z) : Prop :=
  KnapsackStaticSafety weights values item_count capacity width /\
  0 <= rows_done <= item_count + 1 /\
  0 <= rows_done * width <= (item_count + 1) * (capacity + 1) /\
  KnapsackTablePrefixShape dp (rows_done * width) /\
  KnapsackTableValuesBounded dp /\
  KnapsackRowsDone weights values capacity dp rows_done.

Definition KnapsackRowAnnotationState
    (weights values : list Z) (item_count capacity width : Z)
    (dp : list Z) (row col : Z) : Prop :=
  KnapsackStaticSafety weights values item_count capacity width /\
  0 <= row <= item_count /\
  0 <= col <= capacity + 1 /\
  0 <= row * width + col <= (item_count + 1) * (capacity + 1) /\
  KnapsackTablePrefixShape dp (row * width + col) /\
  KnapsackTableValuesBounded dp /\
  KnapsackRowProgress weights values capacity dp row col.

Definition KnapsackResultState
    (weights values : list Z) (item_count capacity : Z)
    (dp : list Z) (answer : Z) : Prop :=
  KnapsackMaxValue weights values item_count capacity answer /\
  0 <= answer <= 4000000 /\
  KnapsackTablePrefixShape dp ((item_count + 1) * (capacity + 1)) /\
  KnapsackTableValuesBounded dp /\
  KnapsackRowsDone weights values capacity dp (item_count + 1).

(* Helper imports migrated from zero_one_knapsack__vc_proving_subagent_merged_proof_manual.v. *)
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

(* Helper lemmas migrated from zero_one_knapsack__vc_proving_subagent_merged_proof_manual.v. *)

Lemma KnapsackRowsDone_to_RowProgress0 :
  forall weights values capacity dp row,
    0 <= capacity ->
    KnapsackRowsDone weights values capacity dp row ->
    KnapsackRowProgress weights values capacity dp row 0.
Proof.
  intros weights values capacity dp row Hcap Hdone.
  unfold KnapsackRowsDone in Hdone.
  unfold KnapsackRowProgress.
  replace (row * (capacity + 1) + 0) with (row * (capacity + 1)) by lia.
  exact Hdone.
Qed.

Lemma KnapsackRowProgress_end_to_RowsDone :
  forall weights values capacity dp row col,
    col = capacity + 1 ->
    KnapsackRowProgress weights values capacity dp row col ->
    KnapsackRowsDone weights values capacity dp (row + 1).
Proof.
  intros weights values capacity dp row col Hcol Hprogress.
  unfold KnapsackRowProgress in Hprogress.
  unfold KnapsackRowsDone.
  replace ((row + 1) * (capacity + 1)) with (row * (capacity + 1) + col) by nia.
  exact Hprogress.
Qed.

Lemma KnapsackRowProgress_index_bound :
  forall weights values capacity dp row col idx,
    KnapsackTablePrefixShape dp (row * (capacity + 1) + col) ->
    KnapsackRowProgress weights values capacity dp row col ->
    0 <= idx < row * (capacity + 1) + col ->
    0 <= idx < Zlength dp.
Proof.
  intros weights values capacity dp row col idx Hshape Hprogress Hidx.
  unfold KnapsackTablePrefixShape in Hshape.
  lia.
Qed.

Lemma KnapsackRowProgress_lookup_cell :
  forall weights values capacity dp row col lookup_row lookup_col,
    KnapsackRowProgress weights values capacity dp row col ->
    0 <= lookup_row ->
    0 <= lookup_col <= capacity ->
    0 <= KnapsackCellIndex capacity lookup_row lookup_col <
      row * (capacity + 1) + col ->
    KnapsackCellCorrect weights values lookup_row lookup_col
      (Znth (KnapsackCellIndex capacity lookup_row lookup_col) dp 0).
Proof.
  intros weights values capacity dp row col lookup_row lookup_col
    Hprogress Hrow Hcol Hidx.
  unfold KnapsackRowProgress, KnapsackTablePrefix in Hprogress.
  apply Hprogress; lia.
Qed.

Lemma KnapsackRowsDone_index_bound :
  forall weights values capacity dp rows_done idx,
    KnapsackTablePrefixShape dp (rows_done * (capacity + 1)) ->
    KnapsackRowsDone weights values capacity dp rows_done ->
    0 <= idx < rows_done * (capacity + 1) ->
    0 <= idx < Zlength dp.
Proof.
  intros weights values capacity dp rows_done idx Hshape Hdone Hidx.
  unfold KnapsackTablePrefixShape in Hshape.
  lia.
Qed.

Lemma KnapsackRowsDone_lookup_cell :
  forall weights values capacity dp rows_done lookup_row lookup_col,
    KnapsackRowsDone weights values capacity dp rows_done ->
    0 <= lookup_row ->
    0 <= lookup_col <= capacity ->
    0 <= KnapsackCellIndex capacity lookup_row lookup_col <
      rows_done * (capacity + 1) ->
    KnapsackCellCorrect weights values lookup_row lookup_col
      (Znth (KnapsackCellIndex capacity lookup_row lookup_col) dp 0).
Proof.
  intros weights values capacity dp rows_done lookup_row lookup_col
    Hdone Hrow Hcol Hidx.
  unfold KnapsackRowsDone, KnapsackTablePrefix in Hdone.
  apply Hdone; lia.
Qed.

Lemma Forall_Z_lt_0_nil:
  forall l, Forall (fun i : Z => 0 <= i < 0) l -> l = nil.
Proof.
  intros l H.
  induction l as [| a l IH]; auto.
  inversion H; subst.
  lia.
Qed.

Lemma sum_map_weights_nonnegative:
  forall weights n picks,
    (forall k, 0 <= k < n -> 1 <= Znth k weights 0) ->
    Forall (fun i : Z => 0 <= i < n) picks ->
    0 <= sum (map (fun i : Z => Znth i weights 0) picks).
Proof.
  intros weights n picks Hweights Hpicks.
  induction picks as [| p picks IH]; simpl; [lia|].
  inversion Hpicks as [| ? ? Hp Htail]; subst.
  specialize (Hweights p Hp).
  specialize (IH Htail).
  lia.
Qed.

Lemma KnapsackPlan_empty:
  forall weights values item_count cap,
    0 <= item_count <= Zlength weights ->
    Zlength weights = Zlength values ->
    0 <= cap ->
    KnapsackPlan weights values item_count cap 0.
Proof.
  intros weights values item_count cap Hcount Hlen Hcap.
  unfold KnapsackPlan.
  split; [exact Hcount|].
  split; [exact Hlen|].
  split; [exact Hcap|].
  exists nil, 0.
  unfold KnapsackPlanWeight, KnapsackPlanValue.
  repeat split; simpl; auto; try lia; constructor.
Qed.

Lemma KnapsackPlan_row0_value_zero:
  forall weights values cap value,
    KnapsackPlan weights values 0 cap value ->
    value = 0.
Proof.
  intros weights values cap value Hplan.
  unfold KnapsackPlan, KnapsackPlanValue in Hplan.
  destruct Hplan as (_ & _ & _ & picks & weight & _ & Hpicks & _ & _ & Hvalue).
  apply Forall_Z_lt_0_nil in Hpicks.
  subst picks.
  simpl in Hvalue.
  lia.
Qed.

Lemma KnapsackPlan_col0_value_zero:
  forall weights values item_count value,
    (forall k, 0 <= k < item_count -> 1 <= Znth k weights 0) ->
    KnapsackPlan weights values item_count 0 value ->
    value = 0.
Proof.
  intros weights values item_count value Hweights Hplan.
  unfold KnapsackPlan, KnapsackPlanWeight, KnapsackPlanValue in Hplan.
  destruct Hplan as (_ & _ & _ & picks & weight & _ & Hpicks & Hweight & Hcap & Hvalue).
  destruct Hvalue as [_ Hvalue].
  destruct picks as [| p picks].
  - simpl in Hvalue.
    lia.
  - pose proof (Forall_inv Hpicks) as Hp.
    pose proof (Forall_inv_tail Hpicks) as Htail.
    simpl in Hweight.
    pose proof (Hweights p Hp) as Hp_weight.
    pose proof (sum_map_weights_nonnegative weights item_count picks Hweights Htail)
      as Htail_nonneg.
    lia.
Qed.

Lemma KnapsackCellCorrect_row0_zero:
  forall weights values cap,
    0 <= cap ->
    Zlength weights = Zlength values ->
    KnapsackCellCorrect weights values 0 cap 0.
Proof.
  intros weights values cap Hcap Hlen.
  unfold KnapsackCellCorrect, KnapsackMaxValue,
    MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists 0.
  split; [split|reflexivity].
  - apply KnapsackPlan_empty.
    + split; [lia|apply Zlength_nonneg].
    + exact Hlen.
    + exact Hcap.
  - intros value Hplan.
    apply KnapsackPlan_row0_value_zero in Hplan.
    lia.
Qed.

Lemma KnapsackCellCorrect_col0_zero:
  forall weights values item_count,
    0 <= item_count <= Zlength weights ->
    Zlength weights = Zlength values ->
    (forall k, 0 <= k < item_count -> 1 <= Znth k weights 0) ->
    KnapsackCellCorrect weights values item_count 0 0.
Proof.
  intros weights values item_count Hcount Hlen Hweights.
  unfold KnapsackCellCorrect, KnapsackMaxValue,
    MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists 0.
  split; [split|reflexivity].
  - apply KnapsackPlan_empty.
    + exact Hcount.
    + exact Hlen.
    + lia.
  - intros value Hplan.
    apply (KnapsackPlan_col0_value_zero weights values item_count value) in Hplan;
      auto.
    lia.
Qed.

Lemma KnapsackRowProgress_append_cell:
  forall weights values capacity dp row col value,
    Zlength dp = KnapsackCellIndex capacity row col ->
    KnapsackRowProgress weights values capacity dp row col ->
    0 <= col <= capacity ->
    KnapsackCellCorrect weights values row col value ->
    KnapsackRowProgress weights values capacity (dp ++ value :: nil) row (col + 1).
Proof.
  intros weights values capacity dp row col value Hlen Hprog Hcol Hcell.
  unfold KnapsackRowProgress in *.
  unfold KnapsackTablePrefix in *.
  intros r c Hr Hc Hidx.
    unfold KnapsackCellIndex in *.
    destruct (Z_lt_ge_dec (r * (capacity + 1) + c)
               (row * (capacity + 1) + col)) as [Hlt|Hge].
    + rewrite app_Znth1; [apply Hprog; lia|].
      rewrite Hlen.
      unfold KnapsackCellIndex.
      lia.
    + assert (r = row /\ c = col) as [-> ->].
      {
        assert (r = row) by nia.
        subst r.
        assert (c = col) by lia.
        auto.
      }
      rewrite app_Znth2; [|rewrite Hlen; unfold KnapsackCellIndex; lia].
      replace (row * (capacity + 1) + col -
                 Zlength dp) with 0 by (rewrite Hlen; unfold KnapsackCellIndex; lia).
      rewrite Znth0_cons.
      exact Hcell.
Qed.

Lemma append_zero_range:
  forall dp k,
    (forall i, 0 <= i < Zlength dp -> 0 <= Znth i dp 0 <= 4000000) ->
    0 <= k < Zlength (dp ++ 0 :: nil) ->
    0 <= Znth k (dp ++ 0 :: nil) 0 <= 4000000.
Proof.
  intros dp k Hrange Hk.
  rewrite Zlength_app_cons in Hk.
  destruct (Z_lt_ge_dec k (Zlength dp)) as [Hlt|Hge].
  - rewrite (app_Znth1 0 dp (0 :: nil) k) by lia.
    apply Hrange; lia.
  - rewrite (app_Znth2 0 dp (0 :: nil) k) by lia.
    replace (k - Zlength dp) with 0 by lia.
    rewrite Znth0_cons.
    lia.
Qed.

Lemma Z_index_unique : forall r i c j C : Z,
  0 <= C ->
  0 <= c <= C ->
  0 <= j <= C ->
  r * (C + 1) + c = i * (C + 1) + j ->
  r = i /\ c = j.
Proof.
  intros r i c j C HC Hc Hj Heq.
  assert (Hrdiv : r = (r * (C + 1) + c) / (C + 1)).
  {
    apply Z.div_unique_pos with (r := c); [lia | ring].
  }
  assert (Hidiv : i = (i * (C + 1) + j) / (C + 1)).
  {
    apply Z.div_unique_pos with (r := j); [lia | ring].
  }
  assert (Hri : r = i) by (rewrite Hrdiv, Hidiv, Heq; reflexivity).
  subst r.
  split; [reflexivity | lia].
Qed.

Lemma NoDup_remove_Z : forall (x : Z) (l : list Z),
  NoDup l -> NoDup (remove Z.eq_dec x l).
Proof.
  intros x l Hnd.
  induction Hnd as [|a l Hnotin Hnd IH]; simpl.
  - constructor.
  - destruct (Z.eq_dec x a).
    + exact IH.
    + constructor.
      * intro Hin.
        apply in_remove in Hin.
        tauto.
      * exact IH.
Qed.

Lemma Forall_remove_Z : forall (P : Z -> Prop) (x : Z) (l : list Z),
  Forall P l -> Forall P (remove Z.eq_dec x l).
Proof.
  intros P x l HFor.
  apply Forall_forall.
  intros y Hy.
  apply in_remove in Hy.
  apply Forall_forall with (x := y) in HFor; tauto.
Qed.

Lemma sum_map_remove_NoDup : forall (f : Z -> Z) (x : Z) (l : list Z),
  NoDup l ->
  In x l ->
  sum (map f l) = f x + sum (map f (remove Z.eq_dec x l)).
Proof.
  intros f x l Hnd Hin.
  induction Hnd as [|a l Hnotin Hnd IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst a.
      destruct (Z.eq_dec x x) as [_ | Hneq]; [|contradiction].
      rewrite notin_remove by exact Hnotin.
      lia.
    + destruct (Z.eq_dec x a) as [Heq | Hneq].
      * subst a. contradiction.
      * simpl. rewrite (IH Hin). lia.
Qed.

Lemma KnapsackPlan_promote_item : forall weights values item cap value,
  item < Zlength weights ->
  KnapsackPlan weights values item cap value ->
  KnapsackPlan weights values (item + 1) cap value.
Proof.
  intros weights values item cap value Hitem_lt Hplan.
  unfold KnapsackPlan in *.
  destruct Hplan as [Hitem [Hlen [Hcap Hexists]]].
  destruct Hexists as [picks [weight [Hnd [HFor [Hweight [Hweight_cap Hvalue]]]]]].
  split; [lia |].
  split; [assumption |].
  split; [assumption |].
  exists picks, weight.
  split; [assumption |].
  split.
  - apply Forall_forall.
    intros x Hinx.
    apply Forall_forall with (x := x) in HFor; [lia | exact Hinx].
  - split; [assumption |].
    split; [assumption | assumption].
Qed.

Lemma KnapsackPlan_add_item : forall weights values item cap value w v,
  0 <= item < Zlength weights ->
  0 <= w ->
  Zlength weights = Zlength values ->
  w = Znth item weights 0 ->
  v = Znth item values 0 ->
  KnapsackPlan weights values item (cap - w) value ->
  KnapsackPlan weights values (item + 1) cap (value + v).
Proof.
  intros weights values item cap value w v Hitem Hw_nonneg Hlen Hw Hv Hplan.
  unfold KnapsackPlan in *.
  destruct Hplan as [Hold_item [Hold_len [Hold_cap Hexists]]].
  destruct Hexists as [picks [weight [Hnd [HFor [Hweight [Hweight_cap Hvalue]]]]]].
  destruct Hvalue as [Hvalue_len Hvalue_eq].
  split; [lia |].
  split; [assumption |].
  split; [lia |].
  exists (item :: picks), (w + weight).
  split.
  - constructor.
    + intro Hin.
      apply Forall_forall with (x := item) in HFor; [lia | exact Hin].
    + exact Hnd.
  - split.
    + constructor; [lia |].
      apply Forall_forall.
      intros x Hinx.
      apply Forall_forall with (x := x) in HFor; [lia | exact Hinx].
    + split.
      * unfold KnapsackPlanWeight in *.
        simpl. subst w. lia.
      * split; [lia |].
        unfold KnapsackPlanValue in *.
        split; [exact Hlen |].
        simpl. subst v. lia.
Qed.

Lemma sum_map_nonneg : forall (f : Z -> Z) (l : list Z),
  (forall x : Z, In x l -> 0 <= f x) ->
  0 <= sum (map f l).
Proof.
  intros f l Hnonneg.
  induction l as [|a l IH]; simpl; [lia |].
  assert (0 <= f a) by (apply Hnonneg; simpl; auto).
  assert (0 <= sum (map f l)).
  {
    apply IH.
    intros x Hinx.
    apply Hnonneg.
    simpl; auto.
  }
  lia.
Qed.

Lemma KnapsackPlan_split_last_item : forall weights values item cap value w v,
  0 <= item < Zlength weights ->
  Zlength weights = Zlength values ->
  w = Znth item weights 0 ->
  v = Znth item values 0 ->
  (forall k : Z, 0 <= k < Zlength weights -> 0 <= Znth k weights 0) ->
  KnapsackPlan weights values (item + 1) cap value ->
  (exists old_value : Z,
      KnapsackPlan weights values item (cap - w) old_value /\
      value = old_value + v) \/
  KnapsackPlan weights values item cap value.
Proof.
  intros weights values item cap value w v Hitem Hlen Hw Hv Hweights_nonneg Hplan.
  unfold KnapsackPlan in Hplan.
  destruct Hplan as [Htarget_item [Htarget_len [Htarget_cap Hexists]]].
  destruct Hexists as [picks [weight [Hnd [HFor [Hweight [Hweight_cap Hvalue]]]]]].
  destruct Hvalue as [Hvalue_len Hvalue_eq].
  destruct (in_dec Z.eq_dec item picks) as [Hin_item | Hnotin_item].
  - left.
    exists (value - v).
    split; [|lia].
    unfold KnapsackPlan.
    split; [lia |].
    split; [exact Htarget_len |].
    assert (Hremove_weight_nonneg :
      0 <= sum (map (fun i : Z => Znth i weights 0) (remove Z.eq_dec item picks))).
    {
      apply sum_map_nonneg.
      intros x Hinx.
      apply in_remove in Hinx.
      destruct Hinx as [Hin_x Hx_ne].
      apply Forall_forall with (x := x) in HFor; [|exact Hin_x].
      apply Hweights_nonneg.
      lia.
    }
    split.
    + unfold KnapsackPlanWeight in Hweight.
      pose proof (sum_map_remove_NoDup (fun i : Z => Znth i weights 0) item picks Hnd Hin_item) as Hsumw.
      rewrite Hweight in Hweight_cap.
      rewrite Hsumw in Hweight_cap.
      subst w.
      lia.
    + exists (remove Z.eq_dec item picks), (weight - w).
      split; [apply NoDup_remove_Z; exact Hnd |].
      split.
      * apply Forall_forall.
        intros x Hinx.
        apply in_remove in Hinx.
        destruct Hinx as [Hin_x Hx_ne].
        apply Forall_forall with (x := x) in HFor; [lia | exact Hin_x].
      * split.
        -- unfold KnapsackPlanWeight in *.
           pose proof (sum_map_remove_NoDup (fun i : Z => Znth i weights 0) item picks Hnd Hin_item) as Hsumw.
           rewrite Hsumw in Hweight.
           subst w.
           lia.
        -- split; [lia |].
           unfold KnapsackPlanValue in *.
           split; [exact Htarget_len |].
           pose proof (sum_map_remove_NoDup (fun i : Z => Znth i values 0) item picks Hnd Hin_item) as Hsumv.
           rewrite Hsumv in Hvalue_eq.
           subst v.
           lia.
  - right.
    unfold KnapsackPlan.
    split; [lia |].
    split; [exact Htarget_len |].
    split; [exact Htarget_cap |].
    exists picks, weight.
    split; [exact Hnd |].
    split.
    + apply Forall_forall.
      intros x Hinx.
      apply Forall_forall with (x := x) in HFor; [|exact Hinx].
      assert (x <> item) by (intro Heq; subst x; contradiction).
      lia.
    + split; [exact Hweight |].
      split; [exact Hweight_cap |].
      unfold KnapsackPlanValue.
      split; [exact Htarget_len | exact Hvalue_eq].
Qed.

Lemma KnapsackCellCorrect_take_better : forall weights values item j w v without prev,
  0 <= item < Zlength weights ->
  Zlength weights = Zlength values ->
  w = Znth item weights 0 ->
  v = Znth item values 0 ->
  0 <= w ->
  (forall k : Z, 0 <= k < Zlength weights -> 0 <= Znth k weights 0) ->
  KnapsackCellCorrect weights values item j without ->
  KnapsackCellCorrect weights values item (j - w) prev ->
  prev + v > without ->
  KnapsackCellCorrect weights values (item + 1) j (prev + v).
Proof.
  intros weights values item j w v without prev Hitem Hlen Hw Hv Hw_nonneg
         Hweights_nonneg Hwithout Hprev Hbetter.
  unfold KnapsackCellCorrect, KnapsackMaxValue in *.
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
  destruct Hwithout as [without_obj [[Hplan_without Hmax_without] Hwithout_eq]].
  destruct Hprev as [prev_obj [[Hplan_prev Hmax_prev] Hprev_eq]].
  subst without_obj prev_obj.
  exists (prev + v).
  split; [|reflexivity].
  split.
  - apply KnapsackPlan_add_item with (w := w) (v := v); try assumption.
  - intros b Hplan_b.
    pose proof (KnapsackPlan_split_last_item weights values item j b w v
                  Hitem Hlen Hw Hv Hweights_nonneg Hplan_b) as Hsplit.
    destruct Hsplit as [[old_value [Hold_plan Hb]] | Hdrop_plan].
    + subst b.
      specialize (Hmax_prev old_value Hold_plan).
      lia.
    + specialize (Hmax_without b Hdrop_plan).
      lia.
Qed.

Lemma KnapsackCellCorrect_keep_without_when_better_or_equal :
  forall weights values item j w v without prev,
  0 <= item < Zlength weights ->
  Zlength weights = Zlength values ->
  w = Znth item weights 0 ->
  v = Znth item values 0 ->
  0 <= w ->
  (forall k : Z, 0 <= k < Zlength weights -> 0 <= Znth k weights 0) ->
  KnapsackCellCorrect weights values item j without ->
  KnapsackCellCorrect weights values item (j - w) prev ->
  prev + v <= without ->
  KnapsackCellCorrect weights values (item + 1) j without.
Proof.
  intros weights values item j w v without prev Hitem Hlen Hw Hv Hw_nonneg
         Hweights_nonneg Hwithout Hprev Hle.
  unfold KnapsackCellCorrect, KnapsackMaxValue in *.
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
  destruct Hwithout as [without_obj [[Hplan_without Hmax_without] Hwithout_eq]].
  destruct Hprev as [prev_obj [[Hplan_prev Hmax_prev] Hprev_eq]].
  subst without_obj prev_obj.
  exists without.
  split; [|reflexivity].
  split.
  - apply KnapsackPlan_promote_item; try assumption; lia.
  - intros b Hplan_b.
    pose proof (KnapsackPlan_split_last_item weights values item j b w v
                  Hitem Hlen Hw Hv Hweights_nonneg Hplan_b) as Hsplit.
    destruct Hsplit as [[old_value [Hold_plan Hb]] | Hdrop_plan].
    + subst b.
      specialize (Hmax_prev old_value Hold_plan).
      lia.
    + specialize (Hmax_without b Hdrop_plan).
      lia.
Qed.

Lemma KnapsackCellCorrect_too_heavy : forall weights values item j w v without,
  0 <= item < Zlength weights ->
  Zlength weights = Zlength values ->
  w = Znth item weights 0 ->
  v = Znth item values 0 ->
  w > j ->
  (forall k : Z, 0 <= k < Zlength weights -> 0 <= Znth k weights 0) ->
  KnapsackCellCorrect weights values item j without ->
  KnapsackCellCorrect weights values (item + 1) j without.
Proof.
  intros weights values item j w v without Hitem Hlen Hw Hv Htoo_heavy
         Hweights_nonneg Hwithout.
  unfold KnapsackCellCorrect, KnapsackMaxValue in *.
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
  destruct Hwithout as [without_obj [[Hplan_without Hmax_without] Hwithout_eq]].
  subst without_obj.
  exists without.
  split; [|reflexivity].
  split.
  - apply KnapsackPlan_promote_item; try assumption; lia.
  - intros b Hplan_b.
    pose proof (KnapsackPlan_split_last_item weights values item j b w v
                  Hitem Hlen Hw Hv Hweights_nonneg Hplan_b) as Hsplit.
    destruct Hsplit as [[old_value [Hold_plan Hb]] | Hdrop_plan].
    + unfold KnapsackPlan in Hold_plan.
      destruct Hold_plan as [_ [_ [Hold_cap _]]].
      lia.
    + specialize (Hmax_without b Hdrop_plan).
      lia.
Qed.

Lemma Forall_range_incl_seq : forall picks n,
  0 <= n ->
  Forall (fun i : Z => 0 <= i < n) picks ->
  incl picks (map Z.of_nat (seq 0 (Z.to_nat n))).
Proof.
  intros picks n Hn HFor.
  unfold incl.
  intros x Hinx.
  apply Forall_forall with (x := x) in HFor; [|exact Hinx].
  apply in_map_iff.
  exists (Z.to_nat x).
  split.
  - apply Z2Nat.id. lia.
  - apply in_seq.
    split; [lia |].
    rewrite Nat.add_0_l.
    apply Z2Nat.inj_lt; lia.
Qed.

Lemma NoDup_Forall_range_length_le : forall picks n,
  0 <= n ->
  NoDup picks ->
  Forall (fun i : Z => 0 <= i < n) picks ->
  Z.of_nat (List.length picks) <= n.
Proof.
  intros picks n Hn Hnd HFor.
  pose proof (Forall_range_incl_seq picks n Hn HFor) as Hincl.
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  lia.
Qed.

Lemma sum_map_values_bound : forall values picks n b,
  Forall (fun i : Z => 0 <= i < n) picks ->
  (forall k : Z, 0 <= k < n -> 0 <= Znth k values 0 <= b) ->
  0 <= sum (map (fun i : Z => Znth i values 0) picks) <=
       Zlength picks * b.
Proof.
  intros values picks n b HFor Hbound.
  induction HFor as [|a picks Ha HFor IH]; simpl.
  - lia.
  - specialize (Hbound a Ha).
    rewrite Zlength_cons.
    lia.
Qed.

Lemma KnapsackCellCorrect_value_bound : forall weights values item cap value n,
  Zlength values = n ->
  0 <= n <= 300 ->
  (forall k : Z, 0 <= k < n -> 0 <= Znth k values 0 <= 10000) ->
  KnapsackCellCorrect weights values item cap value ->
  0 <= value <= 4000000.
Proof.
  intros weights values item cap value n Hvalues_len Hn Hvalues_bound Hcell.
  unfold KnapsackCellCorrect, KnapsackMaxValue in Hcell.
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hcell.
  destruct Hcell as [value_obj [[Hplan _] Hvalue_obj]].
  subst value_obj.
  unfold KnapsackPlan in Hplan.
  destruct Hplan as [Hitem [Hlen [_ Hexists]]].
  destruct Hexists as [picks [weight [Hnd [HFor [_ [_ Hvalue_plan]]]]]].
  unfold KnapsackPlanValue in Hvalue_plan.
  destruct Hvalue_plan as [_ Hvalue_eq].
  assert (HFor_n : Forall (fun i : Z => 0 <= i < n) picks).
  {
    apply Forall_forall.
    intros x Hinx.
    apply Forall_forall with (x := x) in HFor; [|exact Hinx].
    lia.
  }
  pose proof (NoDup_Forall_range_length_le picks n (proj1 Hn) Hnd HFor_n) as Hpicks_len.
  assert (Hpicks_zlen : Zlength picks <= n).
  {
    rewrite Zlength_correct.
    exact Hpicks_len.
  }
  pose proof (sum_map_values_bound values picks n 10000 HFor_n Hvalues_bound) as Hsum.
  rewrite Hvalue_eq.
  lia.
Qed.

Lemma KnapsackRowProgress_append_cell_recurrence : forall weights values capacity dp row col value,
  0 <= col <= capacity ->
  KnapsackRowProgress weights values capacity dp row col ->
  Zlength dp = row * (capacity + 1) + col ->
  KnapsackCellCorrect weights values row col value ->
  KnapsackRowProgress weights values capacity (dp ++ value :: nil) row (col + 1).
Proof.
  intros weights values capacity dp row col value Hcol Hprogress Hdp_len Hcell.
  unfold KnapsackRowProgress in *.
  unfold KnapsackTablePrefix in *.
  intros r c Hr Hc Hidx.
    unfold KnapsackCellIndex in *.
    destruct (Z_lt_dec (r * (capacity + 1) + c) (row * (capacity + 1) + col)) as [Hlt_old | Hnot_lt_old].
    + rewrite app_Znth1.
      * apply Hprogress; try lia.
      * rewrite Hdp_len. lia.
    + assert (Heq_idx : r * (capacity + 1) + c = row * (capacity + 1) + col) by lia.
      pose proof (Z_index_unique r row c col capacity (ltac:(lia)) Hc Hcol Heq_idx) as [Hr_eq Hc_eq].
      subst r c.
      rewrite app_Znth2 by lia.
      replace (row * (capacity + 1) + col - Zlength dp) with 0 by lia.
      simpl.
      exact Hcell.
Qed.

Lemma KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit :
  forall weights values item_count capacity answer,
    KnapsackMaxValue weights values item_count capacity answer ->
    0 <= item_count /\ 0 <= capacity.
Proof.
  intros weights values item_count capacity answer Hmax.
  unfold KnapsackMaxValue, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in Hmax.
  destruct Hmax as [obj [[Hplan _] _]].
  unfold KnapsackPlan in Hplan.
  destruct Hplan as [Hitem [_ [Hcapacity _]]].
  lia.
Qed.

Lemma KnapsackRowAnnotationState_append_cell__row_state_result_refactor :
  forall weights values item_count capacity width dp row col value,
    KnapsackRowAnnotationState weights values item_count capacity width
      dp row col ->
    0 <= col <= capacity ->
    KnapsackCellCorrect weights values row col value ->
    0 <= value <= 4000000 ->
    KnapsackRowAnnotationState weights values item_count capacity width
      (dp ++ value :: nil) row (col + 1).
Proof.
  intros weights values item_count capacity width dp row col value
    Hstate Hcol Hcell Hvalue.
  unfold KnapsackRowAnnotationState in *.
  destruct Hstate as
    [Hsafety [Hrow [Hcol_state [Hwritten [Hshape [Hbounded Hprogress]]]]]].
  destruct Hsafety as [Hitems [Hcapacity [Hwidth [Hwidth_bounds Hinputs]]]].
  split.
  - exact (conj Hitems
      (conj Hcapacity (conj Hwidth (conj Hwidth_bounds Hinputs)))).
  - split; [exact Hrow|].
    split; [nia|].
    split; [nia|].
    split.
    + unfold KnapsackTablePrefixShape in *.
      destruct Hshape as [Hwritten_nonnegative Hlength].
      split; [lia|].
      rewrite Zlength_app_cons, Hlength.
      lia.
    + split.
      * unfold KnapsackTableValuesBounded in *.
        intros k Hk.
        rewrite Zlength_app_cons in Hk.
        destruct (Z_lt_ge_dec k (Zlength dp)) as [Hold | Hnew].
        -- rewrite app_Znth1 by lia.
           apply Hbounded; lia.
        -- rewrite app_Znth2 by lia.
           replace (k - Zlength dp) with 0 by lia.
           rewrite Znth0_cons.
           exact Hvalue.
      * apply KnapsackRowProgress_append_cell_recurrence; try assumption.
        unfold KnapsackTablePrefixShape in Hshape.
        destruct Hshape as [_ Hlength].
        rewrite Hlength, Hwidth.
        reflexivity.
Qed.
Lemma KnapsackRowsAnnotationState_to_Result__row_state_result_refactor :
  forall weights values item_count capacity width dp,
    KnapsackRowsAnnotationState weights values item_count capacity width
      dp (item_count + 1) ->
    KnapsackResultState weights values item_count capacity dp
      (Znth (item_count * width + capacity) dp 0).
Proof.
  intros weights values item_count capacity width dp Hstate.
  unfold KnapsackRowsAnnotationState in Hstate.
  destruct Hstate as
    [Hsafety [_ [_ [Hshape [Hbounded Hdone]]]]].
  destruct Hsafety as [Hitems [Hcapacity [Hwidth [Hwidth_bounds Hinputs]]]].
  unfold KnapsackResultState.
  split.
  - pose proof Hdone as Hcell_source.
    unfold KnapsackRowsDone, KnapsackTablePrefix in Hcell_source.
    specialize (Hcell_source item_count capacity (proj1 Hitems) (ltac:(lia))).
    assert (Hindex :
      0 <= KnapsackCellIndex capacity item_count capacity <
        (item_count + 1) * (capacity + 1)) by
      (unfold KnapsackCellIndex; nia).
    specialize (Hcell_source Hindex).
    replace (item_count * width + capacity) with
      (KnapsackCellIndex capacity item_count capacity) by
      (unfold KnapsackCellIndex; nia).
    exact Hcell_source.
  - split.
    + apply Hbounded.
      unfold KnapsackTablePrefixShape in Hshape.
      destruct Hshape as [_ Hlength].
      rewrite Hlength, Hwidth.
      nia.
    + split.
      * unfold KnapsackTablePrefixShape in *.
        destruct Hshape as [Hnonnegative Hlength].
        split; [nia|].
        rewrite Hlength, Hwidth.
        reflexivity.
      * split; [exact Hbounded|exact Hdone].
Qed.
