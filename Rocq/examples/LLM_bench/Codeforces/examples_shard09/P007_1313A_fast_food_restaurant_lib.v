Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Per-case signature: solve_case(a,b,c:Z)->Z. Output is the maximum number of
   pairwise different nonempty dish sets respecting the three stocks. *)
(* Menu kinds 1..7 denote A, B, C, AB, AC, BC, and ABC. *)
Definition UsesA (kind : Z) : Prop := kind = 1 \/ kind = 4 \/ kind = 5 \/ kind = 7.
Definition UsesB (kind : Z) : Prop := kind = 2 \/ kind = 4 \/ kind = 6 \/ kind = 7.
Definition UsesC (kind : Z) : Prop := kind = 3 \/ kind = 5 \/ kind = 6 \/ kind = 7.

Definition Feeds (a b c guests : Z) : Prop :=
  exists chosen : Z -> Prop,
    #(fun kind : Z => 1 <= kind < 8 /\ chosen kind) = guests /\
    #(fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesA kind) <= a /\
    #(fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesB kind) <= b /\
    #(fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesC kind) <= c.

Definition Pre (a b c : Z) : Prop :=
  (* Stated explicitly in the P007 solver Require, which therefore omits the
     Pre(...) call: 0 <= a <= 10 /\ 0 <= b <= 10 /\ 0 <= c <= 10. *)
  True.
Definition Spec (a b c out : Z) : Prop := max_value_of_subset Z.le (Feeds a b c) (fun x => x) out.

(* The seven low bits of [mask] are the characteristic set of menu kinds.
   These predicates describe the finite set being considered, the prefix of
   menu kinds already counted, and the corresponding mathematical optimum. *)
Definition SelectedByMask (mask kind : Z) : Prop :=
  Z.testbit mask (kind - 1) = true.

Definition FamilyPrefix
    (mask next cnt need_a need_b need_c : Z) : Prop :=
  cnt = #(fun kind : Z =>
            1 <= kind < next /\ SelectedByMask mask kind) /\
  need_a = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\ UsesA kind) /\
  need_b = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\ UsesB kind) /\
  need_c = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\ UsesC kind).

(* While the ingredients of the selected current kind [kind] are scanned,
   [ingredient] is the number of ingredient positions already accounted for.
   Earlier kinds are fully accounted for, whereas the current kind contributes
   to A/B/C after positions 0/1/2 respectively have been processed. *)
Definition DishPrefix
    (mask kind ingredient cnt need_a need_b need_c : Z) : Prop :=
  cnt = #(fun k : Z =>
            1 <= k < kind + 1 /\ SelectedByMask mask k) /\
  need_a = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\ UsesA k /\
               (k < kind \/ 0 < ingredient)) /\
  need_b = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\ UsesB k /\
               (k < kind \/ 1 < ingredient)) /\
  need_c = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\ UsesC k /\
               (k < kind \/ 2 < ingredient)).

Definition MaskFeeds (a b c mask guests : Z) : Prop :=
  guests = #(fun kind : Z =>
               1 <= kind < 8 /\ SelectedByMask mask kind) /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesA kind) <= a /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesB kind) <= b /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesC kind) <= c.

Definition FeedsBeforeMask (a b c next guests : Z) : Prop :=
  guests = 0 \/
  exists mask, 0 <= mask < next /\ MaskFeeds a b c mask guests.

Definition BestBeforeMask (a b c next best : Z) : Prop :=
  max_value_of_subset Z.le
    (FeedsBeforeMask a b c next) (fun x => x) best.

(* Append-only repair: the implementation numbers a menu kind by its three
   ingredient bits.  The original [UsesA]/[UsesB]/[UsesC] declarations above
   use a different sequential enumeration, so the implementation-facing
   predicates below state the bit-mask semantics explicitly. *)
Definition UsesAByBits (kind : Z) : Prop :=
  Z.testbit kind 0 = true.

Definition UsesBByBits (kind : Z) : Prop :=
  Z.testbit kind 1 = true.

Definition UsesCByBits (kind : Z) : Prop :=
  Z.testbit kind 2 = true.

Definition FamilyPrefixByBits
    (mask next cnt need_a need_b need_c : Z) : Prop :=
  cnt = #(fun kind : Z =>
            1 <= kind < next /\ SelectedByMask mask kind) /\
  need_a = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\
               UsesAByBits kind) /\
  need_b = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\
               UsesBByBits kind) /\
  need_c = #(fun kind : Z =>
               1 <= kind < next /\ SelectedByMask mask kind /\
               UsesCByBits kind).

Definition DishPrefixByBits
    (mask kind ingredient cnt need_a need_b need_c : Z) : Prop :=
  cnt = #(fun k : Z =>
            1 <= k < kind + 1 /\ SelectedByMask mask k) /\
  need_a = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\
               UsesAByBits k /\ (k < kind \/ 0 < ingredient)) /\
  need_b = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\
               UsesBByBits k /\ (k < kind \/ 1 < ingredient)) /\
  need_c = #(fun k : Z =>
               1 <= k < kind + 1 /\ SelectedByMask mask k /\
               UsesCByBits k /\ (k < kind \/ 2 < ingredient)).

Definition MaskFeedsByBits (a b c mask guests : Z) : Prop :=
  guests = #(fun kind : Z =>
               1 <= kind < 8 /\ SelectedByMask mask kind) /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesAByBits kind) <= a /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesBByBits kind) <= b /\
  #(fun kind : Z =>
      1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesCByBits kind) <= c.

Definition FeedsBeforeMaskByBits (a b c next guests : Z) : Prop :=
  guests = 0 \/
  exists mask, 0 <= mask < next /\ MaskFeedsByBits a b c mask guests.

Definition BestBeforeMaskByBits (a b c next best : Z) : Prop :=
  max_value_of_subset Z.le
    (FeedsBeforeMaskByBits a b c next) (fun x => x) best.

(* The inner ingredient loop is entered only for a kind selected by the
   current family mask.  Package that branch fact with the dish-prefix state
   so every inner-loop entry, step, and exit uses one complete interface. *)
Definition SelectedDishPrefixByBits
    (mask kind ingredient cnt need_a need_b need_c : Z) : Prop :=
  SelectedByMask mask kind /\
  DishPrefixByBits mask kind ingredient cnt need_a need_b need_c.

Require Import Coq.micromega.Lia.
Lemma best_before_mask_by_bits_zero__prefix_initialization :
  forall a b c, BestBeforeMaskByBits a b c 0 0.
Proof.
  intros a b c.
  unfold BestBeforeMaskByBits, max_value_of_subset, max_object_of_subset.
  exists 0.
  split.
  - split.
    + left.
      reflexivity.
    + intros guests [-> | [mask [[Hlo Hhi] _]]].
      * lia.
      * lia.
  - reflexivity.
Qed.
Lemma family_prefix_by_bits_one_zero__prefix_initialization :
  forall mask, FamilyPrefixByBits mask 1 0 0 0 0.
Proof.
  intros mask.
  unfold FamilyPrefixByBits.
  repeat split;
    cbv [set_card SumLib.Sum.sum enum finite_Z_range' Zrange Zrange_aux];
    reflexivity.
Qed.
Lemma set_card_iff__dish_prefix_transitions :
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
  - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
            1 + fold_right (fun _ acc => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma set_card_Z_as_sum__dish_prefix_transitions :
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
Lemma set_card_Z_extend_true__dish_prefix_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun x : Z => low <= x < high + 1 /\ P x) =
    #(fun x : Z => low <= x < high /\ P x) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__dish_prefix_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [|contradiction].
  lia.
Qed.
Lemma set_card_Z_extend_false__dish_prefix_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun x : Z => low <= x < high + 1 /\ P x) =
    #(fun x : Z => low <= x < high /\ P x).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__dish_prefix_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction |].
  lia.
Qed.
Lemma set_card_Z_range_bounds__dish_prefix_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high ->
    0 <= #(fun x : Z => low <= x < high /\ P x) <= high - low.
Proof.
  intros low high P Hrange.
  rewrite set_card_Z_as_sum__dish_prefix_transitions.
  pose proof (SumLib.ZRange.sum_Z_range_bounds low high
    (fun x => if prop_dec (P x) then 1 else 0) 0 1 Hrange) as Hbounds.
  assert (Hpoint : forall x, low <= x < high ->
    0 <= (if prop_dec (P x) then 1 else 0) <= 1).
  { intros x Hx. destruct (prop_dec (P x)); lia. }
  specialize (Hbounds Hpoint). nia.
Qed.
Lemma set_card_Z_subset_le__dish_prefix_transitions :
  forall (low high : Z) (P Q : Z -> Prop),
    (forall x, low <= x < high -> P x -> Q x) ->
    #(fun x : Z => low <= x < high /\ P x) <=
    #(fun x : Z => low <= x < high /\ Q x).
Proof.
  intros low high P Q Hsub.
  rewrite !set_card_Z_as_sum__dish_prefix_transitions.
  apply SumLib.ZRange.sum_Z_range_le.
  intros x Hx. destruct (prop_dec (P x)); destruct (prop_dec (Q x));
    try lia; exfalso; eauto.
Qed.
Lemma uses_by_bits_card_four__dish_prefix_transitions :
  #(fun k : Z => 1 <= k < 8 /\ UsesAByBits k) <= 4 /\
  #(fun k : Z => 1 <= k < 8 /\ UsesBByBits k) <= 4 /\
  #(fun k : Z => 1 <= k < 8 /\ UsesCByBits k) <= 4.
Proof.
  repeat split; rewrite set_card_Z_as_sum__dish_prefix_transitions;
    repeat (rewrite SumLib.ZRange.sum_Z_range_cons by lia);
    rewrite SumLib.ZRange.sum_Z_range_empty by lia;
    repeat match goal with
    | |- context [prop_dec ?P] => destruct (prop_dec P)
    end; unfold UsesAByBits, UsesBByBits, UsesCByBits in *;
    vm_compute in *; try contradiction; try congruence; lia.
Qed.
Lemma selected_dish_prefix_by_bits_bounds__dish_prefix_transitions :
  forall mask kind ingredient cnt a b c,
    1 <= kind <= 7 ->
    SelectedDishPrefixByBits mask kind ingredient cnt a b c ->
    0 <= a <= 4 /\ 0 <= b <= 4 /\ 0 <= c <= 4.
Proof.
  intros mask kind ingredient cnt a b c Hkind [_ Hprefix].
  unfold DishPrefixByBits in Hprefix.
  destruct Hprefix as (_ & Ha & Hb & Hc).
  destruct uses_by_bits_card_four__dish_prefix_transitions
    as [HfourA [HfourB HfourC]].
  repeat split.
  - rewrite Ha. apply set_card_Z_range_bounds__dish_prefix_transitions. lia.
  - rewrite Ha.
    assert (HeqA : #(fun k : Z =>
      1 <= k < kind + 1 /\ SelectedByMask mask k /\ UsesAByBits k /\
      (k < kind \/ 0 < ingredient)) =
      #(fun k : Z => 1 <= k < 8 /\
      (k < kind + 1 /\ SelectedByMask mask k /\ UsesAByBits k /\
       (k < kind \/ 0 < ingredient)))).
    { apply set_card_iff__dish_prefix_transitions. intros k. intuition lia. }
    rewrite HeqA.
    transitivity (#(fun k : Z => 1 <= k < 8 /\ UsesAByBits k)).
    + apply set_card_Z_subset_le__dish_prefix_transitions.
      intros k Hrange H. tauto.
    + exact HfourA.
  - rewrite Hb. apply set_card_Z_range_bounds__dish_prefix_transitions. lia.
  - rewrite Hb.
    assert (HeqB : #(fun k : Z =>
      1 <= k < kind + 1 /\ SelectedByMask mask k /\ UsesBByBits k /\
      (k < kind \/ 1 < ingredient)) =
      #(fun k : Z => 1 <= k < 8 /\
      (k < kind + 1 /\ SelectedByMask mask k /\ UsesBByBits k /\
       (k < kind \/ 1 < ingredient)))).
    { apply set_card_iff__dish_prefix_transitions. intros k. intuition lia. }
    rewrite HeqB.
    transitivity (#(fun k : Z => 1 <= k < 8 /\ UsesBByBits k)).
    + apply set_card_Z_subset_le__dish_prefix_transitions.
      intros k Hrange H. tauto.
    + exact HfourB.
  - rewrite Hc. apply set_card_Z_range_bounds__dish_prefix_transitions. lia.
  - rewrite Hc.
    assert (HeqC : #(fun k : Z =>
      1 <= k < kind + 1 /\ SelectedByMask mask k /\ UsesCByBits k /\
      (k < kind \/ 2 < ingredient)) =
      #(fun k : Z => 1 <= k < 8 /\
      (k < kind + 1 /\ SelectedByMask mask k /\ UsesCByBits k /\
       (k < kind \/ 2 < ingredient)))).
    { apply set_card_iff__dish_prefix_transitions. intros k. intuition lia. }
    rewrite HeqC.
    transitivity (#(fun k : Z => 1 <= k < 8 /\ UsesCByBits k)).
    + apply set_card_Z_subset_le__dish_prefix_transitions.
      intros k Hrange H. tauto.
    + exact HfourC.
Qed.
Lemma testbit_shiftl_one__dish_prefix_transitions :
  forall bit n,
    0 <= bit -> 0 <= n ->
    Z.testbit (Z.shiftl 1 bit) n = Z.eqb n bit.
Proof.
  intros bit n Hbit Hn.
  rewrite Z.shiftl_spec by lia.
  destruct (Z.eq_dec n bit) as [-> | Hneq].
  - replace (bit - bit) with 0 by lia.
    rewrite Z.eqb_refl. reflexivity.
  - assert (Heqb : Z.eqb n bit = false) by (apply Z.eqb_neq; exact Hneq).
    rewrite Heqb.
    destruct (Z_lt_ge_dec (n - bit) 0) as [Hneg | Hnonneg].
    + rewrite Z.testbit_neg_r by lia. reflexivity.
    + apply Z.bits_above_log2; [lia |].
      change (0 < n - bit). lia.
Qed.
Lemma machine_mask_bit_selected__dish_prefix_transitions :
  forall mask bit,
    0 <= mask < 128 -> 0 <= bit < 7 ->
    Z.land mask (Z.shiftl 1 bit) <> 0 ->
    Z.testbit mask bit = true.
Proof.
  intros mask bit Hmask Hbit Hland.
  destruct (Z.testbit mask bit) eqn:Htest; [reflexivity |].
  exfalso. apply Hland.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.testbit_0_l,
    testbit_shiftl_one__dish_prefix_transitions by lia.
  destruct (Z.eqb n bit) eqn:Heq; simpl.
  - apply Z.eqb_eq in Heq. subst n. rewrite Htest. reflexivity.
  - rewrite Bool.andb_false_r. reflexivity.
Qed.
Lemma machine_mask_bit_unselected__dish_prefix_transitions :
  forall mask bit,
    0 <= mask < 128 -> 0 <= bit < 7 ->
    Z.land mask (Z.shiftl 1 bit) = 0 ->
    Z.testbit mask bit = false.
Proof.
  intros mask bit Hmask Hbit Hland.
  destruct (Z.testbit mask bit) eqn:Htest; [|reflexivity].
  assert (Hlandbit : Z.testbit (Z.land mask (Z.shiftl 1 bit)) bit = true).
  {
    rewrite Z.land_spec,
      testbit_shiftl_one__dish_prefix_transitions, Z.eqb_refl,
      Htest by lia.
    reflexivity.
  }
  rewrite Hland, Z.testbit_0_l in Hlandbit. discriminate.
Qed.
Lemma family_to_selected_dish_zero_by_bits__dish_prefix_transitions :
  forall mask kind cnt a b c,
    1 <= kind ->
    SelectedByMask mask kind ->
    FamilyPrefixByBits mask kind cnt a b c ->
    SelectedDishPrefixByBits mask kind 0 (cnt + 1) a b c.
Proof.
  intros mask kind cnt a b c Hkind Hselected Hprefix.
  split; [exact Hselected |].
  unfold FamilyPrefixByBits in Hprefix.
  unfold DishPrefixByBits.
  destruct Hprefix as (Hcnt & Ha & Hb & Hc).
  repeat split.
  - rewrite Hcnt.
    symmetry.
    apply set_card_Z_extend_true__dish_prefix_transitions; assumption.
  - rewrite Ha. apply set_card_iff__dish_prefix_transitions.
    intros k. intuition lia.
  - rewrite Hb. apply set_card_iff__dish_prefix_transitions.
    intros k. intuition lia.
  - rewrite Hc. apply set_card_iff__dish_prefix_transitions.
    intros k. intuition lia.
Qed.
Lemma dish_component_step_true_card__dish_prefix_transitions :
  forall mask kind ingredient (P : Z -> Prop),
    1 <= kind -> SelectedByMask mask kind -> P kind ->
    #(fun k : Z =>
        1 <= k < kind + 1 /\ SelectedByMask mask k /\ P k /\
        (k < kind \/ ingredient < ingredient)) + 1 =
    #(fun k : Z =>
        1 <= k < kind + 1 /\ SelectedByMask mask k /\ P k /\
        (k < kind \/ ingredient < ingredient + 1)).
Proof.
  intros mask kind ingredient P Hkind Hselected HP.
  assert (Hold :
    #(fun k : Z =>
        1 <= k < kind + 1 /\ SelectedByMask mask k /\ P k /\
        (k < kind \/ ingredient < ingredient)) =
    #(fun k : Z => 1 <= k < kind /\ (SelectedByMask mask k /\ P k))).
  { apply set_card_iff__dish_prefix_transitions. intros k. intuition lia. }
  rewrite Hold. symmetry.
  transitivity
    (#(fun k : Z => 1 <= k < kind + 1 /\ (SelectedByMask mask k /\ P k))).
  - apply set_card_iff__dish_prefix_transitions. intros k. intuition lia.
  - apply set_card_Z_extend_true__dish_prefix_transitions.
    + lia.
    + split; assumption.
Qed.
Lemma dish_component_step_false_card__dish_prefix_transitions :
  forall mask kind ingredient (P : Z -> Prop),
    1 <= kind -> ~ P kind ->
    #(fun k : Z =>
        1 <= k < kind + 1 /\ SelectedByMask mask k /\ P k /\
        (k < kind \/ ingredient < ingredient)) =
    #(fun k : Z =>
        1 <= k < kind + 1 /\ SelectedByMask mask k /\ P k /\
        (k < kind \/ ingredient < ingredient + 1)).
Proof.
  intros mask kind ingredient P Hkind HP.
  assert (Hold :
    #(fun k : Z =>
        1 <= k < kind + 1 /\ SelectedByMask mask k /\ P k /\
        (k < kind \/ ingredient < ingredient)) =
    #(fun k : Z => 1 <= k < kind /\ (SelectedByMask mask k /\ P k))).
  { apply set_card_iff__dish_prefix_transitions. intros k. intuition lia. }
  rewrite Hold.
  symmetry.
  transitivity
    (#(fun k : Z => 1 <= k < kind + 1 /\ (SelectedByMask mask k /\ P k))).
  - apply set_card_iff__dish_prefix_transitions. intros k. intuition lia.
  - apply set_card_Z_extend_false__dish_prefix_transitions.
    + lia.
    + tauto.
Qed.
Lemma dish_component_step_unchanged_card__dish_prefix_transitions :
  forall mask kind ingredient threshold (P : Z -> Prop),
    threshold <> ingredient ->
    #(fun k : Z =>
        1 <= k < kind + 1 /\ SelectedByMask mask k /\ P k /\
        (k < kind \/ threshold < ingredient)) =
    #(fun k : Z =>
        1 <= k < kind + 1 /\ SelectedByMask mask k /\ P k /\
        (k < kind \/ threshold < ingredient + 1)).
Proof.
  intros mask kind ingredient threshold P Hneq.
  apply set_card_iff__dish_prefix_transitions.
  intros k. intuition lia.
Qed.
Lemma selected_dish_step_true_by_bits__dish_prefix_transitions :
  forall mask kind ingredient cnt a b c,
    1 <= kind ->
    0 <= ingredient < 3 ->
    SelectedDishPrefixByBits mask kind ingredient cnt a b c ->
    Z.testbit kind ingredient = true ->
    let old := [a; b; c] in
    let new := replace_Znth ingredient (Znth ingredient old 0 + 1) old in
    SelectedDishPrefixByBits mask kind (ingredient + 1) cnt
      (Znth 0 new 0) (Znth 1 new 0) (Znth 2 new 0).
Proof.
  intros mask kind ingredient cnt a b c Hkind Hd Hprefix Hbit.
  destruct Hprefix as [Hselected Hprefix].
  split; [exact Hselected |].
  unfold DishPrefixByBits in *.
  destruct Hprefix as (Hcnt & Ha & Hb & Hc).
  assert (ingredient = 0 \/ ingredient = 1 \/ ingredient = 2) as Hcases by lia.
  destruct Hcases as [-> | [-> | ->]];
    cbn [replace_Znth replace_nth Znth Z.to_nat nth] in *.
  - change (UsesAByBits kind) in Hbit.
    repeat split; try exact Hcnt.
    + rewrite Ha. apply dish_component_step_true_card__dish_prefix_transitions;
        try assumption; try lia.
    + rewrite Hb. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
    + rewrite Hc. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
  - change (UsesBByBits kind) in Hbit.
    repeat split; try exact Hcnt.
    + rewrite Ha. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
    + rewrite Hb. apply dish_component_step_true_card__dish_prefix_transitions;
        try assumption; try lia.
    + rewrite Hc. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
  - change (UsesCByBits kind) in Hbit.
    repeat split; try exact Hcnt.
    + rewrite Ha. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
    + rewrite Hb. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
    + rewrite Hc. apply dish_component_step_true_card__dish_prefix_transitions;
        try assumption; try lia.
Qed.
Lemma selected_dish_step_false_by_bits__dish_prefix_transitions :
  forall mask kind ingredient cnt a b c,
    1 <= kind ->
    0 <= ingredient < 3 ->
    SelectedDishPrefixByBits mask kind ingredient cnt a b c ->
    Z.testbit kind ingredient = false ->
    SelectedDishPrefixByBits mask kind (ingredient + 1) cnt a b c.
Proof.
  intros mask kind ingredient cnt a b c Hkind Hd Hprefix Hbit.
  destruct Hprefix as [Hselected Hprefix].
  split; [exact Hselected |].
  unfold DishPrefixByBits in *.
  destruct Hprefix as (Hcnt & Ha & Hb & Hc).
  assert (ingredient = 0 \/ ingredient = 1 \/ ingredient = 2) as Hcases by lia.
  destruct Hcases as [-> | [-> | ->]].
  - repeat split; try exact Hcnt.
    + rewrite Ha. apply dish_component_step_false_card__dish_prefix_transitions;
        try lia. unfold UsesAByBits. congruence.
    + rewrite Hb. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
    + rewrite Hc. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
  - repeat split; try exact Hcnt.
    + rewrite Ha. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
    + rewrite Hb. apply dish_component_step_false_card__dish_prefix_transitions;
        try lia. unfold UsesBByBits. congruence.
    + rewrite Hc. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
  - repeat split; try exact Hcnt.
    + rewrite Ha. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
    + rewrite Hb. apply dish_component_step_unchanged_card__dish_prefix_transitions; lia.
    + rewrite Hc. apply dish_component_step_false_card__dish_prefix_transitions;
        try lia. unfold UsesCByBits. congruence.
Qed.
Lemma selected_dish_three_to_family_by_bits__dish_prefix_transitions :
  forall mask kind cnt a b c,
    SelectedDishPrefixByBits mask kind 3 cnt a b c ->
    FamilyPrefixByBits mask (kind + 1) cnt a b c.
Proof.
  intros mask kind cnt a b c [_ Hprefix].
  unfold DishPrefixByBits in Hprefix.
  unfold FamilyPrefixByBits.
  destruct Hprefix as (Hcnt & Ha & Hb & Hc).
  repeat split; try exact Hcnt.
  - rewrite Ha. apply set_card_iff__dish_prefix_transitions.
    intros k; intuition lia.
  - rewrite Hb. apply set_card_iff__dish_prefix_transitions.
    intros k; intuition lia.
  - rewrite Hc. apply set_card_iff__dish_prefix_transitions.
    intros k; intuition lia.
Qed.
Lemma family_prefix_skip_unselected_by_bits__dish_prefix_transitions :
  forall mask kind cnt a b c,
    1 <= kind ->
    ~ SelectedByMask mask kind ->
    FamilyPrefixByBits mask kind cnt a b c ->
    FamilyPrefixByBits mask (kind + 1) cnt a b c.
Proof.
  intros mask kind cnt a b c Hkind Hnot Hprefix.
  unfold FamilyPrefixByBits in *.
  destruct Hprefix as (Hcnt & Ha & Hb & Hc).
  repeat split.
  - rewrite Hcnt.
    symmetry.
    apply set_card_Z_extend_false__dish_prefix_transitions; assumption.
  - rewrite Ha.
    symmetry.
    apply set_card_Z_extend_false__dish_prefix_transitions; [lia | tauto].
  - rewrite Hb.
    symmetry.
    apply set_card_Z_extend_false__dish_prefix_transitions; [lia | tauto].
  - rewrite Hc.
    symmetry.
    apply set_card_Z_extend_false__dish_prefix_transitions; [lia | tauto].
Qed.
Lemma family_prefix_by_bits_eight_mask_feeds__best_before_mask_update :
  forall mask cnt need_a need_b need_c,
    FamilyPrefixByBits mask 8 cnt need_a need_b need_c ->
    cnt = #(fun kind : Z =>
              1 <= kind < 8 /\ SelectedByMask mask kind) /\
    need_a = #(fun kind : Z =>
                 1 <= kind < 8 /\ SelectedByMask mask kind /\
                 UsesAByBits kind) /\
    need_b = #(fun kind : Z =>
                 1 <= kind < 8 /\ SelectedByMask mask kind /\
                 UsesBByBits kind) /\
    need_c = #(fun kind : Z =>
                 1 <= kind < 8 /\ SelectedByMask mask kind /\
                 UsesCByBits kind) /\
    forall a b c,
      need_a <= a -> need_b <= b -> need_c <= c ->
      MaskFeedsByBits a b c mask cnt.
Proof.
  intros mask cnt need_a need_b need_c Hprefix.
  unfold FamilyPrefixByBits in Hprefix.
  destruct Hprefix as (Hcnt & Ha & Hb & Hc).
  split; [exact Hcnt |].
  split; [exact Ha |].
  split; [exact Hb |].
  split; [exact Hc |].
  intros stock_a stock_b stock_c Hle_a Hle_b Hle_c.
  unfold MaskFeedsByBits.
  repeat split; try assumption.
  - rewrite <- Ha. exact Hle_a.
  - rewrite <- Hb. exact Hle_b.
  - rewrite <- Hc. exact Hle_c.
Qed.
Lemma best_before_mask_by_bits_succ_improve__best_before_mask_update :
  forall a b c mask best cnt,
    0 <= mask < 128 ->
    BestBeforeMaskByBits a b c mask best ->
    MaskFeedsByBits a b c mask cnt ->
    best < cnt ->
    BestBeforeMaskByBits a b c (mask + 1) cnt.
Proof.
  intros a b c mask best cnt Hmask Hbest Hfeeds Himprove.
  unfold BestBeforeMaskByBits, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in *.
  destruct Hbest as (old & (Hold_in & Hold_max) & Hold_eq).
  subst old.
  exists cnt.
  split; [split | reflexivity].
  - right. exists mask. split; [lia | exact Hfeeds].
  - intros guests Hguests.
    destruct Hguests as [Hzero | (other & Hother_range & Hother_feeds)].
    + subst guests.
      assert (0 <= best) as Hbest_nonneg.
      { apply Hold_max. left. reflexivity. }
      lia.
    + destruct Hother_range as [Hother_nonneg Hother_lt].
      assert (other < mask \/ other = mask) as Hposition by lia.
      destruct Hposition as [Hbefore | Heq].
      * assert (guests <= best) as Hle_best.
        { apply Hold_max. right. exists other. split; [lia | exact Hother_feeds]. }
        lia.
      * subst other.
        unfold MaskFeedsByBits in Hfeeds, Hother_feeds.
        destruct Hfeeds as [Hcnt _].
        destruct Hother_feeds as [Hguests _].
        lia.
Qed.
Lemma best_before_mask_by_bits_succ_keep_feasible__best_before_mask_update :
  forall a b c mask best cnt,
    0 <= mask < 128 ->
    BestBeforeMaskByBits a b c mask best ->
    MaskFeedsByBits a b c mask cnt ->
    cnt <= best ->
    BestBeforeMaskByBits a b c (mask + 1) best.
Proof.
  intros a b c mask best cnt Hmask Hbest Hfeeds Hkeep.
  unfold BestBeforeMaskByBits, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in *.
  destruct Hbest as (old & (Hold_in & Hold_max) & Hold_eq).
  subst old.
  exists best.
  split; [split | reflexivity].
  - destruct Hold_in as [Hzero | (old_mask & Hold_range & Hold_feeds)].
    + left. exact Hzero.
    + right. exists old_mask. split; [lia | exact Hold_feeds].
  - intros guests Hguests.
    destruct Hguests as [Hzero | (other & Hother_range & Hother_feeds)].
    + apply Hold_max. left. exact Hzero.
    + destruct Hother_range as [Hother_nonneg Hother_lt].
      assert (other < mask \/ other = mask) as Hposition by lia.
      destruct Hposition as [Hbefore | Heq].
      * apply Hold_max. right. exists other. split; [lia | exact Hother_feeds].
      * subst other.
        unfold MaskFeedsByBits in Hfeeds, Hother_feeds.
        destruct Hfeeds as [Hcnt _].
        destruct Hother_feeds as [Hguests _].
        lia.
Qed.
Lemma best_before_mask_by_bits_succ_keep_infeasible__best_before_mask_update :
  forall a b c mask best,
    0 <= mask < 128 ->
    BestBeforeMaskByBits a b c mask best ->
    (forall guests, ~ MaskFeedsByBits a b c mask guests) ->
    BestBeforeMaskByBits a b c (mask + 1) best.
Proof.
  intros a b c mask best Hmask Hbest Hinfeasible.
  unfold BestBeforeMaskByBits, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in *.
  destruct Hbest as (old & (Hold_in & Hold_max) & Hold_eq).
  subst old.
  exists best.
  split; [split | reflexivity].
  - destruct Hold_in as [Hzero | (old_mask & Hold_range & Hold_feeds)].
    + left. exact Hzero.
    + right. exists old_mask. split; [lia | exact Hold_feeds].
  - intros guests Hguests.
    destruct Hguests as [Hzero | (other & Hother_range & Hother_feeds)].
    + apply Hold_max. left. exact Hzero.
    + destruct Hother_range as [Hother_nonneg Hother_lt].
      assert (other < mask \/ other = mask) as Hposition by lia.
      destruct Hposition as [Hbefore | Heq].
      * apply Hold_max. right. exists other. split; [lia | exact Hother_feeds].
      * subst other. exfalso. exact (Hinfeasible guests Hother_feeds).
Qed.
Lemma swap_kind_3_4_involutive__final_result :
  forall kind,
    let swap := fun x : Z =>
      if Z.eq_dec x 3 then 4
      else if Z.eq_dec x 4 then 3
      else x in
    swap (swap kind) = kind /\
    (1 <= kind < 8 -> 1 <= swap kind < 8).
Proof.
  intros kind.
  cbn beta zeta.
  destruct (Z.eq_dec kind 3) as [-> | H3].
  - cbn. lia.
  - destruct (Z.eq_dec kind 4) as [-> | H4].
    + cbn. lia.
    + repeat destruct Z.eq_dec; subst; try contradiction; lia.
Qed.
Lemma uses_by_bits_swap_kind__final_result :
  forall kind, 1 <= kind < 8 ->
    let swap := fun x : Z =>
      if Z.eq_dec x 3 then 4
      else if Z.eq_dec x 4 then 3
      else x in
    (UsesAByBits kind <-> UsesA (swap kind)) /\
    (UsesBByBits kind <-> UsesB (swap kind)) /\
    (UsesCByBits kind <-> UsesC (swap kind)).
Proof.
  intros kind Hkind.
  cbn beta zeta.
  assert (kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/
          kind = 5 \/ kind = 6 \/ kind = 7) as Hcases by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    unfold UsesAByBits, UsesBByBits, UsesCByBits,
      UsesA, UsesB, UsesC;
    repeat split; intro H; vm_compute in H |- *; intuition congruence.
Qed.
Lemma set_card_extensional__final_result :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q)
         (f : A -> A),
    (forall x, f (f x) = x) ->
    (forall x, P x <-> Q (f x)) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ f Hinvol Hequiv.
  assert (Hinjective : forall x y, f x = f y -> x = y).
  {
    intros x y Hxy.
    rewrite <- (Hinvol x), <- (Hinvol y), Hxy.
    reflexivity.
  }
  assert (Hnodup_map :
    forall l : list A, NoDup l -> NoDup (map f l)).
  {
    intros l Hnodup.
    induction Hnodup; simpl.
    - constructor.
    - constructor.
      + intros Hin.
        apply in_map_iff in Hin.
        destruct Hin as [y [Hfy Hy]].
        apply H.
        apply Hinjective in Hfy.
        subst y. exact Hy.
      + exact IHHnodup.
  }
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm :
    Permutation (map f (@enum A P FP)) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - apply Hnodup_map. exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros x.
      rewrite <- (@enum_ok A Q FQ x).
      split.
      + intros Hin.
        apply in_map_iff in Hin.
        destruct Hin as [y [Hxy Hy]].
        subst x.
        apply (proj1 (Hequiv y)).
        apply (proj2 (@enum_ok A P FP y)). exact Hy.
      + intros HQ.
        apply in_map_iff.
        exists (f x). split.
        * exact (Hinvol x).
        * apply (proj1 (@enum_ok A P FP (f x))).
          apply (proj2 (Hequiv (f x))).
          rewrite Hinvol. exact HQ.
  }
  assert (Hfold_perm :
    fold_right (fun _ acc => 1 + acc) 0 (map f (@enum A P FP)) =
    fold_right (fun _ acc => 1 + acc) 0 (@enum A Q FQ)).
  {
    induction Hperm; simpl.
    - reflexivity.
    - exact (f_equal (fun z : Z => 1 + z) IHHperm).
    - reflexivity.
    - etransitivity; eassumption.
  }
  assert (Hfold_map :
    forall l : list A,
      fold_right (fun _ acc => 1 + acc) 0 (map f l) =
      fold_right (fun _ acc => 1 + acc) 0 l).
  {
    induction l as [|x xs IH]; simpl; [reflexivity |].
    exact (f_equal (fun z : Z => 1 + z) IH).
  }
  rewrite Hfold_map in Hfold_perm.
  exact Hfold_perm.
Qed.
Lemma set_card_empty__final_result :
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
Lemma selected_by_mask_128__final_result :
  forall chosen : Z -> Prop,
    exists mask,
      0 <= mask < 128 /\
      forall kind, 1 <= kind < 8 ->
        (SelectedByMask mask kind <-> chosen kind).
Proof.
  intros chosen.
  exists ((if prop_dec (chosen 1) then 1 else 0) +
          (if prop_dec (chosen 2) then 2 else 0) +
          (if prop_dec (chosen 3) then 4 else 0) +
          (if prop_dec (chosen 4) then 8 else 0) +
          (if prop_dec (chosen 5) then 16 else 0) +
          (if prop_dec (chosen 6) then 32 else 0) +
          (if prop_dec (chosen 7) then 64 else 0)).
  destruct (prop_dec (chosen 1)) as [H1 | H1];
  destruct (prop_dec (chosen 2)) as [H2 | H2];
  destruct (prop_dec (chosen 3)) as [H3 | H3];
  destruct (prop_dec (chosen 4)) as [H4 | H4];
  destruct (prop_dec (chosen 5)) as [H5 | H5];
  destruct (prop_dec (chosen 6)) as [H6 | H6];
  destruct (prop_dec (chosen 7)) as [H7 | H7].
  all: split.
  all: try lia.
  all: intros kind Hkind.
  all: assert (kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/
               kind = 5 \/ kind = 6 \/ kind = 7) as Hcases by lia.
  all: destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
  all: unfold SelectedByMask.
  all: cbn.
  all: split.
  all: intro H.
  all: first [discriminate | reflexivity | assumption | contradiction].
Qed.
Lemma feeds_iff_feeds_before_mask_by_bits_128__final_result :
  forall a b c guests,
    0 <= a -> 0 <= b -> 0 <= c ->
    (Feeds a b c guests <-> FeedsBeforeMaskByBits a b c 128 guests).
Proof.
  intros a b c guests Ha0 Hb0 Hc0.
  set (swap := fun x : Z =>
    if Z.eq_dec x 3 then 4
    else if Z.eq_dec x 4 then 3
    else x).
  assert (Hinv : forall x, swap (swap x) = x).
  {
    intros x. unfold swap.
    exact (proj1 (swap_kind_3_4_involutive__final_result x)).
  }
  assert (Hrange : forall x, 1 <= x < 8 -> 1 <= swap x < 8).
  {
    intros x Hx. unfold swap.
    exact (proj2 (swap_kind_3_4_involutive__final_result x) Hx).
  }
  assert (Huses : forall x, 1 <= x < 8 ->
    (UsesAByBits x <-> UsesA (swap x)) /\
    (UsesBByBits x <-> UsesB (swap x)) /\
    (UsesCByBits x <-> UsesC (swap x))).
  {
    intros x Hx. unfold swap.
    exact (uses_by_bits_swap_kind__final_result x Hx).
  }
  split.
  - intros [chosen [Hguests [Ha [Hb Hc]]]].
    destruct (selected_by_mask_128__final_result
      (fun kind => chosen (swap kind))) as [mask [Hmask Hselected]].
    right. exists mask. split; [exact Hmask |].
    unfold MaskFeedsByBits.
    repeat split.
    + rewrite <- Hguests.
      etransitivity.
      * apply (set_card_extensional__final_result
          (fun kind : Z => 1 <= kind < 8 /\ chosen kind)
          (fun kind : Z => 1 <= kind < 8 /\ chosen (swap kind))
          _ _ swap Hinv).
        intros kind. split.
        -- intros [Hkind Hchosen].
           split; [apply Hrange; exact Hkind |].
           rewrite Hinv. exact Hchosen.
        -- intros [Hkind Hchosen].
           split.
           ++ rewrite <- (Hinv kind). apply Hrange. exact Hkind.
           ++ rewrite Hinv in Hchosen. exact Hchosen.
      * apply set_card_extensional__final_result with (f := fun x => x).
        -- reflexivity.
        -- intros kind. simpl. split.
           ++ intros [Hkind Hchosen]. split; [exact Hkind |].
              apply (proj2 (Hselected kind Hkind)). exact Hchosen.
           ++ intros [Hkind Hsel]. split; [exact Hkind |].
              apply (proj1 (Hselected kind Hkind)). exact Hsel.
    + assert (HcardA :
        #(fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesA kind) =
        #(fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesAByBits kind)).
      {
        etransitivity.
        * apply (set_card_extensional__final_result
            (fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesA kind)
            (fun kind : Z => 1 <= kind < 8 /\ chosen (swap kind) /\ UsesAByBits kind)
            _ _ swap Hinv).
          intros kind. split.
          -- intros [Hkind [Hchosen HUa]].
             split; [apply Hrange; exact Hkind |]. split.
             ++ rewrite Hinv. exact Hchosen.
             ++ apply (proj2 (proj1 (Huses (swap kind) (Hrange kind Hkind)))).
                rewrite Hinv. exact HUa.
          -- intros [Hkind [Hchosen HUa]].
             assert (Horig : 1 <= kind < 8).
             { rewrite <- (Hinv kind). apply Hrange. exact Hkind. }
             split; [exact Horig |]. split.
             ++ rewrite Hinv in Hchosen. exact Hchosen.
             ++ apply (proj1 (proj1 (Huses (swap kind) Hkind))) in HUa.
                rewrite Hinv in HUa. exact HUa.
        * apply set_card_extensional__final_result with (f := fun x => x).
          -- reflexivity.
          -- intros kind. simpl. split.
             ++ intros [Hkind [Hchosen HUa]].
                split; [exact Hkind |]. split; [| exact HUa].
                apply (proj2 (Hselected kind Hkind)). exact Hchosen.
             ++ intros [Hkind [Hsel HUa]].
                split; [exact Hkind |]. split; [| exact HUa].
                apply (proj1 (Hselected kind Hkind)). exact Hsel.
      }
      rewrite <- HcardA. exact Ha.
    + assert (HcardB :
        #(fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesB kind) =
        #(fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesBByBits kind)).
      {
        etransitivity.
        * apply (set_card_extensional__final_result
            (fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesB kind)
            (fun kind : Z => 1 <= kind < 8 /\ chosen (swap kind) /\ UsesBByBits kind)
            _ _ swap Hinv).
          intros kind. split.
          -- intros [Hkind [Hchosen HUb]].
             split; [apply Hrange; exact Hkind |]. split.
             ++ rewrite Hinv. exact Hchosen.
             ++ apply (proj2 (proj1 (proj2 (Huses (swap kind) (Hrange kind Hkind))))).
                rewrite Hinv. exact HUb.
          -- intros [Hkind [Hchosen HUb]].
             assert (Horig : 1 <= kind < 8).
             { rewrite <- (Hinv kind). apply Hrange. exact Hkind. }
             split; [exact Horig |]. split.
             ++ rewrite Hinv in Hchosen. exact Hchosen.
             ++ apply (proj1 (proj1 (proj2 (Huses (swap kind) Hkind)))) in HUb.
                rewrite Hinv in HUb. exact HUb.
        * apply set_card_extensional__final_result with (f := fun x => x).
          -- reflexivity.
          -- intros kind. simpl. split.
             ++ intros [Hkind [Hchosen HUb]].
                split; [exact Hkind |]. split; [| exact HUb].
                apply (proj2 (Hselected kind Hkind)). exact Hchosen.
             ++ intros [Hkind [Hsel HUb]].
                split; [exact Hkind |]. split; [| exact HUb].
                apply (proj1 (Hselected kind Hkind)). exact Hsel.
      }
      rewrite <- HcardB. exact Hb.
    + assert (HcardC :
        #(fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesC kind) =
        #(fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesCByBits kind)).
      {
        etransitivity.
        * apply (set_card_extensional__final_result
            (fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesC kind)
            (fun kind : Z => 1 <= kind < 8 /\ chosen (swap kind) /\ UsesCByBits kind)
            _ _ swap Hinv).
          intros kind. split.
          -- intros [Hkind [Hchosen HUc]].
             split; [apply Hrange; exact Hkind |]. split.
             ++ rewrite Hinv. exact Hchosen.
             ++ apply (proj2 (proj2 (Huses (swap kind) (Hrange kind Hkind)))).
                rewrite Hinv. exact HUc.
          -- intros [Hkind [Hchosen HUc]].
             assert (Horig : 1 <= kind < 8).
             { rewrite <- (Hinv kind). apply Hrange. exact Hkind. }
             split; [exact Horig |]. split.
             ++ rewrite Hinv in Hchosen. exact Hchosen.
             ++ apply (proj1 (proj2 (proj2 (Huses (swap kind) Hkind)))) in HUc.
                rewrite Hinv in HUc. exact HUc.
        * apply set_card_extensional__final_result with (f := fun x => x).
          -- reflexivity.
          -- intros kind. simpl. split.
             ++ intros [Hkind [Hchosen HUc]].
                split; [exact Hkind |]. split; [| exact HUc].
                apply (proj2 (Hselected kind Hkind)). exact Hchosen.
             ++ intros [Hkind [Hsel HUc]].
                split; [exact Hkind |]. split; [| exact HUc].
                apply (proj1 (Hselected kind Hkind)). exact Hsel.
      }
      rewrite <- HcardC. exact Hc.
  - intros [Hguests | [mask [_ Hmaskfeeds]]].
    + subst guests.
      exists (fun _ : Z => False).
      repeat split.
      * apply set_card_empty__final_result.
        intros kind [_ Hfalse]. exact Hfalse.
      * rewrite set_card_empty__final_result.
        -- exact Ha0.
        -- intros kind [_ [Hfalse _]]. exact Hfalse.
      * rewrite set_card_empty__final_result.
        -- exact Hb0.
        -- intros kind [_ [Hfalse _]]. exact Hfalse.
      * rewrite set_card_empty__final_result.
        -- exact Hc0.
        -- intros kind [_ [Hfalse _]]. exact Hfalse.
    + exists (fun kind => SelectedByMask mask (swap kind)).
      unfold MaskFeedsByBits in Hmaskfeeds.
      destruct Hmaskfeeds as [Hguests [Ha [Hb Hc]]].
      repeat split.
      * rewrite Hguests.
        symmetry.
        apply (set_card_extensional__final_result
          (fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind)
          (fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask (swap kind))
          _ _ swap Hinv).
        intros kind. split.
        -- intros [Hkind Hsel]. split; [apply Hrange; exact Hkind |].
           rewrite Hinv. exact Hsel.
        -- intros [Hkind Hsel]. split.
           ++ rewrite <- (Hinv kind). apply Hrange. exact Hkind.
           ++ rewrite Hinv in Hsel. exact Hsel.
      * assert (HcardA :
          #(fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesAByBits kind) =
          #(fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask (swap kind) /\ UsesA kind)).
        {
          apply (set_card_extensional__final_result
            (fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesAByBits kind)
            (fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask (swap kind) /\ UsesA kind)
            _ _ swap Hinv).
          intros kind. split.
          -- intros [Hkind [Hsel HUa]].
             split; [apply Hrange; exact Hkind |]. split.
             ++ rewrite Hinv. exact Hsel.
             ++ apply (proj1 (Huses kind Hkind)). exact HUa.
          -- intros [Hkind [Hsel HUa]].
             assert (Horig : 1 <= kind < 8).
             { rewrite <- (Hinv kind). apply Hrange. exact Hkind. }
             split; [exact Horig |]. split.
             ++ rewrite Hinv in Hsel. exact Hsel.
             ++ apply (proj2 (proj1 (Huses kind Horig))). exact HUa.
        }
        rewrite <- HcardA. exact Ha.
      * assert (HcardB :
          #(fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesBByBits kind) =
          #(fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask (swap kind) /\ UsesB kind)).
        {
          apply (set_card_extensional__final_result
            (fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesBByBits kind)
            (fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask (swap kind) /\ UsesB kind)
            _ _ swap Hinv).
          intros kind. split.
          -- intros [Hkind [Hsel HUb]].
             split; [apply Hrange; exact Hkind |]. split.
             ++ rewrite Hinv. exact Hsel.
             ++ apply (proj1 (proj2 (Huses kind Hkind))). exact HUb.
          -- intros [Hkind [Hsel HUb]].
             assert (Horig : 1 <= kind < 8).
             { rewrite <- (Hinv kind). apply Hrange. exact Hkind. }
             split; [exact Horig |]. split.
             ++ rewrite Hinv in Hsel. exact Hsel.
             ++ apply (proj2 (proj1 (proj2 (Huses kind Horig)))). exact HUb.
        }
        rewrite <- HcardB. exact Hb.
      * assert (HcardC :
          #(fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesCByBits kind) =
          #(fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask (swap kind) /\ UsesC kind)).
        {
          apply (set_card_extensional__final_result
            (fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask kind /\ UsesCByBits kind)
            (fun kind : Z => 1 <= kind < 8 /\ SelectedByMask mask (swap kind) /\ UsesC kind)
            _ _ swap Hinv).
          intros kind. split.
          -- intros [Hkind [Hsel HUc]].
             split; [apply Hrange; exact Hkind |]. split.
             ++ rewrite Hinv. exact Hsel.
             ++ apply (proj1 (proj2 (proj2 (Huses kind Hkind)))). exact HUc.
          -- intros [Hkind [Hsel HUc]].
             assert (Horig : 1 <= kind < 8).
             { rewrite <- (Hinv kind). apply Hrange. exact Hkind. }
             split; [exact Horig |]. split.
             ++ rewrite Hinv in Hsel. exact Hsel.
             ++ apply (proj2 (proj2 (proj2 (Huses kind Horig)))). exact HUc.
        }
        rewrite <- HcardC. exact Hc.
Qed.
Lemma best_before_mask_by_bits_128_spec__final_result :
  forall a b c best,
    0 <= a -> 0 <= b -> 0 <= c ->
    (BestBeforeMaskByBits a b c 128 best <-> Spec a b c best).
Proof.
  intros a b c best Ha Hb Hc.
  unfold BestBeforeMaskByBits, Spec,
    MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  split.
  - intros [x [[Hx Hmax] Hxbest]].
    exists x. split; [split | exact Hxbest].
    + apply (proj2 (feeds_iff_feeds_before_mask_by_bits_128__final_result
        a b c x Ha Hb Hc)). exact Hx.
    + intros y Hy.
      apply Hmax.
      apply (proj1 (feeds_iff_feeds_before_mask_by_bits_128__final_result
        a b c y Ha Hb Hc)). exact Hy.
  - intros [x [[Hx Hmax] Hxbest]].
    exists x. split; [split | exact Hxbest].
    + apply (proj1 (feeds_iff_feeds_before_mask_by_bits_128__final_result
        a b c x Ha Hb Hc)). exact Hx.
    + intros y Hy.
      apply Hmax.
      apply (proj2 (feeds_iff_feeds_before_mask_by_bits_128__final_result
        a b c y Ha Hb Hc)). exact Hy.
Qed.
