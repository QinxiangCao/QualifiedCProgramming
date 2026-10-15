Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.
Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P068 solver Require, so dropped here:
       1 <= Zlength a <= 100000 /\
       Forall (fun x => - 10000 <= x <= 10000) a  *)
  True.

Definition Spec (a : list Z) (out : Z) : Prop :=
  let n := Zlength a in out = #(fun q : Z => 0 <= q < n * n /\
   let i := q / n in let j := q mod n in 0 < i < j /\ j < n /\
   (fold_right Z.add 0) (sublist 0 i a) = (fold_right Z.add 0) (sublist i j a) /\
   (fold_right Z.add 0) (sublist i j a) = (fold_right Z.add 0) (sublist j n a)).

(* The sum of the first [k] elements of [a], the building block Spec's own
   sublist-sum equalities are stated in terms of. *)
Definition PrefixSum (a : list Z) (k : Z) : Z :=
  fold_right Z.add 0 (sublist 0 k a).

(* The count of positions [k] in [1, c] whose prefix sum equals [third],
   i.e. how many usable "first cut" candidates the sweep has recorded
   through index [c]. *)
Definition FirstCutCount (a : list Z) (third c : Z) : Z :=
  #(fun k : Z => 1 <= k < c + 1 /\ PrefixSum a k = third).

(* The count of pairs [(k, j)] with [1 <= k < j <= c], [PrefixSum a k = third]
   and [PrefixSum a j = 2 * third], i.e. the count of three-way-equal cut
   pairs whose second cut is at most [c]. *)
Definition ValidPairCount (a : list Z) (third c : Z) : Z :=
  sum_range 1 c
    (fun j => if prop_dec (PrefixSum a j = 2 * third)
              then FirstCutCount a third (j - 1)
              else 0).

Require Import Coq.micromega.Lia.
Lemma sum_empty__prefix_sum_core :
  forall (A : Type) (P : A -> Prop) (H : Finite P) (f : A -> Z),
  (forall x, ~ P x) -> sum P f = 0.
Proof.
  intros A P H f Hempty.
  unfold sum.
  destruct (@enum A P H) as [|x xs] eqn:Heq.
  - reflexivity.
  - exfalso.
    assert (Hin : In x (@enum A P H)) by (rewrite Heq; left; reflexivity).
    apply (proj2 (@enum_ok A P H x)) in Hin.
    exact (Hempty x Hin).
Qed.
Lemma FirstCutCount_zero__prefix_sum_core :
  forall (a : list Z) (third : Z), FirstCutCount a third 0 = 0.
Proof.
  intros a third.
  unfold FirstCutCount, set_card.
  apply sum_empty__prefix_sum_core.
  intros k [Hrange _]. lia.
Qed.
Lemma PrefixSum_succ__prefix_sum_core :
  forall (a : list Z) (k : Z),
  0 <= k < Zlength a ->
  PrefixSum a (k + 1) = PrefixSum a k + Znth k a 0.
Proof.
  intros a k Hk.
  unfold PrefixSum.
  assert (Hfold : forall (l : list Z) (x : Z),
    fold_right Z.add 0 (l ++ [x]) = fold_right Z.add 0 l + x).
  { induction l as [|y l IH]; intros x; simpl; try lia.
    rewrite IH; lia. }
  rewrite (sublist_split 0 (k + 1) k a) by lia.
  rewrite (sublist_single 0 k a) by lia.
  apply Hfold.
Qed.
Lemma fold_right_Zadd_app__loop_step_transitions : forall l1 l2 : list Z,
  fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.
Lemma PrefixSum_succ__loop_step_transitions : forall a k,
  0 <= k < Zlength a ->
  PrefixSum a (k + 1) = PrefixSum a k + Znth k a 0.
Proof.
  intros a k Hk.
  unfold PrefixSum.
  rewrite (sublist_split 0 (k + 1) k a) by lia.
  rewrite fold_right_Zadd_app__loop_step_transitions.
  rewrite (sublist_single 0 k a) by lia.
  simpl. lia.
Qed.
Lemma sum_perm_invariant__loop_step_transitions :
  forall {A : Type} (f : A -> Z) (l1 l2 : list A),
  Permutation l1 l2 ->
  fold_right (fun x acc => f x + acc) 0 l1 =
  fold_right (fun x acc => f x + acc) 0 l2.
Proof.
  intros A f l1 l2 Hperm.
  induction Hperm as [| x l l' Hp IH | x y l | l l' l'' Hp1 IH1 Hp2 IH2].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1, IH2. reflexivity.
Qed.
Lemma sum_pred_iff__loop_step_transitions :
  forall {A : Type} (P Q : A -> Prop) (IP : Finite P) (IQ : Finite Q) (f : A -> Z),
  (forall x, P x <-> Q x) ->
  @sum A P IP f = @sum A Q IQ f.
Proof.
  intros A P Q IP IQ f Hiff.
  unfold sum.
  apply sum_perm_invariant__loop_step_transitions.
  apply NoDup_Permutation.
  - apply (@enum_nodup A P IP).
  - apply (@enum_nodup A Q IQ).
  - intros x.
    rewrite <- (@enum_ok A P IP x).
    rewrite <- (@enum_ok A Q IQ x).
    apply Hiff.
Qed.
Lemma fold_add_filter_prop_dec_eq_indicator__loop_step_transitions :
  forall {A : Type} (l : list A) (Q : A -> Prop),
  fold_right (fun _ acc => 1 + acc) 0
    (filter (fun x => if prop_dec (Q x) then true else false) l) =
  fold_right (fun x acc => (if prop_dec (Q x) then 1 else 0) + acc) 0 l.
Proof.
  intros A l Q.
  induction l as [|x l IH].
  - reflexivity.
  - assert (Hstep1 : filter (fun y => if prop_dec (Q y) then true else false) (x :: l) =
      if prop_dec (Q x)
      then x :: filter (fun y => if prop_dec (Q y) then true else false) l
      else filter (fun y => if prop_dec (Q y) then true else false) l).
    { simpl. destruct (prop_dec (Q x)); reflexivity. }
    assert (Hstep2 : fold_right (fun x0 acc => (if prop_dec (Q x0) then 1 else 0) + acc) 0 (x :: l) =
      (if prop_dec (Q x) then 1 else 0) +
      fold_right (fun x0 acc => (if prop_dec (Q x0) then 1 else 0) + acc) 0 l).
    { reflexivity. }
    rewrite Hstep1, Hstep2.
    destruct (prop_dec (Q x)) as [HQ | HQ].
    + change (1 + fold_right (fun _ acc => 1 + acc) 0
                (filter (fun y => if prop_dec (Q y) then true else false) l) =
              1 + fold_right (fun x0 acc => (if prop_dec (Q x0) then 1 else 0) + acc) 0 l).
      rewrite IH. reflexivity.
    + change (fold_right (fun _ acc => 1 + acc) 0
                (filter (fun y => if prop_dec (Q y) then true else false) l) =
              0 + fold_right (fun x0 acc => (if prop_dec (Q x0) then 1 else 0) + acc) 0 l).
      rewrite IH. lia.
Qed.
Lemma set_card_range_as_sum_range__loop_step_transitions :
  forall (low high : Z) (Q : Z -> Prop) (I : Finite (fun k => low <= k < high /\ Q k)),
  @sum Z (fun k => low <= k < high /\ Q k) I (fun _ => 1) =
  sum_range low (high - 1) (fun k => if prop_dec (Q k) then 1 else 0).
Proof.
  intros low high Q I.
  transitivity
    (@sum Z (fun k => low <= k < high /\ Q k) (finite_Z_range' low high Q) (fun _ => 1)).
  - apply sum_pred_iff__loop_step_transitions.
    intro x. tauto.
  - assert (Henum : @enum Z (fun k => low <= k < high /\ Q k) (finite_Z_range' low high Q)
      = filter (fun x => if prop_dec (Q x) then true else false) (Zrange low high))
      by reflexivity.
    unfold sum. rewrite Henum.
    unfold sum_range.
    replace (high - 1 + 1) with high by lia.
    rewrite sum_range_unfold.
    apply fold_add_filter_prop_dec_eq_indicator__loop_step_transitions.
Qed.
Lemma FirstCutCount_succ__loop_step_transitions : forall a third c,
  0 <= c ->
  FirstCutCount a third (c + 1) =
  FirstCutCount a third c + (if prop_dec (PrefixSum a (c + 1) = third) then 1 else 0).
Proof.
  intros a third c Hc.
  unfold FirstCutCount, set_card.
  rewrite (set_card_range_as_sum_range__loop_step_transitions 1 (c + 1 + 1) (fun k => PrefixSum a k = third)).
  rewrite (set_card_range_as_sum_range__loop_step_transitions 1 (c + 1) (fun k => PrefixSum a k = third)).
  replace (c + 1 + 1 - 1) with (c + 1) by lia.
  replace (c + 1 - 1) with c by lia.
  unfold sum_range.
  rewrite (sum_Z_range_extend_right 1 (c + 1) (fun k => if prop_dec (PrefixSum a k = third) then 1 else 0)) by lia.
  reflexivity.
Qed.
Lemma FirstCutCount_zero__loop_step_transitions : forall a third,
  FirstCutCount a third 0 = 0.
Proof.
  intros a third.
  unfold FirstCutCount, set_card.
  rewrite (set_card_range_as_sum_range__loop_step_transitions 1 (0 + 1) (fun k => PrefixSum a k = third)).
  replace (0 + 1 - 1) with 0 by lia.
  unfold sum_range.
  apply sum_Z_range_empty. lia.
Qed.
Lemma ValidPairCount_succ__loop_step_transitions : forall a third c,
  0 <= c ->
  ValidPairCount a third (c + 1) =
  ValidPairCount a third c +
  (if prop_dec (PrefixSum a (c + 1) = 2 * third) then FirstCutCount a third c else 0).
Proof.
  intros a third c Hc.
  unfold ValidPairCount, sum_range.
  rewrite (sum_Z_range_extend_right 1 (c + 1)
    (fun j => if prop_dec (PrefixSum a j = 2 * third) then FirstCutCount a third (j - 1) else 0)) by lia.
  replace (c + 1 - 1) with c by lia.
  reflexivity.
Qed.
Lemma FirstCutCount_succ_true__loop_step_transitions : forall a third c,
  0 <= c -> PrefixSum a (c + 1) = third ->
  FirstCutCount a third (c + 1) = FirstCutCount a third c + 1.
Proof.
  intros a third c Hc Heq.
  rewrite (FirstCutCount_succ__loop_step_transitions a third c Hc).
  destruct (prop_dec (PrefixSum a (c + 1) = third)) as [_ | Hne]; [reflexivity | contradiction].
Qed.
Lemma FirstCutCount_succ_false__loop_step_transitions : forall a third c,
  0 <= c -> PrefixSum a (c + 1) <> third ->
  FirstCutCount a third (c + 1) = FirstCutCount a third c.
Proof.
  intros a third c Hc Hne.
  rewrite (FirstCutCount_succ__loop_step_transitions a third c Hc).
  destruct (prop_dec (PrefixSum a (c + 1) = third)) as [Heq | _]; [contradiction | lia].
Qed.
Lemma ValidPairCount_succ_true__loop_step_transitions : forall a third c,
  0 <= c -> PrefixSum a (c + 1) = 2 * third ->
  ValidPairCount a third (c + 1) = ValidPairCount a third c + FirstCutCount a third c.
Proof.
  intros a third c Hc Heq.
  rewrite (ValidPairCount_succ__loop_step_transitions a third c Hc).
  destruct (prop_dec (PrefixSum a (c + 1) = 2 * third)) as [_ | Hne]; [reflexivity | contradiction].
Qed.
Lemma ValidPairCount_succ_false__loop_step_transitions : forall a third c,
  0 <= c -> PrefixSum a (c + 1) <> 2 * third ->
  ValidPairCount a third (c + 1) = ValidPairCount a third c.
Proof.
  intros a third c Hc Hne.
  rewrite (ValidPairCount_succ__loop_step_transitions a third c Hc).
  destruct (prop_dec (PrefixSum a (c + 1) = 2 * third)) as [Heq | _]; [contradiction | lia].
Qed.
Lemma fold_count_length__zero_spec_final :
  forall {C : Type} (l : list C),
    fold_right (fun _ (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l).
Proof.
  intros C l.
  induction l as [|x xs IH].
  - reflexivity.
  - cbn [fold_right length].
    rewrite IH, Nat2Z.inj_succ. lia.
Qed.
Lemma set_card_empty__zero_spec_final :
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
Lemma set_card_bijection__zero_spec_final :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
         (FP : Finite P) (FQ : Finite Q) (f : A -> B) (g : B -> A),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> P (g y)) ->
    (forall x, P x -> g (f x) = x) ->
    (forall y, Q y -> f (g y) = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f g Hf Hg Hgf Hfg.
  unfold set_card, SumLib.Sum.sum.
  assert (Hnodup_map : NoDup (map f (@enum A P FP))).
  {
    assert (Hgeneral : forall xs : list A,
      NoDup xs -> (forall x, In x xs -> P x) -> NoDup (map f xs)).
    {
      intros xs Hnodup.
      induction Hnodup as [|x xs Hnotin Hnodup IH]; intros Hall; simpl.
      - constructor.
      - constructor.
        + intro Hin. apply in_map_iff in Hin.
          destruct Hin as [y [Hfy Hy]].
          apply Hnotin.
          assert (HPx : P x) by (apply Hall; left; reflexivity).
          assert (HPy : P y) by (apply Hall; right; exact Hy).
          assert (Hxy : x = y).
          { rewrite <- (Hgf x HPx), <- (Hgf y HPy). congruence. }
          rewrite Hxy. exact Hy.
        + apply IH. intros y Hy. apply Hall. right. exact Hy.
    }
    apply Hgeneral.
    - exact (@enum_nodup A P FP).
    - intros x Hx. apply (proj2 (@enum_ok A P FP x)). exact Hx.
  }
  assert (Hperm : Permutation (map f (@enum A P FP)) (@enum B Q FQ)).
  {
    apply NoDup_Permutation.
    - exact Hnodup_map.
    - exact (@enum_nodup B Q FQ).
    - intros y. rewrite <- (@enum_ok B Q FQ y). split.
      + intros Hin. apply in_map_iff in Hin.
        destruct Hin as [x [Hxy Hx]]. subst y.
        apply Hf. apply (proj2 (@enum_ok A P FP x)). exact Hx.
      + intros HyQ. apply in_map_iff. exists (g y). split.
        * apply Hfg. exact HyQ.
        * apply (proj1 (@enum_ok A P FP (g y))). apply Hg. exact HyQ.
  }
  rewrite !fold_count_length__zero_spec_final.
  rewrite <- (Permutation_length Hperm), length_map.
  reflexivity.
Qed.
Lemma set_card_ext__zero_spec_final :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Heq.
  eapply set_card_bijection__zero_spec_final
    with (f := fun x => x) (g := fun x => x).
  - intros x Hx. apply Heq. exact Hx.
  - intros x Hx. apply Heq. exact Hx.
  - intros. reflexivity.
  - intros. reflexivity.
Qed.
Lemma set_card_disjoint_union__zero_spec_final :
  forall {A : Type} (P Q PQ : A -> Prop)
         (FP : Finite P) (FQ : Finite Q) (FPQ : Finite PQ),
    (forall x, PQ x <-> P x \/ Q x) ->
    (forall x, ~ (P x /\ Q x)) ->
    @set_card A PQ FPQ = @set_card A P FP + @set_card A Q FQ.
Proof.
  intros A P Q PQ FP FQ FPQ Hor Hdisj.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A PQ FPQ) (@enum A P FP ++ @enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A PQ FPQ).
    - apply NoDup_app.
      + exact (@enum_nodup A P FP).
      + exact (@enum_nodup A Q FQ).
      + intros x HinP HinQ.
        apply (Hdisj x).
        split.
        * apply (proj2 (@enum_ok A P FP x)). exact HinP.
        * apply (proj2 (@enum_ok A Q FQ x)). exact HinQ.
    - intro x.
      rewrite in_app_iff.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      rewrite <- (@enum_ok A PQ FPQ x).
      apply Hor.
  }
  rewrite !fold_count_length__zero_spec_final.
  rewrite (Permutation_length Hperm), length_app.
  lia.
Qed.
Lemma fold_add_app__zero_spec_final :
  forall (l1 l2 : list Z),
    fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.
Lemma sublist_sum_as_prefix_diff__zero_spec_final :
  forall (a : list Z) lo hi,
    0 <= lo -> lo <= hi -> hi <= Zlength a ->
    fold_right Z.add 0 (sublist lo hi a) = PrefixSum a hi - PrefixSum a lo.
Proof.
  intros a lo hi Hlo Hle Hhi.
  unfold PrefixSum.
  assert (Hsplit : sublist 0 hi a = sublist 0 lo a ++ sublist lo hi a).
  { apply sublist_split; lia. }
  rewrite Hsplit.
  rewrite fold_add_app__zero_spec_final.
  lia.
Qed.
Lemma sum_three_parts__zero_spec_final :
  forall (a : list Z) i j,
    0 <= i /\ i <= j /\ j <= Zlength a ->
    PrefixSum a i + (PrefixSum a j - PrefixSum a i) +
      (PrefixSum a (Zlength a) - PrefixSum a j) = PrefixSum a (Zlength a).
Proof.
  intros a i j Hrange. lia.
Qed.
Lemma mixed_radix2_encode_decode__zero_spec_final :
  forall n ik jk,
    0 < n -> 0 <= ik < n -> 0 <= jk < n ->
    let q := ik * n + jk in
    0 <= q < n * n /\ q / n = ik /\ q mod n = jk.
Proof.
  intros n ik jk Hn Hik Hjk. cbn.
  split; [nia |].
  split.
  - rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia.
    lia.
  - replace (ik * n + jk) with (jk + ik * n) by ring.
    rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
Qed.
Lemma mixed_radix2_decode_encode__zero_spec_final :
  forall n q,
    0 < n -> 0 <= q < n * n ->
    (q / n) * n + q mod n = q.
Proof.
  intros n q Hn Hq.
  rewrite Z.mul_comm.
  symmetry.
  apply Z.div_mod.
  lia.
Qed.
Lemma finite_pair_rect2__zero_spec_final (lo1 hi1 lo2 hi2 : Z) :
  Finite (fun p : Z * Z => lo1 <= fst p < hi1 /\ lo2 <= snd p < hi2).
Proof.
  exact (Finite_prod (fun x => lo1 <= x < hi1) (fun y => lo2 <= y < hi2)).
Defined.
Lemma finite_pair_filtered2__zero_spec_final
    (lo1 hi1 lo2 hi2 : Z) (Q : Z * Z -> Prop) :
  Finite (fun p : Z * Z => (lo1 <= fst p < hi1 /\ lo2 <= snd p < hi2) /\ Q p).
Proof.
  exact (@Finite_subset (Z * Z) (fun p => lo1 <= fst p < hi1 /\ lo2 <= snd p < hi2) Q
    (finite_pair_rect2__zero_spec_final lo1 hi1 lo2 hi2)).
Defined.
Lemma PairSetCard__zero_spec_final
    (lo1 hi1 lo2 hi2 : Z) (Q : Z * Z -> Prop) : Z.
Proof.
  exact (@set_card (Z * Z) (fun p : Z * Z => (lo1 <= fst p < hi1 /\ lo2 <= snd p < hi2) /\ Q p)
    (finite_pair_filtered2__zero_spec_final lo1 hi1 lo2 hi2 Q)).
Defined.
Lemma valid_pair_count_as_pair_card_nat__zero_spec_final :
  forall (a : list Z) (third : Z) (m : nat),
    ValidPairCount a third (Z.of_nat m) =
    PairSetCard__zero_spec_final 1 (Z.of_nat m + 1) 1 (Z.of_nat m + 1)
      (fun p : Z * Z =>
        fst p < snd p /\
        PrefixSum a (fst p) = third /\ PrefixSum a (snd p) = 2 * third).
Proof.
  intros a third m.
  induction m as [|m IH].
  - unfold ValidPairCount, sum_range.
    rewrite sum_Z_range_empty by lia.
    symmetry.
    unfold PairSetCard__zero_spec_final.
    apply set_card_empty__zero_spec_final.
    intros p [[H1 H2] _]. lia.
  - unfold ValidPairCount, sum_range in *.
    replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by (rewrite Nat2Z.inj_succ; lia).
    rewrite (sum_Z_range_extend_right 1 (Z.of_nat m + 1)
      (fun j => if prop_dec (PrefixSum a j = 2 * third)
                then FirstCutCount a third (j - 1) else 0))
      by lia.
    rewrite IH.
    replace (Z.of_nat m + 1 - 1) with (Z.of_nat m) by lia.
    assert (Hcol :
      (if prop_dec (PrefixSum a (Z.of_nat m + 1) = 2 * third)
       then FirstCutCount a third (Z.of_nat m) else 0) =
      PairSetCard__zero_spec_final 1 (Z.of_nat m + 1) (Z.of_nat m + 1) (Z.of_nat m + 2)
        (fun p : Z * Z =>
          PrefixSum a (fst p) = third /\ PrefixSum a (snd p) = 2 * third)).
    {
      unfold PairSetCard__zero_spec_final.
      destruct (prop_dec (PrefixSum a (Z.of_nat m + 1) = 2 * third)) as [Hthird | Hnot].
      - unfold FirstCutCount.
        apply set_card_bijection__zero_spec_final
          with (f := fun k : Z => (k, Z.of_nat m + 1)) (g := fun p : Z * Z => fst p).
        + intros k Hk. simpl. split; [lia |].
          split; [lia | rewrite Hthird; reflexivity].
        + intros p [[H1 H2] [H3 H4]]. simpl. split; [lia | exact H3].
        + intros k Hk. reflexivity.
        + intros p [[H1 H2] [H3 H4]].
          destruct p as [k j]; simpl in *.
          assert (j = Z.of_nat m + 1) by lia.
          subst j. reflexivity.
      - symmetry. apply set_card_empty__zero_spec_final.
        intros p [[H1 H2] [H3 H4]].
        apply Hnot.
        assert (Hsp : snd p = Z.of_nat m + 1) by lia.
        rewrite <- Hsp. exact H4.
    }
    rewrite Hcol.
    symmetry.
    unfold PairSetCard__zero_spec_final.
    apply set_card_disjoint_union__zero_spec_final.
    + intros p. split.
      * intros [[H1 H2] [H3 [H4 H5]]].
        destruct (Z.eq_dec (snd p) (Z.of_nat m + 1)) as [Heq | Hneq].
        -- right. repeat split; try lia; auto.
        -- left. repeat split; try lia; auto.
      * intros [[[H1 H2] [H3 [H4 H5]]] | [[H1 H2] [H3 H4]]].
        -- repeat split; try lia; auto.
        -- repeat split; try lia; auto.
    + intros p [[[H1 H2] _] [[H1' H2'] _]]. lia.
Qed.
Lemma valid_pair_count_as_pair_card__zero_spec_final :
  forall (a : list Z) (third c : Z),
    0 <= c ->
    ValidPairCount a third c =
    PairSetCard__zero_spec_final 1 (c + 1) 1 (c + 1)
      (fun p : Z * Z =>
        fst p < snd p /\
        PrefixSum a (fst p) = third /\ PrefixSum a (snd p) = 2 * third).
Proof.
  intros a third c Hc.
  rewrite <- (Z2Nat.id c Hc).
  apply valid_pair_count_as_pair_card_nat__zero_spec_final.
Qed.
Lemma valid_pair_count_iff_spec__zero_spec_final :
  forall (a : list Z) (third n : Z),
    n = Zlength a -> 0 < n ->
    ValidPairCount a third (n - 1) =
    #(fun q : Z =>
        0 <= q < n * n /\
        0 < q / n /\ q / n < q mod n /\ q mod n < n /\
        PrefixSum a (q / n) = third /\ PrefixSum a (q mod n) = 2 * third).
Proof.
  intros a third n Hn Hnpos.
  rewrite valid_pair_count_as_pair_card__zero_spec_final by lia.
  unfold PairSetCard__zero_spec_final.
  replace (n - 1 + 1) with n by lia.
  apply set_card_bijection__zero_spec_final
    with (f := fun p : Z * Z => fst p * n + snd p)
         (g := fun q : Z => (q / n, q mod n)).
  - intros p [[H1 H2] [H3 [H4 H5]]].
    pose proof (mixed_radix2_encode_decode__zero_spec_final n (fst p) (snd p)
      ltac:(lia) ltac:(lia) ltac:(lia)) as [Hb [Hd Hm]].
    simpl in *.
    repeat split; try lia; congruence.
  - intros q [H1 [H2 [H3 [H4 [H5 H6]]]]].
    simpl. repeat split; try lia; auto.
  - intros p [[H1 H2] [H3 [H4 H5]]].
    pose proof (mixed_radix2_encode_decode__zero_spec_final n (fst p) (snd p)
      ltac:(lia) ltac:(lia) ltac:(lia)) as [Hb [Hd Hm]].
    destruct p as [k j]; simpl in *.
    f_equal; congruence.
  - intros q [H1 [H2 [H3 [H4 [H5 H6]]]]].
    simpl.
    apply mixed_radix2_decode_encode__zero_spec_final; lia.
Qed.
