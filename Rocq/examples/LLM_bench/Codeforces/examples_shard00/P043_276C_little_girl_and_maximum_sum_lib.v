Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Definition QueryReplyTotal (arr : list Z) (queries : list (Z*Z)) : Z :=
  fold_right Z.add 0 (map (fun q => fold_right Z.add 0
    (sublist (fst q) (snd q + 1) arr)) queries).
Definition Pre (a : list Z) (queries : list (Z*Z)) : Prop :=
  1 <= Zlength a <= 200000 /\ 1 <= Zlength queries <= 200000 /\
  Forall (fun x => 1 <= x <= 200000) a /\
  Forall (fun q => 0 <= fst q <= snd q /\ snd q < Zlength a) queries.
Definition Spec (a : list Z) (queries : list (Z*Z)) (out : Z) : Prop :=
  max_value_of_subset Z.le (fun arranged => Permutation a arranged)
    (fun arranged => QueryReplyTotal arranged queries) out.

(** Number of queries whose inclusive interval covers [position]. *)
Definition QueryCoverage (queries : list (Z * Z)) (position : Z) : Z :=
  #(fun j : Z =>
      0 <= j < Zlength queries /\
      fst (Znth j queries (0, 0)) <= position <=
      snd (Znth j queries (0, 0))).

(** Mathematical value stored at one index of the range-difference array
    after [done] queries have been incorporated. *)
Definition DifferenceValue
    (queries : list (Z * Z)) (done index : Z) : Z :=
  #(fun j : Z =>
      0 <= j < done /\ fst (Znth j queries (0, 0)) = index) -
  #(fun j : Z =>
      0 <= j < done /\ snd (Znth j queries (0, 0)) + 1 = index).

Definition DifferencePrefix
    (queries : list (Z * Z)) (n done : Z) (diff : list Z) : Prop :=
  Zlength diff = n + 1 /\
  0 <= done <= Zlength queries /\
  forall k, 0 <= k <= n ->
    Znth k diff 0 = DifferenceValue queries done k.

(** Positions before [done] have been converted from differences to exact
    coverage counts; positions from [done] onward retain their difference
    values. *)
Definition CoveragePrefixState
    (queries : list (Z * Z)) (n done : Z) (diff : list Z) : Prop :=
  Zlength diff = n + 1 /\
  1 <= done <= n /\
  (forall k, 0 <= k < done ->
     Znth k diff 0 = QueryCoverage queries k) /\
  (forall k, done <= k <= n ->
     Znth k diff 0 = DifferenceValue queries (Zlength queries) k).

Definition CoverageProfile
    (queries : list (Z * Z)) (n : Z) (coverage : list Z) : Prop :=
  Zlength coverage = n /\
  forall k, 0 <= k < n ->
    Znth k coverage 0 = QueryCoverage queries k.

Definition DotProduct (xs ys : list Z) : Z :=
  fold_right Z.add 0
    (map (fun pair => fst pair * snd pair) (combine xs ys)).

Definition DotProductPrefix
    (xs ys : list Z) (done total : Z) : Prop :=
  0 <= done <= Zlength xs /\
  Zlength xs = Zlength ys /\
  total = DotProduct (sublist 0 done xs) (sublist 0 done ys).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma set_card_empty__difference_initialization :
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
Lemma DifferencePrefix_zero__difference_initialization :
  forall queries n,
    0 <= n ->
    DifferencePrefix queries n 0 (repeat 0 (Z.to_nat (n + 1))).
Proof.
  intros queries n Hn.
  unfold DifferencePrefix.
  split.
  - rewrite Zlength_correct, repeat_length.
    lia.
  - split.
    + pose proof (Zlength_nonneg queries).
      lia.
    + intros k Hk.
      rewrite Znth_repeat.
      unfold DifferenceValue.
      assert (Hleft :
        #(fun j : Z => 0 <= j < 0 /\
          fst (Znth j queries (0, 0)) = k) = 0).
      { apply set_card_empty__difference_initialization.
        intros j Hj. lia. }
      assert (Hright :
        #(fun j : Z => 0 <= j < 0 /\
          snd (Znth j queries (0, 0)) + 1 = k) = 0).
      { apply set_card_empty__difference_initialization.
        intros j Hj. lia. }
      rewrite Hleft, Hright.
      lia.
Qed.
Lemma Zlength_replace_Znth__query_difference_update :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v.
  revert n.
  induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma set_card_Z_as_sum__query_difference_update :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend__query_difference_update :
  forall (low high : Z) (P : Z -> Prop),
    low <= high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) +
      (if prop_dec (P high) then 1 else 0).
Proof.
  intros low high P Hrange.
  rewrite !set_card_Z_as_sum__query_difference_update.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  reflexivity.
Qed.
Lemma DifferenceValue_query_step__query_difference_update :
  forall (queries : list (Z * Z)) (done k : Z),
    0 <= done < Zlength queries ->
    DifferenceValue queries (done + 1) k =
      DifferenceValue queries done k +
        (if Z.eq_dec (fst (Znth done queries (0, 0))) k then 1 else 0) -
        (if Z.eq_dec (snd (Znth done queries (0, 0)) + 1) k then 1 else 0).
Proof.
  intros queries done k Hdone.
  unfold DifferenceValue.
  rewrite !set_card_Z_extend__query_difference_update by lia.
  repeat match goal with
  | |- context [prop_dec (?x = ?y)] =>
      destruct (prop_dec (x = y))
  | |- context [Z.eq_dec ?x ?y] =>
      destruct (Z.eq_dec x y)
  end; try congruence; lia.
Qed.
Lemma DifferencePrefix_query_step__query_difference_update :
  forall (queries : list (Z * Z)) (n done : Z) (diff : list Z)
         (left right : Z),
    DifferencePrefix queries n done diff ->
    0 <= done < Zlength queries ->
    fst (Znth done queries (0, 0)) = left ->
    snd (Znth done queries (0, 0)) + 1 = right ->
    0 <= left <= n ->
    0 <= right <= n ->
    DifferencePrefix queries n (done + 1)
      (replace_Znth right
        (Znth right
          (replace_Znth left (Znth left diff 0 + 1) diff) 0 - 1)
        (replace_Znth left (Znth left diff 0 + 1) diff)).
Proof.
  intros queries n done diff left right
    [Hlen [Hdone_prefix Hvalues]] Hdone Hleft Hright Hleft_bound Hright_bound.
  unfold DifferencePrefix.
  split.
  - repeat rewrite Zlength_replace_Znth__query_difference_update. exact Hlen.
  - split; [lia |].
    intros k Hk.
    rewrite (DifferenceValue_query_step__query_difference_update queries done k Hdone).
    rewrite Hleft, Hright.
    rewrite <- (Hvalues k Hk).
    destruct (Z.eq_dec k right) as [Hkr | Hkr].
    + subst k.
      rewrite Znth_replace_Znth_Same by
        (rewrite Zlength_replace_Znth__query_difference_update, Hlen; lia).
      destruct (Z.eq_dec right left) as [Hrl | Hrl].
      * rewrite Hrl in *.
        rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
        destruct (Z.eq_dec left left); try congruence; lia.
      * assert (Hlr : left <> right) by lia.
        pose proof
          (@Znth_replace_Znth_Diff Z 0 diff left right
            (Znth left diff 0 + 1)
            ltac:(rewrite Hlen; lia)
            ltac:(rewrite Hlen; lia) Hlr) as Hreplace.
        rewrite Hreplace.
        destruct (Z.eq_dec left right); try congruence.
        destruct (Z.eq_dec right right); try congruence.
        lia.
    + rewrite Znth_replace_Znth_Diff by
        (try rewrite Zlength_replace_Znth__query_difference_update, Hlen; lia).
      destruct (Z.eq_dec k left) as [Hkl | Hkl].
      * subst k.
        pose proof
          (@Znth_replace_Znth_Same Z 0 diff left
            (Znth left diff 0 + 1) ltac:(rewrite Hlen; lia)) as Hreplace.
        rewrite Hreplace.
        destruct (Z.eq_dec left left); try congruence.
        destruct (Z.eq_dec right left); try congruence; lia.
      * pose proof
          (@Znth_replace_Znth_Diff Z 0 diff left k
            (Znth left diff 0 + 1)
            ltac:(rewrite Hlen; lia)
            ltac:(rewrite Hlen; lia) ltac:(lia)) as Hreplace.
        rewrite Hreplace.
        destruct (Z.eq_dec left k); try congruence.
        destruct (Z.eq_dec right k); try congruence; lia.
Qed.
Lemma Zlength_replace_Znth__coverage_prefix :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l.
  induction l as [|a l IH]; intros n v; simpl; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n) as [|m].
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IH (Z.of_nat m) v).
    replace (Z.to_nat (Z.of_nat m)) with m in IH by lia.
    rewrite IH. lia.
Qed.
Lemma set_card_empty__coverage_prefix :
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
Lemma set_card_iff__coverage_prefix :
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
    - intros z.
      rewrite <- (@enum_ok A P FP z), <- (@enum_ok A Q FQ z).
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
Lemma set_card_Z_as_sum__coverage_prefix :
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
Lemma set_card_Z_range_bounds__coverage_prefix :
  forall (low high : Z) (P : Z -> Prop),
    low <= high ->
    0 <= #(fun x : Z => low <= x < high /\ P x) <= high - low.
Proof.
  intros low high P Hrange.
  rewrite set_card_Z_as_sum__coverage_prefix.
  pose proof (SumLib.ZRange.sum_Z_range_bounds low high
    (fun x => if prop_dec (P x) then 1 else 0) 0 1 Hrange) as Hbounds.
  assert (Hpoint : forall x, low <= x < high ->
    0 <= (if prop_dec (P x) then 1 else 0) <= 1).
  { intros x Hx. destruct (prop_dec (P x)); lia. }
  specialize (Hbounds Hpoint). nia.
Qed.
Lemma DifferenceValue_zero_eq_QueryCoverage__coverage_prefix :
  forall (queries : list (Z * Z)),
    (forall j, 0 <= j < Zlength queries ->
      0 <= fst (Znth j queries (0, 0)) <= snd (Znth j queries (0, 0))) ->
    DifferenceValue queries (Zlength queries) 0 = QueryCoverage queries 0.
Proof.
  intros queries Hvalid.
  unfold DifferenceValue, QueryCoverage.
  assert (Hends :
    #(fun j : Z =>
        0 <= j < Zlength queries /\
        snd (Znth j queries (0, 0)) + 1 = 0) = 0).
  {
    apply set_card_empty__coverage_prefix.
    intros j [[Hj0 Hjlen] Hend].
    specialize (Hvalid j (conj Hj0 Hjlen)).
    lia.
  }
  rewrite Hends, Z.sub_0_r.
  apply set_card_iff__coverage_prefix.
  intros j. split.
  - intros [Hj Hstart].
    split; [exact Hj |].
    specialize (Hvalid j Hj).
    lia.
  - intros [Hj Hcovers].
    split; [exact Hj |].
    specialize (Hvalid j Hj).
    lia.
Qed.
Lemma QueryCoverage_step__coverage_prefix :
  forall (queries : list (Z * Z)) position,
    (forall j, 0 <= j < Zlength queries ->
      0 <= fst (Znth j queries (0, 0)) <= snd (Znth j queries (0, 0))) ->
    QueryCoverage queries position =
      QueryCoverage queries (position - 1) +
      DifferenceValue queries (Zlength queries) position.
Proof.
  intros queries position Hvalid.
  unfold QueryCoverage, DifferenceValue.
  rewrite !set_card_Z_as_sum__coverage_prefix.
  rewrite <- SumLib.Sum.sum_sub.
  rewrite <- SumLib.Sum.sum_add.
  apply SumLib.Sum.sum_ext.
  intros j Hj.
  specialize (Hvalid j Hj).
  destruct (prop_dec
    (fst (Znth j queries (0, 0)) <= position <=
     snd (Znth j queries (0, 0)))) as [Hnow | Hnow];
  destruct (prop_dec
    (fst (Znth j queries (0, 0)) <= position - 1 <=
     snd (Znth j queries (0, 0)))) as [Hprev | Hprev];
  destruct (prop_dec (fst (Znth j queries (0, 0)) = position))
    as [Hstart | Hstart];
  destruct (prop_dec (snd (Znth j queries (0, 0)) + 1 = position))
    as [Hend | Hend]; simpl; lia.
Qed.
Lemma DifferencePrefix_complete_to_CoveragePrefixState_one__coverage_prefix :
  forall (queries : list (Z * Z)) n diff,
    1 <= n ->
    (forall j, 0 <= j < Zlength queries ->
      0 <= fst (Znth j queries (0, 0)) <= snd (Znth j queries (0, 0)) /\
      snd (Znth j queries (0, 0)) < n) ->
    DifferencePrefix queries n (Zlength queries) diff ->
    CoveragePrefixState queries n 1 diff.
Proof.
  intros queries n diff Hn Hvalid Hprefix.
  unfold DifferencePrefix in Hprefix.
  destruct Hprefix as [Hlen [_ Hvalues]].
  unfold CoveragePrefixState.
  split; [exact Hlen |].
  split; [lia |].
  split.
  - intros k Hk.
    assert (k = 0) by lia. subst k.
    rewrite Hvalues by lia.
    apply DifferenceValue_zero_eq_QueryCoverage__coverage_prefix.
    intros j Hj. specialize (Hvalid j Hj). lia.
  - intros k Hk.
    apply Hvalues. lia.
Qed.
Lemma CoveragePrefixState_step__coverage_prefix :
  forall (queries : list (Z * Z)) n done diff,
    (forall j, 0 <= j < Zlength queries ->
      0 <= fst (Znth j queries (0, 0)) <= snd (Znth j queries (0, 0)) /\
      snd (Znth j queries (0, 0)) < n) ->
    1 <= done < n ->
    CoveragePrefixState queries n done diff ->
    CoveragePrefixState queries n (done + 1)
      (replace_Znth done
        (Znth done diff 0 + Znth (done - 1) diff 0) diff).
Proof.
  intros queries n done diff Hvalid Hdone Hstate.
  unfold CoveragePrefixState in Hstate |- *.
  destruct Hstate as [Hlen [Hdone_old [Hbefore Hafter]]].
  split; [rewrite Zlength_replace_Znth__coverage_prefix; exact Hlen |].
  split; [lia |].
  split.
  - intros k Hk.
    destruct (Z.eq_dec k done) as [Heq | Hneq].
    + subst k.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Hafter by lia.
      rewrite Hbefore by lia.
      pose proof (QueryCoverage_step__coverage_prefix queries done
        ltac:(intros j Hj; specialize (Hvalid j Hj); lia)) as Hstep.
      lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply Hbefore. lia.
  - intros k Hk.
    rewrite Znth_replace_Znth_Diff by lia.
    apply Hafter. lia.
Qed.
Lemma CoveragePrefixState_complete_to_CoverageProfile__coverage_prefix :
  forall (queries : list (Z * Z)) n diff,
    CoveragePrefixState queries n n diff ->
    CoverageProfile queries n (sublist 0 n diff).
Proof.
  intros queries n diff Hstate.
  unfold CoveragePrefixState in Hstate.
  destruct Hstate as [Hlen [Hdone [Hcoverage _]]].
  unfold CoverageProfile.
  split.
  - rewrite Zlength_sublist by lia. lia.
  - intros k Hk.
    rewrite Znth_sublist0 by lia.
    apply Hcoverage. exact Hk.
Qed.
Lemma CoverageProfile_bounds__coverage_prefix :
  forall (queries : list (Z * Z)) n q coverage,
    q = Zlength queries ->
    CoverageProfile queries n coverage ->
    forall k, 0 <= k < n -> 0 <= Znth k coverage 0 <= q.
Proof.
  intros queries n q coverage Hq Hprofile k Hk.
  unfold CoverageProfile in Hprofile.
  destruct Hprofile as [_ Hcoverage].
  rewrite Hcoverage by exact Hk.
  unfold QueryCoverage.
  pose proof (set_card_Z_range_bounds__coverage_prefix
    0 (Zlength queries)
    (fun j : Z =>
      fst (Znth j queries (0, 0)) <= k <=
      snd (Znth j queries (0, 0)))
    (Zlength_nonneg queries)) as Hbounds.
  lia.
Qed.
Lemma Permutation_pointwise_bounds__sorting_setup :
  forall (input sorted : list Z) lo hi,
    (forall i, 0 <= i < Zlength input ->
      lo <= Znth i input 0 <= hi) ->
    Permutation input sorted ->
    forall i, 0 <= i < Zlength sorted ->
      lo <= Znth i sorted 0 <= hi.
Proof.
  intros input sorted lo hi Hbounds Hperm i Hi.
  apply (proj1 (Forall_Znth (fun x => lo <= x <= hi) 0 sorted)).
  - eapply Permutation_Forall.
    + exact Hperm.
    + apply (proj2 (Forall_Znth (fun x => lo <= x <= hi) 0 input)).
      exact Hbounds.
  - exact Hi.
Qed.
Lemma Znth_app_left__dot_product_accumulation :
  forall {A : Type} (d : A) (l1 l2 : list A) i,
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A d l1 l2 i Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi. lia.
Qed.
Lemma combine_app__dot_product_accumulation :
  forall {A B : Type} (l1 l2 : list A) (r1 r2 : list B),
    length l1 = length r1 ->
    combine (l1 ++ l2) (r1 ++ r2) =
      combine l1 r1 ++ combine l2 r2.
Proof.
  intros A B l1.
  induction l1 as [| x xs IH]; intros l2 r1 r2 Hlen.
  - destruct r1; simpl in *; [reflexivity | discriminate].
  - destruct r1 as [| y ys]; simpl in Hlen; [discriminate |].
    simpl. f_equal. apply IH. lia.
Qed.
Lemma fold_right_Zadd_app__dot_product_accumulation :
  forall l1 l2 : list Z,
    fold_right Z.add 0 (l1 ++ l2) =
      fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.
Lemma DotProductPrefix_step__dot_product_accumulation :
  forall xs ys done total,
    done < Zlength xs ->
    DotProductPrefix xs ys done total ->
    DotProductPrefix xs ys (done + 1)
      (total + Znth done xs 0 * Znth done ys 0).
Proof.
  intros xs ys done total Hlt Hprefix.
  unfold DotProductPrefix in *.
  destruct Hprefix as (Hdone & Hlen & Htotal).
  split.
  - lia.
  - split.
    + exact Hlen.
    + unfold DotProduct in *.
      rewrite (sublist_split 0 (done + 1) done xs) by lia.
      rewrite (sublist_single 0 done xs) by lia.
      rewrite (sublist_split 0 (done + 1) done ys) by lia.
      rewrite (sublist_single 0 done ys) by lia.
      rewrite combine_app__dot_product_accumulation.
      2: {
        repeat rewrite sublist_length by lia.
        reflexivity.
      }
      rewrite map_app, fold_right_Zadd_app__dot_product_accumulation.
      simpl.
      rewrite Htotal.
      lia.
Qed.
Lemma set_card_Z_as_sum__final_optimality :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma sum_Z_range_interval_indicator__final_optimality :
  forall low high n (f : Z -> Z),
    0 <= low <= high -> high <= n ->
    SumLib.Sum.sum (fun k => low <= k < high) f =
    SumLib.Sum.sum (fun k => 0 <= k < n)
      (fun k => if prop_dec (low <= k < high) then f k else 0).
Proof.
  intros low high n f Hlow Hhigh.
  symmetry.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 low n) by lia.
  rewrite (SumLib.ZRange.sum_Z_range_split low high n) by lia.
  assert (Hbefore :
    SumLib.Sum.sum (fun k => 0 <= k < low)
      (fun k => if prop_dec (low <= k < high) then f k else 0) = 0).
  {
    apply SumLib.ZRange.sum_Z_range_eq_zero.
    intros k Hk. destruct (prop_dec (low <= k < high)); [lia | reflexivity].
  }
  assert (Hmiddle :
    SumLib.Sum.sum (fun k => low <= k < high)
      (fun k => if prop_dec (low <= k < high) then f k else 0) =
    SumLib.Sum.sum (fun k => low <= k < high) f).
  {
    apply SumLib.ZRange.sum_Z_range_ext.
    intros k Hk. destruct (prop_dec (low <= k < high));
      [reflexivity | contradiction].
  }
  assert (Hafter :
    SumLib.Sum.sum (fun k => high <= k < n)
      (fun k => if prop_dec (low <= k < high) then f k else 0) = 0).
  {
    apply SumLib.ZRange.sum_Z_range_eq_zero.
    intros k Hk. destruct (prop_dec (low <= k < high)); [lia | reflexivity].
  }
  rewrite Hbefore, Hmiddle, Hafter. ring.
Qed.
Lemma fold_sum_zero__final_optimality {A : Type} :
  forall (xs : list A),
    fold_right (fun (_ : A) (acc : Z) => 0 + acc) 0 xs = 0.
Proof.
  induction xs as [|x xs IH]; simpl; auto.
Qed.
Lemma fold_sum_add__final_optimality {A : Type} :
  forall (xs : list A) (f g : A -> Z),
    fold_right (fun x acc => (f x + g x) + acc) 0 xs =
    fold_right (fun x acc => f x + acc) 0 xs +
    fold_right (fun x acc => g x + acc) 0 xs.
Proof.
  induction xs as [|x xs IH]; intros f g; simpl; [ring |].
  rewrite IH. ring.
Qed.
Lemma fold_Zsum_nested_swap__final_optimality :
  forall xs ys (f : Z -> Z -> Z),
    fold_right
      (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc)
      0 xs =
    fold_right
      (fun y acc => fold_right (fun x acc => f x y + acc) 0 xs + acc)
      0 ys.
Proof.
  induction xs as [|x xs IH]; intros ys f; simpl.
  - rewrite fold_sum_zero__final_optimality. reflexivity.
  - rewrite IH.
    rewrite <- fold_sum_add__final_optimality.
    reflexivity.
Qed.
Lemma sum_Z_rect_swap__final_optimality :
  forall x_low x_high y_low y_high f,
    SumLib.Sum.sum (fun x => x_low <= x < x_high)
      (fun x => SumLib.Sum.sum (fun y => y_low <= y < y_high)
                    (fun y => f x y)) =
    SumLib.Sum.sum (fun y => y_low <= y < y_high)
      (fun y => SumLib.Sum.sum (fun x => x_low <= x < x_high)
                    (fun x => f x y)).
Proof.
  intros x_low x_high y_low y_high f.
  unfold SumLib.Sum.sum. simpl.
  apply fold_Zsum_nested_swap__final_optimality.
Qed.
Lemma QueryReplyTotal_as_DotProduct__final_optimality :
  forall arr queries coverage n,
    Zlength arr = n ->
    CoverageProfile queries n coverage ->
    (forall j, 0 <= j < Zlength queries ->
      0 <= fst (Znth j queries (0, 0)) <=
           snd (Znth j queries (0, 0)) /\
      snd (Znth j queries (0, 0)) < n) ->
    QueryReplyTotal arr queries = DotProduct arr coverage.
Proof.
  intros arr queries coverage n Harr [Hcoverage_len Hcoverage] Hqueries.
  unfold QueryReplyTotal, DotProduct.
  change (ListLib.sum
    (map (fun q => ListLib.sum (sublist (fst q) (snd q + 1) arr)) queries) =
    ListLib.sum
      (map (fun pair => fst pair * snd pair) (combine arr coverage))).
  rewrite (SumLib.ZRange.list_sum_map_as_Z_range_sum
    (0, 0) (fun q => ListLib.sum (sublist (fst q) (snd q + 1) arr)) queries).
  rewrite (SumLib.ZRange.list_sum_map_combine_as_Z_range_sum
    0 0 Z.mul arr coverage).
  rewrite Hcoverage_len, <- Harr, Z.min_id.
  transitivity
    (SumLib.Sum.sum (fun j => 0 <= j < Zlength queries)
      (fun j => SumLib.Sum.sum (fun k => 0 <= k < Zlength arr)
        (fun k =>
          if prop_dec
            (fst (Znth j queries (0, 0)) <= k <=
             snd (Znth j queries (0, 0)))
          then Znth k arr 0 else 0))).
  - apply SumLib.ZRange.sum_Z_range_ext.
    intros j Hj.
    specialize (Hqueries j Hj) as [[Hleft Hordered] Hright].
    rewrite (SumLib.ZRange.list_sum_sublist_as_Z_range_sum
      arr (fst (Znth j queries (0, 0)))
      (snd (Znth j queries (0, 0)) + 1)) by lia.
    rewrite (sum_Z_range_interval_indicator__final_optimality
      (fst (Znth j queries (0, 0)))
      (snd (Znth j queries (0, 0)) + 1)
      (Zlength arr) (fun k => Znth k arr 0)) by lia.
    apply SumLib.ZRange.sum_Z_range_ext.
    intros k Hk.
    destruct (prop_dec
      (fst (Znth j queries (0, 0)) <= k <
       snd (Znth j queries (0, 0)) + 1));
    destruct (prop_dec
      (fst (Znth j queries (0, 0)) <= k <=
       snd (Znth j queries (0, 0)))); try lia; reflexivity.
  - rewrite (sum_Z_rect_swap__final_optimality
      0 (Zlength queries) 0 (Zlength arr)).
    apply SumLib.ZRange.sum_Z_range_ext.
    intros k Hk.
    rewrite (Hcoverage k ltac:(lia)).
    unfold QueryCoverage.
    rewrite set_card_Z_as_sum__final_optimality.
    rewrite <- SumLib.ZRange.sum_Z_range_factor_l.
    apply SumLib.ZRange.sum_Z_range_ext.
    intros j Hj.
    destruct (prop_dec
      (fst (Znth j queries (0, 0)) <= k <=
       snd (Znth j queries (0, 0)))); simpl; ring.
Qed.
Lemma increasing_permutation_unique__final_optimality :
  forall (xs ys : list Z),
    ListLib.increasing xs -> ListLib.increasing ys ->
    Permutation xs ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] Hxs Hys Hperm.
  - reflexivity.
  - pose proof (Permutation_nil Hperm). discriminate.
  - pose proof (Permutation_nil (Permutation_sym Hperm)). discriminate.
  - simpl in Hxs, Hys.
    assert (Hy_in : In y (x :: xs)).
    { eapply Permutation_in; [exact (Permutation_sym Hperm) | simpl; auto]. }
    assert (Hx_in : In x (y :: ys)).
    { eapply Permutation_in; [exact Hperm | simpl; auto]. }
    assert (Hxy : x <= y).
    {
      destruct Hy_in as [-> | Hy_in]; [lia |].
      eapply ListLib.increasing_aux_head_le_all_In; eauto.
    }
    assert (Hyx : y <= x).
    {
      destruct Hx_in as [-> | Hx_in]; [lia |].
      eapply ListLib.increasing_aux_head_le_all_In; eauto.
    }
    assert (Heq : x = y) by lia. subst y.
    f_equal.
    apply IH.
    + eapply ListLib.increasing_aux_tail_increasing; eauto.
    + eapply ListLib.increasing_aux_tail_increasing; eauto.
    + eapply Permutation_cons_inv; exact Hperm.
Qed.
Lemma list_insert_head_sorted__final_optimality :
  forall a xs,
    ListLib.increasing_aux xs a ->
    ListLib.list_insert a xs = a :: xs.
Proof.
  intros a [|b xs] Hinc; simpl; [reflexivity |].
  destruct Hinc as [Hab Hinc].
  destruct (Z_le_gt_dec a b); [reflexivity | lia].
Qed.
Lemma DotProduct_insert_pair_le__final_optimality :
  forall (x y : Z) (xs ys : list Z),
    ListLib.increasing xs -> ListLib.increasing ys ->
    Zlength xs = Zlength ys ->
    x * y + DotProduct xs ys <=
    DotProduct (ListLib.list_insert x xs) (ListLib.list_insert y ys).
Proof.
  intros x y xs.
  revert x y.
  induction xs as [|a xs IH]; intros x y [|b ys] Hxs Hys Hlen.
  - unfold DotProduct. simpl. lia.
  - rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - rewrite !Zlength_cons in Hlen. simpl in Hxs, Hys.
    assert (Htail_len : Zlength xs = Zlength ys) by lia.
    assert (Hinc_xs : ListLib.increasing xs).
    { eapply ListLib.increasing_aux_tail_increasing; eauto. }
    assert (Hinc_ys : ListLib.increasing ys).
    { eapply ListLib.increasing_aux_tail_increasing; eauto. }
    unfold DotProduct at 1 2.
    simpl.
    fold (DotProduct xs ys).
    destruct (Z_le_gt_dec x a) as [Hxa | Hax];
    destruct (Z_le_gt_dec y b) as [Hyb | Hby]; simpl.
    + unfold DotProduct. simpl. fold (DotProduct xs ys). nia.
    + specialize (IH a y ys Hinc_xs Hinc_ys Htail_len).
      rewrite (list_insert_head_sorted__final_optimality a xs Hxs) in IH.
      unfold DotProduct in IH at 2.
      simpl in IH.
      fold (DotProduct xs ys) in IH.
      nia.
    + specialize (IH x b ys Hinc_xs Hinc_ys Htail_len).
      rewrite (list_insert_head_sorted__final_optimality b ys Hys) in IH.
      unfold DotProduct in IH at 2.
      simpl in IH.
      fold (DotProduct xs ys) in IH.
      nia.
    + specialize (IH x y ys Hinc_xs Hinc_ys Htail_len).
      eapply Z.le_trans with
        (m := a * b + (x * y + DotProduct xs ys)).
      * replace (x * y + (a * b + DotProduct xs ys)) with
          (a * b + (x * y + DotProduct xs ys)) by ring.
        apply Z.le_refl.
      * apply Z.add_le_mono_l. exact IH.
Qed.
Lemma DotProduct_le_sorted__final_optimality :
  forall (xs ys : list Z),
    Zlength xs = Zlength ys ->
    DotProduct xs ys <= DotProduct (ListLib.sort xs) (ListLib.sort ys).
Proof.
  induction xs as [|x xs IH]; intros [|y ys] Hlen.
  - unfold DotProduct. simpl. lia.
  - rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - rewrite !Zlength_cons in Hlen.
    assert (Htail_len : Zlength xs = Zlength ys) by lia.
    unfold DotProduct at 1. simpl. fold (DotProduct xs ys).
    eapply Z.le_trans with
      (m := x * y + DotProduct (ListLib.sort xs) (ListLib.sort ys)).
    + apply Z.add_le_mono_l. apply IH. exact Htail_len.
    + simpl.
      apply DotProduct_insert_pair_le__final_optimality.
      * apply ListLib.sort_list_increasing.
      * apply ListLib.sort_list_increasing.
      * rewrite !Zlength_correct.
        pose proof (Permutation_length (ListLib.sort_list_perm xs)) as Hsx.
        pose proof (Permutation_length (ListLib.sort_list_perm ys)) as Hsy.
        rewrite <- Hsx, <- Hsy.
        rewrite <- !Zlength_correct. exact Htail_len.
Qed.
Lemma sorted_DotProduct_maximal__final_optimality :
  forall (xs ys xs' ys' : list Z),
    Zlength xs = Zlength ys ->
    ListLib.increasing xs -> ListLib.increasing ys ->
    Permutation xs xs' -> Permutation ys ys' ->
    DotProduct xs' ys' <= DotProduct xs ys.
Proof.
  intros xs ys xs' ys' Hlen Hxs Hys Hpx Hpy.
  assert (Hlen' : Zlength xs' = Zlength ys').
  {
    rewrite !Zlength_correct.
    rewrite <- (Permutation_length Hpx), <- (Permutation_length Hpy).
    rewrite <- !Zlength_correct. exact Hlen.
  }
  eapply Z.le_trans.
  - apply DotProduct_le_sorted__final_optimality. exact Hlen'.
  - assert (Hsortx : ListLib.sort xs' = xs).
    {
      apply increasing_permutation_unique__final_optimality.
      - apply ListLib.sort_list_increasing.
      - exact Hxs.
      - eapply Permutation_trans.
        + apply Permutation_sym. apply ListLib.sort_list_perm.
        + apply Permutation_sym. exact Hpx.
    }
    assert (Hsorty : ListLib.sort ys' = ys).
    {
      apply increasing_permutation_unique__final_optimality.
      - apply ListLib.sort_list_increasing.
      - exact Hys.
      - eapply Permutation_trans.
        + apply Permutation_sym. apply ListLib.sort_list_perm.
        + apply Permutation_sym. exact Hpy.
    }
    rewrite Hsortx, Hsorty. lia.
Qed.
Lemma DotProduct_transport_permutation__final_optimality :
  forall (ys ys' : list Z),
    Permutation ys ys' ->
    forall xs, Zlength xs = Zlength ys ->
    exists xs',
      Permutation xs xs' /\ DotProduct xs ys = DotProduct xs' ys'.
Proof.
  intros ys ys' Hperm.
  induction Hperm; intros xs Hlen.
  - destruct xs as [|a xs].
    + exists nil. split; [constructor | reflexivity].
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg xs). lia.
  - destruct xs as [|a xs].
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg l). lia.
    + rewrite !Zlength_cons in Hlen.
      assert (Htail_len : Zlength xs = Zlength l) by lia.
      destruct (IHHperm xs Htail_len) as [xs' [Hpx Hdot]].
      exists (a :: xs'). split.
      { constructor. exact Hpx. }
      { unfold DotProduct in *. simpl in *. lia. }
  - destruct xs as [|a xs].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct xs as [|b xs].
      * rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
      * rewrite !Zlength_cons in Hlen.
        exists (b :: a :: xs). split.
        { apply perm_swap. }
        { unfold DotProduct. simpl. ring. }
  - destruct (IHHperm1 xs Hlen) as [xs1 [Hpx1 Hdot1]].
    assert (Hlen1 : Zlength xs1 = Zlength l') .
    {
      rewrite !Zlength_correct.
      rewrite <- (Permutation_length Hpx1), <- (Permutation_length Hperm1).
      rewrite <- !Zlength_correct. exact Hlen.
    }
    destruct (IHHperm2 xs1 Hlen1) as [xs2 [Hpx2 Hdot2]].
    exists xs2. split.
    + eapply Permutation_trans; eauto.
    + lia.
Qed.
Lemma DotProductPrefix_complete__final_optimality :
  forall (xs ys : list Z) (done total : Z),
    DotProductPrefix xs ys done total ->
    done = Zlength xs ->
    total = DotProduct xs ys.
Proof.
  intros xs ys done total [Hdone [Hlen Htotal]] Hcomplete.
  subst done.
  rewrite (sublist_self xs (Zlength xs) eq_refl) in Htotal.
  rewrite (sublist_self ys (Zlength xs)) in Htotal by lia.
  exact Htotal.
Qed.
