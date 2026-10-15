Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(n:Z)->list Z. Output is any maximum-length list of
   distinct positive allocations summing to all n candies. *)
Definition CandyAllocation (n : Z) (xs : list Z) : Prop :=
  Forall (fun x => x > 0) xs /\ NoDup xs /\ (fold_right Z.add 0) xs=n.
Definition Pre (n : Z) : Prop :=
  (* Stated explicitly in the P017 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 1000. *)
  True.
Definition Spec (n : Z) (out : list Z) : Prop := max_object_of_subset Z.le (CandyAllocation n) (fun ys => Zlength ys) out.

(** The sum [1 + ... + k].  This is the mathematical quantity tracked by
    the first loop, rather than a model of that loop's control flow. *)
Definition triangular (k : Z) : Z := k * (k + 1) / 2.

(** A concrete prefix [1; 2; ...; i], used while the output buffer is being
    initialized. *)
Definition CandyPrefix (i : Z) (xs : list Z) : Prop :=
  Zlength xs = i /\
  forall j, 0 <= j < i -> Znth j xs 0 = j + 1.

(** The final greedy construction: [1; ...; k-1] followed by the remaining
    candies.  This describes the constructed mathematical list independently
    of the implementation's two loops. *)
Definition GreedyCandyPlan (n k : Z) (xs : list Z) : Prop :=
  Zlength xs = k /\
  (forall j, 0 <= j < k - 1 -> Znth j xs 0 = j + 1) /\
  Znth (k - 1) xs 0 = k + (n - triangular k).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma candy_prefix_last_value__arithmetic_and_prefix :
  forall i xs,
    CandyPrefix i xs ->
    1 <= i ->
    Znth (i - 1) xs 0 = i.
Proof.
  intros i xs [_ Hvalues] Hi.
  specialize (Hvalues (i - 1) ltac:(lia)).
  lia.
Qed.
Lemma candy_prefix_snoc__arithmetic_and_prefix :
  forall i xs,
    CandyPrefix i xs ->
    0 <= i ->
    CandyPrefix (i + 1) (xs ++ [i + 1]).
Proof.
  intros i xs [Hlength Hvalues] Hi.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlength.
    lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j i) as [Hbefore | Hat_end].
    + rewrite app_Znth1.
      * apply Hvalues. lia.
      * rewrite Hlength. lia.
    + assert (j = i) by lia.
      subst j.
      rewrite app_Znth2 by lia.
      rewrite Hlength.
      replace (i - i) with 0 by lia.
      rewrite Znth0_cons.
      lia.
Qed.
Lemma triangular_succ__greedy_finalization : forall k,
  triangular (k + 1) = triangular k + (k + 1).
Proof.
  intros k.
  unfold triangular.
  replace ((k + 1) * (k + 1 + 1))
    with (k * (k + 1) + (k + 1) * 2) by ring.
  rewrite Z.div_add by lia.
  ring.
Qed.
Lemma triangular_monotone_nonneg__greedy_finalization : forall a b,
  0 <= a <= b -> triangular a <= triangular b.
Proof.
  intros a b Hab.
  unfold triangular.
  apply Z.div_le_mono; nia.
Qed.
Lemma sum_range_succ__greedy_finalization : forall k,
  0 <= k ->
  SumLib.Sum.sum (fun i => 0 <= i < k) (fun i => i + 1) = triangular k.
Proof.
  intros k Hk.
  remember (Z.to_nat k) as m.
  assert (k = Z.of_nat m) by lia.
  subst k. clear Heqm Hk.
  induction m as [|m IH].
  - rewrite sum_Z_range_empty by lia. reflexivity.
  - replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
    rewrite sum_Z_range_extend_right by lia.
    rewrite IH, triangular_succ__greedy_finalization.
    ring.
Qed.
Lemma candy_prefix_sum__greedy_finalization : forall k xs,
  0 <= k -> CandyPrefix k xs ->
  fold_right Z.add 0 xs = triangular k.
Proof.
  intros k xs Hk [Hlen Hnth].
  change (ListLib.sum xs = triangular k).
  rewrite list_sum_as_Z_range_sum, Hlen.
  rewrite <- sum_range_succ__greedy_finalization by exact Hk.
  apply sum_Z_range_ext.
  intros i Hi.
  apply Hnth. exact Hi.
Qed.
Lemma sum_replace_Znth__greedy_finalization : forall xs i v,
  0 <= i < Zlength xs ->
  fold_right Z.add 0 (replace_Znth i v xs) =
  fold_right Z.add 0 xs - Znth i xs 0 + v.
Proof.
  induction xs as [|a xs IH]; intros i v Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + unfold replace_Znth, Znth. simpl. ring.
    + assert (0 < i) by lia.
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons by lia.
      simpl.
      rewrite IH by lia.
      ring.
Qed.
Lemma sum_permutation__greedy_finalization : forall xs ys,
  Permutation xs ys ->
  fold_right Z.add 0 xs = fold_right Z.add 0 ys.
Proof.
  intros xs ys Hperm.
  induction Hperm; simpl; nia.
Qed.
Lemma sorted_distinct_sum_lower_general__greedy_finalization : forall b xs,
  ListLib.increasing xs ->
  NoDup xs ->
  Forall (fun x => b <= x) xs ->
  Zlength xs * b + triangular (Zlength xs - 1) <=
  fold_right Z.add 0 xs.
Proof.
  intros b xs. revert b.
  induction xs as [|a xs IH]; intros b Hsorted Hnodup Hlower.
  - simpl. unfold triangular. reflexivity.
  - simpl in Hsorted.
    inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    inversion Hlower as [|? ? Hba Hlower']; subst.
    assert (Htail : Forall (fun x => b + 1 <= x) xs).
    {
      rewrite Forall_forall in *.
      intros x Hinx.
      pose proof (ListLib.increasing_aux_head_le_all_In xs a x Hsorted Hinx) as Hall.
      assert (Hax : a <> x) by (intro; subst; contradiction).
      lia.
    }
    pose proof (ListLib.increasing_aux_tail_increasing xs a Hsorted) as Htail_sorted.
    specialize (IH (b + 1) Htail_sorted Hnodup' Htail).
    pose proof (triangular_succ__greedy_finalization (Zlength xs - 1)) as Htri.
    replace (Zlength xs - 1 + 1) with (Zlength xs) in Htri by ring.
    rewrite Zlength_cons.
    change (Z.succ (Zlength xs) * b +
      triangular (Z.succ (Zlength xs) - 1) <=
      a + fold_right Z.add 0 xs).
    replace (Z.succ (Zlength xs)) with (Zlength xs + 1) by lia.
    replace (Zlength xs + 1 - 1) with (Zlength xs) by ring.
    rewrite Htri.
    nia.
Qed.
Lemma distinct_positive_sum_lower__greedy_finalization : forall xs,
  Forall (fun x => x > 0) xs -> NoDup xs ->
  triangular (Zlength xs) <= fold_right Z.add 0 xs.
Proof.
  intros xs Hpos Hnodup.
  pose proof (ListLib.sort_list_perm xs) as Hperm.
  pose proof (ListLib.sort_list_increasing xs) as Hsorted.
  pose proof (Permutation_NoDup Hperm Hnodup) as Hnodup_sorted.
  assert (Hpos_sorted : Forall (fun x => 1 <= x) (ListLib.sort xs)).
  {
    eapply Permutation_Forall; [exact Hperm |].
    rewrite Forall_forall in *.
    intros x Hinx. specialize (Hpos x Hinx). lia.
  }
  pose proof
    (sorted_distinct_sum_lower_general__greedy_finalization
       1 (ListLib.sort xs) Hsorted Hnodup_sorted Hpos_sorted) as Hbound.
  pose proof (Permutation_length Hperm) as Hlen.
  pose proof (sum_permutation__greedy_finalization _ _ Hperm) as Hsum.
  assert (HZlen : Zlength xs = Zlength (ListLib.sort xs)).
  {
    rewrite !Zlength_correct. lia.
  }
  pose proof (triangular_succ__greedy_finalization (Zlength xs - 1)) as Htri.
  replace (Zlength xs - 1 + 1) with (Zlength xs) in Htri by ring.
  rewrite <- HZlen in Hbound.
  rewrite <- Hsum in Hbound.
  nia.
Qed.
Lemma greedy_candy_plan_spec__greedy_finalization : forall n k used written,
  1 <= k -> used = triangular k -> used <= n ->
  n < used + (k + 1) -> CandyPrefix k written ->
  let out := replace_Znth (k - 1)
    (Znth (k - 1) written 0 + (n - used)) written in
  GreedyCandyPlan n k out /\ Spec n out.
Proof.
  intros n k used written Hk Hused Husedn Hnext Hprefix.
  set (out := replace_Znth (k - 1)
    (Znth (k - 1) written 0 + (n - used)) written).
  destruct Hprefix as [Hwritten_len Hwritten_nth].
  assert (Hidx : 0 <= k - 1 < Zlength written) by lia.
  assert (Hout_len : Zlength out = k).
  {
    unfold out. rewrite ListLib.Zlength_replace_Znth. exact Hwritten_len.
  }
  assert (Hout_prefix : forall j, 0 <= j < k - 1 ->
    Znth j out 0 = j + 1).
  {
    intros j Hj. unfold out.
    rewrite Znth_replace_Znth_Diff; try lia.
    apply Hwritten_nth. lia.
  }
  assert (Hout_last : Znth (k - 1) out 0 = k + (n - triangular k)).
  {
    unfold out.
    rewrite Znth_replace_Znth_Same by exact Hidx.
    rewrite Hwritten_nth by lia.
    lia.
  }
  split.
  - unfold GreedyCandyPlan. auto.
  - unfold Spec, max_object_of_subset.
    split.
    + unfold CandyAllocation.
      split.
      * rewrite Forall_nth.
        intros p d Hp.
        assert (Hpz : 0 <= Z.of_nat p < k).
        {
          rewrite <- Hout_len, Zlength_correct.
          lia.
        }
        assert (Hnth : nth p out d = Znth (Z.of_nat p) out 0).
        {
          unfold Znth. rewrite Nat2Z.id.
          apply nth_indep. exact Hp.
        }
        rewrite Hnth.
        destruct (Z_lt_ge_dec (Z.of_nat p) (k - 1)).
        -- rewrite Hout_prefix by lia. lia.
        -- replace (Z.of_nat p) with (k - 1) by lia.
           rewrite Hout_last. lia.
      * split.
        -- rewrite (NoDup_nth out 0).
           intros p q Hp Hq Heq.
           assert (Hpz : 0 <= Z.of_nat p < k).
           {
             rewrite <- Hout_len, Zlength_correct. lia.
           }
           assert (Hqz : 0 <= Z.of_nat q < k).
           {
             rewrite <- Hout_len, Zlength_correct. lia.
           }
           assert (HeqZ : Znth (Z.of_nat p) out 0 =
             Znth (Z.of_nat q) out 0).
           {
             unfold Znth. rewrite !Nat2Z.id. exact Heq.
           }
           clear Heq. rename HeqZ into Heq.
           destruct (Z_lt_ge_dec (Z.of_nat p) (k - 1));
             destruct (Z_lt_ge_dec (Z.of_nat q) (k - 1)).
           ++ rewrite !Hout_prefix in Heq by lia. lia.
           ++ replace (Z.of_nat q) with (k - 1) in Heq by lia.
              rewrite Hout_prefix in Heq by lia.
              rewrite Hout_last in Heq. lia.
           ++ replace (Z.of_nat p) with (k - 1) in Heq by lia.
              rewrite Hout_last in Heq.
              rewrite Hout_prefix in Heq by lia. lia.
           ++ apply Nat2Z.inj. lia.
        -- unfold out.
           rewrite sum_replace_Znth__greedy_finalization by exact Hidx.
           assert (Hwritten_sum : fold_right Z.add 0 written = triangular k).
           {
             apply candy_prefix_sum__greedy_finalization; [lia|].
             split; assumption.
           }
           rewrite Hwritten_sum.
           lia.
    + intros ys Halloc.
      destruct Halloc as [Hpos [Hnodup Hsum]].
      pose proof (distinct_positive_sum_lower__greedy_finalization ys Hpos Hnodup)
        as Hlower.
      assert (Hyslen : 0 <= Zlength ys) by apply Zlength_nonneg.
      rewrite Hsum in Hlower.
      rewrite Hout_len.
      destruct (Z_le_gt_dec (Zlength ys) k); auto.
      pose proof
        (triangular_monotone_nonneg__greedy_finalization
           (k + 1) (Zlength ys) ltac:(lia)) as Hmono.
      pose proof (triangular_succ__greedy_finalization k) as Htri.
      lia.
Qed.
