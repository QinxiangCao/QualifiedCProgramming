Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Pre (piles queries:list Z) : Prop :=
  (* 1 <= Zlength piles <= 100000 /\ 1 <= Zlength queries <= 100000 /\
  Forall (fun x => 1 <= x <= 1000) piles /\ *)
  Forall (fun q => 1 <= q <= (fold_right Z.add 0) piles) queries.
Definition Spec (piles queries out:list Z) : Prop :=
  Zlength out = Zlength queries /\ forall j,0 <= j < Zlength queries ->
    1 <= Znth j out 0 <= Zlength piles /\
    sum_range 0 (Znth j out 0-2) (fun i => Znth i piles 0) < Znth j queries 0 <=
    sum_range 0 (Znth j out 0-1) (fun i => Znth i piles 0).

(* A mathematical prefix-sum profile.  The first predicate also describes a
   proper prefix while the C construction loop is still filling [pre]. *)
Definition PrefixSumsPrefix (piles prefix : list Z) : Prop :=
  1 <= Zlength prefix <= Zlength piles + 1 /\
  forall i, 0 <= i < Zlength prefix ->
    Znth i prefix 0 =
      sum_range 0 (i - 1) (fun k => Znth k piles 0).

Definition PrefixSums (piles prefix : list Z) : Prop :=
  Zlength prefix = Zlength piles + 1 /\
  forall i, 0 <= i <= Zlength piles ->
    Znth i prefix 0 =
      sum_range 0 (i - 1) (fun k => Znth k piles 0).

(* [r] is the one-based pile containing worm label [q]. *)
Definition PileIndex (piles : list Z) (q r : Z) : Prop :=
  1 <= r <= Zlength piles /\
  sum_range 0 (r - 2) (fun i => Znth i piles 0) < q <=
  sum_range 0 (r - 1) (fun i => Znth i piles 0).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma sum_range_upper_bound__prefix_step :
  forall (piles : list Z) n i,
    n = Zlength piles ->
    0 <= i < n ->
    (forall k, 0 <= k < n -> 1 <= Znth k piles 0 <= 1000) ->
    0 <= sum_range 0 i (fun k => Znth k piles 0) <= 1000 * (i + 1).
Proof.
  intros piles n i Hlen Hi Hbounds.
  unfold sum_range.
  pose proof
    (sum_Z_range_bounds 0 (i + 1) (fun k => Znth k piles 0) 0 1000
       ltac:(lia) ltac:(intros k Hk; specialize (Hbounds k ltac:(lia)); lia))
    as Hsum.
  lia.
Qed.
Lemma sum_range_succ__prefix_step :
  forall i (f : Z -> Z),
    0 <= i ->
    sum_range 0 i f = sum_range 0 (i - 1) f + f i.
Proof.
  intros i f Hi.
  unfold sum_range.
  replace (i - 1 + 1) with i by lia.
  rewrite sum_Z_range_extend_right by lia.
  reflexivity.
Qed.
Lemma prefix_sums_extend__prefix_step :
  forall (piles prefix : list Z) i,
    Zlength prefix = i + 1 ->
    0 <= i < Zlength piles ->
    PrefixSumsPrefix piles prefix ->
    PrefixSumsPrefix piles
      (prefix ++ [Znth i prefix 0 + Znth i piles 0]).
Proof.
  intros piles prefix i Hlen Hi Hprefix.
  unfold PrefixSumsPrefix in *.
  destruct Hprefix as [[Hprefix_nonempty Hprefix_bound] Hvalues].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros j Hj.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hj.
    destruct (Z_lt_ge_dec j (Zlength prefix)) as [Hjold | Hjlast].
    + rewrite app_Znth1 by lia.
      apply Hvalues.
      lia.
    + assert (j = i + 1) by lia.
      subst j.
      rewrite app_Znth2 by lia.
      replace (i + 1 - Zlength prefix) with 0 by lia.
      simpl.
      rewrite Hvalues with (i := i) by lia.
      unfold sum_range.
      replace (i - 1 + 1) with i by lia.
      replace (i + 1 - 1 + 1) with (i + 1) by lia.
      rewrite sum_Z_range_extend_right by lia.
      reflexivity.
Qed.
Lemma replace_Znth_app_last__prefix_step :
  forall (prefix : list Z) old value,
    replace_Znth (Zlength prefix) value (prefix ++ [old]) =
    prefix ++ [value].
Proof.
  intros prefix old value.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (Zlength prefix - Zlength prefix) with 0 by lia.
  reflexivity.
Qed.
Lemma prefix_sums_prefix_complete__prefix_exit :
  forall (piles prefix : list Z),
    Zlength prefix = Zlength piles + 1 ->
    PrefixSumsPrefix piles prefix ->
    PrefixSums piles prefix.
Proof.
  intros piles prefix Hlen Hprefix.
  destruct Hprefix as [_ Hvalues].
  unfold PrefixSums.
  split; [exact Hlen |].
  intros i Hi.
  apply Hvalues.
  lia.
Qed.
Lemma query_bound_by_prefix_total__query_step :
  forall piles queries prefix n i,
    Pre piles queries ->
    n = Zlength piles ->
    0 <= n ->
    0 <= i < Zlength queries ->
    PrefixSums piles prefix ->
    Znth i queries 0 <= Znth n prefix 0.
Proof.
  intros piles queries prefix n i Hpre Hn Hn_nonneg Hi Hprefix.
  subst n.
  unfold Pre in Hpre.
  pose proof
    ((proj1 (Forall_Znth
       (fun q => 1 <= q <= fold_right Z.add 0 piles)
       0 queries)) Hpre i Hi) as Hquery.
  unfold PrefixSums in Hprefix.
  destruct Hprefix as [_ Hprefix].
  specialize (Hprefix (Zlength piles) ltac:(lia)).
  pose proof (list_sum_as_Z_range_sum piles) as Hsum.
  unfold ListLib.sum in Hsum.
  unfold sum_range in Hprefix.
  replace (Zlength piles - 1 + 1) with (Zlength piles) in Hprefix by lia.
  rewrite <- Hsum in Hprefix.
  rewrite Hprefix.
  exact (proj2 Hquery).
Qed.
Lemma Znth_app_left__query_step :
  forall (l1 l2 : list Z) (d i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma Znth_app_last__query_step :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma PileIndex_app_single__query_step :
  forall piles queries result i retval,
    Zlength result = i ->
    (forall j, 0 <= j < i ->
      PileIndex piles (Znth j queries 0) (Znth j result 0)) ->
    PileIndex piles (Znth i queries 0) retval ->
    forall j, 0 <= j < i + 1 ->
      PileIndex piles (Znth j queries 0)
        (Znth j (result ++ retval :: nil) 0).
Proof.
  intros piles queries result i retval Hlen Hprefix Hcurrent j Hj.
  destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
  - rewrite Znth_app_left__query_step by lia.
    apply Hprefix; lia.
  - assert (j = i) by lia.
    subst j.
    assert (Hlast : Znth i (result ++ retval :: nil) 0 = retval).
    {
      rewrite <- Hlen.
      apply Znth_app_last__query_step.
    }
    rewrite Hlast.
    exact Hcurrent.
Qed.
