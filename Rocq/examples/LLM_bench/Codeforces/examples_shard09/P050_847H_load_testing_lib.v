Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Mountain (a : list Z) : Prop :=
  exists peak, 0 <= peak < Zlength a /\
    (forall i, 0 <= i < peak -> Znth i a 0 < Znth (i + 1) a 0) /\
    (forall i, peak <= i < Zlength a - 1 -> Znth i a 0 > Znth (i + 1) a 0).
Definition AddedLoad (a : list Z) (cost : Z) : Prop :=
  exists b, Zlength b = Zlength a /\
    (forall i, 0 <= i < Zlength a -> Znth i a 0 <= Znth i b 0) /\ Mountain b /\
    cost = (fold_right Z.add 0) b - (fold_right Z.add 0) a.
Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P050 solver Require, so dropped here:
       1 <= Zlength a <= 100000 /\
       Forall (fun x => 1 <= x <= 1000000000) a  *)
  True.

Definition Spec (a : list Z) (out : Z) : Prop := min_value_of_subset Z.le (AddedLoad a) (fun x => x) out.

(* The pointwise least strictly increasing profile above an input prefix. *)
Definition LeftProfilePrefix (a p : list Z) : Prop :=
  1 <= Zlength p <= Zlength a /\
  (forall i, 0 <= i < Zlength p -> Znth i a 0 <= Znth i p 0) /\
  (forall i, 0 <= i < Zlength p - 1 ->
     Znth i p 0 < Znth (i + 1) p 0) /\
  forall q,
    Zlength q = Zlength p ->
    (forall i, 0 <= i < Zlength q -> Znth i a 0 <= Znth i q 0) ->
    (forall i, 0 <= i < Zlength q - 1 ->
       Znth i q 0 < Znth (i + 1) q 0) ->
    forall i, 0 <= i < Zlength p -> Znth i p 0 <= Znth i q 0.

(* The pointwise least strictly decreasing profile above an input suffix.
   [p] corresponds to [sublist (Zlength a - Zlength p) (Zlength a) a]. *)
Definition RightProfileSuffix (a p : list Z) : Prop :=
  1 <= Zlength p <= Zlength a /\
  (forall j, 0 <= j < Zlength p ->
     Znth (Zlength a - Zlength p + j) a 0 <= Znth j p 0) /\
  (forall j, 0 <= j < Zlength p - 1 ->
     Znth j p 0 > Znth (j + 1) p 0) /\
  forall q,
    Zlength q = Zlength p ->
    (forall j, 0 <= j < Zlength q ->
       Znth (Zlength a - Zlength q + j) a 0 <= Znth j q 0) ->
    (forall j, 0 <= j < Zlength q - 1 ->
       Znth j q 0 > Znth (j + 1) q 0) ->
    forall j, 0 <= j < Zlength p -> Znth j p 0 <= Znth j q 0.

(* Cumulative added load for a completed left profile prefix. *)
Definition PrefixCosts (a inc pre : list Z) : Prop :=
  Zlength pre = Zlength inc /\ Zlength inc <= Zlength a /\
  forall i, 0 <= i < Zlength pre ->
    Znth i pre 0 =
      sum_range 0 i (fun k => Znth k inc 0 - Znth k a 0).

(* Cumulative added load for a completed right profile suffix.  Both lists
   use suffix-relative indexing. *)
Definition SuffixCosts (a dec suf : list Z) : Prop :=
  Zlength suf = Zlength dec /\ Zlength dec <= Zlength a /\
  forall j, 0 <= j < Zlength suf ->
    Znth j suf 0 =
      sum_range j (Zlength suf - 1)
        (fun k =>
           Znth k dec 0 -
           Znth (Zlength a - Zlength suf + k) a 0).

Definition PeakCostValue
    (a inc dec pre suf : list Z) (i : Z) : Z :=
  Znth i pre 0 + Znth i suf 0 - (Znth i inc 0 - Znth i a 0) -
  (Znth i dec 0 - Znth i a 0) +
  (Z.max (Znth i inc 0) (Znth i dec 0) - Znth i a 0).

(* [best] is the least candidate cost among peaks in [0, upto).  The sentinel
   -1 is used only for the empty prefix, exactly as in the C code. *)
Definition BestPeakPrefix
    (a inc dec pre suf : list Z) (upto best : Z) : Prop :=
  (upto = 0 /\ best = -1) \/
  (0 < upto /\ upto <= Zlength a /\
   exists peak,
     0 <= peak < upto /\
     best = PeakCostValue a inc dec pre suf peak /\
     forall j, 0 <= j < upto ->
       best <= PeakCostValue a inc dec pre suf j).

(* Cumulative costs for the portion of [pre] written so far.  The increasing
   profile may already be complete, so its length need only bound [pre]. *)
Definition PartialPrefixCosts (a inc pre : list Z) : Prop :=
  Zlength pre <= Zlength inc /\ Zlength inc <= Zlength a /\
  forall i, 0 <= i < Zlength pre ->
    Znth i pre 0 =
      sum_range 0 i (fun k => Znth k inc 0 - Znth k a 0).

(* Cumulative costs for the written suffix of a complete decreasing profile.
   Both [dec] and [a] are addressed using the suffix offset determined by the
   current length of [suf]. *)
Definition PartialSuffixCosts (a dec suf : list Z) : Prop :=
  Zlength suf <= Zlength dec /\ Zlength dec <= Zlength a /\
  forall j, 0 <= j < Zlength suf ->
    Znth j suf 0 =
      sum_range j (Zlength suf - 1)
        (fun k =>
           Znth (Zlength dec - Zlength suf + k) dec 0 -
           Znth (Zlength a - Zlength suf + k) a 0).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma left_profile_singleton__left_profile :
  forall a,
    1 <= Zlength a ->
    LeftProfilePrefix a [Znth 0 a 0].
Proof.
  intros a Ha.
  unfold LeftProfilePrefix.
  repeat split.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - intros j Hj.
    rewrite Zlength_cons, Zlength_nil in Hj.
    assert (j = 0) by lia. subst j.
    rewrite Znth0_cons. lia.
  - intros j Hj.
    rewrite Zlength_cons, Zlength_nil in Hj. lia.
  - intros q Hqlen Hqa Hqinc j Hj.
    rewrite Zlength_cons, Zlength_nil in Hj.
    assert (j = 0) by lia. subst j.
    rewrite Znth0_cons.
    apply Hqa. rewrite Hqlen, Zlength_cons, Zlength_nil. lia.
Qed.
Lemma left_profile_snoc_input__left_profile :
  forall a p i,
    LeftProfilePrefix a p ->
    Zlength p = i ->
    1 <= i < Zlength a ->
    Znth i a 0 > Znth (i - 1) p 0 + 1 ->
    LeftProfilePrefix a (p ++ [Znth i a 0]).
Proof.
  intros a p i Hprof Hplen Hirange Hnext.
  unfold LeftProfilePrefix in Hprof |- *.
  destruct Hprof as (Hlen & Hdom & Hinc & Hmin).
  destruct Hlen as [Hlo Hhi].
  rewrite Zlength_app_cons.
  repeat split.
  - lia.
  - lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + rewrite app_Znth1 by lia. apply Hdom. lia.
    + assert (j = i) by lia. subst j.
      rewrite app_Znth2 by lia.
      rewrite Hplen, Z.sub_diag, Znth0_cons. lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j (i - 1)) as [Hjold | Hjlast].
    + rewrite app_Znth1 by lia.
      rewrite app_Znth1 by lia.
      apply Hinc. lia.
    + assert (j = i - 1) by lia. subst j.
      rewrite app_Znth1 by lia.
      replace (i - 1 + 1) with i by lia.
      rewrite app_Znth2 by lia.
      rewrite Hplen, Z.sub_diag, Znth0_cons. lia.
  - intros q Hqlen Hqdom Hqinc j Hj.
    assert (Hprefix : forall k, 0 <= k < i -> Znth k p 0 <= Znth k q 0).
    { intros k Hk.
      specialize (Hmin (sublist 0 i q)).
      assert (Hsub_len : Zlength (sublist 0 i q) = i).
      { apply Zlength_sublist0. rewrite Hqlen. lia. }
      specialize (Hmin ltac:(lia)).
      specialize (Hmin ltac:(
        intros x Hx;
        rewrite Znth_sublist0 by lia;
        apply Hqdom;
        rewrite Hqlen;
        lia)).
      specialize (Hmin ltac:(
        intros x Hx;
        rewrite Znth_sublist0 by lia;
        rewrite Znth_sublist0 by lia;
        apply Hqinc;
        rewrite Hqlen;
        lia)).
      specialize (Hmin k ltac:(lia)).
      rewrite Znth_sublist0 in Hmin by lia.
      exact Hmin. }
    destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + rewrite app_Znth1 by lia. apply Hprefix. lia.
    + assert (j = i) by lia. subst j.
      rewrite app_Znth2 by lia.
      rewrite Hplen, Z.sub_diag, Znth0_cons.
      apply Hqdom. rewrite Hqlen. lia.
Qed.
Lemma left_profile_snoc_successor__left_profile :
  forall a p i,
    LeftProfilePrefix a p ->
    Zlength p = i ->
    1 <= i < Zlength a ->
    Znth i a 0 <= Znth (i - 1) p 0 + 1 ->
    LeftProfilePrefix a (p ++ [Znth (i - 1) p 0 + 1]).
Proof.
  intros a p i Hprof Hplen Hirange Hnext.
  unfold LeftProfilePrefix in Hprof |- *.
  destruct Hprof as (Hlen & Hdom & Hinc & Hmin).
  destruct Hlen as [Hlo Hhi].
  rewrite Zlength_app_cons.
  repeat split.
  - lia.
  - lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + rewrite app_Znth1 by lia. apply Hdom. lia.
    + assert (j = i) by lia. subst j.
      rewrite app_Znth2 by lia.
      rewrite Hplen, Z.sub_diag, Znth0_cons. lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j (i - 1)) as [Hjold | Hjlast].
    + rewrite app_Znth1 by lia.
      rewrite app_Znth1 by lia.
      apply Hinc. lia.
    + assert (j = i - 1) by lia. subst j.
      rewrite app_Znth1 by lia.
      replace (i - 1 + 1) with i by lia.
      rewrite app_Znth2 by lia.
      rewrite Hplen, Z.sub_diag, Znth0_cons. lia.
  - intros q Hqlen Hqdom Hqinc j Hj.
    assert (Hprefix : forall k, 0 <= k < i -> Znth k p 0 <= Znth k q 0).
    { intros k Hk.
      specialize (Hmin (sublist 0 i q)).
      assert (Hsub_len : Zlength (sublist 0 i q) = i).
      { apply Zlength_sublist0. rewrite Hqlen. lia. }
      specialize (Hmin ltac:(lia)).
      specialize (Hmin ltac:(
        intros x Hx;
        rewrite Znth_sublist0 by lia;
        apply Hqdom;
        rewrite Hqlen;
        lia)).
      specialize (Hmin ltac:(
        intros x Hx;
        rewrite Znth_sublist0 by lia;
        rewrite Znth_sublist0 by lia;
        apply Hqinc;
        rewrite Hqlen;
        lia)).
      specialize (Hmin k ltac:(lia)).
      rewrite Znth_sublist0 in Hmin by lia.
      exact Hmin. }
    destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + rewrite app_Znth1 by lia. apply Hprefix. lia.
    + assert (j = i) by lia. subst j.
      rewrite app_Znth2 by lia.
      rewrite Hplen, Z.sub_diag, Znth0_cons.
      specialize (Hprefix (i - 1) ltac:(lia)).
      specialize (Hqinc (i - 1) ltac:(rewrite Hqlen, Hplen; lia)).
      replace (i - 1 + 1) with i in Hqinc by lia.
      lia.
Qed.
Lemma Zlength_Zrange_aux__final_result :
  forall low m, Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low.
  induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__final_result :
  forall low high, low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hrange. unfold Zrange.
  rewrite Zlength_Zrange_aux__final_result. lia.
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
Lemma Znth_Zrange__final_result :
  forall low high i,
    low <= high -> 0 <= i < high - low ->
    Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hrange Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__final_result by lia. lia.
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
Lemma right_profile_singleton__right_profile : forall a,
  1 <= Zlength a ->
  RightProfileSuffix a [Znth (Zlength a - 1) a 0].
Proof.
  intros a Ha.
  unfold RightProfileSuffix.
  rewrite !Zlength_cons, !Zlength_nil.
  split.
  - constructor; lia.
  - split.
    + intros j Hj.
      replace j with 0 by lia.
      rewrite Znth0_cons.
      replace (Zlength a - Z.succ 0 + 0) with (Zlength a - 1) by lia.
      reflexivity.
    + split.
      * intros j Hj.
        lia.
      * intros q Hq_len Hq_dom Hq_dec j Hj.
        replace j with 0 by lia.
        rewrite Znth0_cons.
        specialize (Hq_dom 0 ltac:(lia)).
        rewrite Hq_len in Hq_dom.
        replace (Zlength a - Z.succ 0 + 0) with (Zlength a - 1) in Hq_dom by lia.
        lia.
Qed.
Lemma right_profile_cons_input__right_profile : forall a p i,
  0 <= i < Zlength a ->
  Zlength p = Zlength a - i - 1 ->
  RightProfileSuffix a p ->
  Znth i a 0 > Znth 0 p 0 + 1 ->
  RightProfileSuffix a (Znth i a 0 :: p).
Proof.
  intros a p i Hi Hp_len Hp Hguard.
  unfold RightProfileSuffix in *.
  destruct Hp as [[Hp_nonempty Hp_fits] [Hp_dom [Hp_dec Hp_min]]].
  rewrite !Zlength_cons.
  split; [constructor; lia |].
  split.
  - intros j Hj.
    destruct (Z.eq_dec j 0) as [-> | Hj0].
    + rewrite Znth0_cons.
      replace (Zlength a - Z.succ (Zlength p) + 0) with i by lia.
      lia.
    + rewrite Znth_cons by lia.
      specialize (Hp_dom (j - 1) ltac:(simpl in Hj; lia)).
      replace (Zlength a - Z.succ (Zlength p) + j)
        with (Zlength a - Zlength p + (j - 1)) by lia.
      exact Hp_dom.
  - split.
    + intros j Hj.
      destruct (Z.eq_dec j 0) as [-> | Hj0].
      * rewrite Znth0_cons.
        rewrite Znth_cons by lia.
        change (Znth i a 0 > Znth 0 p 0).
        lia.
      * rewrite Znth_cons by lia.
        rewrite Znth_cons by lia.
        replace (j + 1 - 1) with ((j - 1) + 1) by lia.
        apply Hp_dec.
        simpl in Hj.
        lia.
    + intros q Hq_len Hq_dom Hq_dec j Hj.
      destruct q as [| qh qt].
      * rewrite Zlength_nil in Hq_len. lia.
      * rewrite Zlength_cons in Hq_len, Hq_dom, Hq_dec.
        destruct (Z.eq_dec j 0) as [-> | Hj0].
        -- rewrite Znth0_cons.
           specialize (Hq_dom 0 ltac:(simpl; lia)).
           rewrite Znth0_cons in Hq_dom.
           replace (Zlength a - Z.succ (Zlength qt) + 0) with i in Hq_dom by lia.
           exact Hq_dom.
        -- rewrite Znth_cons by lia.
           rewrite Znth_cons by lia.
           apply (Hp_min qt).
           ++ lia.
           ++ intros k Hk.
              specialize (Hq_dom (k + 1) ltac:(simpl; lia)).
              rewrite Znth_cons in Hq_dom by lia.
              replace (k + 1 - 1) with k in Hq_dom by lia.
              replace (Zlength a - Zlength qt + k)
                with (Zlength a - Z.succ (Zlength qt) + (k + 1)) by lia.
              exact Hq_dom.
           ++ intros k Hk.
              specialize (Hq_dec (k + 1) ltac:(simpl; lia)).
              rewrite Znth_cons in Hq_dec by lia.
              rewrite Znth_cons in Hq_dec by lia.
              replace (k + 1 - 1) with k in Hq_dec by lia.
              replace (k + 1 + 1 - 1) with (k + 1) in Hq_dec by lia.
              exact Hq_dec.
           ++ simpl in Hj. lia.
Qed.
Lemma right_profile_cons_successor__right_profile : forall a p i,
  0 <= i < Zlength a ->
  Zlength p = Zlength a - i - 1 ->
  RightProfileSuffix a p ->
  Znth i a 0 <= Znth 0 p 0 + 1 ->
  RightProfileSuffix a (Znth 0 p 0 + 1 :: p).
Proof.
  intros a p i Hi Hp_len Hp Hguard.
  unfold RightProfileSuffix in *.
  destruct Hp as [[Hp_nonempty Hp_fits] [Hp_dom [Hp_dec Hp_min]]].
  rewrite !Zlength_cons.
  split; [constructor; lia |].
  split.
  - intros j Hj.
    destruct (Z.eq_dec j 0) as [-> | Hj0].
    + rewrite Znth0_cons.
      replace (Zlength a - Z.succ (Zlength p) + 0) with i by lia.
      lia.
    + rewrite Znth_cons by lia.
      specialize (Hp_dom (j - 1) ltac:(simpl in Hj; lia)).
      replace (Zlength a - Z.succ (Zlength p) + j)
        with (Zlength a - Zlength p + (j - 1)) by lia.
      exact Hp_dom.
  - split.
    + intros j Hj.
      destruct (Z.eq_dec j 0) as [-> | Hj0].
      * rewrite Znth0_cons.
        rewrite Znth_cons by lia.
        change (Znth 0 p 0 + 1 > Znth 0 p 0).
        lia.
      * rewrite Znth_cons by lia.
        rewrite Znth_cons by lia.
        replace (j + 1 - 1) with ((j - 1) + 1) by lia.
        apply Hp_dec.
        simpl in Hj.
        lia.
    + intros q Hq_len Hq_dom Hq_dec j Hj.
      destruct q as [| qh qt].
      * rewrite Zlength_nil in Hq_len. lia.
      * rewrite Zlength_cons in Hq_len, Hq_dom, Hq_dec.
        assert (Hqt_len : Zlength qt = Zlength p) by lia.
        assert (Hqt_dom : forall k, 0 <= k < Zlength qt ->
            Znth (Zlength a - Zlength qt + k) a 0 <= Znth k qt 0).
        { intros k Hk.
          specialize (Hq_dom (k + 1) ltac:(simpl; lia)).
          rewrite Znth_cons in Hq_dom by lia.
          replace (k + 1 - 1) with k in Hq_dom by lia.
          replace (Zlength a - Zlength qt + k)
            with (Zlength a - Z.succ (Zlength qt) + (k + 1)) by lia.
          exact Hq_dom. }
        assert (Hqt_dec : forall k, 0 <= k < Zlength qt - 1 ->
            Znth k qt 0 > Znth (k + 1) qt 0).
        { intros k Hk.
          specialize (Hq_dec (k + 1) ltac:(simpl; lia)).
          rewrite Znth_cons in Hq_dec by lia.
          rewrite Znth_cons in Hq_dec by lia.
          replace (k + 1 - 1) with k in Hq_dec by lia.
          replace (k + 1 + 1 - 1) with (k + 1) in Hq_dec by lia.
          exact Hq_dec. }
        destruct (Z.eq_dec j 0) as [-> | Hj0].
        -- rewrite Znth0_cons.
           rewrite Znth0_cons.
           specialize (Hp_min qt Hqt_len Hqt_dom Hqt_dec 0 ltac:(lia)).
           specialize (Hq_dec 0 ltac:(simpl; lia)).
           rewrite Znth0_cons in Hq_dec.
           rewrite Znth_cons in Hq_dec by lia.
           change (qh > Znth 0 qt 0) in Hq_dec.
           lia.
        -- rewrite Znth_cons by lia.
           rewrite Znth_cons by lia.
           apply (Hp_min qt Hqt_len Hqt_dom Hqt_dec).
           simpl in Hj.
           lia.
Qed.
Lemma right_profile_head_upper_bound__right_profile : forall a p,
  Zlength a <= 100000 ->
  (forall k, 0 <= k < Zlength a -> Znth k a 0 <= 1000000000) ->
  RightProfileSuffix a p ->
  Znth 0 p 0 + 1 <= 1000100000.
Proof.
  intros a p Ha_len Ha_bound Hp.
  unfold RightProfileSuffix in Hp.
  destruct Hp as [[Hp_pos Hp_len] [Hp_dom [Hp_dec Hp_min]]].
  set (q := map
    (fun j => 1000000000 + (Zlength p - 1 - j))
    (Zrange 0 (Zlength p))).
  assert (Hq_len : Zlength q = Zlength p).
  {
    unfold q.
    rewrite Zlength_map__final_result, Zlength_Zrange__final_result; lia.
  }
  assert (Hq_nth : forall j, 0 <= j < Zlength p ->
      Znth j q 0 = 1000000000 + (Zlength p - 1 - j)).
  {
    intros j Hj.
    unfold q.
    rewrite (@Znth_map__final_result Z Z
      (fun k => 1000000000 + (Zlength p - 1 - k))
      (Zrange 0 (Zlength p)) 0 0 j).
    - rewrite Znth_Zrange__final_result by lia. lia.
    - rewrite Zlength_Zrange__final_result; lia.
  }
  assert (Hq_dom : forall j, 0 <= j < Zlength q ->
      Znth (Zlength a - Zlength q + j) a 0 <= Znth j q 0).
  {
    intros j Hj.
    rewrite Hq_len in Hj |- *.
    rewrite Hq_nth by exact Hj.
    specialize (Ha_bound (Zlength a - Zlength p + j) ltac:(lia)).
    lia.
  }
  assert (Hq_dec : forall j, 0 <= j < Zlength q - 1 ->
      Znth j q 0 > Znth (j + 1) q 0).
  {
    intros j Hj.
    rewrite Hq_len in Hj.
    rewrite !Hq_nth by lia.
    lia.
  }
  specialize (Hp_min q Hq_len Hq_dom Hq_dec 0 ltac:(lia)).
  rewrite Hq_nth in Hp_min by lia.
  lia.
Qed.
Lemma partial_prefix_costs_singleton__prefix_costs :
  forall a inc,
    1 <= Zlength inc ->
    Zlength inc <= Zlength a ->
    PartialPrefixCosts a inc [Znth 0 inc 0 - Znth 0 a 0].
Proof.
  intros a inc Hnonempty Hfits.
  unfold PartialPrefixCosts.
  repeat split.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - exact Hfits.
  - intros i Hi.
    rewrite Zlength_cons, Zlength_nil in Hi.
    assert (i = 0) by lia. subst i.
    rewrite Znth0_cons.
    unfold sum_range.
    rewrite sum_Z_range_single.
    reflexivity.
Qed.
Lemma partial_prefix_costs_snoc__prefix_costs :
  forall a inc pre i,
    PartialPrefixCosts a inc pre ->
    Zlength pre = i ->
    1 <= i < Zlength inc ->
    PartialPrefixCosts a inc
      (pre ++ [Znth (i - 1) pre 0 +
        (Znth i inc 0 - Znth i a 0)]).
Proof.
  intros a inc pre i Hpartial Hlen Hirange.
  unfold PartialPrefixCosts in Hpartial |- *.
  destruct Hpartial as [Hpre_inc [Hinc_a Hcost]].
  rewrite Zlength_app_cons.
  repeat split.
  - lia.
  - exact Hinc_a.
  - intros j Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + rewrite app_Znth1 by lia.
      apply Hcost. lia.
    + assert (j = i) by lia. subst j.
      rewrite app_Znth2 by lia.
      rewrite Hlen, Z.sub_diag, Znth0_cons.
      specialize (Hcost (i - 1) ltac:(lia)).
      unfold sum_range in Hcost |- *.
      rewrite sum_Z_range_extend_right by lia.
      replace (i - 1 + 1) with i in Hcost by lia.
      exact (f_equal
        (fun x => x + (Znth i inc 0 - Znth i a 0)) Hcost).
Qed.
Lemma partial_prefix_costs_full__prefix_costs :
  forall a inc pre,
    PartialPrefixCosts a inc pre ->
    Zlength pre = Zlength inc ->
    PrefixCosts a inc pre.
Proof.
  intros a inc pre Hpartial Hlen.
  unfold PartialPrefixCosts in Hpartial.
  unfold PrefixCosts.
  destruct Hpartial as [_ [Hfits Hcost]].
  repeat split; assumption.
Qed.
Lemma partial_suffix_costs_singleton__suffix_costs :
  forall a dec,
    1 <= Zlength a ->
    Zlength dec = Zlength a ->
    PartialSuffixCosts a dec
      [Znth (Zlength a - 1) dec 0 - Znth (Zlength a - 1) a 0].
Proof.
  intros a dec Ha Hdec.
  unfold PartialSuffixCosts.
  rewrite !Zlength_cons, Zlength_nil.
  repeat split.
  - lia.
  - lia.
  - intros j Hj.
    assert (j = 0) by lia. subst j.
    rewrite Znth0_cons.
    unfold sum_range.
    rewrite sum_Z_range_single.
    replace (Z.succ 0 - 1) with 0 by lia.
    replace (Zlength dec - Z.succ 0 + 0) with (Zlength a - 1) by lia.
    replace (Zlength a - Z.succ 0 + 0) with (Zlength a - 1) by lia.
    reflexivity.
Qed.
Lemma partial_suffix_costs_cons__suffix_costs :
  forall a dec suf i,
    0 <= i < Zlength dec - 1 ->
    Zlength dec = Zlength a ->
    Zlength suf = Zlength dec - i - 1 ->
    PartialSuffixCosts a dec suf ->
    PartialSuffixCosts a dec
      ((Znth 0 suf 0 + (Znth i dec 0 - Znth i a 0)) :: suf).
Proof.
  intros a dec suf i Hi Hdec Hsuf Hpartial.
  unfold PartialSuffixCosts in Hpartial |- *.
  destruct Hpartial as [Hfits [Hdec_a Hcost]].
  rewrite Zlength_cons.
  repeat split.
  - lia.
  - exact Hdec_a.
  - intros j Hj.
    destruct (Z.eq_dec j 0) as [-> | Hj0].
    + rewrite Znth0_cons.
      specialize (Hcost 0 ltac:(rewrite Hsuf; lia)).
      unfold sum_range in Hcost |- *.
      replace (Zlength suf - 1 + 1) with (Zlength suf) in Hcost by lia.
      replace (Z.succ (Zlength suf) - 1 + 1)
        with (Zlength suf + 1) by lia.
      replace (Zlength dec - Z.succ (Zlength suf)) with i by lia.
      replace (Zlength a - Z.succ (Zlength suf)) with i by lia.
      rewrite sum_Z_range_cons by lia.
      replace (0 + 1) with 1 by lia.
      assert (Htail :
        sum (fun x => 1 <= x < Zlength suf + 1)
          (fun k => Znth (i + k) dec 0 - Znth (i + k) a 0) =
        Znth 0 suf 0).
      {
        change
          (sum (fun x => 0 + 1 <= x < Zlength suf + 1)
             (fun k => Znth (i + k) dec 0 - Znth (i + k) a 0) =
           Znth 0 suf 0).
        rewrite sum_Z_range_shift_1.
        rewrite Hcost.
        apply sum_Z_range_ext.
        intros k Hk.
        replace (Zlength a) with (Zlength dec) by lia.
        replace (i + (k + 1)) with
          (Zlength dec - Zlength suf + k) by lia.
        reflexivity.
      }
      rewrite Htail.
      replace (i + 0) with i by lia.
      lia.
    + rewrite Znth_cons by lia.
      specialize (Hcost (j - 1) ltac:(rewrite Hsuf; simpl in Hj; lia)).
      unfold sum_range in Hcost |- *.
      replace (Zlength suf - 1 + 1) with (Zlength suf) in Hcost by lia.
      replace (Z.succ (Zlength suf) - 1 + 1)
        with (Zlength suf + 1) by lia.
      replace (Zlength dec - Z.succ (Zlength suf)) with i by lia.
      replace (Zlength a - Z.succ (Zlength suf)) with i by lia.
      replace j with ((j - 1) + 1) by lia.
      change
        (Znth ((j - 1) + 1 - 1) suf 0 =
         sum (fun x => (j - 1) + 1 <= x < Zlength suf + 1)
           (fun k => Znth (i + k) dec 0 - Znth (i + k) a 0)).
      replace ((j - 1) + 1 - 1) with (j - 1) by lia.
      rewrite sum_Z_range_shift_1.
      rewrite Hcost.
      apply sum_Z_range_ext.
      intros k Hk.
      replace (Zlength a) with (Zlength dec) by lia.
      replace (i + (k + 1)) with
        (Zlength dec - Zlength suf + k) by lia.
      reflexivity.
Qed.
Lemma partial_suffix_costs_full__suffix_costs :
  forall a dec suf,
    Zlength suf = Zlength dec ->
    PartialSuffixCosts a dec suf ->
    SuffixCosts a dec suf.
Proof.
  intros a dec suf Hlen Hpartial.
  unfold PartialSuffixCosts in Hpartial.
  unfold SuffixCosts.
  destruct Hpartial as [Hfits [Hdec_a Hcost]].
  repeat split.
  - exact Hlen.
  - exact Hdec_a.
  - intros j Hj.
    specialize (Hcost j ltac:(lia)).
    replace (Zlength dec - Zlength suf) with 0 in Hcost by lia.
    simpl in Hcost.
    exact Hcost.
Qed.
Lemma partial_suffix_costs_values_bounded__suffix_costs :
  forall a dec suf,
    Zlength dec = Zlength a ->
    Zlength a <= 100000 ->
    RightProfileSuffix a dec ->
    PartialSuffixCosts a dec suf ->
    (forall k, 0 <= k < Zlength a ->
       1 <= Znth k a 0 <= 1000000000) ->
    (forall k, 0 <= k < Zlength dec ->
       1 <= Znth k dec 0 <= 1000100000) ->
    forall j, 0 <= j < Zlength suf ->
      0 <= Znth j suf 0 <= 100010000000000.
Proof.
  intros a dec suf Hdec Halen Hright Hpartial Ha Hdb j Hj.
  unfold RightProfileSuffix in Hright.
  destruct Hright as [Hright_len [Hright_dom Hright_rest]].
  unfold PartialSuffixCosts in Hpartial.
  destruct Hpartial as [Hfits [Hdec_a Hcost]].
  specialize (Hcost j Hj).
  unfold sum_range in Hcost.
  replace (Zlength suf - 1 + 1) with (Zlength suf) in Hcost by lia.
  rewrite Hcost.
  pose proof
    (sum_Z_range_bounds j (Zlength suf)
      (fun k =>
         Znth (Zlength dec - Zlength suf + k) dec 0 -
         Znth (Zlength a - Zlength suf + k) a 0)
      0 1000100000 ltac:(lia)) as Hbounds.
  specialize (Hbounds ltac:(
    intros k Hk;
    specialize (Hdb (Zlength dec - Zlength suf + k) ltac:(lia));
    specialize (Ha (Zlength a - Zlength suf + k) ltac:(lia));
    specialize (Hright_dom (Zlength dec - Zlength suf + k) ltac:(lia));
    replace (Zlength a - Zlength dec +
      (Zlength dec - Zlength suf + k))
      with (Zlength a - Zlength suf + k) in Hright_dom by lia;
    lia)).
  lia.
Qed.
Lemma peak_cost_bounds__best_peak_update :
  forall a inc dec pre suf n i,
    n = Zlength a ->
    Zlength inc = n -> LeftProfilePrefix a inc ->
    Zlength dec = n -> RightProfileSuffix a dec ->
    Zlength pre = n -> PrefixCosts a inc pre ->
    Zlength suf = n -> SuffixCosts a dec suf ->
    0 <= i < n ->
    (forall k, 0 <= k < n ->
      1 <= Znth k a 0 <= 1000000000 /\
      1 <= Znth k inc 0 <= 1000100000 /\
      1 <= Znth k dec 0 <= 1000100000 /\
      0 <= Znth k pre 0 <= 100010000000000 /\
      0 <= Znth k suf 0 <= 100010000000000) ->
    0 <= PeakCostValue a inc dec pre suf i <= 200020000000000.
Proof.
  intros a inc dec pre suf n i Ha Hinc Hleft Hdec Hright
    Hpre Hprefix Hsuf Hsuffix Hi Hbounds.
  destruct Hleft as [_ [Hleft_dom _]].
  destruct Hright as [_ [Hright_dom _]].
  destruct Hprefix as [_ [_ Hprefix_eq]].
  destruct Hsuffix as [_ [_ Hsuffix_eq]].
  pose proof (Hleft_dom i ltac:(lia)) as Hleft_i.
  pose proof (Hright_dom i ltac:(rewrite Hdec; lia)) as Hright_i.
  replace (Zlength a - Zlength dec + i) with i in Hright_i by lia.
  specialize (Hprefix_eq i ltac:(rewrite Hpre; lia)).
  specialize (Hsuffix_eq i ltac:(rewrite Hsuf; lia)).
  specialize (Hbounds i Hi).
  assert (Hprefix_nonneg :
    0 <= sum (fun x => 0 <= x < i)
      (fun k => Znth k inc 0 - Znth k a 0)).
  {
    apply sum_nonneg.
    intros k Hk.
    specialize (Hleft_dom k ltac:(rewrite Hinc; lia)).
    lia.
  }
  assert (Hsuffix_nonneg :
    0 <= sum (fun x => i + 1 <= x < n)
      (fun k => Znth k dec 0 -
        Znth (Zlength a - Zlength suf + k) a 0)).
  {
    apply sum_nonneg.
    intros k Hk.
    specialize (Hright_dom k ltac:(rewrite Hdec; lia)).
    replace (Zlength suf) with (Zlength dec) by lia.
    lia.
  }
  unfold sum_range in Hprefix_eq, Hsuffix_eq.
  rewrite sum_Z_range_extend_right in Hprefix_eq by lia.
  replace (Zlength suf - 1 + 1) with n in Hsuffix_eq by lia.
  rewrite sum_Z_range_cons in Hsuffix_eq by lia.
  replace (Zlength a - Zlength suf + i) with i in Hsuffix_eq by lia.
  unfold PeakCostValue.
  destruct (Z_le_gt_dec (Znth i inc 0) (Znth i dec 0)).
  - rewrite Z.max_r by lia.
    split; lia.
  - rewrite Z.max_l by lia.
    split; lia.
Qed.
Lemma best_peak_prefix_first__best_peak_update :
  forall a inc dec pre suf i,
    i = 0 ->
    0 < Zlength a ->
    BestPeakPrefix a inc dec pre suf 0 (-1) ->
    BestPeakPrefix a inc dec pre suf (i + 1)
      (PeakCostValue a inc dec pre suf i).
Proof.
  intros a inc dec pre suf i Hi Hlen Hsentinel.
  subst i.
  unfold BestPeakPrefix.
  right.
  split; [lia |].
  split; [lia |].
  exists 0.
  split; [lia |].
  split; [reflexivity |].
  intros j Hj.
  replace j with 0 by lia.
  lia.
Qed.
Lemma best_peak_prefix_take_current__best_peak_update :
  forall a inc dec pre suf i best candidate,
    BestPeakPrefix a inc dec pre suf i best ->
    0 <= best ->
    candidate < best ->
    candidate = PeakCostValue a inc dec pre suf i ->
    0 <= i < Zlength a ->
    BestPeakPrefix a inc dec pre suf (i + 1) candidate.
Proof.
  intros a inc dec pre suf i best candidate Hbest Hbest0 Hlt Heq Hi.
  unfold BestPeakPrefix in Hbest |- *.
  destruct Hbest as [[Hi0 Hsentinel] | [Hi0 [Hilen Hbest]]].
  - lia.
  - right.
    split; [lia |].
    split; [lia |].
    exists i.
    split; [lia |].
    split; [exact Heq |].
    intros j Hj.
    destruct Hbest as [peak [Hpeak [Hbest_eq Hleast]]].
    destruct (Z.lt_ge_cases j i) as [Hji | Hji].
    + specialize (Hleast j ltac:(lia)).
      lia.
    + replace j with i by lia.
      rewrite <- Heq.
      lia.
Qed.
Lemma best_peak_prefix_keep_previous__best_peak_update :
  forall a inc dec pre suf i best,
    BestPeakPrefix a inc dec pre suf i best ->
    0 <= best ->
    best <= PeakCostValue a inc dec pre suf i ->
    0 <= i < Zlength a ->
    BestPeakPrefix a inc dec pre suf (i + 1) best.
Proof.
  intros a inc dec pre suf i best Hbest Hbest0 Hcurrent Hi.
  unfold BestPeakPrefix in Hbest |- *.
  destruct Hbest as [[Hi0 Hsentinel] | [Hi0 [Hilen Hbest]]].
  - lia.
  - right.
    split; [lia |].
    split; [lia |].
    destruct Hbest as [peak [Hpeak [Hbest_eq Hleast]]].
    exists peak.
    split; [lia |].
    split; [exact Hbest_eq |].
    intros j Hj.
    destruct (Z.lt_ge_cases j i) as [Hji | Hji].
    + apply Hleast; lia.
    + replace j with i by lia.
      exact Hcurrent.
Qed.
Lemma peak_profile_value__final_result :
  forall (a inc dec : list Z) (p : Z),
  {b : list Z |
   b = map
     (fun k =>
        if k <? p then Znth k inc 0
        else if p <? k then Znth k dec 0
        else Z.max (Znth p inc 0) (Znth p dec 0))
     (Zrange 0 (Zlength a))}.
Proof.
  intros. eexists. reflexivity.
Defined.
Lemma peak_profile_length__final_result :
  forall a inc dec p,
    Zlength (proj1_sig (peak_profile_value__final_result a inc dec p)) =
    Zlength a.
Proof.
  intros. rewrite (proj2_sig (peak_profile_value__final_result a inc dec p)).
  rewrite Zlength_map__final_result, Zlength_Zrange__final_result;
    [lia | apply Zlength_nonneg].
Qed.
Lemma peak_profile_Znth__final_result :
  forall a inc dec p k,
    0 <= k < Zlength a ->
    Znth k (proj1_sig (peak_profile_value__final_result a inc dec p)) 0 =
      if k <? p then Znth k inc 0
      else if p <? k then Znth k dec 0
      else Z.max (Znth p inc 0) (Znth p dec 0).
Proof.
  intros a inc dec p k Hk.
  rewrite (proj2_sig (peak_profile_value__final_result a inc dec p)).
  rewrite (@Znth_map__final_result Z Z
    (fun k =>
       if k <? p then Znth k inc 0
       else if p <? k then Znth k dec 0
       else Z.max (Znth p inc 0) (Znth p dec 0))
    (Zrange 0 (Zlength a)) 0 0 k) by
    (rewrite Zlength_Zrange__final_result; lia).
  rewrite Znth_Zrange__final_result by lia. reflexivity.
Qed.
Lemma profiles_form_peak_mountain__final_result :
  forall a inc dec p,
    Zlength inc = Zlength a ->
    Zlength dec = Zlength a ->
    LeftProfilePrefix a inc ->
    RightProfileSuffix a dec ->
    0 <= p < Zlength a ->
    Zlength (proj1_sig (peak_profile_value__final_result a inc dec p)) =
      Zlength a /\
    (forall k, 0 <= k < Zlength a ->
       Znth k a 0 <=
       Znth k (proj1_sig (peak_profile_value__final_result a inc dec p)) 0) /\
    Mountain (proj1_sig (peak_profile_value__final_result a inc dec p)).
Proof.
  intros a inc dec p Hinc_len Hdec_len Hinc Hdec Hp.
  destruct Hinc as [_ [Hinc_dom [Hinc_strict _]]].
  destruct Hdec as [_ [Hdec_dom [Hdec_strict _]]].
  rewrite peak_profile_length__final_result.
  split; [reflexivity |].
  split.
  - intros k Hk. rewrite peak_profile_Znth__final_result by exact Hk.
    destruct (k <? p) eqn:Hkp.
    + apply Z.ltb_lt in Hkp.
      apply Hinc_dom. rewrite Hinc_len. exact Hk.
    + apply Z.ltb_ge in Hkp.
      destruct (p <? k) eqn:Hpk.
      * apply Z.ltb_lt in Hpk.
        specialize (Hdec_dom k). rewrite Hdec_len in Hdec_dom.
        replace (Zlength a - Zlength a + k) with k in Hdec_dom by lia.
        apply Hdec_dom. exact Hk.
      * apply Z.ltb_ge in Hpk. assert (k = p) by lia. subst k.
        eapply Z.le_trans; [apply Hinc_dom; rewrite Hinc_len; exact Hp |].
        apply Z.le_max_l.
  - exists p. rewrite peak_profile_length__final_result.
    split; [exact Hp |]. split.
    + intros k Hk.
      rewrite !peak_profile_Znth__final_result by lia.
      destruct (k <? p) eqn:Hkp.
      2: { apply Z.ltb_ge in Hkp. lia. }
      apply Z.ltb_lt in Hkp.
      destruct (k + 1 <? p) eqn:Hnext.
      * apply Z.ltb_lt in Hnext. apply Hinc_strict. rewrite Hinc_len. lia.
      * apply Z.ltb_ge in Hnext.
        destruct (p <? k + 1) eqn:Hpk1.
        { apply Z.ltb_lt in Hpk1. lia. }
        apply Z.ltb_ge in Hpk1.
        eapply Z.lt_le_trans.
        -- specialize (Hinc_strict k). rewrite Hinc_len in Hinc_strict.
           replace (k + 1) with p in Hinc_strict by lia.
           apply Hinc_strict. lia.
        -- apply Z.le_max_l.
    + intros k Hk.
      rewrite !peak_profile_Znth__final_result by lia.
      destruct (k <? p) eqn:Hkp.
      { apply Z.ltb_lt in Hkp. lia. }
      apply Z.ltb_ge in Hkp.
      destruct (p <? k) eqn:Hpk.
      * apply Z.ltb_lt in Hpk.
        destruct (k + 1 <? p) eqn:Hnext1.
        { apply Z.ltb_lt in Hnext1. lia. }
        destruct (p <? k + 1) eqn:Hnext2.
        2: { apply Z.ltb_ge in Hnext2. lia. }
        apply Hdec_strict. rewrite Hdec_len. lia.
      * apply Z.ltb_ge in Hpk. assert (k = p) by lia. subst k.
        destruct (p + 1 <? p) eqn:Hnext1.
        { apply Z.ltb_lt in Hnext1. lia. }
        destruct (p <? p + 1) eqn:Hnext2.
        2: { apply Z.ltb_ge in Hnext2. lia. }
        specialize (Hdec_strict p).
        rewrite Hdec_len in Hdec_strict.
        pose proof (Z.le_max_r (Znth p inc 0) (Znth p dec 0)).
        lia.
Qed.
Lemma peak_profile_sum_cost__final_result :
  forall a inc dec pre suf p,
    Zlength inc = Zlength a ->
    Zlength dec = Zlength a ->
    Zlength pre = Zlength a ->
    Zlength suf = Zlength a ->
    PrefixCosts a inc pre ->
    SuffixCosts a dec suf ->
    0 <= p < Zlength a ->
    ListLib.sum (proj1_sig (peak_profile_value__final_result a inc dec p)) -
      ListLib.sum a = PeakCostValue a inc dec pre suf p.
Proof.
  intros a inc dec pre suf p Hinc_len Hdec_len Hpre_len Hsuf_len
    Hpre Hsuf Hp.
  destruct Hpre as [_ [_ Hpre_cost]].
  destruct Hsuf as [_ [_ Hsuf_cost]].
  specialize (Hpre_cost p). rewrite Hpre_len in Hpre_cost.
  specialize (Hsuf_cost p). rewrite Hsuf_len in Hsuf_cost.
  specialize (Hpre_cost Hp). specialize (Hsuf_cost Hp).
  unfold sum_range in Hpre_cost, Hsuf_cost.
  replace (Zlength a - 1 + 1) with (Zlength a) in Hsuf_cost by lia.
  assert (Hsuf_cost_norm :
    Znth p suf 0 =
    sum (fun k => p <= k < Zlength a)
      (fun k => Znth k dec 0 - Znth k a 0)).
  {
    rewrite Hsuf_cost. apply sum_Z_range_ext. intros k Hk.
    replace (Zlength a - Zlength a + k) with k by lia. reflexivity.
  }
  clear Hsuf_cost. rename Hsuf_cost_norm into Hsuf_cost.
  rewrite !list_sum_as_Z_range_sum.
  rewrite peak_profile_length__final_result.
  rewrite <- sum_Z_range_sub.
  rewrite (sum_Z_range_split 0 p (Zlength a)) by lia.
  rewrite (sum_Z_range_split p (p + 1) (Zlength a)) by lia.
  rewrite sum_Z_range_single.
  assert (Hleft :
    sum (fun k => 0 <= k < p)
      (fun k =>
        Znth k (proj1_sig (peak_profile_value__final_result a inc dec p)) 0 -
        Znth k a 0) =
    sum (fun k => 0 <= k < p)
      (fun k => Znth k inc 0 - Znth k a 0)).
  {
    apply sum_Z_range_ext. intros k Hk.
    rewrite peak_profile_Znth__final_result by lia.
    destruct (k <? p) eqn:Hlt; [reflexivity |].
    apply Z.ltb_ge in Hlt. lia.
  }
  assert (Hright :
    sum (fun k => p + 1 <= k < Zlength a)
      (fun k =>
        Znth k (proj1_sig (peak_profile_value__final_result a inc dec p)) 0 -
        Znth k a 0) =
    sum (fun k => p + 1 <= k < Zlength a)
      (fun k => Znth k dec 0 - Znth k a 0)).
  {
    apply sum_Z_range_ext. intros k Hk.
    rewrite peak_profile_Znth__final_result by lia.
    destruct (k <? p) eqn:Hlt.
    - apply Z.ltb_lt in Hlt. exfalso.
      apply (Z.lt_irrefl p).
      eapply Z.lt_trans.
      + eapply Z.lt_le_trans.
        * apply Z.lt_succ_diag_r.
        * exact (proj1 Hk).
      + exact Hlt.
    - destruct (p <? k) eqn:Hgt; [reflexivity |].
      apply Z.ltb_ge in Hgt. exfalso.
      apply (Z.lt_irrefl p).
      eapply Z.lt_le_trans.
      + apply Z.lt_succ_diag_r.
      + eapply Z.le_trans; [exact (proj1 Hk) | exact Hgt].
  }
  rewrite Hleft, Hright.
  rewrite peak_profile_Znth__final_result by exact Hp.
  destruct (p <? p) eqn:Hpp1.
  { apply Z.ltb_lt in Hpp1. exfalso. exact (Z.lt_irrefl p Hpp1). }
  rewrite (sum_Z_range_split 0 p (p + 1)) in Hpre_cost by lia.
  rewrite sum_Z_range_single in Hpre_cost.
  rewrite (sum_Z_range_split p (p + 1) (Zlength a)) in Hsuf_cost by lia.
  rewrite sum_Z_range_single in Hsuf_cost.
  unfold PeakCostValue.
  rewrite Hpre_cost, Hsuf_cost.
  ring.
Qed.
Lemma peak_profile_added_load_cost__final_result :
  forall a inc dec pre suf p,
    Zlength inc = Zlength a ->
    Zlength dec = Zlength a ->
    Zlength pre = Zlength a ->
    Zlength suf = Zlength a ->
    LeftProfilePrefix a inc ->
    RightProfileSuffix a dec ->
    PrefixCosts a inc pre ->
    SuffixCosts a dec suf ->
    0 <= p < Zlength a ->
    AddedLoad a (PeakCostValue a inc dec pre suf p).
Proof.
  intros a inc dec pre suf p Hinc_len Hdec_len Hpre_len Hsuf_len
    Hinc Hdec Hpre Hsuf Hp.
  exists (proj1_sig (peak_profile_value__final_result a inc dec p)).
  pose proof (profiles_form_peak_mountain__final_result
    a inc dec p Hinc_len Hdec_len Hinc Hdec Hp) as Hprofile.
  destruct Hprofile as [Hlen [Hdom Hmountain]].
  split; [exact Hlen |]. split; [exact Hdom |]. split; [exact Hmountain |].
  symmetry. apply peak_profile_sum_cost__final_result; assumption.
Qed.
Lemma left_extension_value__final_result :
  forall (a b : list Z) (p : Z),
  {q : list Z |
   q = map
     (fun k =>
        if k <=? p then Znth k b 0
        else Znth p b 0 + (k - p) * 1000000001)
     (Zrange 0 (Zlength a))}.
Proof. intros. eexists. reflexivity. Defined.
Lemma left_extension_length__final_result :
  forall a b p,
    Zlength (proj1_sig (left_extension_value__final_result a b p)) =
    Zlength a.
Proof.
  intros. rewrite (proj2_sig (left_extension_value__final_result a b p)).
  rewrite Zlength_map__final_result, Zlength_Zrange__final_result;
    [lia | apply Zlength_nonneg].
Qed.
Lemma left_extension_Znth__final_result :
  forall a b p k,
    0 <= k < Zlength a ->
    Znth k (proj1_sig (left_extension_value__final_result a b p)) 0 =
      if k <=? p then Znth k b 0
      else Znth p b 0 + (k - p) * 1000000001.
Proof.
  intros a b p k Hk.
  rewrite (proj2_sig (left_extension_value__final_result a b p)).
  rewrite (@Znth_map__final_result Z Z
    (fun k => if k <=? p then Znth k b 0
              else Znth p b 0 + (k - p) * 1000000001)
    (Zrange 0 (Zlength a)) 0 0 k) by
    (rewrite Zlength_Zrange__final_result; lia).
  rewrite Znth_Zrange__final_result by lia. reflexivity.
Qed.
Lemma left_profile_below_mountain_prefix__final_result :
  forall a inc b p,
    Zlength inc = Zlength a ->
    Zlength b = Zlength a ->
    (forall k, 0 <= k < Zlength a -> Znth k a 0 <= Znth k b 0) ->
    (forall k, 0 <= k < p -> Znth k b 0 < Znth (k + 1) b 0) ->
    0 <= p < Zlength a ->
    (forall k, 0 <= k < Zlength a -> 1 <= Znth k a 0 <= 1000000000) ->
    LeftProfilePrefix a inc ->
    forall k, 0 <= k <= p -> Znth k inc 0 <= Znth k b 0.
Proof.
  intros a inc b p Hinc_len Hb_len Hb_dom Hb_inc Hp Ha_bounds Hinc k Hk.
  destruct Hinc as [_ [_ [_ Hinc_min]]].
  set (q := proj1_sig (left_extension_value__final_result a b p)).
  assert (Hq_len : Zlength q = Zlength inc).
  { unfold q. rewrite left_extension_length__final_result. symmetry. exact Hinc_len. }
  assert (Hq_dom : forall j, 0 <= j < Zlength q -> Znth j a 0 <= Znth j q 0).
  {
    intros j Hj. unfold q in *.
    rewrite left_extension_length__final_result in Hj.
    rewrite left_extension_Znth__final_result by exact Hj.
    destruct (j <=? p) eqn:Hjp.
    - apply Z.leb_le in Hjp. apply Hb_dom. exact Hj.
    - apply Z.leb_gt in Hjp.
      pose proof (Ha_bounds p Hp) as Hap.
      pose proof (Ha_bounds j Hj) as Haj.
      pose proof (Hb_dom p Hp) as Hbp.
      nia.
  }
  assert (Hq_inc : forall j, 0 <= j < Zlength q - 1 ->
    Znth j q 0 < Znth (j + 1) q 0).
  {
    intros j Hj. unfold q in *.
    rewrite left_extension_length__final_result in Hj.
    rewrite !left_extension_Znth__final_result by lia.
    destruct (j <=? p) eqn:Hjp.
    - apply Z.leb_le in Hjp.
      destruct (j + 1 <=? p) eqn:Hnext.
      + apply Z.leb_le in Hnext. apply Hb_inc. lia.
      + apply Z.leb_gt in Hnext.
        assert (j = p) by lia. subst j. nia.
    - apply Z.leb_gt in Hjp.
      destruct (j + 1 <=? p) eqn:Hnext.
      + apply Z.leb_le in Hnext. lia.
      + apply Z.leb_gt in Hnext. nia.
  }
  specialize (Hinc_min q Hq_len Hq_dom Hq_inc k).
  rewrite Hinc_len in Hinc_min.
  specialize (Hinc_min ltac:(lia)).
  unfold q in Hinc_min.
  rewrite left_extension_Znth__final_result in Hinc_min by lia.
  destruct (k <=? p) eqn:Hkp; [exact Hinc_min |].
  apply Z.leb_gt in Hkp. lia.
Qed.
Lemma right_extension_value__final_result :
  forall (a b : list Z) (p : Z),
  {q : list Z |
   q = map
     (fun k =>
        if p <=? k then Znth k b 0
        else Znth p b 0 + (p - k) * 1000000001)
     (Zrange 0 (Zlength a))}.
Proof. intros. eexists. reflexivity. Defined.
Lemma right_extension_length__final_result :
  forall a b p,
    Zlength (proj1_sig (right_extension_value__final_result a b p)) =
    Zlength a.
Proof.
  intros. rewrite (proj2_sig (right_extension_value__final_result a b p)).
  rewrite Zlength_map__final_result, Zlength_Zrange__final_result;
    [lia | apply Zlength_nonneg].
Qed.
Lemma right_extension_Znth__final_result :
  forall a b p k,
    0 <= k < Zlength a ->
    Znth k (proj1_sig (right_extension_value__final_result a b p)) 0 =
      if p <=? k then Znth k b 0
      else Znth p b 0 + (p - k) * 1000000001.
Proof.
  intros a b p k Hk.
  rewrite (proj2_sig (right_extension_value__final_result a b p)).
  rewrite (@Znth_map__final_result Z Z
    (fun k => if p <=? k then Znth k b 0
              else Znth p b 0 + (p - k) * 1000000001)
    (Zrange 0 (Zlength a)) 0 0 k) by
    (rewrite Zlength_Zrange__final_result; lia).
  rewrite Znth_Zrange__final_result by lia. reflexivity.
Qed.
Lemma right_profile_below_mountain_suffix__final_result :
  forall a dec b p,
    Zlength dec = Zlength a ->
    Zlength b = Zlength a ->
    (forall k, 0 <= k < Zlength a -> Znth k a 0 <= Znth k b 0) ->
    (forall k, p <= k < Zlength a - 1 -> Znth k b 0 > Znth (k + 1) b 0) ->
    0 <= p < Zlength a ->
    (forall k, 0 <= k < Zlength a -> 1 <= Znth k a 0 <= 1000000000) ->
    RightProfileSuffix a dec ->
    forall k, p <= k < Zlength a -> Znth k dec 0 <= Znth k b 0.
Proof.
  intros a dec b p Hdec_len Hb_len Hb_dom Hb_dec Hp Ha_bounds Hdec k Hk.
  destruct Hdec as [_ [_ [_ Hdec_min]]].
  set (q := proj1_sig (right_extension_value__final_result a b p)).
  assert (Hq_len : Zlength q = Zlength dec).
  { unfold q. rewrite right_extension_length__final_result. symmetry. exact Hdec_len. }
  assert (Hq_dom : forall j, 0 <= j < Zlength q ->
    Znth (Zlength a - Zlength q + j) a 0 <= Znth j q 0).
  {
    intros j Hj. unfold q in *.
    rewrite right_extension_length__final_result in Hj.
    rewrite right_extension_length__final_result.
    replace (Zlength a - Zlength a + j) with j by lia.
    rewrite right_extension_Znth__final_result by exact Hj.
    destruct (p <=? j) eqn:Hpj.
    - apply Z.leb_le in Hpj. apply Hb_dom. exact Hj.
    - apply Z.leb_gt in Hpj.
      pose proof (Ha_bounds p Hp) as Hap.
      pose proof (Ha_bounds j Hj) as Haj.
      pose proof (Hb_dom p Hp) as Hbp.
      nia.
  }
  assert (Hq_dec : forall j, 0 <= j < Zlength q - 1 ->
    Znth j q 0 > Znth (j + 1) q 0).
  {
    intros j Hj. unfold q in *.
    rewrite right_extension_length__final_result in Hj.
    rewrite !right_extension_Znth__final_result by lia.
    destruct (p <=? j) eqn:Hpj.
    - apply Z.leb_le in Hpj.
      destruct (p <=? j + 1) eqn:Hnext.
      + apply Z.leb_le in Hnext. apply Hb_dec. lia.
      + apply Z.leb_gt in Hnext. lia.
    - apply Z.leb_gt in Hpj.
      destruct (p <=? j + 1) eqn:Hnext.
      + apply Z.leb_le in Hnext. assert (j + 1 = p) by lia. subst p. nia.
      + apply Z.leb_gt in Hnext. nia.
  }
  specialize (Hdec_min q Hq_len Hq_dom Hq_dec k).
  rewrite Hdec_len in Hdec_min.
  specialize (Hdec_min ltac:(lia)).
  unfold q in Hdec_min.
  rewrite right_extension_Znth__final_result in Hdec_min by lia.
  destruct (p <=? k) eqn:Hpk; [exact Hdec_min |].
  apply Z.leb_gt in Hpk. lia.
Qed.
Lemma peak_cost_as_ranges__final_result :
  forall a inc dec pre suf p,
    Zlength inc = Zlength a ->
    Zlength dec = Zlength a ->
    Zlength pre = Zlength a ->
    Zlength suf = Zlength a ->
    PrefixCosts a inc pre ->
    SuffixCosts a dec suf ->
    0 <= p < Zlength a ->
    PeakCostValue a inc dec pre suf p =
      sum (fun k => 0 <= k < p)
        (fun k => Znth k inc 0 - Znth k a 0) +
      (Z.max (Znth p inc 0) (Znth p dec 0) - Znth p a 0) +
      sum (fun k => p + 1 <= k < Zlength a)
        (fun k => Znth k dec 0 - Znth k a 0).
Proof.
  intros a inc dec pre suf p Hinc_len Hdec_len Hpre_len Hsuf_len
    Hpre Hsuf Hp.
  destruct Hpre as [_ [_ Hpre_cost]].
  destruct Hsuf as [_ [_ Hsuf_cost]].
  specialize (Hpre_cost p). rewrite Hpre_len in Hpre_cost.
  specialize (Hsuf_cost p). rewrite Hsuf_len in Hsuf_cost.
  specialize (Hpre_cost Hp). specialize (Hsuf_cost Hp).
  unfold sum_range in Hpre_cost, Hsuf_cost.
  replace (Zlength a - 1 + 1) with (Zlength a) in Hsuf_cost by lia.
  assert (Hsuf_cost_norm :
    Znth p suf 0 =
    sum (fun k => p <= k < Zlength a)
      (fun k => Znth k dec 0 - Znth k a 0)).
  {
    rewrite Hsuf_cost. apply sum_Z_range_ext. intros k Hk.
    replace (Zlength a - Zlength a + k) with k by lia. reflexivity.
  }
  clear Hsuf_cost. rename Hsuf_cost_norm into Hsuf_cost.
  rewrite (sum_Z_range_split 0 p (p + 1)) in Hpre_cost by lia.
  rewrite sum_Z_range_single in Hpre_cost.
  rewrite (sum_Z_range_split p (p + 1) (Zlength a)) in Hsuf_cost by lia.
  rewrite sum_Z_range_single in Hsuf_cost.
  unfold PeakCostValue. rewrite Hpre_cost, Hsuf_cost. ring.
Qed.
Lemma mountain_cost_lower_bound__final_result :
  forall a inc dec pre suf b cost p,
    Zlength inc = Zlength a ->
    Zlength dec = Zlength a ->
    Zlength pre = Zlength a ->
    Zlength suf = Zlength a ->
    LeftProfilePrefix a inc ->
    RightProfileSuffix a dec ->
    PrefixCosts a inc pre ->
    SuffixCosts a dec suf ->
    (forall k, 0 <= k < Zlength a -> 1 <= Znth k a 0 <= 1000000000) ->
    Zlength b = Zlength a ->
    (forall k, 0 <= k < Zlength a -> Znth k a 0 <= Znth k b 0) ->
    0 <= p < Zlength b ->
    (forall k, 0 <= k < p -> Znth k b 0 < Znth (k + 1) b 0) ->
    (forall k, p <= k < Zlength b - 1 -> Znth k b 0 > Znth (k + 1) b 0) ->
    cost = ListLib.sum b - ListLib.sum a ->
    PeakCostValue a inc dec pre suf p <= cost.
Proof.
  intros a inc dec pre suf b cost p Hinc_len Hdec_len Hpre_len Hsuf_len
    Hinc Hdec Hpre Hsuf Ha_bounds Hb_len Hb_dom Hp Hb_inc Hb_dec Hcost.
  rewrite Hb_len in Hp, Hb_dec.
  pose proof (left_profile_below_mountain_prefix__final_result
    a inc b p Hinc_len Hb_len Hb_dom Hb_inc Hp Ha_bounds Hinc) as Hleft.
  pose proof (right_profile_below_mountain_suffix__final_result
    a dec b p Hdec_len Hb_len Hb_dom Hb_dec Hp Ha_bounds Hdec) as Hright.
  assert (Hsum_left :
    sum (fun k => 0 <= k < p)
      (fun k => Znth k inc 0 - Znth k a 0) <=
    sum (fun k => 0 <= k < p)
      (fun k => Znth k b 0 - Znth k a 0)).
  {
    apply sum_Z_range_le. intros k Hk.
    specialize (Hleft k ltac:(lia)). lia.
  }
  assert (Hsum_right :
    sum (fun k => p + 1 <= k < Zlength a)
      (fun k => Znth k dec 0 - Znth k a 0) <=
    sum (fun k => p + 1 <= k < Zlength a)
      (fun k => Znth k b 0 - Znth k a 0)).
  {
    apply sum_Z_range_le. intros k Hk.
    specialize (Hright k ltac:(lia)). lia.
  }
  assert (Hpeak :
    Z.max (Znth p inc 0) (Znth p dec 0) - Znth p a 0 <=
    Znth p b 0 - Znth p a 0).
  {
    specialize (Hleft p ltac:(lia)).
    specialize (Hright p ltac:(lia)).
    apply Z.sub_le_mono_r. apply Z.max_lub; assumption.
  }
  rewrite (peak_cost_as_ranges__final_result a inc dec pre suf p
    Hinc_len Hdec_len Hpre_len Hsuf_len Hpre Hsuf Hp).
  rewrite Hcost.
  rewrite !list_sum_as_Z_range_sum, Hb_len.
  rewrite <- sum_Z_range_sub.
  rewrite (sum_Z_range_split 0 p (Zlength a)) by lia.
  rewrite (sum_Z_range_split p (p + 1) (Zlength a)) by lia.
  rewrite sum_Z_range_single.
  rewrite <- !Z.add_assoc.
  apply Z.add_le_mono; [exact Hsum_left |].
  apply Z.add_le_mono; assumption.
Qed.
Lemma best_peak_full_implies_spec__final_result :
  forall a inc dec pre suf best,
    Zlength inc = Zlength a ->
    Zlength dec = Zlength a ->
    Zlength pre = Zlength a ->
    Zlength suf = Zlength a ->
    LeftProfilePrefix a inc ->
    RightProfileSuffix a dec ->
    PrefixCosts a inc pre ->
    SuffixCosts a dec suf ->
    (forall k, 0 <= k < Zlength a -> 1 <= Znth k a 0 <= 1000000000) ->
    BestPeakPrefix a inc dec pre suf (Zlength a) best ->
    Spec a best.
Proof.
  intros a inc dec pre suf best Hinc_len Hdec_len Hpre_len Hsuf_len
    Hinc Hdec Hpre Hsuf Ha_bounds Hbest.
  assert (Hn : 1 <= Zlength a).
  {
    unfold LeftProfilePrefix in Hinc.
    destruct Hinc as [Hlen _]. rewrite Hinc_len in Hlen. lia.
  }
  unfold BestPeakPrefix in Hbest.
  destruct Hbest as [[Hempty _] | [_ [_ [peak [Hpeak [Hbest_eq Hbest_min]]]]]].
  - lia.
  - unfold Spec, min_value_of_subset, min_object_of_subset.
    exists best. split.
    + split.
      * rewrite Hbest_eq.
        apply peak_profile_added_load_cost__final_result;
          try assumption; exact Hpeak.
      * intros cost Hadded.
        destruct Hadded as [b [Hb_len [Hb_dom [Hmountain Hcost]]]].
        destruct Hmountain as [p [Hp [Hb_inc Hb_dec]]].
        eapply Z.le_trans.
        -- apply Hbest_min. rewrite Hb_len in Hp. exact Hp.
        -- eapply mountain_cost_lower_bound__final_result;
             try eassumption.
    + reflexivity.
Qed.
