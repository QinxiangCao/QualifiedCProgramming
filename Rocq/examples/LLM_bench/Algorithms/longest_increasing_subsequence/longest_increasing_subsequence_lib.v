Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition StrictlyIncreasingValues (l idxs : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength idxs ->
    Znth (Znth p idxs 0) l 0 < Znth (Znth q idxs 0) l 0.

Definition ValidIncreasingSubsequence
    (l : list Z) (limit : Z) (idxs : list Z) : Prop :=
  0 <= limit <= Zlength l /\
  Forall (fun idx => 0 <= idx < limit) idxs /\
  mono_inc idxs /\
  StrictlyIncreasingValues l idxs.

Definition ValidIncreasingSubsequenceEndingAt
    (l : list Z) (i : Z) (idxs : list Z) : Prop :=
  0 <= i < Zlength l /\
  ValidIncreasingSubsequence l (i + 1) idxs /\
  exists prefix, idxs = prefix ++ i :: nil.

Definition LISPrefix (l : list Z) (limit ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => ValidIncreasingSubsequence l limit idxs)
    (fun idxs => Zlength idxs)
    ans.

Definition LISLength (l : list Z) (ans : Z) : Prop :=
  LISPrefix l (Zlength l) ans.

Definition LISEndingAtLength (l : list Z) (i ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => ValidIncreasingSubsequenceEndingAt l i idxs)
    (fun idxs => Zlength idxs)
    ans.

Definition LISDPTablePrefix
    (l dp : list Z) (hi : Z) : Prop :=
  0 <= hi <= Zlength l /\
  Zlength dp = hi /\
  forall k,
    0 <= k < hi ->
    LISEndingAtLength l k (Znth k dp 0) /\
    1 <= Znth k dp 0 <= k + 1.

Definition LISDPInnerCandidate
    (l dp : list Z) (i scanned candidate : Z) : Prop :=
  candidate = 1 \/
  exists k,
    0 <= k < scanned /\
    Znth k l 0 < Znth i l 0 /\
    candidate = Znth k dp 0 + 1.

Definition LISInnerProgress
    (l dp : list Z) (i scanned : Z) : Prop :=
  0 <= i < Zlength l /\
  0 <= scanned <= i /\
  Zlength dp = i + 1 /\
  (forall k,
    0 <= k < i ->
    LISEndingAtLength l k (Znth k dp 0) /\
    1 <= Znth k dp 0 <= k + 1) /\
  max_value_of_subset Z.le
    (fun candidate => LISDPInnerCandidate l dp i scanned candidate)
    (fun candidate => candidate)
    (Znth i dp 0) /\
  1 <= Znth i dp 0 <= i + 1.

Definition LISBestSoFar (l : list Z) (limit ans : Z) : Prop :=
  0 <= limit <= Zlength l /\
  ((limit = 0 /\ ans = 1) \/
   (0 < limit /\ LISPrefix l limit ans)).

Require Import Coq.micromega.Lia.
Lemma lis_inner_progress_entry_bound__inner_foundations :
  forall l dp i scanned k,
    LISInnerProgress l dp i scanned ->
    0 <= k < i ->
    1 <= Znth k dp 0 <= k + 1.
Proof.
  intros l dp i scanned k Hprogress Hk.
  unfold LISInnerProgress in Hprogress.
  destruct Hprogress as [_ [_ [_ [Hprefix _]]]].
  exact (proj2 (Hprefix k Hk)).
Qed.
Lemma lis_inner_progress_init__inner_foundations :
  forall l dp i,
    LISDPTablePrefix l dp i ->
    0 <= i < Zlength l ->
    LISInnerProgress l (dp ++ [1]) i 0.
Proof.
  intros l dp i Hprefix Hi.
  unfold LISDPTablePrefix in Hprefix.
  destruct Hprefix as [Hhi [Hlen Hentries]].
  assert (Hlast : Znth i (dp ++ [1]) 0 = 1).
  {
    rewrite app_Znth2 by lia.
    replace (i - Zlength dp) with 0 by lia.
    rewrite Znth0_cons.
    reflexivity.
  }
  unfold LISInnerProgress.
  split; [exact Hi |].
  split; [lia |].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - split.
    + intros k Hk.
      rewrite app_Znth1 by lia.
      apply Hentries; exact Hk.
    + split.
      * unfold max_value_of_subset, max_object_of_subset.
      exists 1.
      rewrite Hlast.
      split.
        -- split.
           ++ unfold LISDPInnerCandidate.
              left; reflexivity.
           ++ intros candidate Hcandidate.
              unfold LISDPInnerCandidate in Hcandidate.
              destruct Hcandidate as [-> | [k [[Hk0 Hklt] [_ ->]]]].
              ** lia.
              ** lia.
        -- reflexivity.
      * rewrite Hlast.
        lia.
Qed.
Lemma lis_inner_progress_take_candidate__inner_transitions :
  forall l dp i j,
    LISInnerProgress l dp i j ->
    0 <= j < i ->
    Znth j l 0 < Znth i l 0 ->
    Znth i dp 0 < Znth j dp 0 + 1 ->
    LISInnerProgress l
      (replace_Znth i (Znth j dp 0 + 1) dp) i (j + 1).
Proof.
  intros l dp i j Hprogress Hj Hvalues Hlarger.
  unfold LISInnerProgress in *.
  destruct Hprogress as
    [Hi [Hscan [Hlen [Hprefix [Hmaximum Hcurrent_bounds]]]]].
  assert (Hi_dp : 0 <= i < Zlength dp) by (rewrite Hlen; lia).
  split; [exact Hi |].
  split; [lia |].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + intros k Hk.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hprefix. exact Hk.
    + split.
      * unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
        destruct Hmaximum as
          [old_best [[Hold_candidate Hold_upper] Hold_eq]].
        exists (Znth j dp 0 + 1).
        split.
        -- split.
           ++ right. exists j. repeat split; try lia; auto.
              rewrite Znth_replace_Znth_Diff by lia. reflexivity.
           ++ intros candidate Hcandidate.
              unfold LISDPInnerCandidate in Hcandidate.
              destruct Hcandidate as [Hone | [k [Hk [Hkv Hcandidate]]]].
              ** subst candidate. lia.
              ** rewrite Znth_replace_Znth_Diff in Hcandidate by lia.
                 destruct (Z.eq_dec k j) as [-> | Hkj].
                 --- lia.
                 --- assert (Hk_old : 0 <= k < j) by lia.
                     specialize (Hold_upper (Znth k dp 0 + 1)).
                     assert (Hold_k :
                       LISDPInnerCandidate l dp i j (Znth k dp 0 + 1)).
                     { right. exists k. split; [exact Hk_old |].
                       split; [exact Hkv | reflexivity]. }
                     specialize (Hold_upper Hold_k).
                     simpl in Hold_upper. lia.
        -- rewrite Znth_replace_Znth_Same by exact Hi_dp. reflexivity.
      * rewrite Znth_replace_Znth_Same by exact Hi_dp.
        specialize (Hprefix j Hj) as [_ Hj_bounds].
        lia.
Qed.
Lemma lis_inner_progress_skip_dominated__inner_transitions :
  forall l dp i j,
    LISInnerProgress l dp i j ->
    0 <= j < i ->
    Znth j l 0 < Znth i l 0 ->
    Znth j dp 0 + 1 <= Znth i dp 0 ->
    LISInnerProgress l dp i (j + 1).
Proof.
  intros l dp i j Hprogress Hj Hvalues Hdominated.
  unfold LISInnerProgress in *.
  destruct Hprogress as
    [Hi [Hscan [Hlen [Hprefix [Hmaximum Hcurrent_bounds]]]]].
  split; [exact Hi |].
  split; [lia |].
  split; [exact Hlen |].
  split; [exact Hprefix |].
  split.
  - unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hmaximum as
      [best [[Hbest_candidate Hbest_upper] Hbest_eq]].
    exists best. split.
    + split.
      * unfold LISDPInnerCandidate in *.
        destruct Hbest_candidate as [Hone | [k [Hk [Hkv Hcandidate]]]].
        -- left. exact Hone.
        -- right. exists k. split; [lia |].
           split; [exact Hkv | exact Hcandidate].
      * intros candidate Hcandidate.
        unfold LISDPInnerCandidate in Hcandidate.
        destruct Hcandidate as [Hone | [k [Hk [Hkv Hcandidate]]]].
        -- apply Hbest_upper. left. exact Hone.
        -- destruct (Z.eq_dec k j) as [-> | Hkj].
           ++ subst candidate. lia.
           ++ apply Hbest_upper. right. exists k. split; [lia |].
              split; [exact Hkv | exact Hcandidate].
    + exact Hbest_eq.
  - exact Hcurrent_bounds.
Qed.
Lemma lis_inner_progress_skip_nonincreasing__inner_transitions :
  forall l dp i j,
    LISInnerProgress l dp i j ->
    0 <= j < i ->
    Znth i l 0 <= Znth j l 0 ->
    LISInnerProgress l dp i (j + 1).
Proof.
  intros l dp i j Hprogress Hj Hnonincreasing.
  unfold LISInnerProgress in *.
  destruct Hprogress as
    [Hi [Hscan [Hlen [Hprefix [Hmaximum Hcurrent_bounds]]]]].
  split; [exact Hi |].
  split; [lia |].
  split; [exact Hlen |].
  split; [exact Hprefix |].
  split.
  - unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hmaximum as
      [best [[Hbest_candidate Hbest_upper] Hbest_eq]].
    exists best. split.
    + split.
      * unfold LISDPInnerCandidate in *.
        destruct Hbest_candidate as [Hone | [k [Hk [Hkv Hcandidate]]]].
        -- left. exact Hone.
        -- right. exists k. split; [lia |].
           split; [exact Hkv | exact Hcandidate].
      * intros candidate Hcandidate.
        apply Hbest_upper.
        unfold LISDPInnerCandidate in *.
        destruct Hcandidate as [Hone | [k [Hk [Hkv Hcandidate]]]].
        -- left. exact Hone.
        -- assert (k <= j) as Hkj by lia.
           destruct (Z.eq_dec k j) as [-> | Hneq].
           ++ lia.
           ++ right. exists k. split; [lia |].
              split; [exact Hkv | exact Hcandidate].
    + exact Hbest_eq.
  - exact Hcurrent_bounds.
Qed.
Lemma znth_app_singleton_old__inner_transitions :
  forall xs x k,
    0 <= k < Zlength xs ->
    Znth k (xs ++ x :: nil) 0 = Znth k xs 0.
Proof.
  intros xs x k Hk.
  rewrite app_Znth1; auto.
Qed.
Lemma znth_app_singleton_last__inner_transitions :
  forall xs x,
    Znth (Zlength xs) (xs ++ x :: nil) 0 = x.
Proof.
  intros xs x.
  rewrite app_Znth2 by lia.
  replace (Zlength xs - Zlength xs) with 0 by lia.
  reflexivity.
Qed.
Lemma valid_increasing_ending_singleton__inner_transitions :
  forall l i,
    0 <= i < Zlength l ->
    ValidIncreasingSubsequenceEndingAt l i (i :: nil).
Proof.
  intros l i Hi.
  unfold ValidIncreasingSubsequenceEndingAt.
  split; [exact Hi |].
  split.
  - unfold ValidIncreasingSubsequence.
    split; [lia |].
    split.
    + constructor; [lia | constructor].
    + split.
      * apply mono_inc_single.
      * unfold StrictlyIncreasingValues.
        intros p q [Hp [Hpq Hq]].
        rewrite Zlength_cons, Zlength_nil in Hq. lia.
  - exists nil. reflexivity.
Qed.
Lemma valid_increasing_ending_extend__inner_transitions :
  forall l k i idxs,
    ValidIncreasingSubsequenceEndingAt l k idxs ->
    0 <= i < Zlength l ->
    k < i ->
    Znth k l 0 < Znth i l 0 ->
    ValidIncreasingSubsequenceEndingAt l i (idxs ++ i :: nil) /\
    Zlength (idxs ++ i :: nil) = Zlength idxs + 1.
Proof.
  intros l k i idxs Hending Hi Hki Hvalues_ki.
  unfold ValidIncreasingSubsequenceEndingAt in Hending.
  destruct Hending as [Hk [Hvalid [prefix Hidxs]]].
  unfold ValidIncreasingSubsequence in Hvalid.
  destruct Hvalid as [Hlimit [Hall [Hmono Hvalues]]].
  assert (Hlen_pos : 0 < Zlength idxs).
  { rewrite Hidxs, Zlength_app_cons. pose proof (Zlength_nonneg prefix). lia. }
  assert (Hlast : Znth (Zlength idxs - 1) idxs 0 = k).
  { rewrite Hidxs, Zlength_app_cons.
    replace (Zlength prefix + 1 - 1) with (Zlength prefix) by lia.
    apply znth_app_singleton_last__inner_transitions. }
  split.
  - unfold ValidIncreasingSubsequenceEndingAt.
    split; [exact Hi |].
    split.
    + unfold ValidIncreasingSubsequence.
      split; [lia |].
      split.
      * apply Forall_app. split.
        -- eapply Forall_impl with (P := fun x => 0 <= x < k + 1).
           ++ intros x Hx. lia.
           ++ exact Hall.
        -- constructor; [lia | constructor].
      * split.
        -- unfold mono_inc in *.
           intros p q Hp Hpq Hq.
           rewrite Zlength_app_cons in Hq.
           destruct (Z_lt_ge_dec q (Zlength idxs)) as [Hq_old | Hq_last].
           ++ rewrite !znth_app_singleton_old__inner_transitions by lia.
              apply Hmono; lia.
           ++ assert (q = Zlength idxs) by lia. subst q.
              rewrite znth_app_singleton_last__inner_transitions.
              rewrite znth_app_singleton_old__inner_transitions by lia.
              pose proof
                ((proj1 (Forall_Znth (fun x => 0 <= x < k + 1) 0 idxs))
                   Hall p ltac:(lia)) as Hp_bound.
              destruct Hp_bound as [_ Hp_k].
              lia.
        -- unfold StrictlyIncreasingValues in *.
           intros p q [Hp [Hpq Hq]].
           rewrite Zlength_app_cons in Hq.
           destruct (Z_lt_ge_dec q (Zlength idxs)) as [Hq_old | Hq_last].
           ++ rewrite !znth_app_singleton_old__inner_transitions by lia.
              apply Hvalues. lia.
           ++ assert (q = Zlength idxs) by lia. subst q.
              rewrite znth_app_singleton_last__inner_transitions.
              rewrite znth_app_singleton_old__inner_transitions by lia.
              destruct (Z.eq_dec p (Zlength idxs - 1)) as [Hp_last | Hp_old].
              ** subst p. rewrite Hlast. exact Hvalues_ki.
              ** pose proof
                   (Hvalues p (Zlength idxs - 1) ltac:(lia)) as Hp_to_last.
                 rewrite Hlast in Hp_to_last. lia.
    + exists idxs. reflexivity.
  - rewrite Zlength_app_cons. reflexivity.
Qed.
Lemma valid_increasing_ending_split__inner_transitions :
  forall l i idxs,
    ValidIncreasingSubsequenceEndingAt l i idxs ->
    idxs = i :: nil \/
    exists prefix k,
      idxs = prefix ++ i :: nil /\
      ValidIncreasingSubsequenceEndingAt l k prefix /\
      k < i /\
      Znth k l 0 < Znth i l 0 /\
      Zlength idxs = Zlength prefix + 1.
Proof.
  intros l i idxs Hending.
  unfold ValidIncreasingSubsequenceEndingAt in Hending.
  destruct Hending as [Hi [Hvalid [before Hidxs]]].
  unfold ValidIncreasingSubsequence in Hvalid.
  destruct Hvalid as [Hlimit [Hall [Hmono Hvalues]]].
  destruct before as [| a rest].
  - left. simpl in Hidxs. exact Hidxs.
  - assert (Hnonempty : a :: rest <> nil) by discriminate.
    destruct (exists_last Hnonempty) as [before0 [k Hbefore]].
    assert (Hlen_pos : 0 < Zlength (a :: rest)).
    { rewrite Hbefore, Zlength_app_cons.
      pose proof (Zlength_nonneg before0). lia. }
    assert (Hlast : Znth (Zlength (a :: rest) - 1) (a :: rest) 0 = k).
    { rewrite Hbefore, Zlength_app_cons.
      replace (Zlength before0 + 1 - 1) with (Zlength before0) by lia.
      apply znth_app_singleton_last__inner_transitions. }
    rewrite Hidxs in Hall, Hmono, Hvalues.
    apply Forall_app in Hall as [Hall_before Hall_i].
    assert (Hk_bound : 0 <= k < i + 1).
    { pose proof
        ((proj1 (Forall_Znth (fun x => 0 <= x < i + 1) 0 (a :: rest)))
           Hall_before (Zlength (a :: rest) - 1) ltac:(lia)) as Hbound.
      rewrite Hlast in Hbound. exact Hbound. }
    assert (Hki : k < i).
    { unfold mono_inc in Hmono.
      pose proof
        (Hmono (Zlength (a :: rest) - 1) (Zlength (a :: rest))
          ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_app_cons; lia)) as Hord.
      rewrite znth_app_singleton_old__inner_transitions in Hord by lia.
      rewrite znth_app_singleton_last__inner_transitions in Hord.
      rewrite Hlast in Hord. exact Hord. }
    assert (Hvalues_ki : Znth k l 0 < Znth i l 0).
    { unfold StrictlyIncreasingValues in Hvalues.
      pose proof
        (Hvalues (Zlength (a :: rest) - 1) (Zlength (a :: rest))
          ltac:(rewrite Zlength_app_cons; lia)) as Hord.
      rewrite znth_app_singleton_old__inner_transitions in Hord by lia.
      rewrite znth_app_singleton_last__inner_transitions in Hord.
      rewrite Hlast in Hord. exact Hord. }
    right. exists (a :: rest), k.
    split; [exact Hidxs |].
    split.
    + unfold ValidIncreasingSubsequenceEndingAt.
      split; [lia |].
      split.
      * unfold ValidIncreasingSubsequence.
        split; [lia |].
        split.
        -- apply (proj2
             (Forall_Znth (fun x => 0 <= x < k + 1) 0 (a :: rest))).
           intros p Hp.
           pose proof
             ((proj1 (Forall_Znth (fun x => 0 <= x < i + 1) 0 (a :: rest)))
                Hall_before p Hp) as Hp_bound.
           destruct Hp_bound as [Hp_nonneg Hp_before_i].
           destruct (Z.eq_dec p (Zlength (a :: rest) - 1))
             as [Hp_last | Hp_old].
           ++ subst p. rewrite Hlast. lia.
           ++ assert (p < Zlength (a :: rest) - 1) by lia.
              unfold mono_inc in Hmono.
              pose proof
                (Hmono p (Zlength (a :: rest) - 1)
                  ltac:(lia) ltac:(lia)
                  ltac:(rewrite Zlength_app_cons; lia)) as Hp_to_last.
              rewrite !znth_app_singleton_old__inner_transitions in Hp_to_last
                by lia.
              rewrite Hlast in Hp_to_last.
              split; [exact Hp_nonneg | lia].
        -- split.
           ++ unfold mono_inc in *.
              intros p q Hp Hpq Hq.
              specialize (Hmono p q Hp Hpq ltac:(rewrite Zlength_app_cons; lia)).
              rewrite !znth_app_singleton_old__inner_transitions in Hmono by lia.
              exact Hmono.
           ++ unfold StrictlyIncreasingValues in *.
              intros p q Hpq.
              specialize (Hvalues p q ltac:(rewrite Zlength_app_cons; lia)).
              rewrite !znth_app_singleton_old__inner_transitions in Hvalues by lia.
              exact Hvalues.
      * exists before0. exact Hbefore.
    + split; [exact Hki |].
      split; [exact Hvalues_ki |].
      rewrite Hidxs, Zlength_app_cons. reflexivity.
Qed.
Lemma lis_inner_progress_complete__inner_transitions :
  forall l dp i,
    LISInnerProgress l dp i i ->
    LISDPTablePrefix l dp (i + 1).
Proof.
  intros l dp i Hprogress.
  unfold LISInnerProgress in Hprogress.
  destruct Hprogress as
    [Hi [Hscan [Hlen [Hprefix [Hcandidate_max Hcurrent_bounds]]]]].
  assert (Hcandidate_to_valid :
    forall candidate,
      LISDPInnerCandidate l dp i i candidate ->
      exists idxs,
        ValidIncreasingSubsequenceEndingAt l i idxs /\
        Zlength idxs = candidate).
  {
    intros candidate Hcandidate.
    unfold LISDPInnerCandidate in Hcandidate.
    destruct Hcandidate as [Hone | [k [Hk [Hvalues Hcandidate]]]].
    - subst candidate. exists (i :: nil). split.
      + apply valid_increasing_ending_singleton__inner_transitions. exact Hi.
      + rewrite Zlength_cons, Zlength_nil. lia.
    - specialize (Hprefix k Hk) as [Hending_k Hbounds_k].
      unfold LISEndingAtLength,
        MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hending_k.
      destruct Hending_k as
        [idxs [[Hvalid_k Hupper_k] Hidxs_len]].
      destruct
        (valid_increasing_ending_extend__inner_transitions
          l k i idxs Hvalid_k Hi ltac:(lia) Hvalues)
        as [Hvalid_i Hlen_snoc].
      exists (idxs ++ i :: nil). split; [exact Hvalid_i |].
      lia.
  }
  assert (Hvalid_to_candidate_bound :
    forall idxs,
      ValidIncreasingSubsequenceEndingAt l i idxs ->
      exists candidate,
        LISDPInnerCandidate l dp i i candidate /\
        Zlength idxs <= candidate).
  {
    intros idxs Hvalid.
    destruct (valid_increasing_ending_split__inner_transitions l i idxs Hvalid)
      as [Hsingle |
          [prefix [k [Hidxs [Hvalid_k [Hki [Hvalues Hidxs_len]]]]]]].
    - exists 1. split.
      + left. reflexivity.
      + rewrite Hsingle, Zlength_cons, Zlength_nil. lia.
    - pose proof Hvalid_k as Hvalid_k_bounds.
      unfold ValidIncreasingSubsequenceEndingAt in Hvalid_k_bounds.
      destruct Hvalid_k_bounds as [Hk_in_l Hvalid_k_rest].
      assert (Hk_nonneg : 0 <= k) by lia.
      specialize (Hprefix k (conj Hk_nonneg Hki))
        as [Hending_k Hbounds_k].
      unfold LISEndingAtLength,
        MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hending_k.
      destruct Hending_k as
        [best_idxs [[Hbest_valid Hbest_upper] Hbest_len]].
      specialize (Hbest_upper prefix Hvalid_k).
      exists (Znth k dp 0 + 1). split.
      + right. exists k. split; [lia |].
        split; [exact Hvalues | reflexivity].
      + lia.
  }
  assert (Hending_i : LISEndingAtLength l i (Znth i dp 0)).
  {
    unfold LISEndingAtLength,
      MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hcandidate_max as
      [best_candidate [[Hbest_candidate Hbest_upper] Hbest_eq]].
    destruct (Hcandidate_to_valid best_candidate Hbest_candidate)
      as [best_idxs [Hbest_valid Hbest_len]].
    exists best_idxs. split.
    - split; [exact Hbest_valid |].
      intros idxs Hvalid.
      destruct (Hvalid_to_candidate_bound idxs Hvalid)
        as [candidate [Hcandidate Hlen_bound]].
      specialize (Hbest_upper candidate Hcandidate).
      lia.
    - lia.
  }
  unfold LISDPTablePrefix.
  split; [lia |].
  split; [exact Hlen |].
  intros k Hk.
  destruct (Z_lt_ge_dec k i) as [Hk_old | Hk_last].
  - apply Hprefix. lia.
  - assert (k = i) by lia. subst k.
    split; [exact Hending_i | exact Hcurrent_bounds].
Qed.
Lemma lis_dp_table_entry_bounds__outer_best_update :
  forall l dp hi k,
    LISDPTablePrefix l dp hi ->
    0 <= k < hi ->
    LISEndingAtLength l k (Znth k dp 0) /\
    1 <= Znth k dp 0 <= k + 1.
Proof.
  intros l dp hi k Htable Hk.
  unfold LISDPTablePrefix in Htable.
  destruct Htable as [_ [_ Hentries]].
  apply Hentries. exact Hk.
Qed.
Lemma lis_valid_subsequence_extend_limit__outer_best_update :
  forall l old new idxs,
    old <= new ->
    new <= Zlength l ->
    ValidIncreasingSubsequence l old idxs ->
    ValidIncreasingSubsequence l new idxs.
Proof.
  intros l old new idxs Hold_new Hnew Hvalid.
  unfold ValidIncreasingSubsequence in *.
  destruct Hvalid as [Hold [Hall [Hmono Hvalues]]].
  repeat split; try lia; auto.
  eapply Forall_impl with (P := fun idx => 0 <= idx < old); [| exact Hall].
  intros idx Hidx. lia.
Qed.
Lemma lis_valid_prefix_step_cases__outer_best_update :
  forall l i idxs,
    0 <= i < Zlength l ->
    ValidIncreasingSubsequence l (i + 1) idxs ->
    ValidIncreasingSubsequence l i idxs \/
    ValidIncreasingSubsequenceEndingAt l i idxs.
Proof.
  intros l i idxs Hi Hvalid.
  destruct idxs as [| first rest].
  - left.
    unfold ValidIncreasingSubsequence.
    repeat split; try lia.
    + constructor.
    + apply mono_inc_nil.
    + unfold StrictlyIncreasingValues.
      intros p q [Hp [Hpq Hq]].
      rewrite Zlength_nil in Hq. lia.
  - assert (Hnonempty : first :: rest <> nil) by discriminate.
    destruct (exists_last Hnonempty) as [prefix [last Hidxs]].
    rewrite Hidxs in Hvalid.
    pose proof Hvalid as Hparts.
    unfold ValidIncreasingSubsequence in Hparts.
    destruct Hparts as [Hlimit [Hall [Hmono Hvalues]]].
    rewrite Forall_app in Hall.
    destruct Hall as [Hall_prefix Hall_last].
    inversion Hall_last as [| ? ? Hlast_bound _]; subst.
    pose proof (proj1 (mono_inc_iff_ind _) Hmono) as Hmono_ind.
    pose proof
      (proj1 (mono_inc_ind_app prefix (last :: nil)) Hmono_ind)
      as [Hprefix_mono_ind [_ Hcross]].
    destruct (Z_lt_ge_dec last i) as [Hlast_lt | Hlast_ge].
    + left.
      rewrite Hidxs.
      unfold ValidIncreasingSubsequence.
      repeat split; try lia.
      * apply Forall_app. split.
        -- apply Forall_forall.
           intros idx Hin.
           pose proof Hall_prefix as Hall_prefix_forall.
           rewrite Forall_forall in Hall_prefix_forall.
           specialize (Hall_prefix_forall idx Hin).
           assert (Hidx_last : idx < last).
           { eapply Hcross; [exact Hin |]. simpl. auto. }
           lia.
        -- constructor; [lia | constructor].
      * exact Hmono.
      * exact Hvalues.
    + assert (Hlast_i : last = i) by lia.
      subst last.
      right.
      rewrite Hidxs.
      unfold ValidIncreasingSubsequenceEndingAt.
      split; [exact Hi |].
      split; [exact Hvalid |].
      exists prefix. reflexivity.
Qed.
Lemma lis_prefix_empty__outer_best_update :
  forall l,
    LISPrefix l 0 0.
Proof.
  intros l.
  unfold LISPrefix, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset.
  exists (@nil Z).
  split.
  - split.
    + unfold ValidIncreasingSubsequence.
      pose proof (Zlength_nonneg l) as Hlen_nonneg.
      repeat split; try lia.
      * constructor.
      * apply mono_inc_nil.
      * unfold StrictlyIncreasingValues.
        intros p q [Hp [Hpq Hq]].
        rewrite Zlength_nil in Hq. lia.
    + intros idxs Hvalid.
      unfold ValidIncreasingSubsequence in Hvalid.
      destruct Hvalid as [_ [Hall _]].
      destruct idxs as [| idx idxs].
      * rewrite Zlength_nil. lia.
      * inversion Hall. lia.
  - rewrite Zlength_nil. reflexivity.
Qed.
Lemma lis_prefix_step_max__outer_best_update :
  forall l i old current,
    0 <= i < Zlength l ->
    LISPrefix l i old ->
    LISEndingAtLength l i current ->
    LISPrefix l (i + 1) (Z.max old current).
Proof.
  intros l i old current Hi Hold Hcurrent.
  unfold LISPrefix, LISEndingAtLength,
    MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
  destruct Hold as [old_idxs [[Hold_valid Hold_bound] Hold_len]].
  destruct Hcurrent as
    [current_idxs [[Hcurrent_ending Hcurrent_bound] Hcurrent_len]].
  destruct Hcurrent_ending as [_ [Hcurrent_valid _]].
  destruct (Z_le_gt_dec old current) as [Hold_current | Hcurrent_old].
  - exists current_idxs.
    split.
    + split; [exact Hcurrent_valid |].
      intros idxs Hvalid.
      rewrite Hcurrent_len.
      destruct
        (lis_valid_prefix_step_cases__outer_best_update l i idxs Hi Hvalid)
        as [Hvalid_old | Hvalid_current].
      * specialize (Hold_bound idxs Hvalid_old).
        lia.
      * specialize (Hcurrent_bound idxs Hvalid_current).
        lia.
    + rewrite Hcurrent_len, Z.max_r by lia. reflexivity.
  - exists old_idxs.
    split.
    + split.
      * eapply lis_valid_subsequence_extend_limit__outer_best_update
          with (old := i); eauto; lia.
      * intros idxs Hvalid.
        rewrite Hold_len.
        destruct
          (lis_valid_prefix_step_cases__outer_best_update l i idxs Hi Hvalid)
          as [Hvalid_old | Hvalid_current].
        -- specialize (Hold_bound idxs Hvalid_old).
           lia.
        -- specialize (Hcurrent_bound idxs Hvalid_current).
           lia.
    + rewrite Hold_len, Z.max_l by lia. reflexivity.
Qed.
Lemma lis_best_so_far_step__outer_best_update :
  forall l i old current,
    0 <= i < Zlength l ->
    LISPrefix l i old ->
    LISEndingAtLength l i current ->
    LISBestSoFar l (i + 1) (Z.max old current).
Proof.
  intros l i old current Hi Hold Hcurrent.
  unfold LISBestSoFar.
  split; [lia |].
  right. split; [lia |].
  eapply lis_prefix_step_max__outer_best_update; eauto.
Qed.
Lemma lis_best_so_far_full_implies_length__final_result :
  forall (l : list Z) (limit ans : Z),
    0 < limit ->
    Zlength l = limit ->
    LISBestSoFar l limit ans ->
    LISLength l ans.
Proof.
  intros l limit ans Hpositive Hlength Hbest.
  unfold LISBestSoFar in Hbest.
  destruct Hbest as [_ [[Hzero _] | [_ Hprefix]]].
  - lia.
  - unfold LISLength.
    rewrite Hlength.
    exact Hprefix.
Qed.
