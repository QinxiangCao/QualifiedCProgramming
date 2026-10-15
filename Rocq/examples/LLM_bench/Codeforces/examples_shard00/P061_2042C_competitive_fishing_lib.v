Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition FishingScore (f cuts : list Z) (score : Z) : Prop :=
  2 <= Zlength cuts /\ Znth 0 cuts 0 = 0 /\
  Znth (Zlength cuts - 1) cuts 0 = Zlength f /\
  mono_inc cuts /\
  score = fold_right Z.add 0
    (Zmap_range (fun g =>
      g * fold_right Z.add 0
        (map (fun i => if Z.eqb (Znth i f 48) 49 then 1 else -1)
          (Zrange (Znth g cuts 0) (Znth (g + 1) cuts 0))))
      (Zlength cuts - 1)).

Definition Pre (k : Z) (f : list Z) : Prop :=
  2 <= Zlength f <= 200000 /\ 1 <= k <= 1000000000 /\
  (* Character codes: '0' = 48, '1' = 49. *)
  Forall (fun c => c = 48 \/ c = 49) f.

Definition Spec (k : Z) (f : list Z) (out : Z) : Prop :=
  (out = -1 /\ forall candidate : list Z * Z,
    ~ (FishingScore f (fst candidate) (snd candidate) /\ snd candidate >= k)) \/
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      FishingScore f (fst candidate) (snd candidate) /\ snd candidate >= k)
    (fun candidate => Zlength (fst candidate) - 1) out.

Definition FishingValue (c : Z) : Z :=
  if Z.eqb c 49 then 1 else -1.

Definition SuffixGain (f : list Z) (cut : Z) : Z :=
  fold_right Z.add 0
    (map FishingValue (sublist cut (Zlength f) f)).

Definition FishingGains (f : list Z) : list Z :=
  map (SuffixGain f) (Zrange 1 (Zlength f)).

Definition GainBuildState
    (f : list Z) (next : Z) (built : list Z) (current : Z) : Prop :=
  built = sublist next (Zlength f - 1) (FishingGains f) /\
  current = SuffixGain f next.

Definition PreparedGains (f gains : list Z) : Prop :=
  Permutation (FishingGains f) gains /\ ListLib.decreasing gains.

Definition GainSearchState
    (k : Z) (gains : list Z) (next prefix_sum : Z) : Prop :=
  prefix_sum = fold_right Z.add 0 (sublist 0 next gains) /\
  forall count,
    0 <= count <= next ->
    fold_right Z.add 0 (sublist 0 count gains) < k.

Definition FishingSearchResult
    (k : Z) (f gains : list Z) (out : Z) : Prop :=
  (out = -1 /\
   forall count,
     0 <= count <= Zlength gains ->
     fold_right Z.add 0 (sublist 0 count gains) < k) \/
  (2 <= out <= Zlength f /\
   k <= fold_right Z.add 0 (sublist 0 (out - 1) gains) /\
   forall count,
     0 <= count < out - 1 ->
     fold_right Z.add 0 (sublist 0 count gains) < k).

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.micromega.Psatz.
Lemma Zlength_map__gain_construction : forall {A B : Type}
    (g : A -> B) xs,
  Zlength (map g xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__gain_construction : forall {A B : Type}
    (g : A -> B) xs (da : A) (db : B) i,
  0 <= i < Zlength xs ->
  Znth i (map g xs) db = g (Znth i xs da).
Proof.
  intros A B g xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_Zrange_aux__gain_construction : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__gain_construction : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__gain_construction. lia.
Qed.
Lemma Znth_Zrange_aux__gain_construction : forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__gain_construction : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__gain_construction by lia. lia.
Qed.
Lemma fishing_gains_length__gain_construction : forall f,
  2 <= Zlength f ->
  Zlength (FishingGains f) = Zlength f - 1.
Proof.
  intros f Hlen. unfold FishingGains.
  rewrite Zlength_map__gain_construction.
  apply Zlength_Zrange__gain_construction. lia.
Qed.
Lemma fishing_gains_Znth__gain_construction : forall f i,
  0 <= i < Zlength f - 1 ->
  Znth i (FishingGains f) 0 = SuffixGain f (i + 1).
Proof.
  intros f i Hi. unfold FishingGains.
  rewrite (@Znth_map__gain_construction Z Z (SuffixGain f)
    (Zrange 1 (Zlength f)) 0 0 i).
  - rewrite Znth_Zrange__gain_construction by lia.
    replace (1 + i) with (i + 1) by lia. reflexivity.
  - rewrite Zlength_Zrange__gain_construction by lia. lia.
Qed.
Lemma suffix_gain_step__gain_construction : forall f i,
  0 <= i < Zlength f ->
  SuffixGain f i =
    FishingValue (Znth i f 48) + SuffixGain f (i + 1).
Proof.
  intros f i Hi. unfold SuffixGain.
  rewrite (sublist_split i (Zlength f) (i + 1) f) by lia.
  rewrite map_app, fold_right_app.
  pose proof (sublist_single 48 i f Hi) as Hsingle.
  rewrite Hsingle. simpl. reflexivity.
Qed.
Lemma suffix_gain_span_bounds__gain_construction : forall f cut,
  0 <= cut <= Zlength f ->
  (forall j, 0 <= j < Zlength f ->
    Znth j f 0 = 48 \/ Znth j f 0 = 49) ->
  -(Zlength f - cut) <= SuffixGain f cut <= Zlength f - cut.
Proof.
  intros f cut Hcut Hchars. unfold SuffixGain.
  pose proof (list_sum_map_as_Z_range_sum 0 FishingValue
    (sublist cut (Zlength f) f)) as Hsum.
  unfold ListLib.sum in Hsum. rewrite Hsum.
  assert (Hsublen : Zlength (sublist cut (Zlength f) f) =
    Zlength f - cut).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hvalue : forall i,
    0 <= i < Zlength (sublist cut (Zlength f) f) ->
    -1 <= FishingValue
      (Znth i (sublist cut (Zlength f) f) 0) <= 1).
  {
    intros i Hi.
    rewrite Znth_sublist by (rewrite Hsublen in Hi; lia).
    specialize (Hchars (i + cut) ltac:(
      rewrite Zlength_sublist in Hi by lia; lia)).
    destruct Hchars as [Hzero | Hone];
      unfold FishingValue; rewrite Hzero || rewrite Hone; simpl; lia.
  }
  pose proof (sum_Z_range_bounds 0
    (Zlength (sublist cut (Zlength f) f))
    (fun i => FishingValue
      (Znth i (sublist cut (Zlength f) f) 0))
    (-1) 1 ltac:(lia) Hvalue) as Hbounds.
  rewrite Hsublen in Hbounds.
  replace ((Zlength f - cut - 0) * -1) with
    (-(Zlength f - cut)) in Hbounds by lia.
  replace ((Zlength f - cut - 0) * 1) with
    (Zlength f - cut) in Hbounds by lia.
  rewrite Hsublen.
  exact Hbounds.
Qed.
Lemma gain_build_state_step__gain_construction : forall f i tail current,
  0 <= i < Zlength f - 1 ->
  GainBuildState f (i + 1) tail current ->
  GainBuildState f i (current :: tail)
    (current + FishingValue (Znth i f 48)).
Proof.
  intros f i tail current Hi Hstate.
  unfold GainBuildState in *. destruct Hstate as [Htail Hcurrent].
  split.
  - rewrite (sublist_split i (Zlength f - 1) (i + 1)
      (FishingGains f)) by
      (try rewrite fishing_gains_length__gain_construction by lia; lia).
    pose proof (sublist_single 0 i (FishingGains f) ltac:(
      try rewrite fishing_gains_length__gain_construction by lia; lia)) as Hsingle.
    rewrite Hsingle, fishing_gains_Znth__gain_construction by lia.
    simpl. rewrite Hcurrent, Htail. reflexivity.
  - rewrite suffix_gain_step__gain_construction by lia.
    rewrite <- Hcurrent. lia.
Qed.
Lemma gain_build_state_zero__gain_construction : forall f built current,
  2 <= Zlength f ->
  GainBuildState f 0 built current ->
  built = FishingGains f.
Proof.
  intros f built current Hlen [Hbuilt _]. rewrite Hbuilt.
  apply sublist_self.
  symmetry. apply fishing_gains_length__gain_construction. exact Hlen.
Qed.
Lemma suffix_gain_bounds__gain_construction : forall f,
  (forall j, 0 <= j < Zlength f ->
    Znth j f 0 = 48 \/ Znth j f 0 = 49) ->
  forall i, 0 <= i < Zlength f - 1 ->
    -Zlength f <= Znth i (FishingGains f) 0 <= Zlength f.
Proof.
  intros f Hchars i Hi.
  rewrite fishing_gains_Znth__gain_construction by exact Hi.
  pose proof (suffix_gain_span_bounds__gain_construction f (i + 1)
    ltac:(lia) Hchars) as Hbounds.
  lia.
Qed.
Lemma permutation_preserves_Znth_bounds__gain_construction :
  forall src dst lo hi,
  Permutation src dst ->
  (forall i, 0 <= i < Zlength src -> lo <= Znth i src 0 <= hi) ->
  forall j, 0 <= j < Zlength dst -> lo <= Znth j dst 0 <= hi.
Proof.
  intros src dst lo hi Hperm Hbounds.
  assert (Hsrc : Forall (fun x => lo <= x <= hi) src).
  { apply (proj2 (Forall_Znth (fun x => lo <= x <= hi) 0 src)).
    exact Hbounds. }
  assert (Hdst : Forall (fun x => lo <= x <= hi) dst).
  { eapply Permutation_Forall; eauto. }
  apply (proj1 (Forall_Znth (fun x => lo <= x <= hi) 0 dst)).
  exact Hdst.
Qed.
Lemma fold_sublist_snoc__gain_search :
  forall (xs : list Z) i,
    0 <= i < Zlength xs ->
    fold_right Z.add 0 (sublist 0 (i + 1) xs) =
      fold_right Z.add 0 (sublist 0 i xs) + Znth i xs 0.
Proof.
  intros xs i Hi.
  change (ListLib.sum (sublist 0 (i + 1) xs) =
    ListLib.sum (sublist 0 i xs) + Znth i xs 0).
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single 0 i xs) by lia.
  rewrite ListLib.sum_app.
  simpl.
  lia.
Qed.
Lemma fold_right_add_lower__gain_search :
  forall (xs : list Z) lower,
    Forall (fun x => lower <= x) xs ->
    lower * Zlength xs <= fold_right Z.add 0 xs.
Proof.
  intros xs lower Hbound.
  induction Hbound.
  - rewrite Zlength_nil.
    simpl.
    lia.
  - rewrite Zlength_cons.
    simpl fold_right.
    replace (lower * (1 + Zlength l)) with
      (lower * Zlength l + lower) by ring.
    lia.
Qed.
Lemma bounded_prefix_sum_lower__gain_search :
  forall (xs : list Z) n count,
    2 <= n <= 200000 ->
    Zlength xs = n - 1 ->
    (forall j, 0 <= j < n - 1 -> -n <= Znth j xs 0) ->
    0 <= count <= n - 1 ->
    -40000000000 <= fold_right Z.add 0 (sublist 0 count xs).
Proof.
  intros xs n count Hn Hlen Hbound Hcount.
  assert (Hprefix_len : Zlength (sublist 0 count xs) = count).
  { rewrite Zlength_sublist; lia. }
  assert (Hprefix_bound :
    Forall (fun x => -n <= x) (sublist 0 count xs)).
  { apply (proj2 (Forall_Znth (fun x => -n <= x) 0 _)).
    intros j Hj.
    rewrite Znth_sublist by lia.
    apply Hbound.
    lia. }
  pose proof (fold_right_add_lower__gain_search
    (sublist 0 count xs) (-n) Hprefix_bound) as Hsum.
  rewrite Hprefix_len in Hsum.
  nia.
Qed.
Lemma Zlength_map__final_result : forall {A B : Type} (f : A -> B) xs,
  Zlength (map f xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma permutation_Zlength__final_result : forall {A : Type} (xs ys : list A),
  Permutation xs ys -> Zlength xs = Zlength ys.
Proof.
  intros A xs ys H. rewrite !Zlength_correct, (Permutation_length H).
  reflexivity.
Qed.
Lemma Znth_map__final_result : forall {A B : Type} (f : A -> B) xs
    (da : A) (db : B) i,
  0 <= i < Zlength xs ->
  Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Znth_In__final_result : forall {A : Type} (xs : list A) d i,
  0 <= i < Zlength xs -> In (Znth i xs d) xs.
Proof.
  intros A xs d i Hi. unfold Znth. apply nth_In.
  rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Zlength_Zrange_aux__final_result : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__final_result : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__final_result. lia.
Qed.
Lemma Znth_Zrange_aux__final_result : forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__final_result : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__final_result by lia. lia.
Qed.
Lemma map_Znth_Zrange__final_result : forall {A : Type} (xs : list A) d,
  map (fun i => Znth i xs d) (Zrange 0 (Zlength xs)) = xs.
Proof.
  intros A xs d. apply (proj2 (list_eq_ext _ _ d)). split.
  - rewrite Zlength_map__final_result,
      Zlength_Zrange__final_result by apply Zlength_nonneg. lia.
  - intros i Hi.
    rewrite Zlength_map__final_result,
      Zlength_Zrange__final_result in Hi by apply Zlength_nonneg.
    rewrite (@Znth_map__final_result Z A
      (fun j => Znth j xs d) (Zrange 0 (Zlength xs)) 0 d i) by
      (rewrite Zlength_Zrange__final_result by apply Zlength_nonneg; lia).
    rewrite Znth_Zrange__final_result by (pose proof (Zlength_nonneg xs); lia).
    f_equal.
Qed.
Lemma sum_permutation__final_result : forall xs ys : list Z,
  Permutation xs ys -> ListLib.sum xs = ListLib.sum ys.
Proof.
  intros xs ys Hperm. induction Hperm; simpl; lia.
Qed.
Lemma filter_members_firstn__final_result : forall {A : Type}
    (xs : list A) k,
  NoDup xs ->
  Permutation
    (filter (fun x => if prop_dec (In x (firstn k xs)) then true else false) xs)
    (firstn k xs).
Proof.
  intros A xs k Hnd. apply NoDup_Permutation.
  - apply NoDup_filter. exact Hnd.
  - apply (NoDup_app_remove_r (firstn k xs) (skipn k xs)).
    rewrite firstn_skipn. exact Hnd.
  - intros x. rewrite filter_In. split.
    + intros [_ Htest]. destruct (prop_dec (In x (firstn k xs))) as [Hin|Hnot];
        [exact Hin|discriminate].
    + intros Hin. split.
      * rewrite <- (firstn_skipn k xs). apply in_or_app. left. exact Hin.
      * destruct (prop_dec (In x (firstn k xs))) as [_|Hnot];
          [reflexivity|contradiction].
Qed.
Lemma firstn_shift_upper__final_result : forall x xs n,
  Forall (fun y : Z => y <= x) xs ->
  (n < length xs)%nat ->
  ListLib.sum (firstn (S n) xs) <=
  x + ListLib.sum (firstn n xs).
Proof.
  intros x xs. induction xs as [|y ys IH]; intros n Hall Hn.
  - simpl in Hn. exfalso. exact (Nat.nlt_0_r n Hn).
  - inversion Hall as [|? ? Hy Hys]; subst. destruct n as [|n].
    + simpl. lia.
    + simpl in Hn. apply Nat.succ_lt_mono in Hn.
      simpl. specialize (IH n Hys Hn).
      replace (x + (y + ListLib.sum (firstn n ys))) with
        (y + (x + ListLib.sum (firstn n ys))) by ring.
      apply Z.add_le_mono_l. exact IH.
Qed.
Lemma decreasing_filter_sum_le_prefix__final_result :
  forall {A : Type} (f : A -> Z) (test : A -> bool) xs,
    ListLib.decreasing (map f xs) ->
    ListLib.sum (map f (filter test xs)) <=
    ListLib.sum (firstn (length (filter test xs)) (map f xs)).
Proof.
  intros A f test xs. induction xs as [|x xs IH]; intros Hdec; simpl.
  - lia.
  - pose proof (proj2 (mono_noninc_iff_decreasing (f x :: map f xs)) Hdec)
      as Hmono.
    apply mono_noninc_cons in Hmono as [Hhead Htail].
    pose proof (proj1 (mono_noninc_iff_decreasing (map f xs)) Htail)
      as Hdec_tail.
    specialize (IH Hdec_tail).
    destruct (test x) eqn:Htest; simpl.
    + lia.
    + destruct (filter test xs) as [|y ys] eqn:Hfilter; simpl in *; [lia|].
      assert (Hlen : (length ys < length (map f xs))%nat).
      { rewrite length_map. change (S (length ys) <= length xs)%nat.
        replace (S (length ys)) with (length (filter test xs)) by
          (rewrite Hfilter; reflexivity).
        pose proof (filter_length test xs). lia. }
      pose proof (firstn_shift_upper__final_result
        (f x) (map f xs) (length ys) Hhead Hlen) as Hshift.
      eapply Z.le_trans; [exact IH | exact Hshift].
Qed.
Lemma Zlength_firstn_to_nat__final_result : forall {A : Type}
    (xs : list A) k,
  0 <= k <= Zlength xs ->
  Zlength (firstn (Z.to_nat k) xs) = k.
Proof.
  intros A xs k Hk. rewrite !Zlength_correct, length_firstn.
  rewrite Nat.min_l.
  - apply Z2Nat.id. lia.
  - rewrite Zlength_correct in Hk.
    rewrite <- (Nat2Z.id (length xs)). apply Z2Nat.inj_le; lia.
Qed.
Lemma sublist_zero_as_firstn__final_result : forall {A : Type}
    (xs : list A) k,
  sublist 0 k xs = firstn (Z.to_nat k) xs.
Proof.
  intros. unfold sublist. simpl. reflexivity.
Qed.
Lemma sum_sublist_snoc__final_result : forall (xs : list Z) i,
  0 <= i < Zlength xs ->
  ListLib.sum (sublist 0 (i + 1) xs) =
  ListLib.sum (sublist 0 i xs) + Znth i xs 0.
Proof.
  intros xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single 0 i xs) by lia.
  rewrite ListLib.sum_app. simpl. lia.
Qed.
Lemma map_sublist__final_result : forall {A B : Type}
    (fn : A -> B) xs lo hi,
  map fn (sublist lo hi xs) = sublist lo hi (map fn xs).
Proof.
  intros A B fn xs lo hi. unfold sublist.
  rewrite firstn_map, skipn_map. reflexivity.
Qed.
Lemma fishing_segment_as_sublist__final_result : forall f lo hi,
  0 <= lo <= hi -> hi <= Zlength f ->
  fold_right Z.add 0
    (map (fun idx =>
      if Z.eqb (Znth idx f 48) 49 then 1 else -1)
      (Zrange lo hi)) =
  ListLib.sum (map FishingValue (sublist lo hi f)).
Proof.
  intros f lo hi Hlo Hhi.
  rewrite map_sublist__final_result.
  rewrite list_sum_sublist_as_Z_range_sum.
  2: lia.
  2: rewrite Zlength_map__final_result; lia.
  rewrite sum_range_unfold.
  remember (Zrange lo hi) as idxs eqn:Hidxs.
  assert (Hbounds : forall idx, In idx idxs -> lo <= idx < hi).
  { intros idx Hin. rewrite Hidxs in Hin. apply In_Zrange. exact Hin. }
  clear Hidxs. induction idxs as [|idx idxs IH]; simpl.
  - reflexivity.
  - rewrite Znth_map__final_result with (da := 48) by
      (specialize (Hbounds idx ltac:(left; reflexivity)); lia).
    unfold FishingValue. f_equal.
    apply IH. intros j Hj. apply Hbounds. right. exact Hj.
Qed.
Lemma suffix_gain_split__final_result : forall f lo mid,
  0 <= lo <= mid -> mid <= Zlength f ->
  SuffixGain f lo =
  ListLib.sum (map FishingValue (sublist lo mid f)) +
  SuffixGain f mid.
Proof.
  intros f lo mid Hlo Hmid. unfold SuffixGain.
  rewrite (sublist_split lo (Zlength f) mid f) by
    (pose proof (Zlength_nonneg f); lia).
  rewrite map_app, ListLib.sum_app. reflexivity.
Qed.
Lemma fold_right_add_map__final_result : forall {A : Type}
    (fn : A -> Z) xs,
  fold_right Z.add 0 (map fn xs) =
  fold_right (fun x acc => fn x + acc) 0 xs.
Proof.
  intros A fn xs. induction xs; simpl; [reflexivity|].
  rewrite IHxs. reflexivity.
Qed.
Lemma fold_Zrange_aux_one_shift__final_result : forall n f,
  fold_right (fun x acc => f x + acc) 0 (Zrange_aux 1 n) =
  fold_right (fun x acc => f (x + 1) + acc) 0 (Zrange_aux 0 n).
Proof.
  intros n f. replace 1 with (0 + 1) by lia.
  apply fold_Zrange_aux_shift.
Qed.
Lemma weighted_segments_cons__final_result : forall f a b rest w,
  fold_right Z.add 0
    (Zmap_range (fun g =>
      (w + g) * fold_right Z.add 0
        (map (fun idx =>
          if Z.eqb (Znth idx f 48) 49 then 1 else -1)
          (Zrange (Znth g (a :: b :: rest) 0)
                  (Znth (g + 1) (a :: b :: rest) 0))))
      (Zlength (a :: b :: rest) - 1)) =
  w * fold_right Z.add 0
        (map (fun idx =>
          if Z.eqb (Znth idx f 48) 49 then 1 else -1)
          (Zrange a b)) +
  fold_right Z.add 0
    (Zmap_range (fun g =>
      (w + 1 + g) * fold_right Z.add 0
        (map (fun idx =>
          if Z.eqb (Znth idx f 48) 49 then 1 else -1)
          (Zrange (Znth g (b :: rest) 0)
                  (Znth (g + 1) (b :: rest) 0))))
      (Zlength (b :: rest) - 1)).
Proof.
  intros f a b rest w.
  unfold Zmap_range, Zrange.
  rewrite Zlength_cons.
  replace
    (Z.to_nat (Z.succ (Zlength (b :: rest)) - 1 - 0))
    with (S (Z.to_nat (Zlength (b :: rest) - 1 - 0))) by
    (rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia).
  simpl.
  rewrite Znth0_cons, Znth_cons by lia.
  replace (1 - 1) with 0 by lia. rewrite Znth0_cons.
  repeat rewrite fold_right_add_map__final_result.
  rewrite fold_Zrange_aux_one_shift__final_result.
  f_equal.
  - ring.
  - apply fold_Zsum_ext_in. intros g Hg.
    rewrite !Znth_cons by (pose proof (In_Zrange_aux_lb _ _ _ Hg); lia).
    replace (g + 1 - 1) with g by lia.
    replace (g + 1 + 1 - 1) with (g + 1) by lia.
    rewrite (Znth_cons 0 (g + 1 + 1) a (b :: rest)) by
      (pose proof (In_Zrange_aux_lb _ _ _ Hg); lia).
    replace (g + 1 + 1 - 1) with (g + 1) by lia.
    replace (w + (g + 1)) with (w + 1 + g) by lia.
    reflexivity.
Qed.
Lemma suffix_gain_at_end__final_result : forall f,
  SuffixGain f (Zlength f) = 0.
Proof.
  intros f. unfold SuffixGain, sublist.
  rewrite Zlength_correct, Nat2Z.id, firstn_all, skipn_all.
  reflexivity.
Qed.
Lemma mono_inc_tail__final_result : forall a tail,
  mono_inc (a :: tail) -> mono_inc tail.
Proof.
  intros a tail H. apply (proj1 (mono_inc_cons a tail)) in H.
  tauto.
Qed.
Lemma last_of_cons_tail__final_result : forall a b rest,
  Znth (Zlength (a :: b :: rest) - 1) (a :: b :: rest) 0 =
  Znth (Zlength (b :: rest) - 1) (b :: rest) 0.
Proof.
  intros a b rest. rewrite Zlength_cons.
  rewrite Znth_cons by (rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia).
  f_equal. lia.
Qed.
Lemma internal_cuts_cons__final_result : forall (a b c : Z) (rest : list Z),
  sublist 1 (Zlength (a :: b :: c :: rest) - 1) (a :: b :: c :: rest) =
  b :: sublist 1 (Zlength (b :: c :: rest) - 1) (b :: c :: rest).
Proof.
  intros a b c rest.
  unfold sublist. rewrite !Zlength_cons.
  pose proof (Zlength_nonneg rest).
  replace (Z.to_nat (Z.succ (Z.succ (Z.succ (Zlength rest))) - 1))
    with (S (S (Z.to_nat (Zlength rest)))) by lia.
  replace (Z.to_nat (Z.succ (Z.succ (Zlength rest)) - 1))
    with (S (Z.to_nat (Zlength rest))) by lia.
  simpl. reflexivity.
Qed.
Lemma internal_cuts_pair__final_result : forall (a b : Z),
  sublist 1 (Zlength (a :: b :: nil) - 1) (a :: b :: nil) = nil.
Proof.
  intros a b. unfold sublist. simpl. reflexivity.
Qed.
Lemma weighted_segments_single__final_result : forall f b w,
  fold_right Z.add 0
    (Zmap_range (fun g =>
      (w + g) * fold_right Z.add 0
        (map (fun idx =>
          if Z.eqb (Znth idx f 48) 49 then 1 else -1)
          (Zrange (Znth g (b :: nil) 0)
                  (Znth (g + 1) (b :: nil) 0))))
      (Zlength (b :: nil) - 1)) = 0.
Proof.
  intros f b w. unfold Zmap_range, Zrange.
  rewrite Zlength_cons, Zlength_nil. simpl. reflexivity.
Qed.
Lemma fishing_score_internal_cuts__final_result : forall f cuts score,
  FishingScore f cuts score ->
  score = ListLib.sum
    (map (SuffixGain f)
      (sublist 1 (Zlength cuts - 1) cuts)).
Proof.
  intros f cuts score Hscore.
  destruct Hscore as [Hlen [Hfirst [Hlast [Hmono Hscore]]]].
  subst score.
  assert (Hweighted : forall cs w,
    2 <= Zlength cs ->
    0 <= Znth 0 cs 0 ->
    mono_inc cs ->
    Znth (Zlength cs - 1) cs 0 = Zlength f ->
    fold_right Z.add 0
      (Zmap_range (fun g =>
        (w + g) * fold_right Z.add 0
          (map (fun idx =>
            if Z.eqb (Znth idx f 48) 49 then 1 else -1)
            (Zrange (Znth g cs 0) (Znth (g + 1) cs 0))))
        (Zlength cs - 1)) =
    w * SuffixGain f (Znth 0 cs 0) +
    ListLib.sum
      (map (SuffixGain f) (sublist 1 (Zlength cs - 1) cs))).
  {
    induction cs as [|a cs IH]; intros w Hcslen Hcs0 Hcsmono Hcslast.
    - rewrite Zlength_nil in Hcslen. lia.
    - destruct cs as [|b rest].
      + rewrite Zlength_cons, Zlength_nil in Hcslen. lia.
      + rewrite Znth0_cons in Hcs0.
        destruct rest as [|c rest].
        * assert (Hab : a < b).
          { apply (Hcsmono 0 1); lia. }
          assert (Hb : b = Zlength f).
          { rewrite last_of_cons_tail__final_result in Hcslast.
            simpl in Hcslast. exact Hcslast. }
          rewrite weighted_segments_cons__final_result.
          rewrite weighted_segments_single__final_result.
          rewrite internal_cuts_pair__final_result. cbn [map fold_right].
          rewrite Znth0_cons.
          rewrite fishing_segment_as_sublist__final_result by
            (subst b; pose proof (Zlength_nonneg f); lia).
          rewrite (suffix_gain_split__final_result f a b
            ltac:(lia)
            ltac:(subst b; pose proof (Zlength_nonneg f); lia)).
          subst b. rewrite suffix_gain_at_end__final_result. simpl. ring.
        * assert (Hab : a < b).
          { apply (Hcsmono 0 1); lia. }
          assert (Htailmono : mono_inc (b :: c :: rest)).
          { apply mono_inc_tail__final_result with (a := a). exact Hcsmono. }
          assert (Htaillast :
            Znth (Zlength (b :: c :: rest) - 1) (b :: c :: rest) 0 =
            Zlength f).
          { rewrite <- (last_of_cons_tail__final_result a b (c :: rest)).
            exact Hcslast. }
          assert (Hbend : b < Zlength f).
          { rewrite <- Htaillast.
            apply (Htailmono 0 (Zlength (b :: c :: rest) - 1)
              ltac:(lia)
              ltac:(rewrite !Zlength_cons; pose proof (Zlength_nonneg rest); lia)
              ltac:(rewrite !Zlength_cons; pose proof (Zlength_nonneg rest); lia)). }
          rewrite weighted_segments_cons__final_result.
          rewrite (IH (w + 1)
            ltac:(rewrite !Zlength_cons; pose proof (Zlength_nonneg rest); lia)
            ltac:(rewrite Znth0_cons; lia)
            Htailmono Htaillast).
          rewrite internal_cuts_cons__final_result.
          cbn [map ListLib.sum fold_right].
          rewrite !Znth0_cons.
          rewrite fishing_segment_as_sublist__final_result by lia.
          rewrite (suffix_gain_split__final_result f a b ltac:(lia) ltac:(lia)).
          unfold ListLib.sum. ring.
  }
  specialize (Hweighted cuts 0 Hlen ltac:(rewrite Hfirst; lia) Hmono Hlast).
  simpl in Hweighted. exact Hweighted.
Qed.
Lemma filter_selection_permutation__final_result : forall {A : Type}
    (universe chosen : list A),
  NoDup universe ->
  NoDup chosen ->
  (forall x, In x chosen -> In x universe) ->
  Permutation
    (filter (fun x => if prop_dec (In x chosen) then true else false) universe)
    chosen.
Proof.
  intros A universe chosen Huni Hchosen Hincl.
  apply NoDup_Permutation.
  - apply NoDup_filter. exact Huni.
  - exact Hchosen.
  - intros x. rewrite filter_In. split.
    + intros [_ Htest]. destruct (prop_dec (In x chosen)) as [Hin|Hnot];
        [exact Hin|discriminate].
    + intros Hin. split; [apply Hincl; exact Hin|].
      destruct (prop_dec (In x chosen)) as [_|Hnot];
        [reflexivity|contradiction].
Qed.
Lemma decreasing_prefix_maximal__final_result : forall {A : Type}
    (fn : A -> Z) universe chosen sorted,
  Permutation (map fn universe) sorted ->
  ListLib.decreasing sorted ->
  NoDup universe ->
  NoDup chosen ->
  (forall x, In x chosen -> In x universe) ->
  ListLib.sum (map fn chosen) <=
  ListLib.sum (sublist 0 (Zlength chosen) sorted).
Proof.
  intros A fn universe chosen sorted Hperm Hdec Huni Hchosen Hincl.
  assert (Hback : Permutation sorted (map fn universe)) by
    (apply Permutation_sym; exact Hperm).
  destruct (Permutation_map_inv fn universe Hback)
    as [order [Hsorted Horder]].
  assert (Hordernd : NoDup order).
  { eapply Permutation_NoDup; [exact Horder|exact Huni]. }
  assert (Hchosen_order : forall x, In x chosen -> In x order).
  { intros x Hx. eapply Permutation_in; [exact Horder|]. apply Hincl. exact Hx. }
  set (test := fun x : A => if prop_dec (In x chosen) then true else false).
  pose proof (filter_selection_permutation__final_result
    order chosen Hordernd Hchosen Hchosen_order) as Hfilter.
  fold test in Hfilter.
  pose proof (decreasing_filter_sum_le_prefix__final_result
    fn test order) as Hmax.
  rewrite Hsorted in Hdec. specialize (Hmax Hdec).
  pose proof (Permutation_map fn Hfilter) as Hmapperm.
  rewrite (sum_permutation__final_result _ _ Hmapperm) in Hmax.
  rewrite (Permutation_length Hfilter) in Hmax.
  rewrite <- Hsorted in Hmax.
  unfold sublist. simpl.
  rewrite Zlength_correct, Nat2Z.id. exact Hmax.
Qed.
Lemma mono_inc_NoDup__final_result : forall xs,
  mono_inc xs -> NoDup xs.
Proof.
  intros xs Hmono. induction xs as [|x xs IH].
  - constructor.
  - apply mono_inc_cons in Hmono as [Hhead Htail]. constructor.
    + intro Hin. apply Forall_forall with (x := x) in Hhead; auto. lia.
    + apply IH. exact Htail.
Qed.
Lemma NoDup_sublist__final_result : forall {A : Type}
    (xs : list A) lo hi,
  NoDup xs -> NoDup (sublist lo hi xs).
Proof.
  intros A xs lo hi Hnd. unfold sublist.
  assert (Hprefix : NoDup (firstn (Z.to_nat hi) xs)).
  { apply (NoDup_app_remove_r
      (firstn (Z.to_nat hi) xs) (skipn (Z.to_nat hi) xs)).
    rewrite firstn_skipn. exact Hnd. }
  apply (NoDup_app_remove_l
    (firstn (Z.to_nat lo) (firstn (Z.to_nat hi) xs))
    (skipn (Z.to_nat lo) (firstn (Z.to_nat hi) xs))).
  rewrite firstn_skipn. exact Hprefix.
Qed.
Lemma In_Znth_index__final_result : forall {A : Type}
    (xs : list A) d x,
  In x xs -> exists i,
    0 <= i < Zlength xs /\ Znth i xs d = x.
Proof.
  intros A xs d x Hin.
  destruct (In_nth xs x d Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma fishing_internal_cuts_valid__final_result : forall f cuts score,
  FishingScore f cuts score ->
  let internal := sublist 1 (Zlength cuts - 1) cuts in
  NoDup internal /\
  (forall x, In x internal -> In x (Zrange 1 (Zlength f))).
Proof.
  intros f cuts score [Hlen [Hfirst [Hlast [Hmono Hscore]]]].
  simpl. split.
  - apply NoDup_sublist__final_result.
    apply mono_inc_NoDup__final_result. exact Hmono.
  - intros x Hin.
    destruct (In_Znth_index__final_result
      (sublist 1 (Zlength cuts - 1) cuts) 0 x Hin)
      as [q [Hq Hqx]].
    assert (Hintlen :
      Zlength (sublist 1 (Zlength cuts - 1) cuts) = Zlength cuts - 2).
    { rewrite Zlength_sublist by lia. lia. }
    rewrite Hintlen in Hq.
    rewrite Znth_sublist in Hqx by lia.
    assert (Hlower : 0 < x).
    { rewrite <- Hfirst, <- Hqx.
      apply (Hmono 0 (q + 1)); lia. }
    assert (Hupper : x < Zlength f).
    { rewrite <- Hlast, <- Hqx.
      apply (Hmono (q + 1) (Zlength cuts - 1)); lia. }
    apply In_Zrange. lia.
Qed.
Lemma fishing_score_le_sorted_prefix__final_result : forall f cuts score gains,
  FishingScore f cuts score ->
  PreparedGains f gains ->
  score <= ListLib.sum
    (sublist 0 (Zlength cuts - 2) gains).
Proof.
  intros f cuts score gains Hscore [Hperm Hdec].
  pose proof (fishing_score_internal_cuts__final_result
    f cuts score Hscore) as Hdecomp.
  pose proof (fishing_internal_cuts_valid__final_result
    f cuts score Hscore) as Hvalid.
  simpl in Hvalid. destruct Hvalid as [Hnd Hin].
  assert (Huni : NoDup (Zrange 1 (Zlength f))) by apply NoDup_Zrange.
  unfold FishingGains in Hperm.
  pose proof (decreasing_prefix_maximal__final_result
    (SuffixGain f) (Zrange 1 (Zlength f))
    (sublist 1 (Zlength cuts - 1) cuts) gains
    Hperm Hdec Huni Hnd Hin) as Hmax.
  assert (Hintlen :
    Zlength (sublist 1 (Zlength cuts - 1) cuts) = Zlength cuts - 2).
  { destruct Hscore as [Hlen _]. rewrite Zlength_sublist by lia. lia. }
  rewrite Hintlen in Hmax. rewrite Hdecomp. exact Hmax.
Qed.
Lemma fishing_score_of_valid_cuts__final_result : forall f cuts,
  2 <= Zlength cuts ->
  Znth 0 cuts 0 = 0 ->
  Znth (Zlength cuts - 1) cuts 0 = Zlength f ->
  mono_inc cuts ->
  FishingScore f cuts
    (ListLib.sum
      (map (SuffixGain f) (sublist 1 (Zlength cuts - 1) cuts))).
Proof.
  intros f cuts Hlen Hfirst Hlast Hmono.
  set (raw := fold_right Z.add 0
    (Zmap_range (fun g =>
      g * fold_right Z.add 0
        (map (fun i => if Z.eqb (Znth i f 48) 49 then 1 else -1)
          (Zrange (Znth g cuts 0) (Znth (g + 1) cuts 0))))
      (Zlength cuts - 1))).
  assert (Hraw : FishingScore f cuts raw).
  { unfold FishingScore. repeat split; assumption. }
  pose proof (fishing_score_internal_cuts__final_result
    f cuts raw Hraw) as Heq.
  unfold FishingScore. repeat split; try assumption.
  symmetry. exact Heq.
Qed.
Lemma mono_inc_filter__final_result : forall test xs,
  mono_inc xs -> mono_inc (filter test xs).
Proof.
  intros test xs Hmono.
  apply (proj2 (mono_inc_iff_ind (filter test xs))).
  apply (proj1 (mono_inc_iff_ind xs)) in Hmono.
  induction Hmono as [|x xs Htail IH Hall]; simpl.
  - constructor.
  - destruct (test x) eqn:Hx.
    + constructor; [exact IH|].
      rewrite Forall_forall in *. intros y Hy.
      apply filter_In in Hy as [Hy _]. apply Hall. exact Hy.
    + exact IH.
Qed.
Lemma mono_inc_Zrange__final_result : forall lo hi,
  mono_inc (Zrange lo hi).
Proof.
  intros lo hi i j Hi Hij Hj.
  assert (Hle : lo <= hi).
  { destruct (Z_le_gt_dec lo hi); [assumption|].
    unfold Zrange in Hj. replace (Z.to_nat (hi - lo)) with 0%nat in Hj by lia.
    simpl in Hj. rewrite Zlength_nil in Hj. lia. }
  rewrite Zlength_Zrange__final_result in Hj by exact Hle.
  rewrite !Znth_Zrange__final_result by lia. lia.
Qed.
Lemma Znth_app_last__final_result : forall {A : Type}
    (xs : list A) d x,
  Znth (Zlength xs) (xs ++ x :: nil) d = x.
Proof.
  intros A xs d x. unfold Znth. rewrite app_nth2.
  - rewrite Zlength_correct, Nat2Z.id.
    replace (length xs - length xs)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct. lia.
Qed.
Lemma cuts_from_internal_valid__final_result : forall chosen n,
  mono_inc chosen ->
  Forall (fun x => 1 <= x < n) chosen ->
  1 <= n ->
  2 <= Zlength (0 :: chosen ++ n :: nil) /\
  Znth 0 (0 :: chosen ++ n :: nil) 0 = 0 /\
  Znth (Zlength (0 :: chosen ++ n :: nil) - 1)
    (0 :: chosen ++ n :: nil) 0 = n /\
  mono_inc (0 :: chosen ++ n :: nil).
Proof.
  intros chosen n Hmono Hbounds Hn.
  repeat split.
  - rewrite Zlength_cons, Zlength_app, !Zlength_cons, Zlength_nil.
    pose proof (Zlength_nonneg chosen). lia.
  - replace (0 :: chosen ++ n :: nil) with ((0 :: chosen) ++ n :: nil)
      by reflexivity.
    replace (Zlength ((0 :: chosen) ++ n :: nil) - 1)
      with (Zlength (0 :: chosen)) by
      (rewrite Zlength_app, !Zlength_cons, Zlength_nil; lia).
    apply Znth_app_last__final_result.
  - apply (proj2 (mono_inc_iff_ind (0 :: chosen ++ n :: nil))).
    constructor.
    + apply (proj2 (mono_inc_ind_app chosen (n :: nil))).
      split.
      * apply (proj1 (mono_inc_iff_ind chosen)). exact Hmono.
      * split.
        -- constructor; constructor.
        -- intros a b Ha Hb. simpl in Hb. destruct Hb as [->|[]].
           rewrite Forall_forall in Hbounds. specialize (Hbounds a Ha). lia.
    + rewrite Forall_forall. intros x Hx.
      apply in_app_or in Hx. destruct Hx as [Hx|Hx].
      * rewrite Forall_forall in Hbounds. specialize (Hbounds x Hx). lia.
      * simpl in Hx. destruct Hx as [->|[]]. lia.
Qed.
Lemma internal_of_constructed_cuts__final_result : forall chosen n,
  sublist 1 (Zlength (0 :: chosen ++ n :: nil) - 1)
    (0 :: chosen ++ n :: nil) = chosen.
Proof.
  intros chosen n.
  apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite Zlength_sublist by
      (rewrite Zlength_cons, Zlength_app, !Zlength_cons, Zlength_nil;
       pose proof (Zlength_nonneg chosen); lia).
    rewrite Zlength_cons, Zlength_app, !Zlength_cons, Zlength_nil. lia.
  - intros i Hi.
    rewrite Zlength_sublist in Hi by
      (rewrite Zlength_cons, Zlength_app, !Zlength_cons, Zlength_nil;
       pose proof (Zlength_nonneg chosen); lia).
    rewrite Znth_sublist; [|lia|].
    2: { rewrite Zlength_cons, Zlength_app, !Zlength_cons, Zlength_nil in Hi.
         rewrite Zlength_cons, Zlength_app, !Zlength_cons, Zlength_nil.
         lia. }
    rewrite Znth_cons by lia. replace (i + 1 - 1) with i by lia.
    unfold Znth. rewrite app_nth1.
    + reflexivity.
    + rewrite Zlength_cons, Zlength_app, !Zlength_cons, Zlength_nil in Hi.
      rewrite Zlength_correct in Hi. lia.
Qed.
Lemma prefix_realized_by_fishing_score__final_result : forall f gains r,
  PreparedGains f gains ->
  1 <= Zlength f ->
  0 <= r <= Zlength gains ->
  exists cuts,
    FishingScore f cuts (ListLib.sum (sublist 0 r gains)) /\
    Zlength cuts - 1 = r + 1.
Proof.
  intros f gains r [Hperm Hdec] Hflen Hr.
  unfold FishingGains in Hperm.
  assert (Hback : Permutation gains
    (map (SuffixGain f) (Zrange 1 (Zlength f)))) by
    (apply Permutation_sym; exact Hperm).
  destruct (Permutation_map_inv (SuffixGain f)
    (Zrange 1 (Zlength f)) Hback) as [order [Hgains Horder]].
  set (picked := firstn (Z.to_nat r) order).
  set (chosen := filter
    (fun x => if prop_dec (In x picked) then true else false)
    (Zrange 1 (Zlength f))).
  assert (Hordernd : NoDup order).
  { eapply Permutation_NoDup; [exact Horder|apply NoDup_Zrange]. }
  assert (Hpickednd : NoDup picked).
  { subst picked. apply (NoDup_app_remove_r
      (firstn (Z.to_nat r) order) (skipn (Z.to_nat r) order)).
    rewrite firstn_skipn. exact Hordernd. }
  assert (Hpicked_in : forall x, In x picked -> In x (Zrange 1 (Zlength f))).
  { intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact Horder|].
    subst picked. rewrite <- (firstn_skipn (Z.to_nat r) order).
    apply in_or_app. left. exact Hx. }
  assert (Hchosenperm : Permutation chosen picked).
  { subst chosen. apply filter_selection_permutation__final_result;
      [apply NoDup_Zrange|exact Hpickednd|exact Hpicked_in]. }
  assert (Hchosenlen : Zlength chosen = r).
  { rewrite (permutation_Zlength__final_result _ _ Hchosenperm).
    subst picked. apply Zlength_firstn_to_nat__final_result.
    rewrite <- (Zlength_map__final_result (SuffixGain f) order), <- Hgains.
    exact Hr. }
  assert (Hchosenmono : mono_inc chosen).
  { subst chosen. apply mono_inc_filter__final_result.
    apply mono_inc_Zrange__final_result. }
  assert (Hchosenbounds : Forall (fun x => 1 <= x < Zlength f) chosen).
  { rewrite Forall_forall. intros x Hx.
    subst chosen. apply filter_In in Hx as [Hx _]. apply In_Zrange in Hx. lia. }
  exists (0 :: chosen ++ Zlength f :: nil). split.
  - destruct (cuts_from_internal_valid__final_result chosen (Zlength f)
      Hchosenmono Hchosenbounds Hflen)
      as [Hlen [Hfirst [Hlast Hmono]]].
    pose proof (fishing_score_of_valid_cuts__final_result f
      (0 :: chosen ++ Zlength f :: nil) Hlen Hfirst Hlast Hmono) as Hscore.
    rewrite internal_of_constructed_cuts__final_result in Hscore.
    assert (Hsumpicked :
      ListLib.sum (map (SuffixGain f) chosen) =
      ListLib.sum (map (SuffixGain f) picked)).
    { apply sum_permutation__final_result. apply Permutation_map. exact Hchosenperm. }
    rewrite Hsumpicked in Hscore.
    subst picked. rewrite <- firstn_map in Hscore.
    rewrite <- Hgains in Hscore.
    rewrite sublist_zero_as_firstn__final_result. exact Hscore.
  - rewrite Zlength_cons, Zlength_app, !Zlength_cons, Zlength_nil, Hchosenlen.
    lia.
Qed.
Lemma prepared_gains_length__final_result : forall f gains,
  PreparedGains f gains ->
  1 <= Zlength f ->
  Zlength gains = Zlength f - 1.
Proof.
  intros f gains [Hperm Hdec] Hf.
  rewrite <- (permutation_Zlength__final_result _ _ Hperm).
  unfold FishingGains. rewrite Zlength_map__final_result,
    Zlength_Zrange__final_result by lia. lia.
Qed.
Lemma fishing_internal_count_bound__final_result : forall f cuts score,
  FishingScore f cuts score ->
  1 <= Zlength f ->
  0 <= Zlength cuts - 2 <= Zlength f - 1.
Proof.
  intros f cuts score Hscore Hf.
  pose proof (fishing_internal_cuts_valid__final_result
    f cuts score Hscore) as Hvalid.
  simpl in Hvalid. destruct Hvalid as [Hnd Hin].
  assert (Hlenle :
    (length (sublist 1 (Zlength cuts - 1) cuts) <=
     length (Zrange 1 (Zlength f)))%nat).
  { apply NoDup_incl_length; [exact Hnd|].
    intros x Hx. apply Hin. exact Hx. }
  destruct Hscore as [Hcutslen _].
  apply Nat2Z.inj_le in Hlenle.
  rewrite <- !Zlength_correct in Hlenle.
  rewrite Zlength_sublist in Hlenle by lia.
  rewrite Zlength_Zrange__final_result in Hlenle by lia.
  lia.
Qed.
Lemma fishing_search_result_implies_spec__final_result : forall k f gains out,
  1 <= Zlength f ->
  PreparedGains f gains ->
  FishingSearchResult k f gains out ->
  Spec k f out.
Proof.
  intros k f gains out Hflen Hprepared Hresult.
  destruct Hresult as [[Hout Hfail]|[Houtbounds [Hsuccess Hfail]]].
  - left. split; [exact Hout|]. intros [cuts score] Hcandidate.
    simpl in Hcandidate. destruct Hcandidate as [Hscore Hscorek].
    pose proof (fishing_score_le_sorted_prefix__final_result
      f cuts score gains Hscore Hprepared) as Hbound.
    pose proof (fishing_internal_count_bound__final_result
      f cuts score Hscore Hflen) as Hcount.
    pose proof (prepared_gains_length__final_result
      f gains Hprepared Hflen) as Hglen.
    assert (Hrange : 0 <= Zlength cuts - 2 <= Zlength gains).
    { rewrite Hglen. exact Hcount. }
    specialize (Hfail (Zlength cuts - 2) Hrange).
    apply Z.ge_le in Hscorek.
    apply (Z.lt_irrefl k). eapply Z.le_lt_trans.
    + eapply Z.le_trans; [exact Hscorek|exact Hbound].
    + exact Hfail.
  - right. unfold min_value_of_subset, min_object_of_subset.
    assert (Hr : 0 <= out - 1 <= Zlength gains).
    { pose proof (prepared_gains_length__final_result
        f gains Hprepared Hflen) as Hglen. lia. }
    destruct (prefix_realized_by_fishing_score__final_result
      f gains (out - 1) Hprepared Hflen Hr)
      as [cuts [Hcuts Hgroups]].
    exists (cuts, ListLib.sum (sublist 0 (out - 1) gains)).
    split.
    + split.
      * split; [exact Hcuts|]. apply Z.le_ge. exact Hsuccess.
      * intros [other_cuts other_score] Hother.
        simpl in *. destruct Hother as [Hother_score Hother_k].
        apply Z.ge_le in Hother_k.
        pose proof (fishing_score_le_sorted_prefix__final_result
          f other_cuts other_score gains Hother_score Hprepared) as Hbound.
        pose proof (fishing_internal_count_bound__final_result
          f other_cuts other_score Hother_score Hflen) as Hcount.
        destruct (Z_lt_ge_dec (Zlength other_cuts - 1) out) as [Hlt|Hge];
          [|apply Z.ge_le in Hge; lia].
        assert (Hsmall : 0 <= Zlength other_cuts - 2 < out - 1) by lia.
        specialize (Hfail (Zlength other_cuts - 2) Hsmall).
        exfalso. apply (Z.lt_irrefl k). eapply Z.le_lt_trans.
        -- eapply Z.le_trans; [exact Hother_k|exact Hbound].
        -- exact Hfail.
    + simpl. lia.
Qed.
Lemma gain_search_terminal_result__final_result : forall k f gains next cur out,
  GainSearchState k gains next cur ->
  next = Zlength gains ->
  out = -1 ->
  FishingSearchResult k f gains out.
Proof.
  intros k f gains next cur out [_ Hprefix] Hnext Hout.
  left. split; [exact Hout|].
  intros count Hcount. apply Hprefix. rewrite Hnext. exact Hcount.
Qed.
Lemma gain_search_success_result__final_result : forall k f gains next cur,
  1 <= Zlength f ->
  PreparedGains f gains ->
  0 <= next < Zlength gains ->
  cur + Znth next gains 0 >= k ->
  GainSearchState k gains next cur ->
  FishingSearchResult k f gains (next + 2).
Proof.
  intros k f gains next cur Hflen Hprepared Hnext Hcross [Hcur Hprefix].
  apply Z.ge_le in Hcross.
  pose proof (prepared_gains_length__final_result
    f gains Hprepared Hflen) as Hglen.
  right. split.
  - lia.
  - split.
    + replace (next + 2 - 1) with (next + 1) by lia.
      rewrite sum_sublist_snoc__final_result by exact Hnext.
      unfold ListLib.sum. rewrite <- Hcur.
      exact Hcross.
    + intros count Hcount. apply Hprefix. lia.
Qed.
Lemma sum_upper_forall__final_result : forall xs b,
  Forall (fun x : Z => x <= b) xs ->
  ListLib.sum xs <= Zlength xs * b.
Proof.
  intros xs b Hall. induction Hall as [|x xs Hx Hall IH].
  - simpl. lia.
  - rewrite Zlength_cons. unfold ListLib.sum in *. simpl. nia.
Qed.
Lemma prefix_sum_upper_bound__final_result : forall xs count b,
  0 <= count <= Zlength xs ->
  (forall j, 0 <= j < Zlength xs -> Znth j xs 0 <= b) ->
  ListLib.sum (sublist 0 count xs) <= count * b.
Proof.
  intros xs count b Hcount Hbound.
  assert (Hall : Forall (fun x : Z => x <= b) (sublist 0 count xs)).
  { apply Forall_forall. intros x Hin.
    destruct (In_Znth_index__final_result (sublist 0 count xs) 0 x Hin)
      as [j [Hj Hx]].
    rewrite Zlength_sublist in Hj by lia.
    rewrite <- Hx, Znth_sublist by lia. apply Hbound. lia. }
  pose proof (sum_upper_forall__final_result
    (sublist 0 count xs) b Hall) as Hsum.
  rewrite Zlength_sublist in Hsum by lia.
  replace (count - 0) with count in Hsum by lia. exact Hsum.
Qed.
Lemma gain_search_next_sum_upper__final_result : forall k gains next cur b,
  0 <= next < Zlength gains ->
  (forall j, 0 <= j < Zlength gains -> Znth j gains 0 <= b) ->
  GainSearchState k gains next cur ->
  cur + Znth next gains 0 <= (next + 1) * b.
Proof.
  intros k gains next cur b Hnext Hbound [Hcur _].
  pose proof (prefix_sum_upper_bound__final_result
    gains (next + 1) b ltac:(lia) Hbound) as Hsum.
  rewrite sum_sublist_snoc__final_result in Hsum by exact Hnext.
  unfold ListLib.sum in Hsum. rewrite <- Hcur in Hsum. exact Hsum.
Qed.
