Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.

Import ListNotations.
Local Open Scope Z_scope.

Definition LexLE (a b : list Z) : Prop :=
  a = b \/
  (exists i, 0 <= i < Z.min (Zlength a) (Zlength b) /\
    (forall j, 0 <= j < i -> Znth j a 0 = Znth j b 0) /\
    Znth i a 0 < Znth i b 0) \/
  (Zlength a < Zlength b /\ is_prefix a b).

Definition PoloString (n k : Z) (s : list Z) : Prop :=
  Zlength s = n /\
  Forall (fun c => 97 <= c <= 122) s /\
  #(fun c : Z => 97 <= c < 123 /\ In c s) = k /\
  forall i, 0 <= i < n - 1 -> Znth i s 0 <> Znth (i + 1) s 0.

Definition Pre (n k : Z) : Prop :=
  (* Stated explicitly in the P035 solver Require (through its length and
     alphabet_size aliases), which therefore omits the Pre(...) call:
       1 <= n <= 1000000 /\ 1 <= k <= 26. *)
  True.

Definition Spec (n k : Z) (out : option (list Z)) : Prop :=
  (out = None /\ ~ exists s, PoloString n k s) \/
  (exists s, out = Some s /\ PoloString n k s /\
    forall q, PoloString n k q -> LexLE s q).

Definition P035ReturnBridge (out : option (list Z)) (ret : Z) : Prop :=
  (out = None /\ ret = 0) \/
  (exists xs, out = Some xs /\ ret = 1).

Definition AlternatingPrefix (m : Z) : list Z :=
  map (fun i => 97 + i mod 2) (Zrange 0 m).

Definition IncreasingTail (m : Z) : list Z :=
  map (fun i => 99 + i) (Zrange 0 m).

Definition PoloCandidate (n k : Z) : list Z :=
  if Z.eq_dec k 1 then [97]
  else AlternatingPrefix (n - (k - 2)) ++ IncreasingTail (k - 2).

Require Import Coq.micromega.Lia.
Lemma set_card_unique__alternating_prefix :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x,
    P x ->
    (forall y, P y -> y = x) ->
    @set_card A P FP = 1.
Proof.
  intros A P FP x Hx Hunique.
  unfold set_card, SumLib.Sum.sum.
  pose proof (proj1 (@enum_ok A P FP x) Hx) as Hxin.
  remember (@enum A P FP) as es eqn:Hes.
  destruct es as [|a [|b rest]].
  - contradiction.
  - reflexivity.
  - exfalso.
    assert (Ha : P a).
    { apply (proj2 (@enum_ok A P FP a)). rewrite <- Hes. simpl; auto. }
    assert (Hb : P b).
    { apply (proj2 (@enum_ok A P FP b)). rewrite <- Hes. simpl; auto. }
    assert (Hab : a = b) by (rewrite (Hunique a Ha), (Hunique b Hb); reflexivity).
    pose proof (@enum_nodup A P FP) as Hnodup.
    rewrite <- Hes in Hnodup.
    inversion Hnodup as [|? ? Hnotin _]; subst.
    apply Hnotin. simpl. auto.
Qed.
Lemma alternating_prefix_snoc__alternating_prefix : forall i,
  0 <= i ->
  AlternatingPrefix i ++ [97 + i mod 2] =
  AlternatingPrefix (i + 1).
Proof.
  intros i Hi.
  unfold AlternatingPrefix, Zrange.
  replace (Z.to_nat (i + 1 - 0)) with
      (Z.to_nat (i - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app, map_app.
  replace (0 + Z.of_nat (Z.to_nat (i - 0))) with i by
      (rewrite Z2Nat.id by lia; lia).
  cbn [Zrange_aux map].
  reflexivity.
Qed.
Lemma increasing_tail_snoc__candidate_completion : forall i,
  0 <= i ->
  IncreasingTail i ++ [99 + i] = IncreasingTail (i + 1).
Proof.
  intros i Hi.
  unfold IncreasingTail, Zrange.
  replace (i + 1 - 0) with ((i - 0) + 1) by lia.
  rewrite Z2Nat.inj_add by lia.
  simpl Z.to_nat at 1.
  rewrite Zrange_aux_app.
  rewrite Z2Nat.id by lia.
  simpl.
  replace (i - 0) with i by lia.
  rewrite map_app.
  reflexivity.
Qed.
Lemma Zlength_Zrange_aux__candidate_completion : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low.
  induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__candidate_completion : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__candidate_completion.
  lia.
Qed.
Lemma Znth_Zrange_aux__candidate_completion : forall m low i,
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
Lemma Znth_Zrange__candidate_completion : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__candidate_completion by lia.
  lia.
Qed.
Lemma Zlength_map__candidate_completion : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__candidate_completion : forall {A B : Type}
    (f : A -> B) l (da : A) (db : B) i,
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
Lemma alternating_prefix_length__candidate_completion : forall m,
  0 <= m -> Zlength (AlternatingPrefix m) = m.
Proof.
  intros m Hm. unfold AlternatingPrefix.
  rewrite Zlength_map__candidate_completion,
          Zlength_Zrange__candidate_completion by lia.
  lia.
Qed.
Lemma alternating_prefix_Znth__candidate_completion : forall m i,
  0 <= m -> 0 <= i < m ->
  Znth i (AlternatingPrefix m) 0 = 97 + i mod 2.
Proof.
  intros m i Hm Hi. unfold AlternatingPrefix.
  rewrite (@Znth_map__candidate_completion Z Z
    (fun i => 97 + i mod 2) (Zrange 0 m) 0 0 i) by
      (rewrite Zlength_Zrange__candidate_completion by lia; lia).
  rewrite Znth_Zrange__candidate_completion by lia.
  reflexivity.
Qed.
Lemma increasing_tail_length__candidate_completion : forall m,
  0 <= m -> Zlength (IncreasingTail m) = m.
Proof.
  intros m Hm. unfold IncreasingTail.
  rewrite Zlength_map__candidate_completion,
          Zlength_Zrange__candidate_completion by lia.
  lia.
Qed.
Lemma increasing_tail_Znth__candidate_completion : forall m i,
  0 <= m -> 0 <= i < m ->
  Znth i (IncreasingTail m) 0 = 99 + i.
Proof.
  intros m i Hm Hi. unfold IncreasingTail.
  rewrite (@Znth_map__candidate_completion Z Z
    (fun i => 99 + i) (Zrange 0 m) 0 0 i) by
      (rewrite Zlength_Zrange__candidate_completion by lia; lia).
  rewrite Znth_Zrange__candidate_completion by lia.
  reflexivity.
Qed.
Lemma polo_candidate_unfold_multi__candidate_completion : forall n k,
  2 <= k ->
  PoloCandidate n k =
    AlternatingPrefix (n - (k - 2)) ++ IncreasingTail (k - 2).
Proof.
  intros n k Hk. unfold PoloCandidate.
  destruct (Z.eq_dec k 1); [lia | reflexivity].
Qed.
Lemma polo_candidate_length_multi__candidate_completion : forall n k,
  2 <= k -> k <= n -> Zlength (PoloCandidate n k) = n.
Proof.
  intros n k Hk Hkn.
  rewrite polo_candidate_unfold_multi__candidate_completion by lia.
  rewrite Zlength_app, alternating_prefix_length__candidate_completion,
          increasing_tail_length__candidate_completion by lia.
  lia.
Qed.
Lemma polo_candidate_Znth_multi__candidate_completion : forall n k i,
  2 <= k -> k <= n -> 0 <= i < n ->
  Znth i (PoloCandidate n k) 0 =
    if Z_lt_dec i (n - (k - 2))
    then 97 + i mod 2
    else 99 + (i - (n - (k - 2))).
Proof.
  intros n k i Hk Hkn Hi.
  rewrite polo_candidate_unfold_multi__candidate_completion by lia.
  destruct (Z_lt_dec i (n - (k - 2))) as [Hleft | Hright].
  - rewrite app_Znth1 by
        (rewrite alternating_prefix_length__candidate_completion by lia; lia).
    apply alternating_prefix_Znth__candidate_completion; lia.
  - rewrite app_Znth2 by
        (rewrite alternating_prefix_length__candidate_completion by lia; lia).
    rewrite alternating_prefix_length__candidate_completion by lia.
    apply increasing_tail_Znth__candidate_completion; lia.
Qed.
Lemma polo_candidate_forall_multi__candidate_completion : forall n k,
  2 <= k <= 26 -> k <= n ->
  Forall (fun c => 97 <= c <= 122) (PoloCandidate n k).
Proof.
  intros n k Hk Hkn.
  apply (proj2 (Forall_Znth (fun c => 97 <= c <= 122) 0 _)).
  intros i Hi.
  rewrite polo_candidate_length_multi__candidate_completion in Hi by lia.
  rewrite polo_candidate_Znth_multi__candidate_completion by lia.
  destruct (Z_lt_dec i (n - (k - 2))).
  - pose proof (Z.mod_pos_bound i 2 ltac:(lia)). lia.
  - lia.
Qed.
Lemma polo_candidate_adjacent_multi__candidate_completion : forall n k i,
  2 <= k -> k <= n -> 0 <= i < n - 1 ->
  Znth i (PoloCandidate n k) 0 <>
  Znth (i + 1) (PoloCandidate n k) 0.
Proof.
  intros n k i Hk Hkn Hi.
  rewrite !polo_candidate_Znth_multi__candidate_completion by lia.
  destruct (Z_lt_dec i (n - (k - 2))) as [Hil | Hir];
  destruct (Z_lt_dec (i + 1) (n - (k - 2))) as [Hjl | Hjr].
  - pose proof (Z.mod_pos_bound i 2 ltac:(lia)) as Hmi.
    pose proof (Z.mod_pos_bound (i + 1) 2 ltac:(lia)) as Hmj.
    assert (Hmod : (i + 1) mod 2 = (i mod 2 + 1) mod 2).
    { rewrite Z.add_mod by lia. reflexivity. }
    rewrite Hmod.
    assert (i mod 2 = 0 \/ i mod 2 = 1) by lia.
    destruct H as [-> | ->]; discriminate.
  - pose proof (Z.mod_pos_bound i 2 ltac:(lia)). lia.
  - lia.
  - lia.
Qed.
Lemma polo_candidate_membership_multi__candidate_completion : forall n k c,
  2 <= k -> k <= n ->
  (In c (PoloCandidate n k) <-> 97 <= c < 97 + k).
Proof.
  intros n k c Hk Hkn.
  rewrite polo_candidate_unfold_multi__candidate_completion by lia.
  rewrite in_app_iff.
  split.
  - intros [Hin | Hin].
    + unfold AlternatingPrefix in Hin.
      apply in_map_iff in Hin as [x [<- Hx]].
      apply (proj2 (In_Zrange 0 (n - (k - 2)) x)) in Hx.
      pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
    + unfold IncreasingTail in Hin.
      apply in_map_iff in Hin as [x [<- Hx]].
      apply (proj2 (In_Zrange 0 (k - 2) x)) in Hx.
      lia.
  - intros Hc.
    destruct (Z_lt_ge_dec c 99) as [Hsmall | Hlarge].
    + left. unfold AlternatingPrefix. apply in_map_iff.
      destruct Hc as [Hlo Hhi].
      assert (c = 97 \/ c = 98) by lia.
      destruct H as [-> | ->].
      * exists 0. split; [reflexivity |].
        apply (proj1 (In_Zrange 0 (n - (k - 2)) 0)). lia.
      * exists 1. split; [reflexivity |].
        apply (proj1 (In_Zrange 0 (n - (k - 2)) 1)). lia.
    + right. unfold IncreasingTail. apply in_map_iff.
      exists (c - 99). split; [lia |].
      apply (proj1 (In_Zrange 0 (k - 2) (c - 99))). lia.
Qed.
Lemma fold_right_ones_length__candidate_completion : forall l : list Z,
  fold_right (fun _ acc => 1 + acc) 0 l = Z.of_nat (length l).
Proof.
  intro l. rewrite <- Zlength_correct.
  induction l as [|x xs IH].
  - reflexivity.
  - change (1 + fold_right (fun _ acc : Z => 1 + acc) 0 xs =
      Zlength (x :: xs)).
    rewrite IH, Zlength_cons. lia.
Qed.
Lemma polo_candidate_card_multi__candidate_completion : forall n k,
  2 <= k <= 26 -> k <= n ->
  #(fun c : Z => 97 <= c < 123 /\ In c (PoloCandidate n k)) = k.
Proof.
  intros n k Hk Hkn.
  unfold set_card, SumLib.Sum.sum.
  change (fold_right (fun _ acc : Z => 1 + acc) 0
    (filter
      (fun c => if SumLib.Sum.prop_dec (In c (PoloCandidate n k))
                then true else false)
      (Zrange 97 123)) = k).
  assert (Hperm : Permutation
    (filter
      (fun c => if SumLib.Sum.prop_dec (In c (PoloCandidate n k))
                then true else false)
      (Zrange 97 123))
    (Zrange 97 (97 + k))).
  {
    apply NoDup_Permutation.
    - apply NoDup_filter. apply NoDup_Zrange.
    - apply NoDup_Zrange.
    - intro c. rewrite filter_In, <- !In_Zrange.
      destruct (SumLib.Sum.prop_dec (In c (PoloCandidate n k))) as [Hin | Hnot].
      + rewrite polo_candidate_membership_multi__candidate_completion in Hin by lia.
        simpl. split.
        * intros _. exact Hin.
        * intros _. split; [lia | reflexivity].
      + simpl. split.
        * intros [_ Hfalse]. discriminate.
        * intros Hrange. exfalso. apply Hnot.
          apply (proj2 (polo_candidate_membership_multi__candidate_completion
            n k c ltac:(lia) ltac:(lia))).
          exact Hrange.
  }
  rewrite fold_right_ones_length__candidate_completion.
  rewrite (Permutation_length Hperm).
  rewrite <- Zlength_correct.
  rewrite Zlength_Zrange__candidate_completion by lia.
  lia.
Qed.
Lemma polo_card_as_nodup_length__candidate_completion : forall q,
  Forall (fun c => 97 <= c <= 122) q ->
  #(fun c : Z => 97 <= c < 123 /\ In c q) =
  Z.of_nat (length (nodup Z.eq_dec q)).
Proof.
  intros q Halpha.
  unfold set_card, SumLib.Sum.sum.
  change (fold_right (fun _ acc : Z => 1 + acc) 0
    (filter (fun c => if SumLib.Sum.prop_dec (In c q) then true else false)
      (Zrange 97 123)) = Z.of_nat (length (nodup Z.eq_dec q))).
  rewrite !fold_right_ones_length__candidate_completion.
  f_equal.
  apply Permutation_length, NoDup_Permutation.
  - apply NoDup_filter. apply NoDup_Zrange.
  - apply NoDup_nodup.
  - intro c. rewrite filter_In, nodup_In, <- In_Zrange.
    destruct (SumLib.Sum.prop_dec (In c q)) as [Hin | Hnot].
    + simpl. split; [intro; exact Hin | intro; split; [|reflexivity]].
      apply Forall_forall with (x := c) in Halpha.
      * lia.
      * exact Hin.
    + simpl. split.
      * intros [_ Hfalse]. discriminate.
      * intros Hc. contradiction.
Qed.
Lemma nodup_prefix_range_bound__candidate_completion : forall q x lo hi,
  0 <= x < Zlength q ->
  (forall p, 0 <= p <= x -> lo <= Znth p q 0 < hi) ->
  Z.of_nat (length (nodup Z.eq_dec q)) <=
    (hi - lo) + (Zlength q - (x + 1)).
Proof.
  intros q x lo hi Hx Hbound.
  assert (Hincl : incl (nodup Z.eq_dec q)
    (Zrange lo hi ++ sublist (x + 1) (Zlength q) q)).
  {
    intros c Hin. rewrite nodup_In in Hin.
    assert (Hsplit : q = sublist 0 (x + 1) q ++
      sublist (x + 1) (Zlength q) q).
    {
      rewrite <- sublist_split by lia.
      symmetry. apply sublist_self. reflexivity.
    }
    rewrite Hsplit in Hin. apply in_app_iff in Hin as [Hpre | Hsuf].
    - apply in_or_app. left. apply (proj1 (In_Zrange lo hi c)).
      assert (HF : Forall (fun z => lo <= z < hi) (sublist 0 (x + 1) q)).
      {
        apply (proj2 (Forall_Znth (fun z => lo <= z < hi) 0 _)).
        intros p Hp.
        rewrite Zlength_sublist0 in Hp by lia.
        rewrite Znth_sublist0 by lia.
        apply Hbound. lia.
      }
      apply Forall_forall with (x := c) in HF; assumption.
    - apply in_or_app. right. exact Hsuf.
  }
  pose proof (NoDup_incl_length (NoDup_nodup Z.eq_dec q) Hincl) as Hlen.
  rewrite length_app in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Nat2Z.inj_add in Hlen.
  assert (Hlohi : lo <= hi).
  { specialize (Hbound 0 ltac:(lia)). lia. }
  rewrite <- !Zlength_correct in Hlen.
  rewrite Zlength_Zrange__candidate_completion in Hlen by lia.
  rewrite Zlength_sublist in Hlen by lia.
  rewrite <- Zlength_correct.
  exact Hlen.
Qed.
Lemma first_difference_Znth__candidate_completion : forall a b : list Z,
  Zlength a = Zlength b -> a <> b ->
  exists i,
    0 <= i < Zlength a /\
    (forall j, 0 <= j < i -> Znth j a 0 = Znth j b 0) /\
    Znth i a 0 <> Znth i b 0.
Proof.
  induction a as [|x xs IH]; destruct b as [|y ys]; intros Hlen Hneq;
    try (simpl in Hneq; contradiction);
    try (rewrite Zlength_nil, Zlength_cons in Hlen; pose proof (Zlength_nonneg ys); lia);
    try (rewrite Zlength_cons, Zlength_nil in Hlen; pose proof (Zlength_nonneg xs); lia).
  rewrite !Zlength_cons in Hlen.
  destruct (Z.eq_dec x y) as [Heq | Hxy].
  - subst y.
    assert (Htail : xs <> ys) by (intro; subst; contradiction).
    destruct (IH ys ltac:(lia) Htail) as [i [Hi [Hpre Hdiff]]].
    exists (i + 1). split.
    + rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
    + split.
      * intros j Hj. destruct (Z.eq_dec j 0) as [-> | Hj0].
        -- rewrite !Znth0_cons. reflexivity.
        -- rewrite !Znth_cons by lia.
           apply Hpre. lia.
      * rewrite !Znth_cons by lia.
        replace (i + 1 - 1) with i by lia. exact Hdiff.
  - exists 0. split.
    + rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
    + split.
      * intros j Hj. lia.
      * rewrite !Znth0_cons. exact Hxy.
Qed.
Lemma polo_candidate_lex_multi__candidate_completion : forall n k q,
  2 <= k <= 26 -> k <= n ->
  PoloString n k q -> LexLE (PoloCandidate n k) q.
Proof.
  intros n k q Hk Hkn Hq.
  destruct Hq as [Hqlen [Halpha [Hcard Hadj]]].
  destruct (list_eq_dec Z.eq_dec (PoloCandidate n k) q) as [Heq | Hneq].
  - left. exact Heq.
  - right. left.
    assert (Hclen : Zlength (PoloCandidate n k) = n).
    { apply polo_candidate_length_multi__candidate_completion; lia. }
    destruct (first_difference_Znth__candidate_completion
      (PoloCandidate n k) q ltac:(lia) Hneq)
      as [x [Hx [Hpre Hdiff]]].
    exists x. split.
    + rewrite Hclen, Hqlen. rewrite Z.min_id. lia.
    + split; [exact Hpre |].
      assert (Hqx : 97 <= Znth x q 0 <= 122).
      {
        apply (Forall_Znth_Zlength
          (fun c => 97 <= c <= 122) q 0 x Halpha).
        lia.
      }
      rewrite polo_candidate_Znth_multi__candidate_completion in Hdiff by lia.
      rewrite polo_candidate_Znth_multi__candidate_completion by lia.
      destruct (Z_lt_dec x (n - (k - 2))) as [Hprefix | Htail].
      * pose proof (Z.mod_pos_bound x 2 ltac:(lia)) as Hmodbound.
        assert (Hxmod : x mod 2 = 0 \/ x mod 2 = 1) by lia.
        destruct Hxmod as [Hxmod | Hxmod].
        -- rewrite Hxmod in *. lia.
        -- assert (Hxpos : 1 <= x).
           { assert (x <> 0) by
               (intro Heq; subst x; simpl in Hxmod; discriminate).
             lia. }
           assert (Hprevmod : (x - 1) mod 2 = 0).
           {
             pose proof (Z.mod_pos_bound (x - 1) 2 ltac:(lia)) as Hb.
             assert ((x - 1) mod 2 = 0 \/ (x - 1) mod 2 = 1) by lia.
             destruct H as [Hm | Hm]; [exact Hm |].
             pose proof (Z.mod_eq x 2 ltac:(lia)) as Hex.
             pose proof (Z.mod_eq (x - 1) 2 ltac:(lia)) as Hep.
             rewrite Hxmod in Hex. rewrite Hm in Hep. lia.
           }
           specialize (Hadj (x - 1) ltac:(lia)).
           specialize (Hpre (x - 1) ltac:(lia)).
           rewrite polo_candidate_Znth_multi__candidate_completion in Hpre by lia.
           destruct (Z_lt_dec (x - 1) (n - (k - 2))) in Hpre; [|lia].
           rewrite Hprevmod in Hpre.
           replace (x - 1 + 1) with x in Hadj by lia.
           rewrite Hxmod in *.
           lia.
      * assert (Hcand :
          Znth x (PoloCandidate n k) 0 =
          99 + (x - (n - (k - 2)))).
        {
          rewrite polo_candidate_Znth_multi__candidate_completion by lia.
          destruct (Z_lt_dec x (n - (k - 2))); [lia | reflexivity].
        }
        destruct (Z_lt_ge_dec
          (Znth x (PoloCandidate n k) 0) (Znth x q 0)) as [Hgood | Hbad].
        -- rewrite Hcand in Hgood. exact Hgood.
        -- exfalso.
           assert (Hqsmall : Znth x q 0 <
             99 + (x - (n - (k - 2)))) by lia.
           assert (Hnodup : Z.of_nat (length (nodup Z.eq_dec q)) = k).
           {
             rewrite <- polo_card_as_nodup_length__candidate_completion by
               exact Halpha.
             exact Hcard.
           }
           pose proof (nodup_prefix_range_bound__candidate_completion
             q x 97 (99 + (x - (n - (k - 2)))) ltac:(lia)) as Hbound.
           specialize (Hbound ltac:(
             intros p Hp;
             assert (Hpalpha : 97 <= Znth p q 0 <= 122) by
               (apply (Forall_Znth_Zlength
                 (fun c => 97 <= c <= 122) q 0 p Halpha); lia);
             split; [lia |];
             destruct (Z.eq_dec p x) as [-> | Hpx]; [exact Hqsmall |];
             assert (Hplt : p < x) by lia;
             specialize (Hpre p ltac:(lia));
             rewrite polo_candidate_Znth_multi__candidate_completion in Hpre by lia;
             destruct (Z_lt_dec p (n - (k - 2))) as [Hpprefix | Hptail];
             [pose proof (Z.mod_pos_bound p 2 ltac:(lia)); lia | lia])).
           rewrite Hnodup in Hbound.
           lia.
Qed.
Lemma polo_candidate_spec_multi__candidate_completion : forall n k,
  2 <= k <= 26 -> k <= n -> Spec n k (Some (PoloCandidate n k)).
Proof.
  intros n k Hk Hkn. unfold Spec.
  right. exists (PoloCandidate n k).
  split; [reflexivity |]. split.
  - unfold PoloString. repeat split.
    + apply polo_candidate_length_multi__candidate_completion; lia.
    + apply polo_candidate_forall_multi__candidate_completion; assumption.
    + apply polo_candidate_card_multi__candidate_completion; assumption.
    + intros i Hi. apply polo_candidate_adjacent_multi__candidate_completion; lia.
  - intros q Hq. apply polo_candidate_lex_multi__candidate_completion; assumption.
Qed.
Lemma set_card_as_Zlength_enum__impossible_returns :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    @set_card A P FP = Zlength (@enum A P FP).
Proof.
  intros A P FP.
  unfold set_card, SumLib.Sum.sum.
  induction (@enum A P FP) as [|x xs IH].
  - reflexivity.
  - cbn [fold_right].
    rewrite Zlength_cons, IH.
    lia.
Qed.
Lemma polostring_symbol_count_le_length__impossible_returns :
  forall s,
    #(fun c : Z => 97 <= c < 123 /\ In c s) <= Zlength s.
Proof.
  intros s.
  rewrite set_card_as_Zlength_enum__impossible_returns.
  rewrite !Zlength_correct.
  apply Nat2Z.inj_le.
  apply NoDup_incl_length.
  - apply enum_nodup.
  - intros c Hc.
    apply (proj2 (enum_ok c)) in Hc.
    exact (proj2 Hc).
Qed.
Lemma set_card_one_members_equal__impossible_returns :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x y,
    @set_card A P FP = 1 -> P x -> P y -> x = y.
Proof.
  intros A P FP x y Hcard Hx Hy.
  rewrite set_card_as_Zlength_enum__impossible_returns in Hcard.
  pose proof (proj1 (@enum_ok A P FP x) Hx) as Hinx.
  pose proof (proj1 (@enum_ok A P FP y) Hy) as Hiny.
  remember (@enum A P FP) as es eqn:Hes.
  destruct es as [|z [|w ws]].
  - rewrite Zlength_nil in Hcard. lia.
  - simpl in Hinx, Hiny.
    destruct Hinx as [Hinx | []].
    destruct Hiny as [Hiny | []].
    congruence.
  - rewrite !Zlength_cons in Hcard.
    pose proof (Zlength_nonneg ws).
    lia.
Qed.
Lemma polostring_one_symbol_length_le_one__impossible_returns :
  forall n s, PoloString n 1 s -> n <= 1.
Proof.
  intros n s (Hlen & Hall & Hcard & Hadj).
  destruct s as [|a [|b t]].
  - rewrite Zlength_nil in Hlen. lia.
  - rewrite Zlength_cons, Zlength_nil in Hlen. lia.
  - inversion Hall as [|? ? Ha Hall']; subst.
    inversion Hall' as [|? ? Hb _]; subst.
    assert (Hab : a = b).
    {
      eapply set_card_one_members_equal__impossible_returns;
        [exact Hcard | |].
      - split; [lia | simpl; auto].
      - split; [lia | simpl; auto].
    }
    pose proof (Zlength_nonneg t) as Htail.
    specialize (Hadj 0 ltac:(rewrite !Zlength_cons; lia)).
    simpl in Hadj.
    contradiction.
Qed.
