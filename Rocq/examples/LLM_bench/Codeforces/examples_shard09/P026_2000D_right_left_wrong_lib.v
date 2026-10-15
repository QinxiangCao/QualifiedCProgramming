Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope Z_scope.

(* Signature: solve_case(a s:list Z)->Z. A strip cell holds 'L' (76) or 'R' (82),
   and becomes '.' (46) once erased. *)

(* [st'] is [st] with every position in [l, r] replaced by '.'. *)
Definition Erased (st st' : list Z) (l r : Z) : Prop :=
  Zlength st' = Zlength st /\
  forall i, 0 <= i < Zlength st ->
    (   l <= i <= r  /\ Znth i st' 0 = 46) \/
    (~ (l <= i <= r) /\ Znth i st' 0 = Znth i st 0).

(* One operation on a state of (remaining strip, score so far): pick l < r whose
   cells are still 'L' and 'R', add a_l + ... + a_r to the score, and erase the
   whole range. Erasing only removes those cells as future endpoints — an
   enclosing segment may still be chosen afterwards, and its sum counts the
   inner cells again. *)
Definition OpStep (a : list Z) (st st' : list Z * Z) : Prop :=
  exists l r,
    0 <= l < r /\ r < Zlength (fst st) /\
    Znth l (fst st) 0 = 76 /\ Znth r (fst st) 0 = 82 /\
    Erased (fst st) (fst st') l r /\
    snd st' = snd st + sum_range l r (fun i => Znth i a 0).

Definition Pre (a s : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P026 solver Require, which
     therefore omits the Pre(...) call:
       2 <= Zlength a <= 200000 /\ Zlength s = Zlength a /\
       Forall (fun x => 1 <= x <= 100000) a /\
       Forall (fun c => c = 76 \/ c = 82) s. *)
  True.

(* The answer is the largest score reachable by any finite run of operations
   from the initial strip with score 0 (performing no operation is allowed, so
   0 is always attainable). *)
Definition Spec (a s : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun v => exists st, clos_refl_trans (OpStep a) (s, 0) st /\ v = snd st)
    (fun x => x) out.

(* A mathematical prefix-sum profile.  [pref] may be a proper prefix of the
   complete profile while the C loop is still filling its work array. *)
Definition PrefixSumsPrefix (a pref : list Z) : Prop :=
  1 <= Zlength pref <= Zlength a + 1 /\
  forall i, 0 <= i < Zlength pref ->
    Znth i pref 0 = sum_range 0 (i - 1) (fun k => Znth k a 0).

Definition PrefixSums (a pref : list Z) : Prop :=
  Zlength pref = Zlength a + 1 /\
  forall i, 0 <= i <= Zlength a ->
    Znth i pref 0 = sum_range 0 (i - 1) (fun k => Znth k a 0).

Definition PairScore (a : list Z) (pairs : list (Z * Z)) : Z :=
  fold_right
    (fun p acc =>
       sum_range (fst p) (snd p) (fun i => Znth i a 0) + acc)
    0 pairs.

(* [pairs] lists already chosen endpoint pairs from outside to inside.  The
   frontier clauses say precisely which L endpoints lie to the left of [l]
   and which R endpoints lie to the right of [r]; the order clause makes the
   finite pairing independent of any particular implementation. *)
Definition OrderedGreedyPairs
    (s : list Z) (l r : Z) (pairs : list (Z * Z)) : Prop :=
  Forall
    (fun p =>
       0 <= fst p < snd p /\ snd p < Zlength s /\
       Znth (fst p) s 0 = 76 /\ Znth (snd p) s 0 = 82 /\
       fst p < l /\ r < snd p)
  pairs /\
  (forall i j,
     0 <= i /\ i < j /\ j < Zlength pairs ->
     fst (Znth i pairs (0, 0)) < fst (Znth j pairs (0, 0)) /\
     snd (Znth j pairs (0, 0)) < snd (Znth i pairs (0, 0))) /\
  (forall i, 0 <= i < l ->
     (Znth i s 0 = 76 <-> In i (map fst pairs))) /\
  (forall i, r < i < Zlength s ->
     (Znth i s 0 = 82 <-> In i (map snd pairs))).

Definition GreedyProgress
    (a s : list Z) (l r score : Z) : Prop :=
  exists pairs,
    OrderedGreedyPairs s l r pairs /\
    score = PairScore a pairs.

Require Import Coq.micromega.Lia.
Lemma PrefixSumsPrefix_zero__prefix_construction :
  forall a : list Z, PrefixSumsPrefix a (0 :: nil).
Proof.
  intros a.
  unfold PrefixSumsPrefix.
  split.
  - rewrite Zlength_cons, Zlength_nil.
    pose proof (Zlength_nonneg a).
    lia.
  - intros i Hi.
    rewrite Zlength_cons, Zlength_nil in Hi.
    assert (i = 0) by lia.
    subst i.
    rewrite Znth0_cons.
    unfold sum_range.
    rewrite sum_Z_range_empty by lia.
    reflexivity.
Qed.
Lemma PrefixSumsPrefix_snoc__prefix_construction :
  forall (a pref : list Z) (i : Z),
    Zlength pref = i + 1 ->
    0 <= i < Zlength a ->
    PrefixSumsPrefix a pref ->
    PrefixSumsPrefix a (pref ++ [Znth i pref 0 + Znth i a 0]).
Proof.
  intros a pref i Hlen Hi Hpref.
  destruct Hpref as [Hpref_len Hpref_values].
  unfold PrefixSumsPrefix.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  split.
  - lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j (Zlength pref)) as [Hjold | Hjnew].
    + rewrite app_Znth1 by lia.
      apply Hpref_values.
      lia.
    + assert (j = i + 1) by lia.
      subst j.
      rewrite app_Znth2 by lia.
      replace (i + 1 - Zlength pref) with 0 by lia.
      rewrite Znth0_cons.
      rewrite Hpref_values by lia.
      replace (i + 1 - 1) with i by lia.
      unfold sum_range.
      replace (i - 1 + 1) with i by lia.
      rewrite (sum_Z_range_extend_right 0 i (fun k => Znth k a 0)) by lia.
      reflexivity.
Qed.
Lemma PrefixSumsPrefix_complete__prefix_construction :
  forall (a pref : list Z),
    Zlength pref = Zlength a + 1 ->
    PrefixSumsPrefix a pref ->
    PrefixSums a pref.
Proof.
  intros a pref Hlen Hpref.
  destruct Hpref as [_ Hvalues].
  unfold PrefixSums.
  split; [exact Hlen |].
  intros i Hi.
  apply Hvalues.
  lia.
Qed.
Lemma prefix_next_int64_bounds__prefix_construction :
  forall (values pref : list Z) (i n : Z),
    n = Zlength values ->
    n <= 200000 ->
    0 <= i < n ->
    (forall k, 0 <= k < n -> 1 <= Znth k values 0 <= 100000) ->
    Zlength pref = i + 1 ->
    PrefixSumsPrefix values pref ->
    -9223372036854775808 <= Znth i pref 0 + Znth i values 0 <=
      9223372036854775807.
Proof.
  intros values pref i n Hn Hnmax Hi Hvalues Hlen Hpref.
  destruct Hpref as [_ Hprefix].
  pose proof (Hprefix i ltac:(lia)) as Hprefix_i.
  pose proof (Hvalues i Hi) as Hvalue_i.
  assert (Hrange :
    (i - 0) * 1 <= sum_range 0 (i - 1) (fun k => Znth k values 0) <=
    (i - 0) * 100000).
  {
    unfold sum_range.
    replace (i - 1 + 1) with i by lia.
    apply (sum_Z_range_bounds 0 i (fun k => Znth k values 0) 1 100000).
    - lia.
    - intros k Hk.
      apply Hvalues.
      lia.
  }
  rewrite Hprefix_i.
  lia.
Qed.
Lemma prefix_interval_sum_bounds__pair_update :
  forall values prefix n l r,
    n = Zlength values ->
    PrefixSums values prefix ->
    (forall k, 0 <= k < n -> 1 <= Znth k values 0 <= 100000) ->
    0 <= l -> l <= r -> r < n ->
    Znth (r + 1) prefix 0 - Znth l prefix 0 =
      sum_range l r (fun k => Znth k values 0) /\
    0 <= Znth (r + 1) prefix 0 - Znth l prefix 0 <= n * 100000.
Proof.
  intros values prefix n l r Hn Hprefix Hvalues Hl Hlr Hr.
  destruct Hprefix as [_ Hprefix].
  pose proof (Hprefix (r + 1) ltac:(lia)) as Hpr.
  pose proof (Hprefix l ltac:(lia)) as Hpl.
  replace (r + 1 - 1) with r in Hpr by lia.
  assert (Hsplit :
    sum_range 0 r (fun k => Znth k values 0) =
    sum_range 0 (l - 1) (fun k => Znth k values 0) +
    sum_range l r (fun k => Znth k values 0)).
  {
    unfold sum_range.
    replace (r + 1) with (r + 1) by reflexivity.
    replace (l - 1 + 1) with l by lia.
    apply sum_Z_range_split. lia.
  }
  assert (Hbounds :
    (r + 1 - l) * 1 <= sum_range l r (fun k => Znth k values 0) <=
    (r + 1 - l) * 100000).
  {
    unfold sum_range.
    apply sum_Z_range_bounds.
    - lia.
    - intros k Hk. apply Hvalues. lia.
  }
  rewrite Hpr, Hpl, Hsplit.
  split; [ring |].
  lia.
Qed.
Lemma Znth_map_Z__pair_update :
  forall (A : Type) (f : A -> Z) (xs : list A) (d : A) i,
    Znth i (map f xs) (f d) = f (Znth i xs d).
Proof.
  intros A f xs d i.
  unfold Znth.
  apply map_nth.
Qed.
Lemma Znth_map_inrange__pair_update :
  forall (A : Type) (f : A -> Z) (xs : list A) (d : A) dz i,
    0 <= i < Zlength xs ->
    Znth i (map f xs) dz = f (Znth i xs d).
Proof.
  intros A f xs d dz i Hi.
  transitivity (Znth i (map f xs) (f d)).
  - unfold Znth. apply nth_indep.
    rewrite length_map. rewrite Zlength_correct in Hi. lia.
  - apply Znth_map_Z__pair_update.
Qed.
Lemma Zlength_map__pair_update :
  forall (A B : Type) (f : A -> B) xs,
    Zlength (map f xs) = Zlength xs.
Proof.
  intros A B f xs.
  rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_app_left__pair_update :
  forall (A : Type) (xs ys : list A) (d : A) i,
    0 <= i < Zlength xs ->
    Znth i (xs ++ ys) d = Znth i xs d.
Proof.
  intros A xs ys d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_app_last__pair_update :
  forall (A : Type) (xs : list A) (d x : A),
    Znth (Zlength xs) (xs ++ [x]) d = x.
Proof.
  intros A xs d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length xs)) - length xs)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct. lia.
Qed.
Lemma mono_inc_NoDup__pair_update :
  forall xs, mono_inc xs -> NoDup xs.
Proof.
  intros xs Hmono.
  induction xs as [|x xs IH].
  - constructor.
  - apply mono_inc_cons in Hmono as [Hhead Htail].
    constructor.
    + intro Hin.
      apply Forall_forall with (x := x) in Hhead; auto. lia.
    + apply IH. exact Htail.
Qed.
Lemma NoDup_map_Z_to_nat__pair_update :
  forall picks,
    Forall (fun i => 0 <= i) picks ->
    NoDup picks ->
    NoDup (map Z.to_nat picks).
Proof.
  intros picks Hnonneg Hnodup.
  induction picks as [|x picks IH]; simpl.
  - constructor.
  - inversion Hnonneg as [|? ? Hx Hpicks_nonneg]; subst.
    inversion Hnodup as [|? ? Hnotin Hpicks_nodup]; subst.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hy Hin]].
      apply Hnotin.
      apply Z2Nat.inj in Hy; auto.
      * subst; auto.
      * apply Forall_forall with (x := y) in Hpicks_nonneg; auto.
    + apply IH; auto.
Qed.
Lemma NoDup_range_length__pair_update :
  forall limit picks,
    0 <= limit ->
    NoDup picks ->
    Forall (fun i => 0 <= i < limit) picks ->
    Zlength picks <= limit.
Proof.
  intros limit picks Hlimit Hnodup Hforall.
  assert (Hnonneg : Forall (fun i => 0 <= i) picks).
  {
    eapply (Forall_impl (P := fun i => 0 <= i < limit)).
    - intros x Hx. lia.
    - exact Hforall.
  }
  pose proof (NoDup_map_Z_to_nat__pair_update picks Hnonneg Hnodup) as Hmapnodup.
  assert (Hin_range : incl (map Z.to_nat picks) (seq 0 (Z.to_nat limit))).
  {
    intros x Hx.
    apply in_map_iff in Hx as [z [Hz Hin]]; subst.
    apply in_seq.
    apply Forall_forall with (x := z) in Hforall; auto.
    lia.
  }
  pose proof (NoDup_incl_length Hmapnodup Hin_range) as Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  rewrite Zlength_correct.
  exact Hlen.
Qed.
Lemma PairScore_app_single__pair_update :
  forall a pairs l r,
    PairScore a (pairs ++ [(l, r)]) =
    PairScore a pairs + sum_range l r (fun i => Znth i a 0).
Proof.
  intros a pairs l r.
  induction pairs as [|p pairs IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.
Lemma PairScore_bound_by_count__pair_update :
  forall a pairs n,
    n = Zlength a ->
    (forall k, 0 <= k < n -> 1 <= Znth k a 0 <= 100000) ->
    Forall
      (fun p =>
         0 <= fst p < snd p /\ snd p < n /\
         True)
      pairs ->
    0 <= PairScore a pairs <= Zlength pairs * n * 100000.
Proof.
  intros a pairs n Hn Hvalues Hpairs.
  induction Hpairs as [|p pairs Hp Hpairs IH].
  - unfold PairScore. rewrite Zlength_nil. simpl. lia.
  - destruct Hp as [[Hfst Hlt] [Hsnd _]].
    assert (Hsum :
      0 <= sum_range (fst p) (snd p) (fun i => Znth i a 0) <= n * 100000).
    {
      unfold sum_range.
      pose proof (sum_Z_range_bounds (fst p) (snd p + 1)
        (fun i => Znth i a 0) 1 100000 ltac:(lia)) as Hb.
      specialize (Hb ltac:(intros i Hi; apply Hvalues; lia)).
      lia.
    }
    unfold PairScore in *. simpl.
    rewrite Zlength_cons.
    nia.
Qed.
Lemma GreedyProgress_take_pair__pair_update :
  forall a s l r score,
    0 <= l -> l < r -> r < Zlength s ->
    Znth l s 0 = 76 -> Znth r s 0 = 82 ->
    GreedyProgress a s l r score ->
    GreedyProgress a s (l + 1) (r - 1)
      (score + sum_range l r (fun i => Znth i a 0)).
Proof.
  intros a s l r score Hl Hlr Hr HL HR Hprogress.
  destruct Hprogress as [pairs [Hordered Hscore]].
  exists (pairs ++ [(l, r)]).
  split.
  2: rewrite PairScore_app_single__pair_update, Hscore; ring.
  destruct Hordered as [Hvalid [Horder [Hleft Hright]]].
  unfold OrderedGreedyPairs.
  split.
  - apply Forall_app. split; [|constructor; [|constructor]].
    + eapply Forall_impl; [|exact Hvalid].
      intros p Hp. destruct Hp as [[Hp0 Hpord] [Hpn [HpL [HpR [Hpl Hpr]]]]].
      repeat split; try assumption; lia.
    + simpl. repeat split; try assumption; lia.
  - split.
    + intros i j [Hi [Hij Hj]].
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hj.
      destruct (Z_lt_ge_dec j (Zlength pairs)) as [Hjold | Hjlast].
      * rewrite !Znth_app_left__pair_update by lia.
        apply Horder. lia.
      * assert (j = Zlength pairs) by lia. subst j.
        rewrite Znth_app_last__pair_update.
        rewrite Znth_app_left__pair_update by lia.
        apply (proj1 (Forall_Znth _ (0, 0) _) Hvalid i ltac:(lia)).
    + split.
      * intros i Hi.
        rewrite map_app. simpl.
        destruct (Z_lt_ge_dec i l) as [Hil | Hil].
        -- rewrite in_app_iff. simpl.
           rewrite Hleft by lia.
           split; intros H.
           ++ left. exact H.
           ++ destruct H as [H | [H | H]]; auto; [subst i; lia | contradiction].
        -- assert (i = l) by lia. subst i.
           rewrite HL. rewrite in_app_iff. simpl.
           split; intros; [right; auto | reflexivity].
      * intros i Hi.
        rewrite map_app. simpl.
        destruct (Z_lt_ge_dec r i) as [Hri | Hri].
        -- rewrite in_app_iff. simpl.
           rewrite Hright by lia.
           split; intros H.
           ++ left. exact H.
           ++ destruct H as [H | [H | H]]; auto; [subst i; lia | contradiction].
        -- assert (i = r) by lia. subst i.
           rewrite HR. rewrite in_app_iff. simpl.
           split; intros; [right; auto | reflexivity].
Qed.
Lemma GreedyProgress_score_bound__pair_update :
  forall a s l r score n,
    n = Zlength a -> Zlength s = n ->
    0 <= l -> l <= r + 2 -> r < n -> n <= 200000 ->
    (forall k, 0 <= k < n -> 1 <= Znth k a 0 <= 100000) ->
    GreedyProgress a s l r score ->
    score <= 2000000000000000.
Proof.
  intros a s l r score n Hn Hs Hl Hlr Hr Hnmax Hvalues Hprogress.
  destruct Hprogress as [pairs [Hordered Hscore]].
  destruct Hordered as [Hvalid [Horder _]].
  assert (Hfstmono : mono_inc (map fst pairs)).
  {
    intros i j Hi Hij Hj.
    rewrite Zlength_map__pair_update in Hj.
    rewrite (Znth_map_inrange__pair_update _ fst pairs (0, 0) 0 i) by lia.
    rewrite (Znth_map_inrange__pair_update _ fst pairs (0, 0) 0 j) by lia.
    exact (proj1 (Horder i j ltac:(lia))).
  }
  assert (Hsndmono : mono_inc (map (fun p => n - 1 - snd p) pairs)).
  {
    intros i j Hi Hij Hj.
    rewrite Zlength_map__pair_update in Hj.
    rewrite (Znth_map_inrange__pair_update _ (fun p => n - 1 - snd p)
      pairs (0, 0) 0 i) by lia.
    rewrite (Znth_map_inrange__pair_update _ (fun p => n - 1 - snd p)
      pairs (0, 0) 0 j) by lia.
    pose proof (proj2 (Horder i j ltac:(lia))). lia.
  }
  assert (Hfstbounds : Forall (fun x => 0 <= x < l) (map fst pairs)).
  {
    rewrite Forall_map.
    eapply Forall_impl; [|exact Hvalid].
    intros p Hp. destruct Hp as [[Hp0 _] [_ [_ [_ [Hpl _]]]]]. lia.
  }
  assert (Hsndbounds :
    Forall (fun x => 0 <= x < n - r - 1)
      (map (fun p => n - 1 - snd p) pairs)).
  {
    rewrite Forall_map.
    eapply Forall_impl; [|exact Hvalid].
    intros p Hp. destruct Hp as [[_ _] [Hpn [_ [_ [_ Hpr]]]]]. lia.
  }
  pose proof (NoDup_range_length__pair_update l (map fst pairs) Hl
    (mono_inc_NoDup__pair_update _ Hfstmono) Hfstbounds) as HlenL.
  pose proof (NoDup_range_length__pair_update (n - r - 1)
    (map (fun p => n - 1 - snd p) pairs) ltac:(lia)
    (mono_inc_NoDup__pair_update _ Hsndmono) Hsndbounds) as HlenR.
  rewrite !Zlength_map__pair_update in HlenL, HlenR.
  assert (Hcount : 2 * Zlength pairs <= n + 1) by lia.
  assert (Hpairbound : 0 <= PairScore a pairs <= Zlength pairs * n * 100000).
  {
    apply PairScore_bound_by_count__pair_update with (n := n); try assumption.
    eapply Forall_impl; [|exact Hvalid].
    intros p Hp. destruct Hp as [Hpord [Hpn _]].
    split; [exact Hpord |]. split; [rewrite Hs in Hpn; exact Hpn | exact I].
  }
  rewrite Hscore.
  pose proof (Zlength_nonneg pairs) as Hcount0.
  assert (Zlength pairs <= 100000) by lia.
  assert (0 <= n) by (rewrite Hn; apply Zlength_nonneg).
  nia.
Qed.
Lemma GreedyProgress_initial__control_projection :
  forall (a s : list Z) (n : Z),
    Zlength s = n ->
    GreedyProgress a s 0 (n - 1) 0.
Proof.
  intros a s n Hlen.
  unfold GreedyProgress.
  exists nil.
  split.
  - unfold OrderedGreedyPairs.
    split.
    + constructor.
    + split.
      * intros i j (Hi & Hij & Hj).
        change (j < 0) in Hj.
        lia.
      * split.
        -- intros i (Hi & Hbound).
           lia.
        -- intros i (Hi & Hbound).
           rewrite Hlen in Hbound.
           lia.
  - reflexivity.
Qed.
Lemma GreedyProgress_skip_non_L__frontier_skip :
  forall a s l r score,
    Znth l s 0 <> 76 ->
    GreedyProgress a s l r score ->
    GreedyProgress a s (l + 1) r score.
Proof.
  intros a s l r score HnotL [pairs [Hpairs Hscore]].
  exists pairs.
  split; [| exact Hscore].
  unfold OrderedGreedyPairs in *.
  destruct Hpairs as [Hvalid [Hordered [Hleft Hright]]].
  split.
  - apply Forall_forall.
    intros p Hin.
    apply Forall_forall with (x := p) in Hvalid; [| exact Hin].
    destruct Hvalid as [Hbounds [Hlen [HcellL [HcellR [Hpl Hrp]]]]].
    repeat split; try assumption; lia.
  - split.
    + exact Hordered.
    + split.
      * intros i Hi.
        assert (i < l \/ i = l) as Hil by lia.
        destruct Hil as [Hil | ->].
        -- apply Hleft; lia.
        -- split.
           ++ intros Heq.
              exfalso.
              exact (HnotL Heq).
           ++ intros Hin.
              apply in_map_iff in Hin.
              destruct Hin as [p [Hp Hin]].
              apply Forall_forall with (x := p) in Hvalid; [| exact Hin].
              destruct Hvalid as [_ [_ [_ [_ [Hpl _]]]]].
              simpl in Hp.
              exfalso.
              lia.
      * exact Hright.
Qed.
Lemma GreedyProgress_skip_non_R__frontier_skip :
  forall a s l r score,
    Znth r s 0 <> 82 ->
    GreedyProgress a s l r score ->
    GreedyProgress a s l (r - 1) score.
Proof.
  intros a s l r score HnotR [pairs [Hpairs Hscore]].
  exists pairs.
  split; [| exact Hscore].
  unfold OrderedGreedyPairs in *.
  destruct Hpairs as [Hvalid [Hordered [Hleft Hright]]].
  split.
  - apply Forall_forall.
    intros p Hin.
    apply Forall_forall with (x := p) in Hvalid; [| exact Hin].
    destruct Hvalid as [Hbounds [Hlen [HcellL [HcellR [Hpl Hrp]]]]].
    repeat split; try assumption; lia.
  - split.
    + exact Hordered.
    + split.
      * exact Hleft.
      * intros i Hi.
        assert (i = r \/ r < i) as Hir by lia.
        destruct Hir as [-> | Hir].
        -- split.
           ++ intros Heq.
              exfalso.
              exact (HnotR Heq).
           ++ intros Hin.
              apply in_map_iff in Hin.
              destruct Hin as [p [Hp Hin]].
              apply Forall_forall with (x := p) in Hvalid; [| exact Hin].
              destruct Hvalid as [_ [_ [_ [_ [_ Hrp]]]]].
              simpl in Hp.
              exfalso.
              lia.
        -- apply Hright; lia.
Qed.
Lemma erased_exists__final_result :
  forall xs l r,
    0 <= l <= r -> r < Zlength xs ->
    exists ys, Erased xs ys l r.
Proof.
  induction xs as [|x xs IH]; intros l r Hlr Hr.
  - unfold Zlength in Hr. simpl in Hr. lia.
  - destruct (Z.eq_dec l 0) as [Hl|Hl].
    + subst l.
      destruct (Z.eq_dec r 0) as [Hr0|Hr0].
      * subst r. exists (46 :: xs). split; [reflexivity|].
        intros i Hi.
        destruct (Z.eq_dec i 0) as [->|Hi0].
        -- left. simpl. auto.
        -- right. split; [lia|].
           rewrite !Znth_cons by lia. reflexivity.
      * assert (0 < r) by lia.
        assert (Hlr' : 0 <= 0 <= r - 1) by lia.
        assert (Hr' : r - 1 < Zlength xs).
        { rewrite Zlength_cons in Hr. lia. }
        destruct (IH 0 (r - 1) Hlr' Hr') as [ys [Hlen Herase]].
        exists (46 :: ys). split.
        -- rewrite !Zlength_cons. rewrite Hlen. reflexivity.
        -- intros i Hi.
           destruct (Z.eq_dec i 0) as [->|Hi0].
           ++ left. simpl. auto.
           ++ assert (0 < i) by lia.
              specialize (Herase (i - 1)).
              assert (Htail : 0 <= i - 1 < Zlength xs) by
                (rewrite Zlength_cons in Hi; lia).
              specialize (Herase Htail).
              rewrite !Znth_cons by lia.
              destruct Herase as [[Hin Heq]|[Hout Heq]].
              ** left. split; [lia|exact Heq].
              ** right. split; [lia|exact Heq].
    + assert (0 < l) by lia.
      assert (Hlr' : 0 <= l - 1 <= r - 1) by lia.
      assert (Hr' : r - 1 < Zlength xs).
      { rewrite Zlength_cons in Hr. lia. }
      destruct (IH (l - 1) (r - 1) Hlr' Hr') as [ys [Hlen Herase]].
      exists (x :: ys). split.
      * rewrite !Zlength_cons. rewrite Hlen. reflexivity.
      * intros i Hi.
        destruct (Z.eq_dec i 0) as [->|Hi0].
        -- right. simpl. split; [lia|reflexivity].
        -- assert (0 < i) by lia.
           specialize (Herase (i - 1)).
           assert (Htail : 0 <= i - 1 < Zlength xs) by
             (rewrite Zlength_cons in Hi; lia).
           specialize (Herase Htail).
           rewrite !Znth_cons by lia.
           destruct Herase as [[Hin Heq]|[Hout Heq]].
           ++ left. split; [lia|exact Heq].
           ++ right. split; [lia|exact Heq].
Qed.
Lemma ordered_head_tail__final_result :
  forall (p : Z * Z) ps,
    (forall i j,
       0 <= i /\ i < j /\ j < Zlength (p :: ps) ->
       fst (Znth i (p :: ps) (0, 0)) < fst (Znth j (p :: ps) (0, 0)) /\
       snd (Znth j (p :: ps) (0, 0)) < snd (Znth i (p :: ps) (0, 0))) ->
    Forall (fun q => fst p < fst q /\ snd q < snd p) ps.
Proof.
  intros p ps Horder.
  apply Forall_forall. intros q Hq.
  apply In_nth with (d := (0, 0)) in Hq.
  destruct Hq as [k [Hk Hnth]].
  apply Nat2Z.inj_lt in Hk.
  specialize (Horder 0 (Z.of_nat (S k))).
  assert (Hidx : 0 <= 0 /\ 0 < Z.of_nat (S k) /\
                 Z.of_nat (S k) < Zlength (p :: ps)).
  { rewrite Zlength_cons, Zlength_correct. lia. }
  specialize (Horder Hidx).
  unfold Znth in Horder.
  replace (Z.to_nat (Z.of_nat (S k))) with (S k) in Horder by lia.
  simpl in Horder.
  rewrite Hnth in Horder.
  exact Horder.
Qed.
Lemma ordered_pairs_nested__final_result :
  forall ps,
    (forall i j,
       0 <= i /\ i < j /\ j < Zlength ps ->
       fst (Znth i ps (0, 0)) < fst (Znth j ps (0, 0)) /\
       snd (Znth j ps (0, 0)) < snd (Znth i ps (0, 0))) ->
    ForallOrdPairs
      (fun p q => fst p < fst q /\ snd q < snd p) ps.
Proof.
  induction ps as [|p ps IH]; intros Horder.
  - constructor.
  - constructor.
    + apply ordered_head_tail__final_result. exact Horder.
    + apply IH. intros i j Hij.
      specialize (Horder (i + 1) (j + 1)).
      assert (Hshift : 0 <= i + 1 /\ i + 1 < j + 1 /\
                       j + 1 < Zlength (p :: ps)).
      { rewrite Zlength_cons in *. lia. }
      specialize (Horder Hshift).
      rewrite !Znth_cons in Horder by lia.
      replace (i + 1 - 1) with i in Horder by lia.
      replace (j + 1 - 1) with j in Horder by lia.
      exact Horder.
Qed.
Lemma nested_pairs_reachable__final_result :
  forall (a s : list Z) ps lo hi,
    Forall
      (fun p =>
         0 <= fst p < snd p /\ snd p < Zlength s /\
         Znth (fst p) s 0 = 76 /\ Znth (snd p) s 0 = 82) ps ->
    ForallOrdPairs
      (fun p q => fst p < fst q /\ snd q < snd p) ps ->
    Forall (fun p => lo < fst p /\ snd p < hi) ps ->
    exists t,
      clos_refl_trans (OpStep a) (s, 0) (t, PairScore a ps) /\
      Zlength t = Zlength s /\
      (forall i, 0 <= i < Zlength s ->
         (i <= lo \/ hi <= i) -> Znth i t 0 = Znth i s 0).
Proof.
  intros a s ps.
  induction ps as [|p ps IH]; intros lo hi Hvalid Hnested Hbounds.
  - exists s. split.
    + reflexivity.
    + split; [reflexivity|]. intros; reflexivity.
  - inversion Hvalid as [|? ? Hpvalid Hvalid']; subst.
    inversion Hnested as [|? ? Hpinner Hnested']; subst.
    inversion Hbounds as [|? ? Hpbound Hbounds']; subst.
    destruct (IH (fst p) (snd p) Hvalid' Hnested' Hpinner)
      as [t [Hreach [Hlen Houtside]]].
    destruct Hpvalid as [Hplr [Hpr [HpL HpR]]].
    assert (HtL : Znth (fst p) t 0 = 76).
    { rewrite Houtside; auto; lia. }
    assert (HtR : Znth (snd p) t 0 = 82).
    { rewrite Houtside; auto; lia. }
    destruct (erased_exists__final_result t (fst p) (snd p))
      as [t' Herased]; try lia.
    exists t'. split.
    + etransitivity; [exact Hreach|].
      unfold clos_refl_trans.
      exists 1%nat. simpl.
      exists (t', PairScore a (p :: ps)). split.
      * exists (fst p), (snd p).
        simpl fst. simpl snd.
        split; [exact Hplr|].
        split; [rewrite Hlen; exact Hpr|].
        split; [exact HtL|].
        split; [exact HtR|].
        split; [exact Herased|].
        simpl. lia.
      * reflexivity.
    + destruct Herased as [Htlen Hterase].
      split.
      * rewrite Htlen, Hlen. reflexivity.
      * intros i Hi Hfar.
        specialize (Hterase i).
        assert (Hit : 0 <= i < Zlength t) by (rewrite Hlen; exact Hi).
        specialize (Hterase Hit).
        destruct Hterase as [[Hin Heq]|[Hout Heq]].
        -- destruct Hpbound as [Hlop Hphi]. lia.
        -- rewrite Heq.
           apply Houtside; auto.
           destruct Hpbound as [Hlop Hphi]. lia.
Qed.
Lemma run_summary__final_result :
  forall (a s : list Z) st,
    clos_refl_trans (OpStep a) (s, 0) st ->
    exists ops,
      snd st = PairScore a ops /\
      Forall
        (fun p =>
           0 <= fst p < snd p /\ snd p < Zlength s /\
           Znth (fst p) s 0 = 76 /\ Znth (snd p) s 0 = 82) ops /\
      NoDup (map fst ops) /\ NoDup (map snd ops) /\
      Zlength (fst st) = Zlength s /\
      (forall i, 0 <= i < Zlength s ->
         Znth i (fst st) 0 = Znth i s 0 \/ Znth i (fst st) 0 = 46) /\
      (forall p, In p ops ->
         Znth (fst p) (fst st) 0 = 46 /\
         Znth (snd p) (fst st) 0 = 46).
Proof.
  intros a s st Hrun.
  unfold clos_refl_trans in Hrun.
  destruct Hrun as [m Hrun].
  pose proof (nsteps_nsteps' (OpStep a) m) as Hconvert.
  sets_unfold in Hconvert.
  apply Hconvert in Hrun. clear Hconvert.
  revert st Hrun.
  induction m as [|m IH]; intros st Hrun.
  - simpl in Hrun.
    revert Hrun. sets_unfold. intros Hrun. subst st.
    exists (@nil (Z * Z)).
    split; [reflexivity|].
    split; [constructor|].
    split; [constructor|].
    split; [constructor|].
    split; [reflexivity|].
    split.
    + intros i Hi. left. reflexivity.
    + intros p Hin. contradiction.
  - simpl in Hrun.
    destruct Hrun as [mid [Hprev Hstep]].
    destruct (IH mid Hprev) as
      [ops [Hscore [Hvalid [Hleftdup [Hrightdup
        [Hlen [Hsame HerasedOld]]]]]]].
    sets_unfold in Hstep.
    destruct mid as [cur oldscore].
    destruct st as [cur' newscore].
    simpl fst in *. simpl snd in *.
    destruct Hstep as [x [y [Hxy [Hylen [Hxcur [Hycur
      [Herase Hnewscore]]]]]]].
    simpl fst in Hylen, Hxcur, Hycur, Herase.
    simpl snd in Hnewscore.
    assert (Hxorig : Znth x s 0 = 76).
    { specialize (Hsame x).
      assert (Hxbound : 0 <= x < Zlength s).
      { rewrite <- Hlen. lia. }
      specialize (Hsame Hxbound).
      destruct Hsame as [Heq|Hdot].
      - rewrite <- Heq. exact Hxcur.
      - rewrite Hdot in Hxcur. lia. }
    assert (Hyorig : Znth y s 0 = 82).
    { specialize (Hsame y).
      assert (0 <= y < Zlength s) by (rewrite Hlen in Hylen; lia).
      specialize (Hsame H).
      destruct Hsame as [Heq|Hdot].
      - rewrite <- Heq. exact Hycur.
      - rewrite Hdot in Hycur. lia. }
    assert (Hxnew : Znth x cur' 0 = 46).
    { destruct Herase as [HeraseLen HeraseAt].
      specialize (HeraseAt x ltac:(lia)).
      destruct HeraseAt as [[Hin Heq]|[Hout Heq]]; [exact Heq|lia]. }
    assert (Hynew : Znth y cur' 0 = 46).
    { destruct Herase as [HeraseLen HeraseAt].
      specialize (HeraseAt y ltac:(lia)).
      destruct HeraseAt as [[Hin Heq]|[Hout Heq]]; [exact Heq|lia]. }
    exists ((x, y) :: ops).
    split.
    + simpl. rewrite Hnewscore, Hscore. lia.
    + split.
      * constructor.
        -- simpl. split; [exact Hxy|].
           split; [rewrite <- Hlen; exact Hylen|].
           split; assumption.
        -- exact Hvalid.
      * split.
        -- simpl. constructor; [|exact Hleftdup].
           intro Hin.
           apply in_map_iff in Hin.
           destruct Hin as [q [Hqx Hqin]].
           specialize (HerasedOld q Hqin).
           simpl in Hqx. subst x.
           destruct HerasedOld as [Hq _]. rewrite Hq in Hxcur. lia.
        -- split.
           ++ simpl. constructor; [|exact Hrightdup].
              intro Hin.
              apply in_map_iff in Hin.
              destruct Hin as [q [Hqy Hqin]].
              specialize (HerasedOld q Hqin).
              simpl in Hqy. subst y.
              destruct HerasedOld as [_ Hq]. rewrite Hq in Hycur. lia.
           ++ split.
              ** destruct Herase as [HeraseLen _].
                 rewrite HeraseLen, Hlen. reflexivity.
              ** split.
                 --- intros i Hi.
                     destruct Herase as [HeraseLen HeraseAt].
                     specialize (HeraseAt i ltac:(rewrite Hlen; exact Hi)).
                     destruct HeraseAt as [[Hin Heq]|[Hout Heq]].
                     { right. exact Heq. }
                     { rewrite Heq. apply Hsame. exact Hi. }
                 --- intros q Hqin.
                     simpl in Hqin. destruct Hqin as [Hq|Hqin].
                     { inversion Hq. subst q. simpl. auto. }
                     { specialize (HerasedOld q Hqin).
                       destruct HerasedOld as [HqL HqR].
                       split.
                       * destruct Herase as [HeraseLen HeraseAt].
                         specialize (HeraseAt (fst q)).
                         assert (0 <= fst q < Zlength cur).
                         { apply Forall_forall with (x := q) in Hvalid; auto.
                           lia. }
                         specialize (HeraseAt H).
                         destruct HeraseAt as [[Hin Heq]|[Hout Heq]];
                           [exact Heq|now rewrite Heq].
                       * destruct Herase as [HeraseLen HeraseAt].
                         specialize (HeraseAt (snd q)).
                         assert (0 <= snd q < Zlength cur).
                         { apply Forall_forall with (x := q) in Hvalid; auto.
                           rewrite Hlen. lia. }
                         specialize (HeraseAt H).
                         destruct HeraseAt as [[Hin Heq]|[Hout Heq]];
                           [exact Heq|now rewrite Heq]. }
Qed.
Lemma NoDup_map_filter__final_result :
  forall (A B : Type) (f : A -> B) (test : A -> bool) xs,
    NoDup (map f xs) -> NoDup (map f (filter test xs)).
Proof.
  intros A B f test xs Hnd.
  induction xs as [|x xs IH]; simpl in *.
  - constructor.
  - inversion Hnd as [|? ? Hnotin Htail]; subst.
    destruct (test x) eqn:Htest; simpl.
    + constructor.
      * intro Hin. apply Hnotin.
        apply in_map_iff in Hin.
        destruct Hin as [y [Hy Hin]].
        apply in_map_iff. exists y. split; [exact Hy|].
        apply filter_In in Hin. tauto.
      * apply IH. exact Htail.
    + apply IH. exact Htail.
Qed.
Lemma cover_count_le_greedy__final_result :
  forall (s : list Z) l r greedy ops k,
    l >= r -> l <= r + 1 ->
    Forall
      (fun p =>
         0 <= fst p < snd p /\ snd p < Zlength s /\
         Znth (fst p) s 0 = 76 /\ Znth (snd p) s 0 = 82 /\
         fst p < l /\ r < snd p) greedy ->
    (forall i, 0 <= i < l ->
       (Znth i s 0 = 76 <-> In i (map fst greedy))) ->
    (forall i, r < i < Zlength s ->
       (Znth i s 0 = 82 <-> In i (map snd greedy))) ->
    (forall i, 0 <= i < Zlength s ->
       Znth i s 0 = 76 \/ Znth i s 0 = 82) ->
    Forall
      (fun p =>
         0 <= fst p < snd p /\ snd p < Zlength s /\
         Znth (fst p) s 0 = 76 /\ Znth (snd p) s 0 = 82) ops ->
    NoDup (map fst ops) -> NoDup (map snd ops) ->
    (length
       (filter
         (fun p =>
            if Z_le_dec (fst p) k then
              if Z_le_dec k (snd p) then true else false
            else false) ops) <=
     length
       (filter
         (fun p =>
            if Z_le_dec (fst p) k then
              if Z_le_dec k (snd p) then true else false
            else false) greedy))%nat.
Proof.
  intros s l r greedy ops k Hterm Hgap Hgreedy Hleft Hright Hchars
    Hops HndL HndR.
  set (covers := fun p : Z * Z =>
    if Z_le_dec (fst p) k then
      if Z_le_dec k (snd p) then true else false
    else false).
  assert (Hleft_case : k <= r ->
    (forall q, In q (filter covers ops) -> fst q < l) ->
    (length (filter covers ops) <= length (filter covers greedy))%nat).
  { intros Hkr Hstrict.
    assert (Hnd : NoDup (map fst (filter covers ops))).
    { apply NoDup_map_filter__final_result. exact HndL. }
    assert (Hincl : incl (map fst (filter covers ops))
                         (map fst (filter covers greedy))).
    { intros x Hxin.
      apply in_map_iff in Hxin.
      destruct Hxin as [q [Hqx Hqf]]. subst x.
      pose proof Hqf as Hqfiltered.
      apply filter_In in Hqf. destruct Hqf as [Hqin Hcover].
      unfold covers in Hcover.
      destruct (Z_le_dec (fst q) k) as [Hqk|Hqk]; try discriminate.
      destruct (Z_le_dec k (snd q)) as [Hkq|Hkq]; try discriminate.
      apply Forall_forall with (x := q) in Hops; auto.
      destruct Hops as [Hqlr [Hqr [HqL HqR]]].
      assert (Hmap : In (fst q) (map fst greedy)).
      { specialize (Hstrict q Hqfiltered).
        apply (proj1 (Hleft (fst q) ltac:(lia))). exact HqL. }
      apply in_map_iff in Hmap.
      destruct Hmap as [p [Hp Hpin]].
      apply in_map_iff. exists p. split; [exact Hp|].
      apply filter_In. split; [exact Hpin|].
      unfold covers.
      apply Forall_forall with (x := p) in Hgreedy; auto.
      destruct Hgreedy as [Hplr [Hpr [HpL [HpR [Hpl Hrp]]]]].
      rewrite Hp.
      destruct (Z_le_dec (fst q) k); [|lia].
      destruct (Z_le_dec k (snd p)); [reflexivity|lia]. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
    rewrite !length_map in Hlen. exact Hlen. }
  assert (Hright_case : l <= k ->
    (forall q, In q (filter covers ops) -> r < snd q) ->
    (length (filter covers ops) <= length (filter covers greedy))%nat).
  { intros Hlk Hstrict.
    assert (Hnd : NoDup (map snd (filter covers ops))).
    { apply NoDup_map_filter__final_result. exact HndR. }
    assert (Hincl : incl (map snd (filter covers ops))
                         (map snd (filter covers greedy))).
    { intros y Hyin.
      apply in_map_iff in Hyin.
      destruct Hyin as [q [Hqy Hqf]]. subst y.
      pose proof Hqf as Hqfiltered.
      apply filter_In in Hqf. destruct Hqf as [Hqin Hcover].
      unfold covers in Hcover.
      destruct (Z_le_dec (fst q) k) as [Hqk|Hqk]; try discriminate.
      destruct (Z_le_dec k (snd q)) as [Hkq|Hkq]; try discriminate.
      apply Forall_forall with (x := q) in Hops; auto.
      destruct Hops as [Hqlr [Hqr [HqL HqR]]].
      assert (Hmap : In (snd q) (map snd greedy)).
      { specialize (Hstrict q Hqfiltered).
        apply (proj1 (Hright (snd q) ltac:(lia))). exact HqR. }
      apply in_map_iff in Hmap.
      destruct Hmap as [p [Hp Hpin]].
      apply in_map_iff. exists p. split; [exact Hp|].
      apply filter_In. split; [exact Hpin|].
      unfold covers.
      apply Forall_forall with (x := p) in Hgreedy; auto.
      destruct Hgreedy as [Hplr [Hpr [HpL [HpR [Hpl Hrp]]]]].
      rewrite Hp.
      destruct (Z_le_dec (fst p) k); [|lia].
      destruct (Z_le_dec k (snd q)); [reflexivity|lia]. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
    rewrite !length_map in Hlen. exact Hlen. }
  destruct (Z_lt_dec k l) as [Hkl|Hkl].
  { apply Hleft_case; [lia|]. intros q Hqf.
    apply filter_In in Hqf. destruct Hqf as [_ Hcov].
    unfold covers in Hcov.
    destruct (Z_le_dec (fst q) k); try discriminate.
    destruct (Z_le_dec k (snd q)); try discriminate. lia. }
  destruct (Z_lt_dec r k) as [Hrk|Hrk].
  { apply Hright_case; [lia|]. intros q Hqf.
    apply filter_In in Hqf. destruct Hqf as [_ Hcov].
    unfold covers in Hcov.
    destruct (Z_le_dec (fst q) k); try discriminate.
    destruct (Z_le_dec k (snd q)); try discriminate. lia. }
  assert (Hk : k = l /\ k = r) by lia.
  destruct Hk as [-> Hlr]. subst r.
  destruct (filter covers ops) as [|q qs] eqn:Hfiltered.
  - simpl. lia.
  - assert (Hqin : In q ops).
    { assert (Hqf : In q (filter covers ops)).
      { rewrite Hfiltered. left. reflexivity. }
      apply filter_In in Hqf. exact (proj1 Hqf). }
    pose proof Hops as HopsAll.
    apply Forall_forall with (x := q) in Hops; auto.
    destruct Hops as [Hqlr [Hqr [HqL HqR]]].
    assert (Hkbounds : 0 <= l < Zlength s).
    { assert (Hqf : In q (filter covers ops)).
      { rewrite Hfiltered. left. reflexivity. }
      apply filter_In in Hqf. destruct Hqf as [_ Hcov].
      unfold covers in Hcov.
      destruct (Z_le_dec (fst q) l); try discriminate.
      destruct (Z_le_dec l (snd q)); try discriminate.
      lia. }
    specialize (Hchars l Hkbounds).
    destruct Hchars as [HcharL|HcharR].
    + apply Hright_case; [lia|]. intros q' Hq'f.
      rewrite <- Hfiltered in Hq'f.
      apply filter_In in Hq'f. destruct Hq'f as [Hq'in Hq'cov].
      apply Forall_forall with (x := q') in HopsAll; auto.
      destruct HopsAll as [Hq'lr [Hq'r [Hq'L Hq'R]]].
      unfold covers in Hq'cov.
      destruct (Z_le_dec (fst q') l); try discriminate.
      destruct (Z_le_dec l (snd q')); try discriminate.
      destruct (Z.eq_dec (snd q') l) as [Heq|Heq]; [|lia].
      rewrite Heq in Hq'R. rewrite Hq'R in HcharL. lia.
    + apply Hleft_case; [lia|]. intros q' Hq'f.
      rewrite <- Hfiltered in Hq'f.
      apply filter_In in Hq'f. destruct Hq'f as [Hq'in Hq'cov].
      apply Forall_forall with (x := q') in HopsAll; auto.
      destruct HopsAll as [Hq'lr [Hq'r [Hq'L Hq'R]]].
      unfold covers in Hq'cov.
      destruct (Z_le_dec (fst q') l); try discriminate.
      destruct (Z_le_dec l (snd q')); try discriminate.
      destruct (Z.eq_dec (fst q') l) as [Heq|Heq]; [|lia].
      rewrite Heq in Hq'L. rewrite Hq'L in HcharR. lia.
Qed.
Lemma sum_cover_indicator__final_result :
  forall n l r (f : Z -> Z),
    0 <= l < r -> r < n ->
    sum (fun k => 0 <= k < n)
      (fun k =>
         if Z_le_dec l k then
           if Z_le_dec k r then f k else 0
         else 0) =
    sum_range l r f.
Proof.
  intros n l r f Hlr Hrn.
  rewrite (sum_Z_range_split 0 l n) by lia.
  rewrite (sum_Z_range_split l (r + 1) n) by lia.
  rewrite (sum_Z_range_eq_zero 0 l).
  2: { intros k Hk.
       destruct (Z_le_dec l k); [lia|reflexivity]. }
  rewrite (sum_Z_range_eq_zero (r + 1) n).
  2: { intros k Hk.
       destruct (Z_le_dec l k); [|reflexivity].
       destruct (Z_le_dec k r); [lia|reflexivity]. }
  rewrite Z.add_0_l, Z.add_0_r.
  unfold sum_range.
  apply sum_Z_range_ext.
  intros k Hk.
  destruct (Z_le_dec l k); [|lia].
  destruct (Z_le_dec k r); [reflexivity|lia].
Qed.
Lemma PairScore_as_cover_sum__final_result :
  forall (a : list Z) ps n,
    Forall (fun p => 0 <= fst p < snd p /\ snd p < n) ps ->
    PairScore a ps =
    sum (fun k => 0 <= k < n)
      (fun k =>
         Znth k a 0 *
         Z.of_nat
           (length
             (filter
               (fun p =>
                  if Z_le_dec (fst p) k then
                    if Z_le_dec k (snd p) then true else false
                  else false) ps))).
Proof.
  intros a ps n Hvalid.
  induction ps as [|p ps IH].
  - simpl. symmetry. apply sum_Z_range_eq_zero.
    intros k Hk. ring.
  - inversion Hvalid as [|? ? Hp Hvalid']; subst.
    specialize (IH Hvalid').
    simpl PairScore.
    rewrite <- (sum_cover_indicator__final_result n (fst p) (snd p)
      (fun k => Znth k a 0)) by tauto.
    rewrite IH.
    rewrite <- sum_Z_range_add.
    apply sum_Z_range_ext.
    intros k Hk.
    simpl filter.
    destruct (Z_le_dec (fst p) k) as [Hpk|Hpk].
    + destruct (Z_le_dec k (snd p)) as [Hkp|Hkp].
      * simpl. lia.
      * simpl. lia.
    + simpl. lia.
Qed.
Lemma terminal_GreedyProgress_Spec__final_result :
  forall (n : Z) (s a : list Z) (score r l : Z),
    2 <= n -> n <= 200000 ->
    (forall k, 0 <= k /\ k < n ->
       1 <= Znth k a 0 /\ Znth k a 0 <= 100000) ->
    (forall k, 0 <= k /\ k < n ->
       Znth k s 0 = 76 \/ Znth k s 0 = 82) ->
    n = Zlength a -> Zlength s = n ->
    0 <= l -> l < n -> 0 <= r -> r < n ->
    l <= r + 1 -> l >= r ->
    GreedyProgress a s l r score ->
    Spec a s score.
Proof.
  intros n s a score r l Hn Hnmax Ha Hs Halen Hslen
    Hl0 Hln Hr0 Hrn Hlr Hterm Hgreedy.
  destruct Hgreedy as [pairs [Hpairs Hscore]].
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists score.
  split.
  - split.
    + destruct Hpairs as [Hvalid [Horder [Hleft Hright]]].
      assert (Hvalid' :
        Forall
          (fun p =>
             0 <= fst p < snd p /\ snd p < Zlength s /\
             Znth (fst p) s 0 = 76 /\ Znth (snd p) s 0 = 82) pairs).
      { apply Forall_forall. intros p Hin.
        apply Forall_forall with (x := p) in Hvalid; auto.
        tauto. }
      assert (Hnested :
        ForallOrdPairs
          (fun p q => fst p < fst q /\ snd q < snd p) pairs).
      { apply ordered_pairs_nested__final_result. exact Horder. }
      assert (Hbounds :
        Forall (fun p => -1 < fst p /\ snd p < n) pairs).
      { apply Forall_forall. intros p Hin.
        apply Forall_forall with (x := p) in Hvalid; auto.
        rewrite Hslen in Hvalid. lia. }
      destruct (nested_pairs_reachable__final_result
        a s pairs (-1) n Hvalid' Hnested Hbounds)
        as [t [Hreach [Htlen Houtside]]].
      exists (t, PairScore a pairs). split; [exact Hreach|].
      simpl. exact Hscore.
    + intros b [st [Hrun Hb]]. subst b.
      destruct (run_summary__final_result a s st Hrun) as
        [ops [HopsScore [HopsValid [HndL [HndR
          [HstLen [HstSame HstErased]]]]]]].
      rewrite HopsScore, Hscore.
      destruct Hpairs as [Hgreedy [Horder [Hleft Hright]]].
      assert (HpairBounds :
        Forall (fun p => 0 <= fst p < snd p /\ snd p < n) pairs).
      { apply Forall_forall. intros p Hpin.
        apply Forall_forall with (x := p) in Hgreedy; auto.
        rewrite <- Hslen. tauto. }
      assert (HopsBounds :
        Forall (fun p => 0 <= fst p < snd p /\ snd p < n) ops).
      { apply Forall_forall. intros p Hpin.
        apply Forall_forall with (x := p) in HopsValid; auto.
        rewrite <- Hslen. tauto. }
      rewrite (PairScore_as_cover_sum__final_result a ops n HopsBounds).
      rewrite (PairScore_as_cover_sum__final_result a pairs n HpairBounds).
      apply sum_Z_range_le.
      intros k Hk.
      assert (Hchars' : forall i, 0 <= i < Zlength s ->
        Znth i s 0 = 76 \/ Znth i s 0 = 82).
      { intros i Hi. apply Hs. rewrite Hslen in Hi. exact Hi. }
      pose proof (cover_count_le_greedy__final_result
        s l r pairs ops k Hterm Hlr Hgreedy Hleft Hright Hchars'
        HopsValid HndL HndR) as Hcount.
      apply Nat2Z.inj_le in Hcount.
      specialize (Ha k Hk).
      nia.
  - reflexivity.
Qed.
