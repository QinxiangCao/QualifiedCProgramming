Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition RespectsDistance (k : Z) (occupied : Z -> Prop) : Prop :=
  forall i j, occupied i -> occupied j -> i <> j -> Z.abs (i - j) > k.

Definition AdditionalTables (s : list Z) (k : Z) (extra : Z -> Prop) : Prop :=
  (forall i, extra i -> 0 <= i < Zlength s /\ Znth i s 48 = 48) /\
  RespectsDistance k
    (fun i => (0 <= i < Zlength s /\ Znth i s 48 = 49) \/ extra i).

Definition Pre (k : Z) (s : list Z) : Prop :=
  1 <= k <= Zlength s /\ Zlength s <= 200000 /\
  (* Character codes: '0' = 48, '1' = 49. *)
  Forall (fun c => c = 48 \/ c = 49) s /\
  RespectsDistance k (fun i => 0 <= i < Zlength s /\ Znth i s 48 = 49).

Definition Spec (k : Z) (s : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      AdditionalTables s k (fst candidate) /\
      snd candidate = #(fun i : Z =>
        0 <= i < Zlength s /\ fst candidate i))
    snd out.

(** [RightNearest] gives the first originally occupied table at or to the
    right of [from].  [Zlength s + k] is the sentinel used when that suffix
    contains no occupied table. *)
Definition RightNearest
    (s : list Z) (k from nearest : Z) : Prop :=
  0 <= from <= Zlength s /\
  ((nearest = Zlength s + k /\
    forall j, from <= j < Zlength s -> Znth j s 48 <> 49) \/
   (from <= nearest < Zlength s /\
    Znth nearest s 48 = 49 /\
    forall j, from <= j < nearest -> Znth j s 48 <> 49)).

(** Pointwise meaning of the initialized suffix of the auxiliary table. *)
Definition RightNearestSuffix
    (s : list Z) (k from : Z) (values : list Z) : Prop :=
  Zlength values = Zlength s - from /\
  forall off, 0 <= off < Zlength values ->
    RightNearest s k (from + off) (Znth off values 0).

(** [LastOccupiedBefore] gives the rightmost original or additional occupied
    position in the processed prefix.  The negative value [-k-1] is the same
    canonical sentinel used by the C loop when that prefix is empty. *)
Definition LastOccupiedBefore
    (s : list Z) (k : Z) (extra : Z -> Prop)
    (processed last : Z) : Prop :=
  (last = - k - 1 /\
   forall j, 0 <= j < processed ->
     ~ ((0 <= j < Zlength s /\ Znth j s 48 = 49) \/ extra j)) \/
  (0 <= last < processed /\
   ((0 <= last < Zlength s /\ Znth last s 48 = 49) \/ extra last) /\
   forall j, last < j < processed ->
     ~ ((0 <= j < Zlength s /\ Znth j s 48 = 49) \/ extra j)).

(** Mathematical state of a left-to-right greedy placement.  It exposes an
    actually chosen feasible set, the last occupied position, its cardinality,
    and optimality among all feasible additions restricted to the processed
    prefix.  Among equally large prefix placements, the chosen placement ends
    no later than a competitor.  This canonical dominance is what makes a
    left-distance skip preserve optimality.  The predicate is independent of
    how the program finds that set. *)
Definition PrefixPlacementState
    (s : list Z) (k processed last answer : Z) : Prop :=
  0 <= processed <= Zlength s /\
  exists extra : Z -> Prop,
    AdditionalTables s k extra /\
    (forall j, extra j -> j < processed) /\
    answer = #(fun j : Z => 0 <= j < processed /\ extra j) /\
    LastOccupiedBefore s k extra processed last /\
    (forall competitor : Z -> Prop,
      AdditionalTables s k competitor ->
      #(fun j : Z => 0 <= j < processed /\ competitor j) <= answer) /\
    forall competitor,
      AdditionalTables s k competitor ->
      #(fun j : Z => 0 <= j < processed /\ competitor j) = answer ->
      exists competitor_last,
        LastOccupiedBefore s k competitor processed competitor_last /\
        last <= competitor_last.

Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Psatz.
Lemma right_nearest_bounds__nearest_suffix :
  forall s k from nearest,
    0 <= k ->
    RightNearest s k from nearest ->
    from <= nearest <= Zlength s + k.
Proof.
  intros s k from nearest Hk Hnearest.
  unfold RightNearest in Hnearest.
  destruct Hnearest as [Hfrom [[-> _] | [Hbounds _]]]; lia.
Qed.
Lemma right_nearest_suffix_empty__nearest_suffix :
  forall s k,
    0 <= k ->
    RightNearestSuffix s k (Zlength s) nil.
Proof.
  intros s k Hk.
  unfold RightNearestSuffix.
  rewrite Zlength_nil.
  split; [lia |].
  intros off Hoff.
  lia.
Qed.
Lemma right_nearest_suffix_cons_hit__nearest_suffix :
  forall s k from values,
    0 <= from < Zlength s ->
    Znth from s 48 = 49 ->
    RightNearestSuffix s k (from + 1) values ->
    RightNearestSuffix s k from (from :: values).
Proof.
  intros s k from values Hfrom Hhit Hsuffix.
  unfold RightNearestSuffix in *.
  destruct Hsuffix as [Hlen Hsuffix].
  split.
  - rewrite Zlength_cons, Hlen. lia.
  - intros off Hoff.
    rewrite Zlength_cons in Hoff.
    destruct (Z.eq_dec off 0) as [-> | Hoff0].
    + rewrite Znth0_cons.
      unfold RightNearest.
      split; [lia |].
      right.
      repeat split; try lia; auto.
    + rewrite Znth_cons by lia.
      specialize (Hsuffix (off - 1)).
      replace (from + off) with (from + 1 + (off - 1)) by lia.
      apply Hsuffix.
      lia.
Qed.
Lemma right_nearest_suffix_cons_miss__nearest_suffix :
  forall s k from nearest values,
    0 <= from < Zlength s ->
    Znth from s 48 <> 49 ->
    RightNearest s k (from + 1) nearest ->
    RightNearestSuffix s k (from + 1) values ->
    RightNearestSuffix s k from (nearest :: values).
Proof.
  intros s k from nearest values Hfrom Hmiss Hnearest Hsuffix.
  assert (Hnearest_from : RightNearest s k from nearest).
  {
    unfold RightNearest in *.
    destruct Hnearest as [Hrange [[Hsent Hnone] | [Hbounds [Hhit Hnone]]]].
    - split; [lia |].
      left. split; [exact Hsent |].
      intros j Hj.
      destruct (Z.eq_dec j from) as [-> | Hneq]; [exact Hmiss |].
      apply Hnone. lia.
    - split; [lia |].
      right. repeat split; try lia; auto.
      intros j Hj.
      destruct (Z.eq_dec j from) as [-> | Hneq]; [exact Hmiss |].
      apply Hnone. lia.
  }
  unfold RightNearestSuffix in *.
  destruct Hsuffix as [Hlen Hsuffix].
  split.
  - rewrite Zlength_cons, Hlen. lia.
  - intros off Hoff.
    rewrite Zlength_cons in Hoff.
    destruct (Z.eq_dec off 0) as [-> | Hoff0].
    + rewrite Znth0_cons.
      replace (from + 0) with from by lia.
      exact Hnearest_from.
    + rewrite Znth_cons by lia.
      specialize (Hsuffix (off - 1)).
      replace (from + off) with (from + 1 + (off - 1)) by lia.
      apply Hsuffix.
      lia.
Qed.
Lemma set_card_iff__greedy_transitions :
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
Lemma set_card_Z_as_sum__greedy_transitions :
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
Lemma set_card_Z_extend_true__greedy_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun x : Z => low <= x < high + 1 /\ P x) =
    #(fun x : Z => low <= x < high /\ P x) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__greedy_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [|contradiction].
  lia.
Qed.
Lemma set_card_Z_extend_false__greedy_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun x : Z => low <= x < high + 1 /\ P x) =
    #(fun x : Z => low <= x < high /\ P x).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__greedy_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction |].
  lia.
Qed.
Lemma prefix_placement_initial__greedy_transitions :
  forall s k,
    Pre k s ->
    PrefixPlacementState s k 0 (- k - 1) 0.
Proof.
  intros s k Hpre.
  destruct Hpre as [[Hk Hklen] [Hlen [Hchars Horig]]].
  unfold PrefixPlacementState.
  split; [lia |].
  exists (fun _ : Z => False).
  split.
  - unfold AdditionalTables. split.
    + intros j Hj. contradiction.
    + intros x y [Hx | Hx] [Hy | Hy] Hneq;
        try contradiction; eapply Horig; eauto.
  - split.
    + intros j Hj. contradiction.
    + split.
      * rewrite set_card_Z_as_sum__greedy_transitions.
        rewrite SumLib.ZRange.sum_Z_range_empty by lia.
        reflexivity.
      * split.
        -- unfold LastOccupiedBefore. left. split; [reflexivity | lia].
        -- split.
           ++ intros competitor Hcompetitor.
              rewrite set_card_Z_as_sum__greedy_transitions.
              rewrite SumLib.ZRange.sum_Z_range_empty by lia.
              lia.
           ++ intros competitor Hcompetitor Hcard.
              exists (- k - 1).
              split; [|lia].
              unfold LastOccupiedBefore. left. split; [reflexivity | lia].
Qed.
Lemma occupied_left_of_last__greedy_transitions :
  forall s k extra processed last j,
    LastOccupiedBefore s k extra processed last ->
    0 <= j < processed ->
    ((0 <= j < Zlength s /\ Znth j s 48 = 49) \/ extra j) ->
    j <= last.
Proof.
  intros s k extra processed last j Hlast Hj Hocc.
  destruct Hlast as [[Hsent Hnone] | [[Hlast0 Hlastp] [Hocclast Hnone]]].
  - exfalso. apply (Hnone j Hj Hocc).
  - destruct (Z_lt_ge_dec last j); [exfalso; eapply Hnone; eauto; lia | lia].
Qed.
Lemma last_lower_bound__greedy_transitions :
  forall s k extra processed last,
    0 <= k ->
    LastOccupiedBefore s k extra processed last ->
    - k - 1 <= last.
Proof.
  intros s k extra processed last Hk Hlast.
  destruct Hlast as [[-> _] | [[Hlast _] _]]; lia.
Qed.
Lemma right_nearest_excludes_close__greedy_transitions :
  forall s k i r,
    0 <= i < Zlength s ->
    Znth i s 48 <> 49 ->
    RightNearest s k i r ->
    r - i <= k ->
    exists q, i < q <= i + k /\ 0 <= q < Zlength s /\ Znth q s 48 = 49.
Proof.
  intros s k i r Hi Hempty Hr Hgap.
  unfold RightNearest in Hr.
  destruct Hr as [_ [[Hsent Hnone] | [[Hir Hrlen] [Hocc Hnone]]]].
  - subst r. lia.
  - assert (Hneq : i <> r) by (intro Heq; subst r; contradiction).
    exists r. repeat split; try lia; exact Hocc.
Qed.
Lemma extra_not_at_original__greedy_transitions :
  forall s k extra i,
    AdditionalTables s k extra ->
    Znth i s 48 = 49 ->
    ~ extra i.
Proof.
  intros s k extra i [Hsupport Hdist] Hocc Hex.
  specialize (Hsupport i Hex). lia.
Qed.
Lemma prefix_placement_add__greedy_transitions :
  forall s k values i last answer,
    Pre k s ->
    0 <= i < Zlength s ->
    Znth i s 48 = 48 ->
    PrefixPlacementState s k i last answer ->
    i - last > k ->
    RightNearestSuffix s k 0 values ->
    Znth i values 0 - i > k ->
    PrefixPlacementState s k (i + 1) i (answer + 1).
Proof.
  intros s k values i last answer Hpre Hi Hempty Hstate Hleft Hsuffix Hright.
  destruct Hpre as [[Hk Hklen] Hpre_rest].
  unfold PrefixPlacementState in Hstate |- *.
  destruct Hstate as [Hprocessed [extra [Hadd [Hsupport [Hanswer [Hlast [Hopt Hdom]]]]]]].
  split; [lia |].
  exists (fun x => extra x \/ x = i).
  assert (Hextra_i : ~ extra i) by (intro Hx; specialize (Hsupport i Hx); lia).
  assert (Hr_i : RightNearest s k i (Znth i values 0)).
  {
    unfold RightNearestSuffix in Hsuffix.
    destruct Hsuffix as [Hvalues Hsuffix].
    apply Hsuffix. lia.
  }
  assert (Hfar_orig : forall x,
    (0 <= x < Zlength s /\ Znth x s 48 = 49) ->
    x <> i -> Z.abs (x - i) > k).
  {
    intros x Hxorig Hxi.
    destruct (Z_lt_ge_dec x i) as [Hxi_lt | Hxi_ge].
    - assert (Hxle : x <= last).
      {
        eapply occupied_left_of_last__greedy_transitions.
        + exact Hlast.
        + lia.
        + left. exact Hxorig.
      }
      rewrite Z.abs_neq by lia. lia.
    - assert (Hix : i < x) by lia.
      unfold RightNearest in Hr_i.
      destruct Hr_i as [_ [[Hsent Hnone] | [[Hir Hrlen] [Hrocc Hnone]]]].
      + exfalso. apply (Hnone x); lia.
      + assert (Znth i values 0 <= x).
        {
          destruct (Z_lt_ge_dec x (Znth i values 0)); [|lia].
          exfalso. apply (Hnone x); lia.
        }
        rewrite Z.abs_eq by lia. lia.
  }
  assert (Hnewadd : AdditionalTables s k (fun x => extra x \/ x = i)).
  {
    unfold AdditionalTables in Hadd |- *.
    destruct Hadd as [Hsupport_full Hdistance].
    split.
    - intros x [Hx | ->]; [apply Hsupport_full; exact Hx | tauto].
    - unfold RespectsDistance in Hdistance |- *.
      intros x y Hx Hy Hneq.
      destruct Hx as [Hxorig | [Hxextra | ->]];
      destruct Hy as [Hyorig | [Hyextra | ->]].
      + eapply Hdistance; eauto.
      + eapply Hdistance; eauto.
      + apply Hfar_orig; assumption.
      + eapply Hdistance; eauto.
      + eapply Hdistance; eauto.
      + pose proof (Hsupport_full x Hxextra) as Hxrange.
        assert (Hxlt : x < i) by (apply Hsupport in Hxextra; lia).
        replace (Z.abs (x - i)) with (i - x) by (rewrite Z.abs_neq; lia).
        assert (Hxle : x <= last).
        { eapply occupied_left_of_last__greedy_transitions.
          - exact Hlast.
          - lia.
          - right; exact Hxextra. }
        lia.
      + pose proof (Hfar_orig y Hyorig ltac:(lia)) as Hfar.
        destruct (Z_lt_ge_dec y i).
        * rewrite Z.abs_neq in Hfar by lia.
          rewrite Z.abs_eq by lia. lia.
        * rewrite Z.abs_eq in Hfar by lia.
          rewrite Z.abs_neq by lia. lia.
      + pose proof (Hsupport_full y Hyextra) as Hyrange.
        assert (Hylt : y < i) by (apply Hsupport in Hyextra; lia).
        replace (Z.abs (i - y)) with (i - y) by (rewrite Z.abs_eq; lia).
        assert (Hyle : y <= last).
        { eapply occupied_left_of_last__greedy_transitions.
          - exact Hlast.
          - lia.
          - right; exact Hyextra. }
        lia.
      + contradiction.
  }
  split; [exact Hnewadd |].
  split.
  - intros x [Hx | ->]; [specialize (Hsupport x Hx); lia | lia].
  - split.
    + rewrite set_card_Z_extend_true__greedy_transitions by (lia || tauto).
      assert (Hsame :
        #(fun x : Z => 0 <= x < i /\ (extra x \/ x = i)) =
        #(fun x : Z => 0 <= x < i /\ extra x)).
      { apply set_card_iff__greedy_transitions. intro x. intuition lia. }
      rewrite Hsame. lia.
    + split.
      * unfold LastOccupiedBefore. right.
        split; [lia |]. split.
        -- right; right; reflexivity.
        -- intros x Hx. lia.
      * split.
        -- intros competitor Hcompetitor.
           destruct (classic (competitor i)) as [Hci | Hnci].
           ++ rewrite set_card_Z_extend_true__greedy_transitions by (lia || assumption).
              specialize (Hopt competitor Hcompetitor). lia.
           ++ rewrite set_card_Z_extend_false__greedy_transitions by (lia || assumption).
              specialize (Hopt competitor Hcompetitor). lia.
        -- intros competitor Hcompetitor Hcard.
           assert (Hci : competitor i).
           {
             destruct (classic (competitor i)) as [Hci | Hnci]; [exact Hci |].
             rewrite set_card_Z_extend_false__greedy_transitions in Hcard by (lia || assumption).
             specialize (Hopt competitor Hcompetitor). lia.
           }
           exists i. split; [|lia].
           unfold LastOccupiedBefore. right.
           split; [lia |]. split.
           ++ right; exact Hci.
           ++ intros x Hx. lia.
Qed.
Lemma competitor_cannot_use_left_skip__greedy_transitions :
  forall s k i last answer competitor,
    Pre k s ->
    0 <= i < Zlength s ->
    PrefixPlacementState s k i last answer ->
    i - last <= k ->
    AdditionalTables s k competitor ->
    #(fun x : Z => 0 <= x < i /\ competitor x) = answer ->
    ~ competitor i.
Proof.
  intros s k i last answer competitor Hpre Hi Hstate Hgap Hcomp Hcardeq Hci.
  destruct Hpre as [[Hk Hklen] Hpre_rest].
  unfold PrefixPlacementState in Hstate.
  destruct Hstate as [Hprocessed [extra [Hadd [Hsupport [Hanswer [Hlast [Hopt Hdom]]]]]]].
  specialize (Hdom competitor Hcomp Hcardeq).
  destruct Hdom as [competitor_last [Hclast Hlastle]].
  destruct Hclast as [[Hsent Hnone] | [[Hcl0 Hcli] [Hclocc Hnone]]].
  - subst competitor_last.
    pose proof (last_lower_bound__greedy_transitions s k extra i last ltac:(lia) Hlast).
    lia.
  - destruct Hcomp as [Hcsupport Hcdist].
    specialize (Hcdist i competitor_last).
    assert (Hdist : Z.abs (i - competitor_last) > k).
    {
      apply Hcdist.
      - right. exact Hci.
      - exact Hclocc.
      - lia.
    }
    rewrite Z.abs_eq in Hdist by lia. lia.
Qed.
Lemma prefix_placement_skip_left__greedy_transitions :
  forall s k i last answer,
    Pre k s ->
    0 <= i < Zlength s ->
    Znth i s 48 = 48 ->
    PrefixPlacementState s k i last answer ->
    i - last <= k ->
    PrefixPlacementState s k (i + 1) last answer.
Proof.
  intros s k i last answer Hpre Hi Hempty Hstate Hgap.
  pose proof Hstate as Hstate0.
  unfold PrefixPlacementState in Hstate |- *.
  destruct Hstate as [Hprocessed [extra [Hadd [Hsupport [Hanswer [Hlast [Hopt Hdom]]]]]]].
  split; [lia |]. exists extra.
  assert (Hextra_i : ~ extra i) by (intro Hx; specialize (Hsupport i Hx); lia).
  assert (Hnotocc_i : ~ ((0 <= i < Zlength s /\ Znth i s 48 = 49) \/ extra i)).
  { intros [[_ H] | H]; [lia | contradiction]. }
  assert (Hlast_i : last < i).
  {
    destruct Hpre as [[Hk _] _].
    destruct Hlast as [[Hsent _] | [[_ Hli] _]]; [subst last; lia | lia].
  }
  split; [exact Hadd |].
  split.
  - intros x Hx. specialize (Hsupport x Hx). lia.
  - split.
    + rewrite set_card_Z_extend_false__greedy_transitions by (lia || assumption). exact Hanswer.
    + split.
      * unfold LastOccupiedBefore in Hlast |- *.
    destruct Hlast as [[Hsent Hnone] | [[Hl0 Hli] [Hlocc Hnone]]].
        -- left. split; [exact Hsent |]. intros x Hx.
      destruct (Z_lt_ge_dec x i); [apply Hnone; lia |].
      assert (x = i) by lia. subst x. exact Hnotocc_i.
        -- right. repeat split; try lia; try exact Hlocc.
      intros x Hx. destruct (Z_lt_ge_dec x i); [apply Hnone; lia |].
      assert (x = i) by lia. subst x. exact Hnotocc_i.
      * split.
        -- intros competitor Hcomp.
           destruct (classic (competitor i)) as [Hci | Hnci].
           ++ rewrite set_card_Z_extend_true__greedy_transitions by (lia || assumption).
              pose proof (Hopt competitor Hcomp) as Hle.
              destruct (Z_lt_ge_dec
                (#(fun x : Z => 0 <= x < i /\ competitor x)) answer) as [Hlt | Hge]; [lia |].
              assert (Heq : #(fun x : Z => 0 <= x < i /\ competitor x) = answer) by lia.
              exfalso. eapply competitor_cannot_use_left_skip__greedy_transitions; eauto.
           ++ rewrite set_card_Z_extend_false__greedy_transitions by (lia || assumption).
              apply Hopt; exact Hcomp.
        -- intros competitor Hcomp Hcard.
           destruct (classic (competitor i)) as [Hci | Hnci].
           ++ exists i. split; [|lia].
              unfold LastOccupiedBefore. right.
              split; [lia |]. split.
              ** right; exact Hci.
              ** intros x Hx. lia.
           ++ rewrite set_card_Z_extend_false__greedy_transitions in Hcard by (lia || assumption).
              specialize (Hdom competitor Hcomp Hcard).
              destruct Hdom as [competitor_last [Hclast Hle]].
              exists competitor_last. split; [|exact Hle].
              unfold LastOccupiedBefore in Hclast |- *.
              destruct Hclast as [[Hsent Hnone] | [[Hl0 Hli] [Hlocc Hnone]]].
              ** left. split; [exact Hsent |]. intros x Hx.
                 destruct (Z_lt_ge_dec x i); [apply Hnone; lia |].
                 assert (x = i) by lia. subst x. intros [Horig | Hextra].
                 --- destruct Horig as [_ H49]. lia.
                 --- contradiction.
              ** right. split; [lia |]. split; [exact Hlocc |].
                 intros x Hx. destruct (Z_lt_ge_dec x i); [apply Hnone; lia |].
                 assert (x = i) by lia. subst x. intros [Horig | Hextra].
                 --- destruct Horig as [_ H49]. lia.
                 --- contradiction.
Qed.
Lemma prefix_placement_skip_right__greedy_transitions :
  forall s k values i last answer,
    Pre k s ->
    0 <= i < Zlength s ->
    Znth i s 48 = 48 ->
    PrefixPlacementState s k i last answer ->
    RightNearestSuffix s k 0 values ->
    Znth i values 0 - i <= k ->
    PrefixPlacementState s k (i + 1) last answer.
Proof.
  intros s k values i last answer Hpre Hi Hempty Hstate Hsuffix Hgap.
  assert (Hr_i : RightNearest s k i (Znth i values 0)).
  {
    unfold RightNearestSuffix in Hsuffix.
    destruct Hsuffix as [Hvalues Hsuffix]. apply Hsuffix. lia.
  }
  destruct (right_nearest_excludes_close__greedy_transitions
    s k i (Znth i values 0) Hi ltac:(lia) Hr_i Hgap)
    as [q [[Hiq Hqgap] [[Hq0 Hqlen] Hqocc]]].
  unfold PrefixPlacementState in Hstate |- *.
  destruct Hstate as [Hprocessed [extra [Hadd [Hsupport [Hanswer [Hlast [Hopt Hdom]]]]]]].
  split; [lia |]. exists extra.
  assert (Hextra_i : ~ extra i) by (intro Hx; specialize (Hsupport i Hx); lia).
  assert (Hnotocc_i : ~ ((0 <= i < Zlength s /\ Znth i s 48 = 49) \/ extra i)).
  { intros [[_ H] | H]; [lia | contradiction]. }
  assert (Hcompetitor_i : forall competitor, AdditionalTables s k competitor -> ~ competitor i).
  {
    intros competitor [Hcsupport Hcdist] Hci.
    specialize (Hcdist i q).
    assert (Hd := Hcdist (or_intror Hci) (or_introl (conj (conj Hq0 Hqlen) Hqocc)) ltac:(lia)).
    rewrite Z.abs_neq in Hd by lia. lia.
  }
  split; [exact Hadd |].
  split.
  - intros x Hx. specialize (Hsupport x Hx). lia.
  - split.
    + rewrite set_card_Z_extend_false__greedy_transitions by (lia || assumption). exact Hanswer.
    + split.
      * unfold LastOccupiedBefore in Hlast |- *.
    destruct Hlast as [[Hsent Hnone] | [[Hl0 Hli] [Hlocc Hnone]]].
        -- left. split; [exact Hsent |]. intros x Hx.
      destruct (Z_lt_ge_dec x i); [apply Hnone; lia |].
      assert (x = i) by lia. subst x. exact Hnotocc_i.
        -- right. repeat split; try lia; try exact Hlocc.
      intros x Hx. destruct (Z_lt_ge_dec x i); [apply Hnone; lia |].
      assert (x = i) by lia. subst x. exact Hnotocc_i.
      * split.
        -- intros competitor Hcomp.
    rewrite set_card_Z_extend_false__greedy_transitions by (lia || auto using Hcompetitor_i).
    apply Hopt; exact Hcomp.
        -- intros competitor Hcomp Hcard.
    assert (Hnci := Hcompetitor_i competitor Hcomp).
    rewrite set_card_Z_extend_false__greedy_transitions in Hcard by (lia || assumption).
    specialize (Hdom competitor Hcomp Hcard).
    destruct Hdom as [competitor_last [Hclast Hle]].
    exists competitor_last. split; [|exact Hle].
    unfold LastOccupiedBefore in Hclast |- *.
    destruct Hclast as [[Hsent Hnone] | [[Hl0 Hli] [Hlocc Hnone]]].
        ++ left. split; [exact Hsent |]. intros x Hx.
           destruct (Z_lt_ge_dec x i); [apply Hnone; lia |].
           assert (x = i) by lia. subst x. intros [Horig | Hextra];
             [destruct Horig as [_ H49]; lia | contradiction].
        ++ right. split; [lia |]. split; [exact Hlocc |].
           intros x Hx. destruct (Z_lt_ge_dec x i); [apply Hnone; lia |].
           assert (x = i) by lia. subst x. intros [Horig | Hextra];
             [destruct Horig as [_ H49]; lia | contradiction].
Qed.
Lemma prefix_placement_original_occupied__greedy_transitions :
  forall s k i last answer,
    Pre k s ->
    0 <= i < Zlength s ->
    Znth i s 48 = 49 ->
    PrefixPlacementState s k i last answer ->
    PrefixPlacementState s k (i + 1) i answer.
Proof.
  intros s k i last answer Hpre Hi Hocc Hstate.
  unfold PrefixPlacementState in Hstate |- *.
  destruct Hstate as [Hprocessed [extra [Hadd [Hsupport [Hanswer [Hlast [Hopt Hdom]]]]]]].
  split; [lia |]. exists extra.
  assert (Hextra_i : ~ extra i) by (eapply extra_not_at_original__greedy_transitions; eauto).
  assert (Hlast_i : last < i).
  {
    destruct Hpre as [[Hk _] _].
    destruct Hlast as [[Hsent _] | [[_ Hli] _]]; [subst last; lia | lia].
  }
  split; [exact Hadd |].
  split.
  - intros x Hx. specialize (Hsupport x Hx). lia.
  - split.
    + rewrite set_card_Z_extend_false__greedy_transitions by (lia || assumption). exact Hanswer.
    + split.
      * unfold LastOccupiedBefore. right.
        split; [lia |]. split.
        -- left. tauto.
        -- intros x Hx. lia.
      * split.
        -- intros competitor Hcomp.
           assert (Hnci : ~ competitor i) by (eapply extra_not_at_original__greedy_transitions; eauto).
           rewrite set_card_Z_extend_false__greedy_transitions by (lia || assumption).
           apply Hopt; exact Hcomp.
        -- intros competitor Hcomp Hcard.
           exists i. split; [|lia].
           unfold LastOccupiedBefore. right.
           split; [lia |]. split.
           ++ left. tauto.
           ++ intros x Hx. lia.
Qed.
Lemma prefix_placement_complete_spec__final_result :
  forall (s : list Z) (k processed last answer : Z),
    processed = Zlength s ->
    PrefixPlacementState s k processed last answer ->
    Spec k s answer.
Proof.
  intros s k processed last answer Hprocessed Hstate.
  subst processed.
  unfold PrefixPlacementState in Hstate.
  destruct Hstate as
    [_ [extra [Hadditional [Hsupport [Hanswer [Hlast [Hoptimal Hdominance]]]]]]].
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists (extra, answer).
  split.
  - split.
    + simpl. split; [exact Hadditional | exact Hanswer].
    + intros [competitor candidate_answer] Hcandidate.
      simpl in Hcandidate |- *.
      destruct Hcandidate as [Hcompetitor Hcandidate_answer].
      cbn in Hcandidate_answer.
      rewrite Hcandidate_answer.
      exact (Hoptimal competitor Hcompetitor).
  - reflexivity.
Qed.
