Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition BadCardSegment (x : Z) (seg : list Z) : Prop :=
  forall ids : Z -> Prop,
    fold_right Z.mul 1
      (map (fun i => Znth i seg 0)
        (@enum Z (fun i => 0 <= i < Zlength seg /\ ids i) _)) <> x.

Definition BadPartition (x : Z) (a cuts : list Z) : Prop :=
  2 <= Zlength cuts /\ Znth 0 cuts 0 = 0 /\
  Znth (Zlength cuts - 1) cuts 0 = Zlength a /\
  mono_inc cuts /\
  forall i, 0 <= i < Zlength cuts - 1 ->
    BadCardSegment x (sublist (Znth i cuts 0) (Znth (i + 1) cuts 0) a).

Definition Pre (x : Z) (a : list Z) : Prop :=
  2 <= x <= 100000 /\ 1 <= Zlength a <= 100000 /\
  Forall (fun v => 1 <= v <= 200000 /\ v <> x) a.

Definition Spec (x : Z) (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (BadPartition x a)
    (fun cuts => Zlength cuts - 1) out.

(** A direct mathematical description of the products represented by the
    program's divisor table.  This deliberately reuses the same finite choice
    of indices as [BadCardSegment], so later bridge lemmas do not need a second
    encoding of subsequences. *)
Definition SelectedProduct (seg : list Z) (ids : Z -> Prop) : Z :=
  fold_right Z.mul 1
    (map (fun i => Znth i seg 0)
      (@enum Z (fun i => 0 <= i < Zlength seg /\ ids i) _)).

Definition ProductReachable (seg : list Z) (p : Z) : Prop :=
  exists ids : Z -> Prop, SelectedProduct seg ids = p.

Definition ReachableDivisorProducts
    (x : Z) (seg products : list Z) : Prop :=
  NoDup products /\
  forall p,
    In p products <->
      1 <= p <= x /\ (exists k, x = p * k) /\ ProductReachable seg p.

(** The pure relation between the active product list and the byte table.
    Array length and ownership remain explicit C facts/resources. *)
Definition ValuableBitmap
    (x : Z) (products bitmap : list Z) : Prop :=
  forall p, 0 <= p <= x ->
    Znth p bitmap 0 =
      if in_dec Z.eq_dec p products then 1 else 0.

Definition ValuablePrefixCuts
    (x : Z) (a : list Z) (i segments : Z) (starts : list Z) : Prop :=
  Zlength starts = segments /\
  1 <= segments /\
  Znth 0 starts 0 = 0 /\
  mono_inc starts /\
  0 <= Znth (Zlength starts - 1) starts 0 <= i /\
  ((i = 0 /\ starts = (0 :: nil)) \/
   (0 < i /\ Znth (Zlength starts - 1) starts 0 < i)) /\
  (forall k, 0 <= k < Zlength starts - 1 ->
    BadCardSegment x
      (sublist (Znth k starts 0) (Znth (k + 1) starts 0) a)) /\
  BadCardSegment x
    (sublist (Znth (Zlength starts - 1) starts 0) i a) /\
  (forall alternative,
    BadPartition x (sublist 0 i a) alternative ->
    segments <= Zlength alternative - 1).

(** Outer-loop business state: the completed greedy cuts are already a lower
    bound for every partition of the processed prefix, and [products] exactly
    represents the reachable divisor products of the live final segment. *)
Definition ValuableOuterState
    (x : Z) (a : list Z) (i segments : Z) (products : list Z) : Prop :=
  exists starts,
    ValuablePrefixCuts x a i segments starts /\
    ReachableDivisorProducts x
      (sublist (Znth (Zlength starts - 1) starts 0) i a) products.

(** Inner-loop state after scanning [scanned] entries of the snapshot
    [base].  The list [products] is the old set plus precisely the valid
    products obtained by using the new card once, and [reaches] records whether
    x has appeared among those products. *)
Definition ValuableClosureState
    (x : Z) (seg : list Z) (v : Z) (base : list Z)
    (scanned : Z) (products : list Z) (reaches : Z) : Prop :=
  ReachableDivisorProducts x seg base /\
  NoDup products /\
  (forall p,
    In p products <->
      In p base \/
      exists q,
        In q (sublist 0 scanned base) /\
        p = q * v /\ 1 <= p <= x /\ exists k, x = p * k) /\
  ((reaches = 1 /\
      exists q, In q (sublist 0 scanned base) /\ q * v = x) \/
   (reaches = 0 /\
      forall q, In q (sublist 0 scanned base) -> q * v <> x)).

(** During reset, entries before [cleared] have been removed, so the bitmap
    represents exactly the as-yet uncleared suffix of the distinct product
    list. *)
Definition ValuableClearingState
    (x : Z) (products : list Z) (cleared : Z) (bitmap : list Z) : Prop :=
  ValuableBitmap x
    (sublist cleared (Zlength products) products) bitmap.

(** A strengthened greedy-history state carried in parallel with
    [ValuableOuterState].  The same cut-start witness is tied to the live
    reachable-product table, and every completed cut records the trigger that
    forced it: extending the preceding bad segment through the boundary card
    makes that segment non-bad. *)
Definition ValuableForcedHistory
    (x : Z) (a : list Z) (i segments : Z) (products : list Z) : Prop :=
  exists starts,
    ValuablePrefixCuts x a i segments starts /\
    ReachableDivisorProducts x
      (sublist (Znth (Zlength starts - 1) starts 0) i a) products /\
    forall k, 0 <= k < Zlength starts - 1 ->
      ~ BadCardSegment x
          (sublist (Znth k starts 0)
            (Znth (k + 1) starts 0 + 1) a).

(** Cumulative cut alignment for every competing partition of the current or
    a future input prefix.  The [k]-th alternative boundary is no later than
    the [k]-th completed greedy boundary.  Because both boundary lists are
    strictly increasing, these canonical boundaries are already an ordered
    injection; the explicit length conjunct is its counting consequence. *)
Definition ValuablePartitionAlignment
    (x : Z) (a : list Z) (processed segments : Z)
    (starts : list Z) : Prop :=
  forall endpoint alternative,
    processed <= endpoint <= Zlength a ->
    BadPartition x (sublist 0 endpoint a) alternative ->
    segments <= Zlength alternative - 1 /\
    forall k, 0 <= k < segments ->
      Znth k alternative 0 <= Znth k starts 0.

(** The revision-3 outer history keeps the old mathematical interfaces as
    projections, but additionally owns the cross-partition alignment needed
    to transport and increment the universal partition-count lower bound. *)
Definition ValuableAlignedHistory
    (x : Z) (a : list Z) (processed segments : Z)
    (products : list Z) : Prop :=
  exists starts,
    ValuablePrefixCuts x a processed segments starts /\
    ReachableDivisorProducts x
      (sublist (Znth (Zlength starts - 1) starts 0) processed a) products /\
    (forall k, 0 <= k < Zlength starts - 1 ->
      ~ BadCardSegment x
          (sublist (Znth k starts 0)
            (Znth (k + 1) starts 0 + 1) a)) /\
    ValuablePartitionAlignment x a processed segments starts.

Require Import Coq.micromega.Lia.

Lemma valuable_partition_alignment_initial : forall x a,
  ValuablePartitionAlignment x a 0 1 (0 :: nil).
Proof.
  intros x a endpoint alternative Hend Hpart.
  destruct Hpart as [Hlen [Hfirst [Hlast [Hmono Hbad]]]].
  split; [lia|].
  intros k Hk. assert (k = 0) by lia. subst k.
  rewrite Hfirst. reflexivity.
Qed.

Lemma valuable_partition_alignment_no_cut : forall x a i segments starts,
  ValuablePartitionAlignment x a i segments starts ->
  ValuablePartitionAlignment x a (i + 1) segments starts.
Proof.
  intros x a i segments starts Halign endpoint alternative Hend Hpart.
  apply Halign with (endpoint := endpoint); [lia|exact Hpart].
Qed.

Lemma valuable_aligned_history_to_forced : forall x a i segments products,
  ValuableAlignedHistory x a i segments products ->
  ValuableForcedHistory x a i segments products.
Proof.
  intros x a i segments products
    [starts [Hcuts [Hreach [Hforced Halign]]]].
  exists starts. split; [exact Hcuts|].
  split; [exact Hreach|exact Hforced].
Qed.

Lemma valuable_aligned_history_to_outer : forall x a i segments products,
  ValuableAlignedHistory x a i segments products ->
  ValuableOuterState x a i segments products.
Proof.
  intros x a i segments products
    [starts [Hcuts [Hreach [Hforced Halign]]]].
  exists starts. split; assumption.
Qed.

Lemma valuable_aligned_history_alignment : forall x a i segments products,
  ValuableAlignedHistory x a i segments products ->
  exists starts,
    ValuablePrefixCuts x a i segments starts /\
    ValuablePartitionAlignment x a i segments starts.
Proof.
  intros x a i segments products
    [starts [Hcuts [Hreach [Hforced Halign]]]].
  exists starts. split; assumption.
Qed.

Lemma valuable_aligned_history_initial : forall x a products,
  ValuablePrefixCuts x a 0 1 (0 :: nil) ->
  ReachableDivisorProducts x (sublist 0 0 a) products ->
  ValuableAlignedHistory x a 0 1 products.
Proof.
  intros x a products Hcuts Hreach.
  exists (0 :: nil). split; [exact Hcuts|].
  split; [exact Hreach|]. split.
  - intros k Hk. simpl in Hk. lia.
  - apply valuable_partition_alignment_initial.
Qed.

Require Import Coq.ZArith.Zquot.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.Classical_Prop.
Lemma valuable_initial_states__initialization :
  forall (x : Z) (a : list Z),
    2 <= x ->
    ValuableOuterState x a 0 1 (1 :: nil) /\
    ValuableForcedHistory x a 0 1 (1 :: nil) /\
    ValuableAlignedHistory x a 0 1 (1 :: nil) /\
    Zlength (replace_Znth 1 1 (repeat 0 (Z.to_nat (x + 1)))) = x + 1 /\
    ValuableBitmap x (1 :: nil)
      (replace_Znth 1 1 (repeat 0 (Z.to_nat (x + 1)))).
Proof.
  intros x a Hx.
  assert (Hempty_product : forall ids : Z -> Prop,
      SelectedProduct nil ids = 1).
  {
    intro ids.
    assert (Henum :
      @enum Z (fun i => 0 <= i < Zlength (@nil Z) /\ ids i) _ = nil).
    {
      destruct (@enum Z
        (fun i => 0 <= i < Zlength (@nil Z) /\ ids i) _)
        as [|j js] eqn:He; [reflexivity |].
      exfalso.
      assert (Hin : In j
        (@enum Z (fun i => 0 <= i < Zlength (@nil Z) /\ ids i) _)).
      { rewrite He. simpl. auto. }
      apply (proj2 ((@enum_ok Z
        (fun i => 0 <= i < Zlength (@nil Z) /\ ids i) _) j)) in Hin.
      destruct Hin as [Hrange _].
      rewrite Zlength_nil in Hrange. lia.
    }
    unfold SelectedProduct.
    rewrite Henum. reflexivity.
  }
  assert (Hbad : BadCardSegment x nil).
  {
    unfold BadCardSegment.
    intro ids.
    change (SelectedProduct nil ids <> x).
    rewrite Hempty_product. lia.
  }
  assert (Hprefix : ValuablePrefixCuts x a 0 1 (0 :: nil)).
  {
    unfold ValuablePrefixCuts.
    refine (conj _ (conj _ (conj _ (conj _
      (conj _ (conj _ (conj _ (conj _ _)))))))).
    - reflexivity.
    - lia.
    - reflexivity.
    - unfold mono_inc. intros p q Hp Hpq Hq. exfalso.
      rewrite Zlength_cons, Zlength_nil in Hq. lia.
    - change (0 <= 0 <= 0). split; lia.
    - left. split; reflexivity.
    - intros k Hk. exfalso. simpl in Hk. lia.
    - change (BadCardSegment x nil). exact Hbad.
    - intros alternative Halternative.
      unfold BadPartition in Halternative.
      destruct Halternative as [Hlength _]. lia.
  }
  assert (Hreachable : ReachableDivisorProducts x nil (1 :: nil)).
  {
    unfold ReachableDivisorProducts.
    split.
    - constructor.
      + simpl. tauto.
      + constructor.
    - intro p. split.
      + intro Hin.
        simpl in Hin. destruct Hin as [Hp | []]. subst p.
        split; [lia |].
        split.
        * exists x. lia.
        * exists (fun _ => False). apply Hempty_product.
      + intros [[Hp1 Hpx] [[k Hdiv] [ids Hselected]]].
        rewrite Hempty_product in Hselected. subst p. simpl. auto.
  }
  split.
  - exists (0 :: nil). split; [exact Hprefix |].
    change (ReachableDivisorProducts x nil (1 :: nil)).
    exact Hreachable.
  - split.
    + exists (0 :: nil).
      refine (conj Hprefix (conj _ _)).
      * change (ReachableDivisorProducts x nil (1 :: nil)).
        exact Hreachable.
      * intros k Hk. exfalso. simpl in Hk. lia.
    + split.
      * apply valuable_aligned_history_initial; [exact Hprefix |].
        change (ReachableDivisorProducts x nil (1 :: nil)).
        exact Hreachable.
      * assert (Hlength :
          Zlength (repeat 0 (Z.to_nat (x + 1))) = x + 1).
        {
          rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
          reflexivity.
        }
        assert (Hreplace_len : forall (l : list Z) (n : nat),
            length (replace_nth n l 1) = length l).
        {
          intros l.
          induction l as [|b l IH]; intros n; simpl.
          - reflexivity.
          - destruct n; simpl; [reflexivity |].
            rewrite IH. reflexivity.
        }
        split.
        -- transitivity (Zlength (repeat 0 (Z.to_nat (x + 1))));
             [| exact Hlength].
           unfold replace_Znth.
           rewrite !Zlength_correct, Hreplace_len. reflexivity.
        -- unfold ValuableBitmap.
        intros p Hp.
           destruct (in_dec Z.eq_dec p (1 :: nil)) as [Hin | Hnotin].
           ++ simpl in Hin. destruct Hin as [Hp1 | []]. subst p.
              rewrite Znth_replace_Znth_Same by lia. reflexivity.
           ++ assert (Hp1 : p <> 1).
              { intro Heq. subst p. apply Hnotin. simpl. auto. }
              rewrite Znth_replace_Znth_Diff by lia.
              apply Znth_repeat_lt. lia.
Qed.
Lemma valuable_closure_initial__initialization :
  forall x a i segments products v,
    ValuableAlignedHistory x a i segments products ->
    exists segment,
      ValuableClosureState x segment v products 0 products 0.
Proof.
  intros x a i segments products v
    [starts [Hcuts [Hreach [Hforced Halign]]]].
  exists (sublist (Znth (Zlength starts - 1) starts 0) i a).
  unfold ValuableClosureState.
  split; [exact Hreach |].
  split; [exact (proj1 Hreach) |].
  split.
  - intros p.
    rewrite Zsublist_nil by lia.
    split.
    + intro Hp. left. exact Hp.
    + intros [Hp | [q [Hq _]]].
      * exact Hp.
      * contradiction.
  - right.
    split; [reflexivity |].
    intros q Hq.
    rewrite Zsublist_nil in Hq by lia.
    contradiction.
Qed.
Lemma positive_remainder_divisor_le__initialization :
  forall x v,
    0 < x ->
    0 < v ->
    Z.rem x v = 0 ->
    v <= x.
Proof.
  intros x v Hx Hv Hrem.
  assert (Hmod : x mod v = 0).
  {
    apply (proj1 (Zrem_Zmod_zero x v ltac:(lia))).
    exact Hrem.
  }
  apply (proj1 (Z.mod_divide x v ltac:(lia))) in Hmod.
  apply Z.divide_pos_le; assumption.
Qed.
Lemma valuable_product_quot_bound__control_routing :
  forall x v q,
    0 <= x ->
    0 < v ->
    q <= Z.quot x v ->
    q * v <= x.
Proof.
  intros x v q Hx Hv Hq.
  rewrite Zquot_Zdiv_pos in Hq by lia.
  pose proof (Z.div_mod x v ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound x v ltac:(lia)) as Hmod.
  nia.
Qed.
Lemma valuable_closure_zero_scan__inner_entry :
  forall x seg v base,
    ReachableDivisorProducts x seg base ->
    ValuableClosureState x seg v base 0 base 0.
Proof.
  intros x seg v base Hreachable.
  unfold ValuableClosureState.
  destruct Hreachable as [Hnodup Hmembers].
  split.
  - split; assumption.
  - split; [exact Hnodup |].
    split.
    + intros p.
      rewrite Zsublist_nil by lia.
      split.
      * intro Hp. left. exact Hp.
      * intros [Hp | [q [Hq _]]].
        -- exact Hp.
        -- contradiction.
    + right.
      split; [reflexivity |].
      intros q Hq.
      rewrite Zsublist_nil in Hq by lia.
      contradiction.
Qed.
Lemma sublist_snoc_prefix__append_cycle :
  forall {A : Type} (d : A) (l : list A) i,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l d :: nil.
Proof.
  intros A d l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single d i l) by lia.
  reflexivity.
Qed.
Lemma valuable_bitmap_fresh__append_cycle :
  forall x products bitmap p,
    ValuableBitmap x products bitmap ->
    0 <= p <= x ->
    Zlength bitmap = x + 1 ->
    Znth p bitmap 0 = 0 ->
    ValuableBitmap x (products ++ p :: nil) (replace_Znth p 1 bitmap).
Proof.
  intros x products bitmap p Hbitmap Hp Hlen Hzero.
  assert (Hfresh : ~ In p products).
  {
    intro Hin.
    specialize (Hbitmap p Hp).
    destruct (in_dec Z.eq_dec p products) as [Hin' | Hnotin].
    - rewrite Hbitmap in Hzero. discriminate.
    - contradiction.
  }
  intros q Hq.
  destruct (Z.eq_dec q p) as [Heq | Hneq].
  - subst q.
    rewrite Znth_replace_Znth_Same by lia.
    destruct (in_dec Z.eq_dec p (products ++ p :: nil)) as [Hin | Hnotin].
    + reflexivity.
    + exfalso. apply Hnotin. apply in_or_app. right. simpl. auto.
  - rewrite Znth_replace_Znth_Diff by lia.
    specialize (Hbitmap q Hq).
    destruct (in_dec Z.eq_dec q products) as [Hinold | Hnotold];
      destruct (in_dec Z.eq_dec q (products ++ p :: nil)) as [Hinnew | Hnotnew].
    + exact Hbitmap.
    + exfalso. apply Hnotnew. apply in_or_app. left. exact Hinold.
    + apply in_app_or in Hinnew. destruct Hinnew as [Hinnew | Hinnew].
      * contradiction.
      * simpl in Hinnew. destruct Hinnew as [Heq | []].
        exfalso. apply Hneq. symmetry. exact Heq.
    + exact Hbitmap.
Qed.
Lemma valuable_closure_append_fresh__append_cycle :
  forall x seg v base scanned products reaches p,
    0 <= scanned < Zlength base ->
    p = Znth scanned base 0 * v ->
    1 <= p <= x ->
    (exists k, x = p * k) ->
    ~ In p products ->
    ValuableClosureState x seg v base scanned products reaches ->
    ValuableClosureState x seg v base (scanned + 1)
      (products ++ p :: nil) (if Z.eq_dec p x then 1 else reaches).
Proof.
  intros x seg v base scanned products reaches p Hscanned Hp Hbounds
    Hdiv Hfresh Hstate.
  assert (Hprefix :
      sublist 0 (scanned + 1) base =
        sublist 0 scanned base ++ Znth scanned base 0 :: nil).
  { apply sublist_snoc_prefix__append_cycle. exact Hscanned. }
  unfold ValuableClosureState in *.
  destruct Hstate as [Hbase [Hnodup [Hmembers Hreaches]]].
  split; [exact Hbase |].
  split.
  - apply NoDup_app. repeat split; try assumption.
    + constructor; [intro H; inversion H | constructor].
    + intros z Hz [Heq | []]. subst z. contradiction.
  - split.
    + intro r. split.
      * intro Hr.
        apply in_app_or in Hr.
        destruct Hr as [Hrold | Hrnew].
        -- apply Hmembers in Hrold.
           destruct Hrold as [Hrbase | [q [Hq Hfacts]]].
           ++ left. exact Hrbase.
           ++ right. exists q. split.
              ** rewrite Hprefix. apply in_or_app. left. exact Hq.
              ** exact Hfacts.
        -- simpl in Hrnew. destruct Hrnew as [Hrp | []]. subst r.
           right. exists (Znth scanned base 0). split.
           ++ rewrite Hprefix. apply in_or_app. right. simpl. auto.
           ++ split; [exact Hp |]. split; assumption.
      * intro Hr.
        destruct Hr as [Hrbase | [q [Hq [Hr [Hrbounds Hrdiv]]]]].
        -- apply in_or_app. left. apply Hmembers. left. exact Hrbase.
        -- rewrite Hprefix in Hq.
           apply in_app_or in Hq.
           destruct Hq as [Hqold | Hqnew].
           ++ apply in_or_app. left. apply Hmembers. right.
              exists q. exact (conj Hqold (conj Hr (conj Hrbounds Hrdiv))).
           ++ simpl in Hqnew. destruct Hqnew as [Hqeq | []].
              subst q r. rewrite <- Hp.
              apply in_or_app. right. simpl. auto.
    + destruct (Z.eq_dec p x) as [Hpx | Hpx].
      * left. split; [reflexivity |].
        exists (Znth scanned base 0). split.
        -- rewrite Hprefix. apply in_or_app. right. simpl. auto.
        -- rewrite <- Hp. exact Hpx.
      * destruct Hreaches as [[Hone [q [Hq Hqx]]] | [Hzero Hnone]].
        -- left. split; [exact Hone |]. exists q. split.
           ++ rewrite Hprefix. apply in_or_app. left. exact Hq.
           ++ exact Hqx.
        -- right. split; [exact Hzero |]. intros q Hq.
           rewrite Hprefix in Hq. apply in_app_or in Hq.
           destruct Hq as [Hqold | Hqnew].
           ++ apply Hnone. exact Hqold.
           ++ simpl in Hqnew. destruct Hqnew as [Hqeq | []].
              subst q. rewrite <- Hp. exact Hpx.
Qed.
Lemma valuable_closure_duplicate__append_cycle :
  forall x seg v base scanned products reaches p,
    0 <= scanned < Zlength base ->
    p = Znth scanned base 0 * v ->
    In p products ->
    ValuableClosureState x seg v base scanned products reaches ->
    ValuableClosureState x seg v base (scanned + 1) products
      (if Z.eq_dec p x then 1 else reaches).
Proof.
  intros x seg v base scanned products reaches p Hscanned Hp Hin Hstate.
  assert (Hprefix :
      sublist 0 (scanned + 1) base =
        sublist 0 scanned base ++ Znth scanned base 0 :: nil).
  { apply sublist_snoc_prefix__append_cycle. exact Hscanned. }
  unfold ValuableClosureState in *.
  destruct Hstate as [Hbase [Hnodup [Hmembers Hreaches]]].
  split; [exact Hbase |]. split; [exact Hnodup |]. split.
  - intro r. split.
    + intro Hr. apply Hmembers in Hr.
      destruct Hr as [Hrbase | [q [Hq Hfacts]]].
      * left. exact Hrbase.
      * right. exists q. split.
        -- rewrite Hprefix. apply in_or_app. left. exact Hq.
        -- exact Hfacts.
    + intro Hr. destruct Hr as [Hrbase | [q [Hq Hfacts]]].
      * apply Hmembers. left. exact Hrbase.
      * rewrite Hprefix in Hq. apply in_app_or in Hq.
        destruct Hq as [Hqold | Hqnew].
        -- apply Hmembers. right. exists q. split; assumption.
        -- simpl in Hqnew. destruct Hqnew as [Hqeq | []].
           destruct Hfacts as [Hr [Hbounds Hdiv]].
           subst q. rewrite Hr, <- Hp. exact Hin.
  - destruct (Z.eq_dec p x) as [Hpx | Hpx].
    + left. split; [reflexivity |].
      exists (Znth scanned base 0). split.
      * rewrite Hprefix. apply in_or_app. right. simpl. auto.
      * rewrite <- Hp. exact Hpx.
    + destruct Hreaches as [[Hone [q [Hq Hqx]]] | [Hzero Hnone]].
      * left. split; [exact Hone |]. exists q. split.
        -- rewrite Hprefix. apply in_or_app. left. exact Hq.
        -- exact Hqx.
      * right. split; [exact Hzero |]. intros q Hq.
        rewrite Hprefix in Hq. apply in_app_or in Hq.
        destruct Hq as [Hqold | Hqnew].
        -- apply Hnone. exact Hqold.
        -- simpl in Hqnew. destruct Hqnew as [Hqeq | []].
           subst q. rewrite <- Hp. exact Hpx.
Qed.
Lemma valuable_closure_skip__append_cycle :
  forall x seg v base scanned products reaches,
    0 <= scanned < Zlength base ->
    ValuableClosureState x seg v base scanned products reaches ->
    (x < Znth scanned base 0 * v \/
     Z.rem x (Znth scanned base 0 * v) <> 0) ->
    ValuableClosureState x seg v base (scanned + 1) products reaches.
Proof.
  intros x seg v base scanned products reaches Hscanned Hstate Hinvalid.
  assert (Hprefix :
      sublist 0 (scanned + 1) base =
        sublist 0 scanned base ++ Znth scanned base 0 :: nil).
  { apply sublist_snoc_prefix__append_cycle. exact Hscanned. }
  unfold ValuableClosureState in *.
  destruct Hstate as [Hbase [Hnodup [Hmembers Hreaches]]].
  split; [exact Hbase |]. split; [exact Hnodup |]. split.
  - intro p. specialize (Hmembers p). rewrite Hmembers. split.
    + intros [Hinbase | [q [Hinq Hfacts]]].
      * left. exact Hinbase.
      * right. exists q. split.
        -- rewrite Hprefix. apply in_or_app. left. exact Hinq.
        -- exact Hfacts.
    + intros [Hinbase | [q [Hinq Hfacts]]].
      * left. exact Hinbase.
      * rewrite Hprefix in Hinq. apply in_app_or in Hinq.
        destruct Hinq as [Hinq | Hinq].
        -- right. exists q. split; assumption.
        -- simpl in Hinq. destruct Hinq as [Hq | []]. subst q.
           destruct Hfacts as [Hp [Hbounds Hdivides]]. subst p.
           destruct Hinvalid as [Hlarge | Hnondiv].
           ++ lia.
           ++ exfalso. apply Hnondiv.
              destruct Hdivides as [k Hk]. rewrite Hk.
              rewrite (Z.mul_comm (Znth scanned base 0 * v) k).
              apply Z_rem_mult.
  - destruct Hreaches as [[Hr [q [Hinq Hqx]]] | [Hr Hnone]].
    + left. split; [exact Hr |]. exists q. split.
      * rewrite Hprefix. apply in_or_app. left. exact Hinq.
      * exact Hqx.
    + right. split; [exact Hr |]. intros q Hinq.
      rewrite Hprefix in Hinq. apply in_app_or in Hinq.
      destruct Hinq as [Hinq | Hinq].
      * exact (Hnone q Hinq).
      * simpl in Hinq. destruct Hinq as [Hq | []]. subst q.
        destruct Hinvalid as [Hlarge | Hnondiv].
        -- lia.
        -- intro Heq. apply Hnondiv. rewrite Heq. apply Z_rem_same.
Qed.
Lemma quotient_and_remainder_product_bounds__append_cycle :
  forall x v q,
    0 <= x ->
    0 < v ->
    Z.rem x v = 0 ->
    Z.quot x v < q ->
    x < q * v.
Proof.
  intros x v q Hx Hv Hrem Hq.
  rewrite Zquot_Zdiv_pos in Hq by lia.
  assert (Hmod : x mod v = 0).
  {
    apply (proj1 (Zrem_Zmod_zero x v ltac:(lia))).
    exact Hrem.
  }
  pose proof (Z.div_mod x v ltac:(lia)) as Hdiv.
  nia.
Qed.
Lemma valuable_nodup_positive_bounded_length__append_cycle :
  forall x products,
    1 <= x ->
    NoDup products ->
    (forall p, In p products -> 1 <= p < x) ->
    Zlength products < x.
Proof.
  intros x products Hx Hnodup Hbounds.
  assert (Hmapnodup : NoDup (map Z.to_nat products)).
  {
    apply NoDup_map_NoDup_ForallPairs.
    - unfold ForallPairs. intros a b Ha Hb Heq.
      apply Z2Nat.inj in Heq;
        pose proof (Hbounds _ Ha);
        pose proof (Hbounds _ Hb);
        lia.
    - exact Hnodup.
  }
  assert (Hincl : incl (map Z.to_nat products)
      (seq 1 (Z.to_nat (x - 1)))).
  {
    intros n Hn.
    apply in_map_iff in Hn.
    destruct Hn as [p [Hpn Hp]]. subst n.
    apply in_seq.
    pose proof (Hbounds p Hp).
    lia.
  }
  pose proof (NoDup_incl_length Hmapnodup Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite !Zlength_correct.
  rewrite Z2Nat.id in Hlen by lia.
  lia.
Qed.
Lemma valuable_nodup_bounded_length__append_cycle :
  forall x products,
    1 <= x ->
    NoDup products ->
    (forall p, In p products -> 1 <= p <= x) ->
    Zlength products <= x.
Proof.
  intros x products Hx Hnodup Hbounds.
  assert (Hmapnodup : NoDup (map Z.to_nat products)).
  {
    apply NoDup_map_NoDup_ForallPairs.
    - unfold ForallPairs. intros a b Ha Hb Heq.
      apply Z2Nat.inj in Heq;
        pose proof (Hbounds _ Ha);
        pose proof (Hbounds _ Hb);
        lia.
    - exact Hnodup.
  }
  assert (Hincl : incl (map Z.to_nat products)
      (seq 1 (Z.to_nat x))).
  {
    intros n Hn.
    apply in_map_iff in Hn.
    destruct Hn as [p [Hpn Hp]]. subst n.
    apply in_seq.
    pose proof (Hbounds p Hp).
    lia.
  }
  pose proof (NoDup_incl_length Hmapnodup Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite !Zlength_correct.
  rewrite Z2Nat.id in Hlen by lia.
  lia.
Qed.
Lemma valuable_clearing_step__clearing_reset :
  forall x products bitmap cleared,
    0 <= cleared < Zlength products ->
    Zlength bitmap = x + 1 ->
    NoDup products ->
    (forall k, 0 <= k < Zlength products ->
      1 <= Znth k products 0 <= x) ->
    ValuableClearingState x products cleared bitmap ->
    ValuableClearingState x products (cleared + 1)
      (replace_Znth (Znth cleared products 0) 0 bitmap).
Proof.
  intros x products bitmap cleared Hcleared Hbitmap_len Hnodup
    Hproduct_bounds Hclearing.
  unfold ValuableClearingState, ValuableBitmap in *.
  assert (Hsuffix :
      sublist cleared (Zlength products) products =
        Znth cleared products 0 ::
          sublist (cleared + 1) (Zlength products) products).
  {
    rewrite (sublist_split cleared (Zlength products) (cleared + 1) products)
      by lia.
    rewrite (sublist_single 0 cleared products) by lia.
    reflexivity.
  }
  assert (Hwhole :
      products =
        sublist 0 cleared products ++
          Znth cleared products 0 ::
            sublist (cleared + 1) (Zlength products) products).
  {
    rewrite <- (sublist_self products (Zlength products) eq_refl) at 1.
    rewrite (sublist_split 0 (Zlength products) cleared products) by lia.
    rewrite Hsuffix.
    reflexivity.
  }
  assert (Hhead_notin :
      ~ In (Znth cleared products 0)
          (sublist (cleared + 1) (Zlength products) products)).
  {
    rewrite Hwhole in Hnodup.
    apply NoDup_remove_2 in Hnodup.
    rewrite in_app_iff in Hnodup.
    tauto.
  }
  intros p Hp.
  pose proof (Hproduct_bounds cleared Hcleared) as Hhead_bounds.
  destruct (Z.eq_dec p (Znth cleared products 0)) as [Heq | Hneq].
  - subst p.
    rewrite Znth_replace_Znth_Same by lia.
    destruct (in_dec Z.eq_dec (Znth cleared products 0)
      (sublist (cleared + 1) (Zlength products) products)) as [Hin | Hnotin].
    + contradiction.
    + reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    specialize (Hclearing p Hp).
    rewrite Hsuffix in Hclearing.
    destruct (in_dec Z.eq_dec p
      (Znth cleared products 0 ::
        sublist (cleared + 1) (Zlength products) products)) as [Hin_old | Hnot_old];
    destruct (in_dec Z.eq_dec p
      (sublist (cleared + 1) (Zlength products) products)) as [Hin_new | Hnot_new].
    + exact Hclearing.
    + simpl in Hin_old.
      destruct Hin_old as [Heq | Hin_old].
      * exfalso. apply Hneq. symmetry. exact Heq.
      * exfalso. apply Hnot_new. exact Hin_old.
    + exfalso. apply Hnot_old. simpl. right. exact Hin_new.
    + exact Hclearing.
Qed.
Lemma valuable_clearing_reset__clearing_reset :
  forall x products bitmap cleared,
    1 <= x ->
    Zlength bitmap = x + 1 ->
    Zlength products <= cleared ->
    cleared <= Zlength products ->
    ValuableClearingState x products cleared bitmap ->
    Zlength (replace_Znth 1 1 bitmap) = x + 1 /\
    ValuableBitmap x (1 :: nil) (replace_Znth 1 1 bitmap).
Proof.
  intros x products bitmap cleared Hx Hbitmap_len Hlower Hupper Hclearing.
  assert (Hcleared : cleared = Zlength products) by lia.
  subst cleared.
  unfold ValuableClearingState, ValuableBitmap in Hclearing.
  rewrite Zsublist_nil in Hclearing by lia.
  assert (Hreplace_len : forall (l : list Z) (n : nat),
      length (replace_nth n l 1) = length l).
  {
    intros l.
    induction l as [|b l IH]; intros n; simpl.
    - reflexivity.
    - destruct n; simpl; [reflexivity |].
      rewrite IH. reflexivity.
  }
  split.
  - transitivity (Zlength bitmap); [| exact Hbitmap_len].
    unfold replace_Znth.
    rewrite !Zlength_correct.
    rewrite Hreplace_len. reflexivity.
  - unfold ValuableBitmap.
    intros p Hp.
    destruct (Z.eq_dec p 1) as [Heq | Hneq].
    + subst p.
      rewrite Znth_replace_Znth_Same by lia.
      destruct (in_dec Z.eq_dec 1 (1 :: nil)) as [Hin | Hnotin].
      * reflexivity.
      * exfalso. apply Hnotin. simpl. auto.
    + rewrite Znth_replace_Znth_Diff by lia.
      specialize (Hclearing p Hp).
      simpl in Hclearing.
      rewrite Hclearing.
      destruct (in_dec Z.eq_dec p (1 :: nil)) as [Hin | Hnotin].
      * simpl in Hin. destruct Hin as [Heq | Hin].
        -- exfalso. apply Hneq. symmetry. exact Heq.
        -- contradiction.
      * reflexivity.
Qed.
Lemma fold_right_mul_permutation__outer_transition :
  forall xs ys : list Z,
    Permutation xs ys ->
    fold_right Z.mul 1 xs = fold_right Z.mul 1 ys.
Proof.
  intros xs ys Hperm.
  induction Hperm; simpl; try reflexivity.
  - rewrite IHHperm. reflexivity.
  - ring.
  - rewrite IHHperm1, IHHperm2. reflexivity.
Qed.
Lemma fold_right_mul_app__outer_transition :
  forall xs ys : list Z,
    fold_right Z.mul 1 (xs ++ ys) =
      fold_right Z.mul 1 xs * fold_right Z.mul 1 ys.
Proof.
  intros xs ys. induction xs as [|x xs IH]; simpl.
  - destruct (fold_right Z.mul 1 ys); reflexivity.
  - rewrite IH. ring.
Qed.
Lemma selected_product_ids_ext__outer_transition :
  forall (seg : list Z) (ids1 ids2 : Z -> Prop),
    (forall j, 0 <= j < Zlength seg -> (ids1 j <-> ids2 j)) ->
    SelectedProduct seg ids1 = SelectedProduct seg ids2.
Proof.
  intros seg ids1 ids2 Hids.
  unfold SelectedProduct.
  apply fold_right_mul_permutation__outer_transition.
  apply Permutation_map.
  apply NoDup_Permutation.
  - apply enum_nodup.
  - apply enum_nodup.
  - intro j. rewrite <- !enum_ok. split.
    + intros [Hj Hsel]. split; [exact Hj|].
      apply (proj1 (Hids j Hj)); exact Hsel.
    + intros [Hj Hsel]. split; [exact Hj|].
      apply (proj2 (Hids j Hj)); exact Hsel.
Qed.
Lemma selected_product_snoc_formula__outer_transition :
  forall (seg : list Z) (v : Z) (ids : Z -> Prop),
    SelectedProduct (seg ++ v :: nil) ids =
      SelectedProduct seg ids *
        (if prop_dec (ids (Zlength seg)) then v else 1).
Proof.
  intros seg v ids.
  set (n := Zlength seg).
  unfold SelectedProduct.
  set (eold :=
    @enum Z (fun j => 0 <= j < Zlength seg /\ ids j) _).
  set (enew :=
    @enum Z
      (fun j => 0 <= j < Zlength (seg ++ v :: nil) /\ ids j) _).
  destruct (prop_dec (ids n)) as [Hlast | Hlast].
  - assert (Hperm :
      Permutation
        enew (eold ++ n :: nil)).
    {
      apply NoDup_Permutation.
      - unfold enew. apply enum_nodup.
      - apply NoDup_app.
        + unfold eold. apply enum_nodup.
        + constructor; [simpl; tauto|constructor].
        + intros j Hj [Heq | []]. subst j.
          unfold eold in Hj. apply (proj2 (enum_ok n)) in Hj.
          destruct Hj as [Hrange _]. subst n. lia.
      - intro j. rewrite in_app_iff. unfold enew, eold.
        rewrite <- !enum_ok. simpl.
        rewrite Zlength_app_cons. subst n.
        split.
        + intros [Hrange Hsel].
          destruct (Z.eq_dec j (Zlength seg)) as [Heq | Hneq].
          * right. left. symmetry. exact Heq.
          * left. split; [lia|exact Hsel].
        + intros [[Hrange Hsel] | [Heq | []]].
          * split; [lia|exact Hsel].
          * subst j. split; [pose proof (Zlength_nonneg seg); lia|exact Hlast].
    }
    pose proof (Permutation_map
      (fun j => Znth j (seg ++ v :: nil) 0) Hperm) as Hmap.
    rewrite map_app in Hmap. simpl in Hmap.
    assert (Holdmap :
      map (fun j => Znth j (seg ++ v :: nil) 0)
        eold =
      map (fun j => Znth j seg 0)
        eold).
    {
      apply map_ext_in. intros j Hj.
      unfold eold in Hj. apply (proj2 (enum_ok j)) in Hj.
      destruct Hj as [Hrange _].
      rewrite app_Znth1 by lia. reflexivity.
    }
    rewrite Holdmap in Hmap.
    rewrite app_Znth2 in Hmap by (subst n; lia).
    replace (n - Zlength seg) with 0 in Hmap by (subst n; lia).
    rewrite Znth0_cons in Hmap.
    apply fold_right_mul_permutation__outer_transition in Hmap.
    rewrite fold_right_mul_app__outer_transition in Hmap. simpl in Hmap.
    rewrite Z.mul_1_r in Hmap.
    exact Hmap.
  - assert (Hperm :
      Permutation
        enew eold).
    {
      apply NoDup_Permutation.
      - unfold enew. apply enum_nodup.
      - unfold eold. apply enum_nodup.
      - intro j. unfold enew, eold. rewrite <- !enum_ok.
        rewrite Zlength_app_cons.
        split.
        + intros [Hj Hsel]. split; [|exact Hsel].
          destruct (Z.eq_dec j (Zlength seg)); [subst; contradiction|lia].
        + intros [Hj Hsel]. split; [lia|exact Hsel].
    }
    pose proof (Permutation_map
      (fun j => Znth j (seg ++ v :: nil) 0) Hperm) as Hmap.
    assert (Holdmap :
      map (fun j => Znth j (seg ++ v :: nil) 0)
        eold =
      map (fun j => Znth j seg 0)
        eold).
    {
      apply map_ext_in. intros j Hj.
      unfold eold in Hj. apply (proj2 (enum_ok j)) in Hj.
      destruct Hj as [Hrange _].
      rewrite app_Znth1 by lia. reflexivity.
    }
    rewrite Holdmap in Hmap.
    apply fold_right_mul_permutation__outer_transition in Hmap.
    rewrite Z.mul_1_r.
    exact Hmap.
Qed.
Lemma product_reachable_snoc_iff__outer_transition :
  forall (seg : list Z) (v p : Z),
    ProductReachable (seg ++ v :: nil) p <->
      ProductReachable seg p \/
      exists q, ProductReachable seg q /\ p = q * v.
Proof.
  intros seg v p. split.
  - intros [ids Hprod].
    rewrite selected_product_snoc_formula__outer_transition in Hprod.
    destruct (prop_dec (ids (Zlength seg))) as [Hlast | Hlast].
    + right. exists (SelectedProduct seg ids). split.
      * exists ids. reflexivity.
      * symmetry. exact Hprod.
    + left. exists ids. simpl in Hprod. lia.
  - intros [Hold | [q [[ids Hq] Hp]]].
    + destruct Hold as [ids Hids].
      exists (fun j => ids j /\ j <> Zlength seg).
      rewrite selected_product_snoc_formula__outer_transition.
      assert (Heq :
        SelectedProduct seg (fun j => ids j /\ j <> Zlength seg) =
        SelectedProduct seg ids).
      {
        apply selected_product_ids_ext__outer_transition.
        intros j Hj. split; [tauto|]. intro H. split; [exact H|lia].
      }
      rewrite Heq, Hids.
      destruct (prop_dec
        ((fun j => ids j /\ j <> Zlength seg) (Zlength seg)));
        [tauto|lia].
    + exists (fun j => ids j \/ j = Zlength seg).
      rewrite selected_product_snoc_formula__outer_transition.
      assert (Heq :
        SelectedProduct seg (fun j => ids j \/ j = Zlength seg) =
        SelectedProduct seg ids).
      {
        apply selected_product_ids_ext__outer_transition.
        intros j Hj. split; [intros [H|H]; [exact H|lia]|tauto].
      }
      rewrite Heq, Hq.
      destruct (prop_dec
        ((fun j => ids j \/ j = Zlength seg) (Zlength seg)));
        [symmetry; exact Hp|tauto].
Qed.
Lemma product_reachable_sublist_mono__outer_transition :
  forall (whole : list Z) lo hi p,
    0 <= lo <= hi -> hi <= Zlength whole ->
    ProductReachable (sublist lo hi whole) p ->
    ProductReachable whole p.
Proof.
  intros whole lo hi p Hlohi Hhi [ids Hprod].
  set (lifted := fun j : Z =>
    exists k, 0 <= k < hi - lo /\ ids k /\ j = lo + k).
  exists lifted.
  unfold SelectedProduct in *.
  assert (Hlen : Zlength (sublist lo hi whole) = hi - lo).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hperm :
    Permutation
      (map (fun k => lo + k)
        (@enum Z
          (fun k => 0 <= k < Zlength (sublist lo hi whole) /\ ids k) _))
      (@enum Z (fun j => 0 <= j < Zlength whole /\ lifted j) _)).
  {
    apply NoDup_Permutation.
    - apply Injective_map_NoDup_in.
      + intros x y Hx Hy Heq. lia.
      + apply enum_nodup.
    - apply enum_nodup.
    - intro j. rewrite in_map_iff, <- enum_ok. split.
      + intros [k [Heq Hk]]. subst j.
        apply (proj2 (enum_ok k)) in Hk.
        destruct Hk as [Hkrange Hids].
        split; [rewrite Hlen in Hkrange; lia|].
        exists k. rewrite Hlen in Hkrange. tauto.
      + intros [Hj [k [Hkrange [Hids Heq]]]].
        exists k. split; [symmetry; exact Heq|].
        apply (proj1 (enum_ok k)). rewrite Hlen. tauto.
  }
  pose proof (Permutation_map (fun j => Znth j whole 0) Hperm) as Hmap.
  rewrite map_map in Hmap.
  assert (Hvalues :
    map (fun k => Znth (lo + k) whole 0)
      (@enum Z
        (fun k => 0 <= k < Zlength (sublist lo hi whole) /\ ids k) _) =
    map (fun k => Znth k (sublist lo hi whole) 0)
      (@enum Z
        (fun k => 0 <= k < Zlength (sublist lo hi whole) /\ ids k) _)).
  {
    apply map_ext_in. intros k Hk.
    apply (proj2 (enum_ok k)) in Hk.
    destruct Hk as [Hkrange _].
    rewrite Znth_sublist by lia. f_equal. lia.
  }
  rewrite Hvalues in Hmap.
  apply Permutation_sym in Hmap.
  apply fold_right_mul_permutation__outer_transition in Hmap.
  rewrite Hmap. exact Hprod.
Qed.
Lemma selected_product_nil__outer_transition :
  forall ids : Z -> Prop, SelectedProduct nil ids = 1.
Proof.
  intro ids. unfold SelectedProduct.
  destruct (@enum Z (fun j => 0 <= j < Zlength (@nil Z) /\ ids j) _)
    as [|j js] eqn:He; [reflexivity|].
  exfalso.
  assert (Hin : In j
    (@enum Z (fun j => 0 <= j < Zlength (@nil Z) /\ ids j) _)).
  { rewrite He. simpl. auto. }
  apply (proj2 (enum_ok j)) in Hin. destruct Hin as [Hrange _].
  rewrite Zlength_nil in Hrange. lia.
Qed.
Lemma closure_to_reachable_snoc__outer_transition :
  forall x actual shadow v base products reaches,
    2 <= x -> 1 <= v ->
    ValuableClosureState x shadow v base (Zlength base) products reaches ->
    ReachableDivisorProducts x actual base ->
    BadCardSegment x actual ->
    ReachableDivisorProducts x (actual ++ v :: nil) products /\
    (reaches = 0 -> BadCardSegment x (actual ++ v :: nil)) /\
    (reaches = 1 -> ~ BadCardSegment x (actual ++ v :: nil)).
Proof.
  intros x actual shadow v base products reaches Hx Hv Hclosure
    Hactual Hbad.
  unfold ValuableClosureState in Hclosure.
  destruct Hclosure as [_ [Hnodup [Hmembers Hreaches]]].
  rewrite sublist_self in Hmembers by reflexivity.
  rewrite sublist_self in Hreaches by reflexivity.
  assert (Hnew : ReachableDivisorProducts x (actual ++ v :: nil) products).
  {
    unfold ReachableDivisorProducts in Hactual |- *.
    destruct Hactual as [Hbase_nodup Hbase_members].
    split; [exact Hnodup|]. intro p. split.
    - intro Hp. apply Hmembers in Hp.
      destruct Hp as [Hpbase | [q [Hqbase [Hp [Hpbounds Hpdiv]]]]].
      + apply Hbase_members in Hpbase.
        destruct Hpbase as [Hpbounds [Hpdiv Hpreach]].
        split; [exact Hpbounds|]. split; [exact Hpdiv|].
        apply product_reachable_snoc_iff__outer_transition. left. exact Hpreach.
      + apply Hbase_members in Hqbase.
        destruct Hqbase as [Hqbounds [Hqdiv Hqreach]].
        split; [exact Hpbounds|]. split; [exact Hpdiv|].
        apply product_reachable_snoc_iff__outer_transition. right.
        exists q. tauto.
    - intros [Hpbounds [Hpdiv Hpreach]].
      apply product_reachable_snoc_iff__outer_transition in Hpreach.
      apply Hmembers.
      destruct Hpreach as [Hpreach | [q [Hqreach Hp]]].
      + left. apply Hbase_members. tauto.
      + right. exists q. split.
        * apply Hbase_members. split.
          -- split; nia.
          -- split.
             ++ destruct Hpdiv as [k Hk]. exists (v * k). nia.
             ++ exact Hqreach.
        * tauto.
  }
  split; [exact Hnew|]. split.
  - intro Hzero. unfold BadCardSegment. intros ids Hselected.
    assert (Hxin : In x products).
    {
      apply Hnew. split; [lia|]. split.
      - exists 1. ring.
      - exists ids. exact Hselected.
    }
    apply Hmembers in Hxin.
    destruct Hxin as [Hbase | [q [Hq [Hqx _]]]].
    + apply Hactual in Hbase.
      destruct Hbase as [_ [_ [oldids Hold]]].
      exact (Hbad oldids Hold).
    + destruct Hreaches as [[Hone' _] | [Hzero' Hnone]].
      * lia.
      * apply (Hnone q Hq).
        symmetry. exact Hqx.
  - intros Hone Hbadnew.
    destruct Hreaches as [[Hone' [q [Hq Hqx]]] | [Hzero Hnone]].
    + assert (Hxin : In x products).
      {
        apply Hmembers. right. exists q.
        split; [exact Hq|]. split; [symmetry; exact Hqx|].
        split; [lia|]. exists 1. ring.
      }
      apply Hnew in Hxin.
      destruct Hxin as [_ [_ [ids Hids]]].
      exact (Hbadnew ids Hids).
    + lia.
Qed.
Lemma reachable_singleton_products__outer_transition :
  forall x v,
    2 <= x -> 1 <= v <= x -> (exists k, x = v * k) ->
    (v <> 1 -> ReachableDivisorProducts x (v :: nil) (1 :: v :: nil)) /\
    (v = 1 -> ReachableDivisorProducts x (v :: nil) (1 :: nil)).
Proof.
  intros x v Hx Hv Hdiv. split.
  - intro Hv1. unfold ReachableDivisorProducts. split.
    + constructor; [simpl; tauto|constructor; [simpl; tauto|constructor]].
    + intro p. split.
      * intros [Hp | [Hp | []]]; subst p.
        -- split; [lia|]. split; [exists x; ring|].
           unfold ProductReachable. exists (fun _ => False).
           change (SelectedProduct (nil ++ v :: nil) (fun _ => False) = 1).
           rewrite selected_product_snoc_formula__outer_transition.
           rewrite selected_product_nil__outer_transition.
           destruct (prop_dec False); [contradiction|ring].
        -- split; [exact Hv|]. split; [exact Hdiv|].
           unfold ProductReachable. exists (fun j => j = 0).
           change (SelectedProduct (nil ++ v :: nil) (fun j => j = 0) = v).
           rewrite selected_product_snoc_formula__outer_transition.
           rewrite selected_product_nil__outer_transition, Zlength_nil.
           destruct (prop_dec (0 = 0)); [ring|contradiction].
      * intros [Hpbounds [Hpdiv Hpreach]].
        change (ProductReachable (nil ++ v :: nil) p) in Hpreach.
        apply product_reachable_snoc_iff__outer_transition in Hpreach.
        destruct Hpreach as [[ids Hids] | [q [[ids Hids] Hp]]].
        -- rewrite selected_product_nil__outer_transition in Hids.
           left. lia.
        -- rewrite selected_product_nil__outer_transition in Hids.
           right. left. nia.
  - intro Heq. subst v.
    unfold ReachableDivisorProducts. split.
    + constructor; [simpl; tauto|constructor].
    + intro p. split.
      * intros [Hp | []]. subst p. split; [lia|]. split.
        -- exists x. ring.
        -- unfold ProductReachable. exists (fun _ => False).
           change (SelectedProduct (nil ++ 1 :: nil) (fun _ => False) = 1).
           rewrite selected_product_snoc_formula__outer_transition.
           rewrite selected_product_nil__outer_transition.
           destruct (prop_dec False); [contradiction|ring].
      * intros [Hpbounds [Hpdiv Hpreach]].
        change (ProductReachable (nil ++ 1 :: nil) p) in Hpreach.
        apply product_reachable_snoc_iff__outer_transition in Hpreach.
        destruct Hpreach as [[ids Hids] | [q [[ids Hids] Hp]]].
        -- rewrite selected_product_nil__outer_transition in Hids.
           left. lia.
        -- rewrite selected_product_nil__outer_transition in Hids.
           left. nia.
Qed.
Lemma reachable_products_nondivisible_snoc__outer_transition :
  forall x seg products v,
    1 <= v -> Z.rem x v <> 0 ->
    ReachableDivisorProducts x seg products ->
    ReachableDivisorProducts x (seg ++ v :: nil) products.
Proof.
  intros x seg products v Hv Hrem Hreach.
  unfold ReachableDivisorProducts in Hreach |- *.
  destruct Hreach as [Hnodup Hmembers]. split; [exact Hnodup|].
  intro p. split.
  - intro Hp. apply Hmembers in Hp.
    destruct Hp as [Hbounds [Hdiv Hpreach]].
    split; [exact Hbounds|]. split; [exact Hdiv|].
    apply product_reachable_snoc_iff__outer_transition. left. exact Hpreach.
  - intros [Hbounds [Hdiv Hpreach]].
    apply product_reachable_snoc_iff__outer_transition in Hpreach.
    destruct Hpreach as [Hpreach | [q [Hqreach Hp]]].
    + apply Hmembers. tauto.
    + exfalso. apply Hrem.
      destruct Hdiv as [k Hk].
      rewrite Hk, Hp.
      replace (q * v * k) with ((q * k) * v) by ring.
      apply Z_rem_mult.
Qed.
Lemma not_bad_product_reachable__outer_transition :
  forall x seg,
    ~ BadCardSegment x seg -> ProductReachable seg x.
Proof.
  intros x seg Hnotbad. unfold BadCardSegment in Hnotbad.
  unfold ProductReachable. apply NNPP. intro Hnone.
  apply Hnotbad. intros ids Heq. apply Hnone. exists ids. exact Heq.
Qed.
Lemma valuable_aligned_no_cut__outer_transition :
  forall x a i segments old_products new_products,
    0 <= i < Zlength a ->
    ValuableAlignedHistory x a i segments old_products ->
    (forall starts,
      ValuablePrefixCuts x a i segments starts ->
      ReachableDivisorProducts x
        (sublist (Znth (Zlength starts - 1) starts 0) i a) old_products ->
      ReachableDivisorProducts x
        (sublist (Znth (Zlength starts - 1) starts 0) (i + 1) a)
        new_products /\
      BadCardSegment x
        (sublist (Znth (Zlength starts - 1) starts 0) (i + 1) a)) ->
    ValuableAlignedHistory x a (i + 1) segments new_products.
Proof.
  intros x a i segments old_products new_products Hi Haligned Hstep.
  unfold ValuableAlignedHistory in Haligned |- *.
  destruct Haligned as [starts [Hcuts [Hreach [Hforced Halign]]]].
  pose proof Hcuts as Hcuts0.
  destruct (Hstep starts Hcuts Hreach) as [Hreach' Hbad'].
  unfold ValuablePrefixCuts in Hcuts.
  destruct Hcuts as
    (Hlen & Hsegments & Hfirst & Hmono & Hlast & Hend &
     Hbad_completed & Hbad_final & Hlower).
  exists starts. split.
  - unfold ValuablePrefixCuts.
    refine (conj Hlen (conj Hsegments (conj Hfirst (conj Hmono
      (conj _ (conj _ (conj Hbad_completed (conj Hbad' _)))))))).
    + lia.
    + right. split; [lia|]. lia.
    + intros alternative Halternative.
      assert (Hendpoint : i <= i + 1 <= Zlength a) by lia.
      destruct (Halign (i + 1) alternative Hendpoint Halternative)
        as [Hcount _].
      exact Hcount.
  - split; [exact Hreach'|]. split; [exact Hforced|].
    apply valuable_partition_alignment_no_cut. exact Halign.
Qed.
Lemma valuable_aligned_forced_cut__outer_transition :
  forall x a i segments old_products new_products,
    0 <= i < Zlength a ->
    ValuableAlignedHistory x a i segments old_products ->
    (forall starts,
      ValuablePrefixCuts x a i segments starts ->
      ReachableDivisorProducts x
        (sublist (Znth (Zlength starts - 1) starts 0) i a) old_products ->
      ProductReachable
        (sublist (Znth (Zlength starts - 1) starts 0) (i + 1) a) x) ->
    ReachableDivisorProducts x (sublist i (i + 1) a) new_products ->
    BadCardSegment x (sublist i (i + 1) a) ->
    ValuableAlignedHistory x a (i + 1) (segments + 1) new_products.
Proof.
  intros x a i segments old_products new_products Hi Haligned Htrigger
    Hnewreach Hnewbad.
  unfold ValuableAlignedHistory in Haligned |- *.
  destruct Haligned as [starts [Hcuts [Hreach [Hforced Halign]]]].
  pose proof Hcuts as Hcuts0.
  pose proof (Htrigger starts Hcuts Hreach) as Htrigger_reach.
  unfold ValuablePrefixCuts in Hcuts.
  destruct Hcuts as
    (Hlen & Hsegments & Hfirst & Hmono & Hlast & Hend &
     Hbad_completed & Hbad_final & Hlower).
  assert (Hpositive : 0 < i).
  {
    destruct (Z.eq_dec i 0) as [Heq|Hneq]; [|lia].
    subst i.
    assert (Hlast_zero : Znth (Zlength starts - 1) starts 0 = 0) by lia.
    destruct Htrigger_reach as [ids Hids].
    exfalso.
    apply (Hnewbad ids).
    rewrite Hlast_zero in Hids. exact Hids.
  }
  assert (Hold_last : Znth (Zlength starts - 1) starts 0 < i).
  {
    destruct Hend as [[Hzero _] | [Hpos Hlt]]; [lia|exact Hlt].
  }
  assert (Hnewalign : ValuablePartitionAlignment x a (i + 1)
    (segments + 1) (starts ++ i :: nil)).
  {
    unfold ValuablePartitionAlignment.
    intros endpoint alternative Hendpoint Halt.
    assert (Hold_endpoint : i <= endpoint <= Zlength a) by lia.
    destruct (Halign endpoint alternative Hold_endpoint Halt)
      as [Hcount Hbounds].
    pose proof Halt as Halt0.
    unfold BadPartition in Halt.
    destruct Halt as [Halt_len [Halt_first [Halt_last [Halt_mono Halt_bad]]]].
    assert (Hprefix_len : Zlength (sublist 0 endpoint a) = endpoint).
    { rewrite Zlength_sublist by lia. lia. }
    assert (Hs_range : 0 <= segments - 1 < segments) by lia.
    pose proof (Hbounds (segments - 1) Hs_range) as Hprev_le.
    assert (Hprev_le_last :
      Znth (segments - 1) alternative 0 <=
      Znth (Zlength starts - 1) starts 0).
    {
      replace (Zlength starts - 1) with (segments - 1) by lia.
      exact Hprev_le.
    }
    assert (Hboundary : Znth segments alternative 0 <= i).
    {
      destruct (Z_le_gt_dec (Znth segments alternative 0) i) as [Hle|Hgt];
        [exact Hle|].
      exfalso.
      assert (Halt_prev_nonneg : 0 <= Znth (segments - 1) alternative 0).
      {
        destruct (Z.eq_dec (segments - 1) 0) as [Heq|Hneq].
        - rewrite Heq, Halt_first. lia.
        - pose proof (Halt_mono 0 (segments - 1)
            ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
          rewrite Halt_first in Hinc. lia.
      }
      assert (Halt_s_upper : Znth segments alternative 0 <= endpoint).
      {
        destruct (Z.eq_dec segments (Zlength alternative - 1)) as [Heq|Hneq].
        - rewrite Heq, Halt_last, Hprefix_len. lia.
        - pose proof (Halt_mono segments (Zlength alternative - 1)
            ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
          rewrite Halt_last, Hprefix_len in Hinc. lia.
      }
      specialize (Halt_bad (segments - 1) ltac:(lia)).
      replace (segments - 1 + 1) with segments in Halt_bad by lia.
      assert (Hnormalize :
        sublist (Znth (segments - 1) alternative 0)
          (Znth segments alternative 0) (sublist 0 endpoint a) =
        sublist (Znth (segments - 1) alternative 0)
          (Znth segments alternative 0) a).
      {
        apply Zsublist_Zsublist0.
        - exact Halt_prev_nonneg.
        - split; [lia|exact Halt_s_upper].
      }
      rewrite Hnormalize in Halt_bad.
      assert (Hembedded : ProductReachable
        (sublist (Znth (segments - 1) alternative 0)
          (Znth segments alternative 0) a) x).
      {
        eapply product_reachable_sublist_mono__outer_transition
          with (lo := Znth (Zlength starts - 1) starts 0 -
                        Znth (segments - 1) alternative 0)
               (hi := i + 1 - Znth (segments - 1) alternative 0).
        - lia.
        - rewrite Zlength_sublist by lia. lia.
        - rewrite Zsublist_Zsublist by lia.
          replace
            (Znth (Zlength starts - 1) starts 0 -
               Znth (segments - 1) alternative 0 +
             Znth (segments - 1) alternative 0)
            with (Znth (Zlength starts - 1) starts 0) by lia.
          replace
            (i + 1 - Znth (segments - 1) alternative 0 +
             Znth (segments - 1) alternative 0)
            with (i + 1) by lia.
          exact Htrigger_reach.
      }
      destruct Hembedded as [ids Hids].
      exact (Halt_bad ids Hids).
    }
    assert (Hcount' : segments + 1 <= Zlength alternative - 1).
    {
      destruct (Z.eq_dec segments (Zlength alternative - 1)) as [Heq|Hneq].
      - rewrite Heq, Halt_last, Hprefix_len in Hboundary. lia.
      - lia.
    }
    split; [exact Hcount'|].
    intros k Hk.
    destruct (Z_lt_ge_dec k segments) as [Hkold|Hknew].
    - rewrite app_Znth1 by (rewrite Hlen; lia).
      apply Hbounds. lia.
    - assert (Hkeq : k = segments) by lia. subst k.
      rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite Hlen. replace (segments - segments) with 0 by lia.
      rewrite Znth0_cons. exact Hboundary.
  }
  exists (starts ++ i :: nil). split.
  - unfold ValuablePrefixCuts.
    refine (conj _ (conj _ (conj _ (conj _
      (conj _ (conj _ (conj _ (conj _ _)))))))).
    + rewrite Zlength_app_cons, Hlen. lia.
    + lia.
    + rewrite app_Znth1 by (rewrite Hlen; lia). exact Hfirst.
    + unfold mono_inc in *.
      intros p q Hp Hpq Hq.
      rewrite Zlength_app_cons, Hlen in Hq.
      destruct (Z_lt_ge_dec q segments) as [Hqold|Hqnew].
      * rewrite !app_Znth1 by (rewrite Hlen; lia).
        eapply Hmono; lia.
      * assert (Hqeq : q = segments) by lia. subst q.
        rewrite (app_Znth2 0 starts (i :: nil) segments) by lia.
        rewrite Hlen. replace (segments - segments) with 0 by lia.
        rewrite Znth0_cons.
        rewrite app_Znth1 by (rewrite Hlen; lia).
        destruct (Z.eq_dec p (segments - 1)) as [Heq|Hneq].
        -- subst p. rewrite <- Hlen. exact Hold_last.
        -- pose proof (Hmono p (segments - 1) Hp ltac:(lia) ltac:(lia))
             as Hinc.
           rewrite <- Hlen in Hinc. lia.
    + rewrite Zlength_app_cons, Hlen.
      replace (segments + 1 - 1) with segments by lia.
      rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite Hlen. replace (segments - segments) with 0 by lia.
      rewrite Znth0_cons. lia.
    + right. split; [lia|].
      rewrite Zlength_app_cons, Hlen.
      replace (segments + 1 - 1) with segments by lia.
      rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite Hlen. replace (segments - segments) with 0 by lia.
      rewrite Znth0_cons. lia.
    + rewrite Zlength_app_cons, Hlen. intros k Hk.
      destruct (Z_lt_ge_dec k (segments - 1)) as [Hkold|Hklast].
      * rewrite !app_Znth1 by (rewrite Hlen; lia).
        apply Hbad_completed. lia.
      * assert (Hkeq : k = segments - 1) by lia. subst k.
        rewrite app_Znth1 by (rewrite Hlen; lia).
        replace (segments - 1 + 1) with segments by lia.
        rewrite app_Znth2 by (rewrite Hlen; lia).
        rewrite Hlen. replace (segments - segments) with 0 by lia.
        rewrite Znth0_cons.
        replace (segments - 1) with (Zlength starts - 1) by lia.
        exact Hbad_final.
    + rewrite Zlength_app_cons, Hlen.
      replace (segments + 1 - 1) with segments by lia.
      rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite Hlen. replace (segments - segments) with 0 by lia.
      rewrite Znth0_cons. exact Hnewbad.
    + intros alternative Halternative.
      destruct (Hnewalign (i + 1) alternative) as [Hcount _].
      * lia.
      * exact Halternative.
      * exact Hcount.
  - split.
    + rewrite Zlength_app_cons, Hlen.
      replace (segments + 1 - 1) with segments by lia.
      rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite Hlen. replace (segments - segments) with 0 by lia.
      rewrite Znth0_cons. exact Hnewreach.
    + split.
      * rewrite Zlength_app_cons, Hlen. intros k Hk.
        destruct (Z_lt_ge_dec k (segments - 1)) as [Hkold|Hklast].
        -- rewrite !app_Znth1 by (rewrite Hlen; lia).
           apply Hforced. lia.
        -- assert (Hkeq : k = segments - 1) by lia. subst k.
           rewrite app_Znth1 by (rewrite Hlen; lia).
           replace (segments - 1 + 1) with segments by lia.
           rewrite app_Znth2 by (rewrite Hlen; lia).
           rewrite Hlen. replace (segments - segments) with 0 by lia.
           rewrite Znth0_cons.
           intro Hbadtrigger.
           replace (segments - 1) with (Zlength starts - 1)
             in Hbadtrigger by lia.
           destruct Htrigger_reach as [ids Hids].
           exact (Hbadtrigger ids Hids).
      * exact Hnewalign.
Qed.
Lemma sublist_snoc__outer_transition :
  forall (A : Type) (d : A) (a : list A) lo i,
    0 <= lo /\ lo <= i /\ i < Zlength a ->
    sublist lo (i + 1) a = sublist lo i a ++ Znth i a d :: nil.
Proof.
  intros A d a lo i Hbounds.
  rewrite (sublist_split lo (i + 1) i a) by lia.
  rewrite (sublist_single d i a) by lia.
  reflexivity.
Qed.
Lemma reachable_table_absent_bad__outer_transition :
  forall x seg products,
    1 <= x ->
    ReachableDivisorProducts x seg products ->
    ~ In x products ->
    BadCardSegment x seg.
Proof.
  intros x seg products Hx Hreach Habsent ids Hids.
  apply Habsent.
  destruct Hreach as [_ Hreach].
  apply Hreach.
  split; [lia|].
  split; [exists 1; lia|].
  exists ids. exact Hids.
Qed.
Lemma valuable_bitmap_zero_not_member__outer_transition :
  forall x products bitmap p,
    ValuableBitmap x products bitmap ->
    0 <= p <= x ->
    Znth p bitmap 0 = 0 ->
    ~ In p products.
Proof.
  intros x products bitmap p Hbitmap Hp Hzero Hin.
  specialize (Hbitmap p Hp).
  destruct (in_dec Z.eq_dec p products) as [Hin' | Hnotin].
  - rewrite Hbitmap in Hzero. discriminate.
  - contradiction.
Qed.
Lemma valuable_bitmap_nonzero_member__outer_transition :
  forall x products bitmap p,
    ValuableBitmap x products bitmap ->
    0 <= p <= x ->
    Znth p bitmap 0 <> 0 ->
    In p products.
Proof.
  intros x products bitmap p Hbitmap Hp Hnonzero.
  specialize (Hbitmap p Hp).
  destruct (in_dec Z.eq_dec p products) as [Hin | Hnotin].
  - exact Hin.
  - rewrite Hbitmap in Hnonzero. contradiction.
Qed.
Lemma pre_value_not_x__outer_transition :
  forall x a i,
    Pre x a ->
    0 <= i < Zlength a ->
    Znth i a 0 <> x.
Proof.
  intros x a i Hpre Hi.
  unfold Pre in Hpre.
  destruct Hpre as [_ [_ Hall]].
  apply Forall_forall with (x := Znth i a 0) in Hall.
  - tauto.
  - apply Znth_In_Zlength. exact Hi.
Qed.
Lemma Zlength_replace_Znth__outer_transition :
  forall (A : Type) (i : Z) (v : A) (a : list A),
    Zlength (replace_Znth i v a) = Zlength a.
Proof.
  intros A i v a.
  rewrite !Zlength_correct.
  apply f_equal.
  unfold replace_Znth.
  generalize (Z.to_nat i).
  induction a as [|h t IH]; intros n; simpl; [reflexivity|].
  destruct n; simpl; [reflexivity|rewrite IH; reflexivity].
Qed.
Lemma rem_zero_divides__outer_transition :
  forall x v, Z.rem x v = 0 -> exists k, x = v * k.
Proof.
  intros x v Hrem.
  apply Zrem_divides. exact Hrem.
Qed.
Lemma valuable_aligned_history_complete__final_result :
  forall (x : Z) (a : list Z) (segments : Z) (products : list Z),
    Pre x a ->
    ValuableAlignedHistory x a (Zlength a) segments products ->
    Spec x a segments.
Proof.
  intros x a segments products Hpre Hhistory.
  unfold Pre in Hpre.
  destruct Hpre as [_ [Halen _]].
  unfold ValuableAlignedHistory in Hhistory.
  destruct Hhistory as
    [starts [Hprefix [_ [_ Halign]]]].
  unfold ValuablePrefixCuts in Hprefix.
  destruct Hprefix as
    (Hstarts_len & Hsegments & Hfirst & Hmono & Hlast_bounds &
     Hendcase & Hbad_prefix & Hbad_final & Hlower).
  assert (Hlast_lt :
    Znth (Zlength starts - 1) starts 0 < Zlength a).
  {
    destruct Hendcase as [[Hzero _] | [_ Hlt]].
    - lia.
    - exact Hlt.
  }
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (starts ++ Zlength a :: nil).
  split.
  - split.
    + unfold BadPartition.
      split.
      * rewrite Zlength_app_cons, Hstarts_len. lia.
      * split.
        -- rewrite app_Znth1 by lia. exact Hfirst.
        -- split.
           ++ rewrite Zlength_app_cons.
              replace (Zlength starts + 1 - 1) with (Zlength starts) by lia.
              rewrite app_Znth2 by lia.
              replace (Zlength starts - Zlength starts) with 0 by lia.
              rewrite Znth0_cons. reflexivity.
           ++ split.
              ** unfold mono_inc in *.
                 intros p q Hp Hpq Hq.
                 rewrite Zlength_app_cons in Hq.
                 destruct (Z_lt_ge_dec q (Zlength starts)) as [Hqold | Hqnew].
                 --- rewrite !app_Znth1 by lia.
                     eapply Hmono; lia.
                 --- assert (Hqeq : q = Zlength starts) by lia.
                     subst q.
                     rewrite app_Znth1 by lia.
                     rewrite app_Znth2 by lia.
                     replace (Zlength starts - Zlength starts) with 0 by lia.
                     rewrite Znth0_cons.
                     destruct (Z.eq_dec p (Zlength starts - 1)) as [-> | Hneq].
                     +++ exact Hlast_lt.
                     +++ pose proof
                           (Hmono p (Zlength starts - 1) Hp
                             ltac:(lia) ltac:(lia)) as Hstrict.
                         lia.
              ** rewrite Zlength_app_cons.
                 intros k Hk.
                 destruct (Z_lt_ge_dec k (Zlength starts - 1))
                   as [Hkold | Hklast].
                 --- rewrite !app_Znth1 by lia.
                     apply Hbad_prefix. lia.
                 --- assert (Hkeq : k = Zlength starts - 1) by lia.
                     subst k.
                     rewrite app_Znth1 by lia.
                     replace (Zlength starts - 1 + 1)
                       with (Zlength starts) by lia.
                     rewrite app_Znth2 by lia.
                     replace (Zlength starts - Zlength starts) with 0 by lia.
                     rewrite Znth0_cons.
                     exact Hbad_final.
    + intros alternative Halternative.
      rewrite Zlength_app_cons, Hstarts_len.
      assert (Halternative_prefix :
        BadPartition x (sublist 0 (Zlength a) a) alternative).
      {
        rewrite sublist_self by reflexivity.
        exact Halternative.
      }
      specialize
        (Halign (Zlength a) alternative ltac:(lia) Halternative_prefix).
      destruct Halign as [Hlower_aligned _].
      lia.
  - rewrite Zlength_app_cons, Hstarts_len. lia.
Qed.
