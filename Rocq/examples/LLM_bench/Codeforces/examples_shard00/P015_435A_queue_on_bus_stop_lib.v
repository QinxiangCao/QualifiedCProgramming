Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ValidBusLoading (groups : list Z) (capacity : Z) (cuts : list Z) : Prop :=
  2 <= Zlength cuts /\
  Znth 0 cuts 0 = 0 /\
  Znth (Zlength cuts - 1) cuts 0 = Zlength groups /\
  mono_inc cuts /\
  (forall k, 0 <= k < Zlength cuts - 1 ->
     fold_right Z.add 0
       (sublist (Znth k cuts 0) (Znth (k + 1) cuts 0) groups) <= capacity).

Definition Pre (capacity : Z) (groups : list Z) : Prop :=
  1 <= Zlength groups <= 100 /\
  1 <= capacity <= 100 /\
  Forall (fun size => 1 <= size <= capacity) groups.

Definition Spec (capacity : Z) (groups : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (ValidBusLoading groups capacity)
    (fun cuts => Zlength cuts - 1) out.

Definition GreedyBusLoading
    (groups : list Z) (capacity : Z) (cuts : list Z) : Prop :=
  ValidBusLoading groups capacity cuts /\
  (forall k, 0 <= k < Zlength cuts - 2 ->
     capacity <
       fold_right Z.add 0
         (sublist (Znth k cuts 0) (Znth (k + 1) cuts 0 + 1) groups)).

Definition GreedyPrefixState
    (groups : list Z) (capacity buses used : Z) : Prop :=
  (groups = nil /\ buses = 1 /\ used = 0) \/
  exists cuts,
    GreedyBusLoading groups capacity cuts /\
    Zlength cuts = buses + 1 /\
    used =
      fold_right Z.add 0
        (sublist (Znth (Zlength cuts - 2) cuts 0) (Zlength groups) groups).

Require Import Coq.micromega.Lia.
Lemma Zlength_replace_Znth__greedy_transitions :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l.
  induction l as [|a l IH]; intros n v; simpl; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n) as [|m].
  - simpl. repeat rewrite Zlength_cons. lia.
  - simpl. repeat rewrite Zlength_cons.
    specialize (IH (Z.of_nat m) v).
    replace (Z.to_nat (Z.of_nat m)) with m in IH by lia.
    rewrite IH. lia.
Qed.
Lemma Znth_app_left__greedy_transitions :
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
Lemma Znth_app_last__greedy_transitions :
  forall {A : Type} (d x : A) (l : list A),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros A d x l.
  unfold Znth.
  rewrite app_nth2.
  - replace (Z.to_nat (Zlength l) - length l)%nat with 0%nat.
    + simpl. reflexivity.
    + rewrite Zlength_correct, Nat2Z.id. lia.
  - rewrite Zlength_correct, Nat2Z.id. lia.
Qed.
Lemma sublist_app_left__greedy_transitions :
  forall {A : Type} (l : list A) x lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    sublist lo hi (l ++ x :: nil) = sublist lo hi l.
Proof.
  intros A l x lo hi Hlohi Hhi.
  apply sublist_split_app_l; assumption.
Qed.
Lemma sublist_snoc__greedy_transitions :
  forall {A : Type} (d : A) (l : list A) i,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l d :: nil.
Proof.
  intros A d l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single d i l) by lia.
  reflexivity.
Qed.
Lemma sublist_snoc_end__greedy_transitions :
  forall {A : Type} (l : list A) x lo,
    0 <= lo <= Zlength l ->
    sublist lo (Zlength l + 1) (l ++ x :: nil) =
      sublist lo (Zlength l) l ++ x :: nil.
Proof.
  intros A l x lo Hlo.
  rewrite (sublist_split lo (Zlength l + 1) (Zlength l) (l ++ x :: nil))
    by (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite sublist_app_left__greedy_transitions by lia.
  rewrite (sublist_single x (Zlength l) (l ++ x :: nil)).
  - rewrite Znth_app_last__greedy_transitions. reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.
Lemma sublist_same__greedy_transitions :
  forall {A : Type} (l : list A) i,
    sublist i i l = nil.
Proof.
  intros A l i.
  unfold sublist.
  apply skipn_all2.
  rewrite length_firstn. lia.
Qed.
Lemma fold_right_add_snoc__greedy_transitions :
  forall (l : list Z) x,
    fold_right Z.add 0 (l ++ x :: nil) = fold_right Z.add 0 l + x.
Proof.
  induction l as [|a l IH]; intros x.
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.
Lemma mono_inc_snoc__greedy_transitions :
  forall cuts last,
    1 <= Zlength cuts ->
    mono_inc cuts ->
    Znth (Zlength cuts - 1) cuts 0 < last ->
    mono_inc (cuts ++ last :: nil).
Proof.
  intros cuts last Hlen Hmono Hlast a b Ha Hab Hb.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hb.
  destruct (Z_lt_ge_dec b (Zlength cuts)) as [Hb_old | Hb_new].
  - rewrite !Znth_app_left__greedy_transitions by lia.
    apply Hmono; lia.
  - assert (b = Zlength cuts) by lia. subst b.
    rewrite Znth_app_last__greedy_transitions.
    rewrite Znth_app_left__greedy_transitions by lia.
    destruct (Z.eq_dec a (Zlength cuts - 1)) as [Ha_last | Ha_before].
    + subst a. exact Hlast.
    + eapply Z.lt_trans with (m := Znth (Zlength cuts - 1) cuts 0).
      * apply Hmono; lia.
      * exact Hlast.
Qed.
Lemma mono_inc_replace_last__greedy_transitions :
  forall cuts last,
    2 <= Zlength cuts ->
    mono_inc cuts ->
    Znth (Zlength cuts - 1) cuts 0 < last ->
    mono_inc (replace_Znth (Zlength cuts - 1) last cuts).
Proof.
  intros cuts last Hlen Hmono Hlast a b Ha Hab Hb.
  rewrite Zlength_replace_Znth__greedy_transitions in Hb.
  destruct (Z.eq_dec b (Zlength cuts - 1)) as [Hb_last | Hb_old].
  - subst b.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Znth_replace_Znth_Diff by lia.
    destruct (Z.eq_dec a (Zlength cuts - 1)) as [Ha_last | Ha_before].
    + lia.
    + eapply Z.lt_trans with (m := Znth (Zlength cuts - 1) cuts 0).
      * apply Hmono; lia.
      * exact Hlast.
  - rewrite !Znth_replace_Znth_Diff by lia.
    apply Hmono; lia.
Qed.
Lemma valid_cut_bounds__greedy_transitions :
  forall groups capacity cuts j,
    ValidBusLoading groups capacity cuts ->
    0 <= j < Zlength cuts ->
    0 <= Znth j cuts 0 <= Zlength groups /\
    (j < Zlength cuts - 1 -> Znth j cuts 0 < Zlength groups).
Proof.
  intros groups capacity cuts j Hvalid Hj.
  unfold ValidBusLoading in Hvalid.
  destruct Hvalid as [Hlen [Hfirst [Hlast [Hmono Hsegments]]]].
  assert (Hlast_index : 0 <= Zlength cuts - 1 < Zlength cuts) by lia.
  split.
  - split.
    + destruct (Z.eq_dec j 0) as [-> | Hj0].
      * rewrite Hfirst. lia.
      * pose proof (Hmono 0 j ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
        rewrite Hfirst in Hbound. lia.
    + destruct (Z.eq_dec j (Zlength cuts - 1)) as [-> | Hjlast].
      * rewrite Hlast. lia.
      * pose proof
          (Hmono j (Zlength cuts - 1) ltac:(lia) ltac:(lia) ltac:(lia))
          as Hbound.
        rewrite Hlast in Hbound. lia.
  - intros Hjstrict.
    pose proof
      (Hmono j (Zlength cuts - 1) ltac:(lia) ltac:(lia) ltac:(lia))
      as Hbound.
    rewrite Hlast in Hbound. exact Hbound.
Qed.
Lemma greedy_prefix_state_singleton__greedy_transitions :
  forall capacity x,
    1 <= x <= capacity ->
    GreedyPrefixState (x :: nil) capacity 1 x.
Proof.
  intros capacity x Hx.
  unfold GreedyPrefixState.
  right.
  exists (0 :: 1 :: nil).
  split.
  - unfold GreedyBusLoading.
    split.
    + unfold ValidBusLoading.
      split.
      * repeat rewrite Zlength_cons. rewrite Zlength_nil. lia.
      * split.
        -- unfold Znth. simpl. reflexivity.
        -- split.
          ++ repeat rewrite Zlength_cons. rewrite Zlength_nil.
             unfold Znth. simpl. reflexivity.
          ++ split.
             ** unfold mono_inc. intros a b Ha Hab Hb.
                repeat rewrite Zlength_cons in Hb. rewrite Zlength_nil in Hb.
                assert (a = 0 /\ b = 1) by lia.
                destruct H as [-> ->]. unfold Znth. simpl. lia.
             ** intros k Hk.
                repeat rewrite Zlength_cons in Hk. rewrite Zlength_nil in Hk.
                assert (k = 0) by lia. subst k.
                simpl. lia.
    + intros k Hk.
      repeat rewrite Zlength_cons in Hk. rewrite Zlength_nil in Hk. lia.
  - split.
    + repeat rewrite Zlength_cons. rewrite Zlength_nil. lia.
    + repeat rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
Qed.
Lemma greedy_prefix_state_overflow_snoc__greedy_transitions :
  forall groups capacity buses used x,
    1 <= x <= capacity ->
    capacity < used + x ->
    GreedyPrefixState groups capacity buses used ->
    GreedyPrefixState (groups ++ x :: nil) capacity (buses + 1) x.
Proof.
  intros groups capacity buses used x Hx Hover Hstate.
  unfold GreedyPrefixState in Hstate |- *.
  destruct Hstate as [[Hnil [Hbuses Hused0]] |
      [cuts [Hgreedy [Hcount Hused]]]].
  - subst groups buses used.
    exfalso. lia.
  - right.
    exists (cuts ++ (Zlength groups + 1) :: nil).
    unfold GreedyBusLoading in Hgreedy.
    destruct Hgreedy as [Hvalid Hboundary].
    pose proof Hvalid as Hvalid_for_bounds.
    unfold ValidBusLoading in Hvalid.
    destruct Hvalid as
      [Hcutlen [Hfirst [Hlast [Hmono Hsegments]]]].
    pose proof (Zlength_nonneg groups) as Hgroups_len.
    split.
    + unfold GreedyBusLoading.
      split.
      * unfold ValidBusLoading.
        split.
        -- rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
        -- split.
           ++ rewrite Znth_app_left__greedy_transitions by lia.
              exact Hfirst.
           ++ split.
              ** repeat rewrite Zlength_app.
                 repeat rewrite Zlength_cons.
                 repeat rewrite Zlength_nil.
                 replace (Zlength cuts + Z.succ 0 - 1) with (Zlength cuts) by lia.
                 rewrite Znth_app_last__greedy_transitions. lia.
              ** split.
                 --- apply mono_inc_snoc__greedy_transitions.
                     +++ lia.
                     +++ exact Hmono.
                     +++ rewrite Hlast. lia.
                 --- intros k Hk.
                     rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
                     destruct (Z.eq_dec k (Zlength cuts - 1)) as [Hk_last | Hk_old].
                     +++ subst k.
                         rewrite Znth_app_left__greedy_transitions by lia.
                         replace (Zlength cuts - 1 + 1) with (Zlength cuts) by lia.
                         rewrite Znth_app_last__greedy_transitions.
                         rewrite Hlast.
                         rewrite sublist_snoc_end__greedy_transitions by lia.
                         rewrite sublist_same__greedy_transitions.
                         simpl. lia.
                     +++ assert (Hk_range : 0 <= k < Zlength cuts - 1) by lia.
                         specialize (Hsegments k Hk_range).
                         pose proof
                           (valid_cut_bounds__greedy_transitions
                              groups capacity cuts k Hvalid_for_bounds ltac:(lia))
                           as [[Hstart_nonneg Hstart_le] Hstart_lt].
                         pose proof
                           (valid_cut_bounds__greedy_transitions
                              groups capacity cuts (k + 1) Hvalid_for_bounds ltac:(lia))
                           as [[Hend_nonneg Hend_le] Hend_lt].
                         pose proof
                           (Hmono k (k + 1) ltac:(lia) ltac:(lia) ltac:(lia))
                           as Hcuts_order.
                         rewrite !Znth_app_left__greedy_transitions by lia.
                         rewrite sublist_app_left__greedy_transitions by lia.
                         exact Hsegments.
      * intros k Hk.
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
        destruct (Z_lt_ge_dec k (Zlength cuts - 2)) as [Hk_old | Hk_new].
        -- specialize (Hboundary k ltac:(lia)).
           pose proof
             (valid_cut_bounds__greedy_transitions
                groups capacity cuts k Hvalid_for_bounds ltac:(lia))
             as [[Hstart_nonneg Hstart_le] Hstart_lt].
           pose proof
             (valid_cut_bounds__greedy_transitions
                groups capacity cuts (k + 1) Hvalid_for_bounds ltac:(lia))
             as [[Hend_nonneg Hend_le] Hend_lt].
           pose proof
             (Hmono k (k + 1) ltac:(lia) ltac:(lia) ltac:(lia))
             as Hcuts_order.
           rewrite !Znth_app_left__greedy_transitions by lia.
           rewrite sublist_app_left__greedy_transitions by lia.
           exact Hboundary.
        -- assert (k = Zlength cuts - 2) by lia. subst k.
           rewrite !Znth_app_left__greedy_transitions by lia.
           replace (Zlength cuts - 2 + 1) with (Zlength cuts - 1) by lia.
           rewrite Hlast.
           pose proof
             (valid_cut_bounds__greedy_transitions
                groups capacity cuts (Zlength cuts - 2)
                Hvalid_for_bounds ltac:(lia))
             as [[Hstart_nonneg Hstart_le] Hstart_lt].
           rewrite sublist_snoc_end__greedy_transitions by lia.
           rewrite fold_right_add_snoc__greedy_transitions.
           rewrite <- Hused. exact Hover.
    + split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * repeat rewrite Zlength_app.
        repeat rewrite Zlength_cons.
        repeat rewrite Zlength_nil.
        replace (Zlength cuts + Z.succ 0 - 2) with (Zlength cuts - 1) by lia.
        rewrite Znth_app_left__greedy_transitions by lia.
        rewrite Hlast.
        rewrite sublist_snoc_end__greedy_transitions by lia.
        rewrite sublist_same__greedy_transitions.
        simpl. lia.
Qed.
Lemma greedy_prefix_state_fit_snoc__greedy_transitions :
  forall groups capacity buses used x,
    1 <= x <= capacity ->
    used + x <= capacity ->
    GreedyPrefixState groups capacity buses used ->
    GreedyPrefixState (groups ++ x :: nil) capacity buses (used + x).
Proof.
  intros groups capacity buses used x Hx Hfit Hstate.
  unfold GreedyPrefixState in Hstate |- *.
  destruct Hstate as [[Hnil [Hbuses Hused0]] |
      [cuts [Hgreedy [Hcount Hused]]]].
  - subst groups buses used.
    simpl.
    apply greedy_prefix_state_singleton__greedy_transitions.
    exact Hx.
  - right.
    exists (replace_Znth (Zlength cuts - 1) (Zlength groups + 1) cuts).
    unfold GreedyBusLoading in Hgreedy.
    destruct Hgreedy as [Hvalid Hboundary].
    pose proof Hvalid as Hvalid_for_bounds.
    unfold ValidBusLoading in Hvalid.
    destruct Hvalid as
      [Hcutlen [Hfirst [Hlast [Hmono Hsegments]]]].
    pose proof (Zlength_nonneg groups) as Hgroups_len.
    split.
    + unfold GreedyBusLoading.
      split.
      * unfold ValidBusLoading.
        split.
        -- rewrite Zlength_replace_Znth__greedy_transitions. exact Hcutlen.
        -- split.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hfirst.
           ++ split.
              ** rewrite Zlength_replace_Znth__greedy_transitions.
                 rewrite Znth_replace_Znth_Same by lia.
                 rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
              ** split.
                 --- apply mono_inc_replace_last__greedy_transitions.
                     +++ exact Hcutlen.
                     +++ exact Hmono.
                     +++ rewrite Hlast. lia.
                 --- intros k Hk.
                     rewrite Zlength_replace_Znth__greedy_transitions in Hk.
                     destruct (Z_lt_ge_dec k (Zlength cuts - 2)) as [Hk_old | Hk_new].
                     +++ assert (Hk_range : 0 <= k < Zlength cuts - 1) by lia.
                         specialize (Hsegments k Hk_range).
                         pose proof
                           (valid_cut_bounds__greedy_transitions
                              groups capacity cuts k Hvalid_for_bounds ltac:(lia))
                           as [[Hstart_nonneg Hstart_le] Hstart_lt].
                         pose proof
                           (valid_cut_bounds__greedy_transitions
                              groups capacity cuts (k + 1) Hvalid_for_bounds ltac:(lia))
                           as [[Hend_nonneg Hend_le] Hend_lt].
                         pose proof
                           (Hmono k (k + 1) ltac:(lia) ltac:(lia) ltac:(lia))
                           as Hcuts_order.
                         rewrite !Znth_replace_Znth_Diff by lia.
                         rewrite sublist_app_left__greedy_transitions by lia.
                         exact Hsegments.
                     +++ assert (k = Zlength cuts - 2) by lia. subst k.
                         rewrite Znth_replace_Znth_Diff by lia.
                         replace (Zlength cuts - 2 + 1) with (Zlength cuts - 1) by lia.
                         rewrite Znth_replace_Znth_Same by lia.
                         pose proof
                           (valid_cut_bounds__greedy_transitions
                              groups capacity cuts (Zlength cuts - 2)
                              Hvalid_for_bounds ltac:(lia))
                           as [[Hstart_nonneg Hstart_le] Hstart_lt].
                         rewrite sublist_snoc_end__greedy_transitions by lia.
                         rewrite fold_right_add_snoc__greedy_transitions.
                         rewrite <- Hused. exact Hfit.
      * intros k Hk.
        rewrite Zlength_replace_Znth__greedy_transitions in Hk.
        specialize (Hboundary k Hk).
        pose proof
          (valid_cut_bounds__greedy_transitions
             groups capacity cuts k Hvalid_for_bounds ltac:(lia))
          as [[Hstart_nonneg Hstart_le] Hstart_lt].
        pose proof
          (valid_cut_bounds__greedy_transitions
             groups capacity cuts (k + 1) Hvalid_for_bounds ltac:(lia))
          as [[Hend_nonneg Hend_le] Hend_lt].
        pose proof
          (Hmono k (k + 1) ltac:(lia) ltac:(lia) ltac:(lia))
          as Hcuts_order.
        rewrite !Znth_replace_Znth_Diff by lia.
        rewrite sublist_app_left__greedy_transitions by lia.
        exact Hboundary.
    + split.
      * rewrite Zlength_replace_Znth__greedy_transitions. exact Hcount.
      * repeat rewrite Zlength_app.
        repeat rewrite Zlength_cons.
        repeat rewrite Zlength_nil.
        rewrite Zlength_replace_Znth__greedy_transitions.
        rewrite Znth_replace_Znth_Diff by lia.
        pose proof
          (valid_cut_bounds__greedy_transitions
             groups capacity cuts (Zlength cuts - 2)
             Hvalid_for_bounds ltac:(lia))
          as [[Hstart_nonneg Hstart_le] Hstart_lt].
        rewrite sublist_snoc_end__greedy_transitions by lia.
        rewrite fold_right_add_snoc__greedy_transitions.
        rewrite <- Hused. reflexivity.
Qed.
Lemma greedy_prefix_state_overflow_step__greedy_transitions :
  forall groups capacity buses used i,
    0 <= i < Zlength groups ->
    1 <= Znth i groups 0 <= capacity ->
    capacity < used + Znth i groups 0 ->
    GreedyPrefixState (sublist 0 i groups) capacity buses used ->
    GreedyPrefixState (sublist 0 (i + 1) groups)
      capacity (buses + 1) (Znth i groups 0).
Proof.
  intros groups capacity buses used i Hi Hx Hover Hstate.
  rewrite (sublist_snoc__greedy_transitions 0 groups i) by exact Hi.
  apply (greedy_prefix_state_overflow_snoc__greedy_transitions
    (sublist 0 i groups) capacity buses used (Znth i groups 0)); assumption.
Qed.
Lemma greedy_prefix_state_fit_step__greedy_transitions :
  forall groups capacity buses used i,
    0 <= i < Zlength groups ->
    1 <= Znth i groups 0 <= capacity ->
    used + Znth i groups 0 <= capacity ->
    GreedyPrefixState (sublist 0 i groups) capacity buses used ->
    GreedyPrefixState (sublist 0 (i + 1) groups)
      capacity buses (used + Znth i groups 0).
Proof.
  intros groups capacity buses used i Hi Hx Hfit Hstate.
  rewrite (sublist_snoc__greedy_transitions 0 groups i) by exact Hi.
  apply (greedy_prefix_state_fit_snoc__greedy_transitions
    (sublist 0 i groups) capacity buses used (Znth i groups 0)); assumption.
Qed.
Lemma sum_nonnegative_pointwise__final_result :
  forall xs,
    (forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0) ->
    0 <= fold_right Z.add 0 xs.
Proof.
  intros xs Hnonneg.
  pose proof (proj2 (Forall_Znth (fun x => 0 <= x) 0 xs) Hnonneg) as Hall.
  clear Hnonneg.
  induction xs as [| x xs IH]; inversion Hall as [| ? ? Hx Htail]; subst; simpl.
  - lia.
  - specialize (IH Htail). lia.
Qed.
Lemma sum_sublist_nonnegative__final_result :
  forall groups lo hi,
    (forall k, 0 <= k < Zlength groups -> 0 <= Znth k groups 0) ->
    0 <= lo <= hi ->
    hi <= Zlength groups ->
    0 <= fold_right Z.add 0 (sublist lo hi groups).
Proof.
  intros groups lo hi Hnonneg Hlo Hhi.
  apply sum_nonnegative_pointwise__final_result.
  intros k Hk.
  rewrite Zlength_sublist in Hk by lia.
  rewrite Znth_sublist by lia.
  apply Hnonneg. lia.
Qed.
Lemma sum_sublist_inclusion__final_result :
  forall groups outer_lo inner_lo inner_hi outer_hi,
    (forall k, 0 <= k < Zlength groups -> 0 <= Znth k groups 0) ->
    0 <= outer_lo <= inner_lo ->
    inner_lo <= inner_hi <= outer_hi ->
    outer_hi <= Zlength groups ->
    fold_right Z.add 0 (sublist inner_lo inner_hi groups) <=
    fold_right Z.add 0 (sublist outer_lo outer_hi groups).
Proof.
  intros groups outer_lo inner_lo inner_hi outer_hi Hnonneg Hleft Hright Hbound.
  rewrite (sublist_split outer_lo outer_hi inner_lo groups) by lia.
  rewrite (sublist_split inner_lo outer_hi inner_hi groups) by lia.
  rewrite !ListLib.sum_app.
  pose proof (sum_sublist_nonnegative__final_result
    groups outer_lo inner_lo Hnonneg ltac:(lia) ltac:(lia)).
  pose proof (sum_sublist_nonnegative__final_result
    groups inner_hi outer_hi Hnonneg ltac:(lia) ltac:(lia)).
  unfold ListLib.sum.
  lia.
Qed.
Lemma valid_bus_loading_cut_bounds__final_result :
  forall groups capacity cuts k,
    ValidBusLoading groups capacity cuts ->
    0 <= k < Zlength cuts ->
    0 <= Znth k cuts 0 <= Zlength groups.
Proof.
  intros groups capacity cuts k
    [Hlen [Hfirst [Hlast [Hmono Hsegments]]]] Hk.
  assert (Hlastidx : 0 <= Zlength cuts - 1 < Zlength cuts) by lia.
  split.
  - destruct (Z.eq_dec k 0) as [-> | Hne].
    + rewrite Hfirst. lia.
    + specialize (Hmono 0 k ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite Hfirst in Hmono. lia.
  - destruct (Z.eq_dec k (Zlength cuts - 1)) as [-> | Hne].
    + rewrite Hlast. lia.
    + specialize (Hmono k (Zlength cuts - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite Hlast in Hmono. lia.
Qed.
Lemma greedy_bus_loading_optimal_positive__final_result :
  forall groups capacity cuts,
    (forall k, 0 <= k < Zlength groups ->
       1 <= Znth k groups 0 <= capacity) ->
    GreedyBusLoading groups capacity cuts ->
    min_value_of_subset Z.le (ValidBusLoading groups capacity)
      (fun candidate => Zlength candidate - 1) (Zlength cuts - 1).
Proof.
  intros groups capacity cuts Hpositive Hgreedy.
  destruct Hgreedy as [Hvalid Hmaximal].
  destruct Hvalid as [Hclen [Hcfirst [Hclast [Hcmono Hccap]]]].
  assert (Hvalid_again : ValidBusLoading groups capacity cuts).
  { repeat split; assumption. }
  assert (Hnonneg : forall k, 0 <= k < Zlength groups ->
      0 <= Znth k groups 0).
  { intros k Hk. specialize (Hpositive k Hk). lia. }
  unfold min_value_of_subset, min_object_of_subset.
  exists cuts. split.
  - split.
    + exact Hvalid_again.
    + intros candidate Hcandidate.
      destruct Hcandidate as
        [Hdlen [Hdfirst [Hdlast [Hdmono Hdcap]]]].
      assert (Hcandidate_again : ValidBusLoading groups capacity candidate).
      { repeat split; assumption. }
      assert (Hdom : forall n : nat,
          Z.of_nat n < Zlength cuts ->
          Z.of_nat n < Zlength candidate ->
          Znth (Z.of_nat n) candidate 0 <= Znth (Z.of_nat n) cuts 0).
      { intro n. induction n as [| n IH].
        - intros Hng Hnd. simpl.
          rewrite Hdfirst, Hcfirst. lia.
        - rewrite Nat2Z.inj_succ.
          intros Hng Hnd.
          assert (Hprev_g : Z.of_nat n < Zlength cuts) by lia.
          assert (Hprev_d : Z.of_nat n < Zlength candidate) by lia.
          specialize (IH Hprev_g Hprev_d).
          destruct (Z.eq_dec (Z.of_nat n) (Zlength cuts - 2)) as [Hfinal | Hnotfinal].
          + assert (Hidx : Z.succ (Z.of_nat n) = Zlength cuts - 1) by lia.
            rewrite Hidx, Hclast.
            pose proof (valid_bus_loading_cut_bounds__final_result
              groups capacity candidate (Z.succ (Z.of_nat n))
              Hcandidate_again ltac:(lia)).
            rewrite Hidx in H. lia.
          + assert (Hmaxidx : 0 <= Z.of_nat n < Zlength cuts - 2) by lia.
            specialize (Hmaximal (Z.of_nat n) Hmaxidx).
            pose proof (valid_bus_loading_cut_bounds__final_result
              groups capacity cuts (Z.of_nat n)
              Hvalid_again ltac:(lia)) as Hgprev.
            pose proof (valid_bus_loading_cut_bounds__final_result
              groups capacity cuts (Z.succ (Z.of_nat n))
              Hvalid_again ltac:(lia)) as Hgnext.
            pose proof (valid_bus_loading_cut_bounds__final_result
              groups capacity candidate (Z.of_nat n)
              Hcandidate_again ltac:(lia)) as Hdprev.
            pose proof (valid_bus_loading_cut_bounds__final_result
              groups capacity candidate (Z.succ (Z.of_nat n))
              Hcandidate_again ltac:(lia)) as Hdnext.
            pose proof (Hcmono (Z.of_nat n) (Z.succ (Z.of_nat n))
              ltac:(lia) ltac:(lia) ltac:(lia)) as Hcgstep.
            specialize (Hdcap (Z.of_nat n) ltac:(lia)).
            destruct (Z_lt_ge_dec
              (Znth (Z.succ (Z.of_nat n)) cuts 0)
              (Znth (Z.succ (Z.of_nat n)) candidate 0)) as [Hlt | Hge].
            * pose proof (sum_sublist_inclusion__final_result
                groups
                (Znth (Z.of_nat n) candidate 0)
                (Znth (Z.of_nat n) cuts 0)
                (Znth (Z.succ (Z.of_nat n)) cuts 0 + 1)
                (Znth (Z.succ (Z.of_nat n)) candidate 0)
                Hnonneg ltac:(lia) ltac:(lia) ltac:(lia)) as Hinclusion.
              replace (Z.of_nat n + 1) with (Z.succ (Z.of_nat n)) in Hmaximal by lia.
              replace (Z.of_nat n + 1) with (Z.succ (Z.of_nat n)) in Hdcap by lia.
              lia.
            * lia. }
      destruct (Z_le_gt_dec (Zlength cuts) (Zlength candidate)) as [Hlength | Hshort].
      * lia.
      * assert (Hlast_d_nat :
          Z.of_nat (Z.to_nat (Zlength candidate - 1)) = Zlength candidate - 1).
        { rewrite Z2Nat.id by lia. reflexivity. }
        specialize (Hdom (Z.to_nat (Zlength candidate - 1))).
        rewrite Hlast_d_nat in Hdom.
        specialize (Hdom ltac:(lia) ltac:(lia)).
        rewrite Hdlast in Hdom.
        assert (Hgstrict :
          Znth (Zlength candidate - 1) cuts 0 <
          Znth (Zlength cuts - 1) cuts 0).
        { apply Hcmono; lia. }
        rewrite Hclast in Hgstrict. lia.
  - reflexivity.
Qed.
