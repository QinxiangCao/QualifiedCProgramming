Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(weights:list Z)->Z, with 1 = YES and 0 = NO. Output is positive exactly when
   a subset of whole apples has half the total weight. *)
Definition Pre (w : list Z) : Prop :=
  (* The solver Require states these constraints explicitly:
       1 <= Zlength w <= 100 /\
       Forall (fun x => x = 100 \/ x = 200) w. *)
  True.

Definition WeightValues (w : list Z) : Prop :=
  forall i, 0 <= i < Zlength w ->
    Znth i w 0 = 100 \/ Znth i w 0 = 200.

Lemma weight_values_of_explicit_require :
  forall (w : list Z) (n : Z),
    n = Zlength w ->
    (forall i, 0 <= i < n ->
      Znth i w 0 = 100 \/ Znth i w 0 = 200) ->
    WeightValues w.
Proof.
  unfold WeightValues.
  intros w n Hlen Hvalues i Hi.
  apply Hvalues.
  rewrite Hlen.
  exact Hi.
Qed.
Definition FairSplit (w : list Z) : Prop :=
  exists chosen : list Z,
    Zlength chosen = Zlength w /\ 
    Forall (fun b => b = 0 \/ b = 1) chosen /\
    2 * (fold_right Z.add 0) (map (fun q => fst q * snd q) (combine chosen w)) = (fold_right Z.add 0) w.
Definition Spec (w : list Z) (out : Z) : Prop :=
  (out = 1 /\ FairSplit w) \/ (out = 0 /\ ~FairSplit w).

Definition SolverReturnBridge (out ret : Z) : Prop :=
  (out = 1 /\ ret = 1) \/ (out = 0 /\ ret = 0).

(* The executable program measures weight in units of 100 grams.  These
   predicates describe the mathematical meaning of its running total and of
   the finite reachability table; they do not prescribe an implementation. *)
Definition UnitWeight (x : Z) : Z := x / 100.

Definition UnitSum (w : list Z) : Z :=
  fold_right Z.add 0 (map UnitWeight w).

Definition PrefixUnitTotal (w : list Z) (i total : Z) : Prop :=
  0 <= i <= Zlength w /\
  total = UnitSum (sublist 0 i w).

Definition UnitSelectableSum (w : list Z) (target : Z) : Prop :=
  exists chosen : list Z,
    Zlength chosen = Zlength w /\
    Forall (fun b => b = 0 \/ b = 1) chosen /\
    target =
      fold_right Z.add 0
        (map (fun q => fst q * UnitWeight (snd q)) (combine chosen w)).

Definition ReachTable
    (w : list Z) (i total : Z) (table : list Z) : Prop :=
  Zlength table = 205 /\
  (forall k, 0 <= k < 205 -> Znth k table 0 = 0 \/ Znth k table 0 = 1) /\
  forall k, 0 <= k <= total ->
    (Znth k table 0 <> 0 <->
     UnitSelectableSum (sublist 0 i w) k).

Definition ReachInnerProgress
    (w : list Z) (i s total : Z) (table : list Z) : Prop :=
  Zlength table = 205 /\
  (forall k, 0 <= k < 205 -> Znth k table 0 = 0 \/ Znth k table 0 = 1) /\
  (forall k, 0 <= k <= total -> s < k ->
    (Znth k table 0 <> 0 <->
     UnitSelectableSum (sublist 0 (i + 1) w) k)) /\
  forall k, 0 <= k <= total -> k <= s ->
    (Znth k table 0 <> 0 <->
     UnitSelectableSum (sublist 0 i w) k).

Require Import Coq.micromega.Lia.
Lemma weight_at_from_pre__prefix_scan :
  forall weights i,
    WeightValues weights ->
    0 <= i < Zlength weights ->
    Znth i weights 0 = 100 \/ Znth i weights 0 = 200.
Proof.
  intros weights i Hweights Hi.
  exact (Hweights i Hi).
Qed.
Lemma unit_weight_at_from_pre__prefix_scan :
  forall weights i,
    WeightValues weights ->
    0 <= i < Zlength weights ->
    UnitWeight (Znth i weights 0) = 1 \/
    UnitWeight (Znth i weights 0) = 2.
Proof.
  intros weights i Hpre Hi.
  pose proof (weight_at_from_pre__prefix_scan weights i Hpre Hi) as Hweight.
  destruct Hweight as [Hweight | Hweight]; rewrite Hweight;
    unfold UnitWeight; compute; auto.
Qed.
Lemma prefix_unit_total_step__prefix_scan :
  forall weights i total,
    0 <= i < Zlength weights ->
    PrefixUnitTotal weights i total ->
    PrefixUnitTotal weights (i + 1)
      (total + UnitWeight (Znth i weights 0)).
Proof.
  intros weights i total Hi [Hi_prefix Htotal].
  unfold PrefixUnitTotal, UnitSum in *.
  split.
  - lia.
  - rewrite Htotal.
    rewrite (sublist_split 0 (i + 1) i weights) by lia.
    rewrite (sublist_single 0 i weights) by lia.
    rewrite map_app, fold_right_app.
    replace (fold_right Z.add 0 (map UnitWeight [Znth i weights 0]))
      with (UnitWeight (Znth i weights 0)) by (simpl; lia).
    assert (Hfold : forall (l : list Z) z,
      fold_right Z.add z l = fold_right Z.add 0 l + z).
    {
      induction l as [| x l IH]; intros z; simpl.
      - lia.
      - rewrite IH. lia.
    }
    rewrite (Hfold (map UnitWeight (sublist 0 i weights))
      (UnitWeight (Znth i weights 0))).
    lia.
Qed.
Lemma reach_table_to_inner_at_total__reach_initialization :
  forall (w : list Z) (i total : Z) (table : list Z),
    ReachTable w i total table ->
    ReachInnerProgress w i total total table.
Proof.
  intros w i total table [Hlen [Hbits Hold]].
  unfold ReachInnerProgress.
  split; [exact Hlen |].
  split; [exact Hbits |].
  split.
  - intros k Hrange Hgt. lia.
  - intros k Hrange _. apply Hold. exact Hrange.
Qed.
Lemma pre_unit_weight_bounds__reach_initialization :
  forall (w : list Z) (i : Z),
    WeightValues w ->
    0 <= i < Zlength w ->
    1 <= UnitWeight (Znth i w 0) <= 2.
Proof.
  intros w i Hweights Hi.
  pose proof (Hweights i Hi) as Hweight.
  unfold UnitWeight.
  destruct Hweight as [Hweight | Hweight].
  - rewrite Hweight. change (1 <= 1 <= 2). lia.
  - rewrite Hweight. change (1 <= 2 <= 2). lia.
Qed.
Lemma pre_weight_classification__reach_initialization :
  forall (w : list Z) (i : Z),
    WeightValues w ->
    0 <= i < Zlength w ->
    Znth i w 0 = 100 \/ Znth i w 0 = 200.
Proof.
  intros w i Hweights Hi.
  exact (Hweights i Hi).
Qed.
Lemma pre_unit_sum_lower_bound__reach_initialization :
  forall (w : list Z),
    WeightValues w ->
    Zlength w <= UnitSum w.
Proof.
  intros w Hweights.
  assert (Hall : Forall (fun x => x = 100 \/ x = 200) w).
  { apply (proj2 (Forall_Znth (fun x => x = 100 \/ x = 200) 0 w)).
    exact Hweights. }
  clear Hweights.
  unfold UnitSum.
  induction Hall as [| x xs Hx Hall IH].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons. simpl.
    unfold UnitWeight in IH |- *.
    destruct Hx as [Hx | Hx].
    + rewrite Hx. change (Zlength xs + 1 <= 1 + fold_right Z.add 0 (map (fun x => x / 100) xs)). lia.
    + rewrite Hx. change (Zlength xs + 1 <= 2 + fold_right Z.add 0 (map (fun x => x / 100) xs)). lia.
Qed.
Lemma combine_app_same_length__inner_dp_transitions :
  forall {A B : Type} (l1 l2 : list A) (r1 r2 : list B),
    length l1 = length r1 ->
    combine (l1 ++ l2) (r1 ++ r2) =
    combine l1 r1 ++ combine l2 r2.
Proof.
  intros A B l1.
  induction l1 as [|a l1 IH]; intros l2 r1 r2 Hlen.
  - destruct r1; simpl in Hlen; [reflexivity | discriminate].
  - destruct r1 as [|b r1]; simpl in Hlen; [discriminate |].
    simpl.
    f_equal.
    apply IH.
    lia.
Qed.
Lemma fold_right_Z_add_acc__inner_dp_transitions :
  forall (l : list Z) (acc : Z),
    fold_right Z.add acc l = fold_right Z.add 0 l + acc.
Proof.
  induction l as [|a l IH]; intros acc; simpl.
  - lia.
  - rewrite IH.
    lia.
Qed.
Lemma fold_right_Z_add_singleton__inner_dp_transitions :
  forall z : Z, fold_right Z.add 0 [z] = z.
Proof.
  intros z.
  change (z + 0 = z).
  apply Z.add_0_r.
Qed.
Lemma unit_selectable_sum_app_singleton__inner_dp_transitions :
  forall (w : list Z) (x k : Z),
    UnitSelectableSum (w ++ [x]) k <->
    UnitSelectableSum w k \/
    UnitSelectableSum w (k - UnitWeight x).
Proof.
  intros w x k.
  unfold UnitSelectableSum.
  split.
  - intros [chosen [Hlen [Hbits Hsum]]].
    induction chosen as [|b prefix _] using rev_ind.
    + rewrite !Zlength_correct, !length_app in Hlen.
      simpl in Hlen.
      lia.
    + rewrite !Zlength_correct, !length_app in Hlen.
      simpl in Hlen.
      assert (Hprefix_len : length prefix = length w).
      { lia. }
      rewrite Forall_app in Hbits.
      destruct Hbits as [Hprefix_bits Hlast_bits].
      assert (Hb : b = 0 \/ b = 1).
      { inversion Hlast_bits. assumption. }
      rewrite (combine_app_same_length__inner_dp_transitions
                 prefix [b] w [x] Hprefix_len) in Hsum.
      rewrite map_app, fold_right_app in Hsum.
      rewrite fold_right_Z_add_acc__inner_dp_transitions in Hsum.
      simpl in Hsum.
      destruct Hb as [Hb0 | Hb1].
      * left.
        rewrite Hb0 in Hsum.
        exists prefix.
        split.
        { now rewrite !Zlength_correct, Hprefix_len. }
        split.
        { exact Hprefix_bits. }
        lia.
      * right.
        rewrite Hb1 in Hsum.
        exists prefix.
        split.
        { now rewrite !Zlength_correct, Hprefix_len. }
        split.
        { exact Hprefix_bits. }
        lia.
  - intros [[chosen [Hlen [Hbits Hsum]]] |
             [chosen [Hlen [Hbits Hsum]]]].
    + exists (chosen ++ [0]).
      assert (Hnatlen : length chosen = length w).
      { rewrite !Zlength_correct in Hlen. lia. }
      split.
      { rewrite !Zlength_correct, !length_app. simpl. lia. }
      split.
      { rewrite Forall_app. simpl. auto. }
      rewrite (combine_app_same_length__inner_dp_transitions
                 chosen [0] w [x] Hnatlen).
      rewrite map_app.
      cbn [map combine fst snd].
      rewrite fold_right_app.
      rewrite fold_right_Z_add_acc__inner_dp_transitions.
      rewrite Z.mul_0_l, Z.add_0_r.
      exact Hsum.
    + exists (chosen ++ [1]).
      assert (Hnatlen : length chosen = length w).
      { rewrite !Zlength_correct in Hlen. lia. }
      split.
      { rewrite !Zlength_correct, !length_app. simpl. lia. }
      split.
      { rewrite Forall_app. simpl. auto. }
      rewrite (combine_app_same_length__inner_dp_transitions
                 chosen [1] w [x] Hnatlen).
      rewrite map_app.
      cbn [map combine fst snd].
      rewrite fold_right_app.
      rewrite fold_right_Z_add_acc__inner_dp_transitions.
      rewrite Z.mul_1_l.
      rewrite fold_right_Z_add_singleton__inner_dp_transitions.
      rewrite <- Hsum.
      symmetry.
      apply Z.sub_add.
Qed.
Lemma unit_selectable_sum_snoc_cases__inner_dp_transitions :
  forall (weights : list Z) (i u k : Z),
    0 <= i < Zlength weights ->
    u = UnitWeight (Znth i weights 0) ->
    (UnitSelectableSum (sublist 0 (i + 1) weights) k <->
     UnitSelectableSum (sublist 0 i weights) k \/
     UnitSelectableSum (sublist 0 i weights) (k - u)).
Proof.
  intros weights i u k Hi Hu.
  rewrite (sublist_split 0 (i + 1) i weights) by lia.
  rewrite (@sublist_single Z 0 i weights) by lia.
  rewrite unit_selectable_sum_app_singleton__inner_dp_transitions.
  subst u.
  reflexivity.
Qed.
Lemma Forall_firstn__inner_dp_transitions :
  forall {A : Type} (P : A -> Prop) (n : nat) (l : list A),
    Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n.
  induction n as [|n IH]; intros l Hl.
  - simpl. constructor.
  - destruct l as [|a l].
    + simpl. constructor.
    + inversion Hl; subst.
      simpl.
      constructor; auto.
Qed.
Lemma Forall_skipn__inner_dp_transitions :
  forall {A : Type} (P : A -> Prop) (n : nat) (l : list A),
    Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n.
  induction n as [|n IH]; intros l Hl.
  - simpl. exact Hl.
  - destruct l as [|a l].
    + simpl. constructor.
    + inversion Hl; subst.
      simpl.
      apply IH.
      assumption.
Qed.
Lemma Forall_sublist__inner_dp_transitions :
  forall {A : Type} (P : A -> Prop) (lo hi : Z) (l : list A),
    Forall P l -> Forall P (sublist lo hi l).
Proof.
  intros A P lo hi l Hl.
  unfold sublist.
  apply Forall_skipn__inner_dp_transitions.
  apply Forall_firstn__inner_dp_transitions.
  exact Hl.
Qed.
Lemma unit_selectable_sum_nonnegative__inner_dp_transitions :
  forall (w : list Z) (k : Z),
    Forall (fun x => x = 100 \/ x = 200) w ->
    UnitSelectableSum w k ->
    0 <= k.
Proof.
  intros w k Hw [chosen [Hlen [Hbits Hsum]]].
  revert w k Hw Hlen Hsum.
  induction chosen as [|b chosen IH]; intros w k Hw Hlen Hsum.
  - destruct w as [|x w].
    + simpl in Hsum. lia.
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct w as [|x w].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + inversion Hbits as [|b' chosen' Hb Hbits'];
        subst b' chosen'.
      inversion Hw as [|x' w' Hx Hw']; subst x' w'.
      rewrite !Zlength_correct in Hlen.
      simpl in Hlen, Hsum.
      assert (Htail :
        0 <= fold_right Z.add 0
          (map (fun q : Z * Z => fst q * UnitWeight (snd q))
               (combine chosen w))).
      { apply (IH Hbits' w _ Hw').
        - rewrite !Zlength_correct. lia.
        - reflexivity. }
      assert (Hunit : 0 <= UnitWeight x).
      { unfold UnitWeight.
        apply Z_div_nonneg_nonneg; [destruct Hx; lia | lia]. }
      destruct Hb as [Hb0 | Hb1].
      * rewrite Hb0, Z.mul_0_l in Hsum. lia.
      * rewrite Hb1, Z.mul_1_l in Hsum. lia.
Qed.
Lemma Zlength_replace_Znth__inner_dp_transitions :
  forall {A : Type} (l : list A) (i : Z) (v : A),
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros A l i v.
  unfold replace_Znth.
  rewrite !Zlength_correct.
  generalize (Z.to_nat i) as n.
  induction l as [|a l IH]; intros n; simpl.
  - reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + specialize (IH n).
      apply Nat2Z.inj in IH.
      now rewrite IH.
Qed.
Lemma valid_Znth__inner_dp_transitions :
  forall weights i,
    WeightValues weights ->
    0 <= i < Zlength weights ->
    Znth i weights 0 = 100 \/ Znth i weights 0 = 200.
Proof.
  intros weights i Hvalid Hi.
  exact (Hvalid i Hi).
Qed.
Lemma unit_weight_quot__inner_dp_transitions :
  forall x,
    x = 100 \/ x = 200 ->
    Z.quot x 100 = UnitWeight x.
Proof.
  intros x [-> | ->]; reflexivity.
Qed.
Lemma reach_inner_finish__inner_dp_transitions :
  forall weights i s u total table,
    WeightValues weights ->
    0 <= i < Zlength weights ->
    u = Z.quot (Znth i weights 0) 100 ->
    1 <= u ->
    s < u ->
    u - 1 <= s ->
    ReachInnerProgress weights i s total table ->
    ReachTable weights (i + 1) total table.
Proof.
  intros weights i s u total table Hpre Hi Hu Hu_pos Hsu Hus Hreach.
  assert (Hs : s = u - 1) by lia.
  pose proof (valid_Znth__inner_dp_transitions weights i Hpre Hi) as Hitem.
  assert (Hu_unit : u = UnitWeight (Znth i weights 0)).
  { rewrite <- (unit_weight_quot__inner_dp_transitions
                  (Znth i weights 0) Hitem).
    exact Hu. }
  assert (Hweights : Forall (fun x => x = 100 \/ x = 200) weights).
  { apply (proj2 (Forall_Znth (fun x => x = 100 \/ x = 200) 0 weights)).
    exact Hpre. }
  destruct Hreach as [Hlen [Hbits [Hnew Hold]]].
  unfold ReachTable.
  split; [exact Hlen |].
  split; [exact Hbits |].
  intros k Hk.
  destruct (Z_lt_le_dec s k) as [Hsk | Hks].
  - apply Hnew; lia.
  - assert (Hnot_take :
        ~ UnitSelectableSum (sublist 0 i weights) (k - u)).
    { intro Htake.
      pose proof (unit_selectable_sum_nonnegative__inner_dp_transitions
                    (sublist 0 i weights) (k - u)
                    (Forall_sublist__inner_dp_transitions
                       (fun x => x = 100 \/ x = 200) 0 i weights Hweights)
                    Htake) as Hnonneg.
      lia. }
    rewrite (unit_selectable_sum_snoc_cases__inner_dp_transitions
               weights i u k Hi Hu_unit).
    specialize (Hold k Hk Hks).
    tauto.
Qed.
Lemma reach_inner_mark_step__inner_dp_transitions :
  forall weights i s u total table,
    WeightValues weights ->
    0 <= i < Zlength weights ->
    u = Z.quot (Znth i weights 0) 100 ->
    1 <= u ->
    s >= u ->
    s <= total ->
    total <= 200 ->
    ReachInnerProgress weights i s total table ->
    Znth (s - u) table 0 <> 0 ->
    ReachInnerProgress weights i (s - 1) total
      (replace_Znth s 1 table).
Proof.
  intros weights i s u total table Hpre Hi Hu Hu_pos Hsu Hst Htotal
         Hreach Hpred.
  pose proof (valid_Znth__inner_dp_transitions weights i Hpre Hi) as Hitem.
  assert (Hu_unit : u = UnitWeight (Znth i weights 0)).
  { rewrite <- (unit_weight_quot__inner_dp_transitions
                  (Znth i weights 0) Hitem).
    exact Hu. }
  destruct Hreach as [Hlen [Hbits [Hnew Hold]]].
  unfold ReachInnerProgress.
  split.
  - rewrite Zlength_replace_Znth__inner_dp_transitions.
    exact Hlen.
  - split.
    + intros k Hk.
      destruct (Z.eq_dec k s) as [-> | Hne].
      * right.
        rewrite Znth_replace_Znth_Same by (try rewrite Hlen; lia).
        reflexivity.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
        apply Hbits.
        exact Hk.
    + split.
      * intros k Hk Hboundary.
        destruct (Z.eq_dec k s) as [-> | Hne].
        -- rewrite Znth_replace_Znth_Same by (try rewrite Hlen; lia).
           rewrite (unit_selectable_sum_snoc_cases__inner_dp_transitions
                      weights i u s Hi Hu_unit).
           split.
           { intros Hnz.
             right.
             apply (proj1 (Hold (s - u) ltac:(lia) ltac:(lia))).
             exact Hpred. }
           { intros Hselect. lia. }
        -- rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
           apply Hnew; lia.
      * intros k Hk Hboundary.
        rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
        apply Hold; lia.
Qed.
Lemma reach_inner_skip_step__inner_dp_transitions :
  forall weights i s u total table,
    WeightValues weights ->
    0 <= i < Zlength weights ->
    u = Z.quot (Znth i weights 0) 100 ->
    1 <= u ->
    s >= u ->
    ReachInnerProgress weights i s total table ->
    Znth (s - u) table 0 = 0 ->
    ReachInnerProgress weights i (s - 1) total table.
Proof.
  intros weights i s u total table Hpre Hi Hu Hu_pos Hsu Hreach Hpred.
  pose proof (valid_Znth__inner_dp_transitions weights i Hpre Hi) as Hitem.
  assert (Hu_unit : u = UnitWeight (Znth i weights 0)).
  { rewrite <- (unit_weight_quot__inner_dp_transitions
                  (Znth i weights 0) Hitem).
    exact Hu. }
  destruct Hreach as [Hlen [Hbits [Hnew Hold]]].
  unfold ReachInnerProgress.
  split; [exact Hlen |].
  split; [exact Hbits |].
  split.
  - intros k Hk Hboundary.
    destruct (Z.eq_dec k s) as [-> | Hne].
    + rewrite (unit_selectable_sum_snoc_cases__inner_dp_transitions
                 weights i u s Hi Hu_unit).
      assert (Hpred_old :
          ~ UnitSelectableSum (sublist 0 i weights) (s - u)).
      { intro Hselect.
        pose proof (proj2 (Hold (s - u) ltac:(lia) ltac:(lia))
                          Hselect) as Hnz.
        apply Hnz.
        exact Hpred. }
      specialize (Hold s ltac:(lia) ltac:(lia)).
      tauto.
    + apply Hnew; lia.
  - intros k Hk Hboundary.
    apply Hold; lia.
Qed.
Lemma weight_sum_unit_scale__final_result :
  forall w,
    Forall (fun x => x = 100 \/ x = 200) w ->
    fold_right Z.add 0 w = 100 * UnitSum w.
Proof.
  intros w Hweights. unfold UnitSum.
  induction Hweights as [|x xs Hx Hxs IH].
  - reflexivity.
  - simpl. destruct Hx as [-> | ->].
    + change (UnitWeight 100) with 1. rewrite IH.
      change
        (100 + 100 * fold_right Z.add 0 (map UnitWeight xs) =
         100 * (1 + fold_right Z.add 0 (map UnitWeight xs))).
      ring.
    + change (UnitWeight 200) with 2. rewrite IH.
      change
        (200 + 100 * fold_right Z.add 0 (map UnitWeight xs) =
         100 * (2 + fold_right Z.add 0 (map UnitWeight xs))).
      ring.
Qed.
Lemma selected_sum_unit_scale__final_result :
  forall w chosen,
    Forall (fun x => x = 100 \/ x = 200) w ->
    Zlength chosen = Zlength w ->
    fold_right Z.add 0
      (map (fun q => fst q * snd q) (combine chosen w)) =
    100 * fold_right Z.add 0
      (map (fun q => fst q * UnitWeight (snd q)) (combine chosen w)).
Proof.
  intros w chosen Hweights. revert chosen.
  induction Hweights as [|x xs Hx Hxs IH]; intros chosen Hlen.
  - destruct chosen as [|b bs].
    + reflexivity.
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct chosen as [|b bs].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + assert (Hlen_tail : Zlength bs = Zlength xs).
      { rewrite !Zlength_correct in *. simpl in Hlen. lia. }
      specialize (IH bs Hlen_tail).
      simpl. destruct Hx as [-> | ->].
      * change (UnitWeight 100) with 1. rewrite IH.
        change
          (b * 100 + 100 * fold_right Z.add 0
             (map (fun q => fst q * UnitWeight (snd q)) (combine bs xs)) =
           100 * (b * 1 + fold_right Z.add 0
             (map (fun q => fst q * UnitWeight (snd q)) (combine bs xs)))).
        ring.
      * change (UnitWeight 200) with 2. rewrite IH.
        change
          (b * 200 + 100 * fold_right Z.add 0
             (map (fun q => fst q * UnitWeight (snd q)) (combine bs xs)) =
           100 * (b * 2 + fold_right Z.add 0
             (map (fun q => fst q * UnitWeight (snd q)) (combine bs xs)))).
        ring.
Qed.
Lemma fair_split_unit_balance__final_result :
  forall w chosen,
    WeightValues w ->
    Zlength chosen = Zlength w ->
    Forall (fun b => b = 0 \/ b = 1) chosen ->
    (2 * fold_right Z.add 0
           (map (fun q => fst q * snd q) (combine chosen w)) =
       fold_right Z.add 0 w <->
     2 * fold_right Z.add 0
           (map (fun q => fst q * UnitWeight (snd q))
                (combine chosen w)) =
       UnitSum w).
Proof.
  intros w chosen Hvalid Hlen _.
  assert (Hweights : Forall (fun x => x = 100 \/ x = 200) w).
  { apply (proj2 (Forall_Znth (fun x => x = 100 \/ x = 200) 0 w)).
    exact Hvalid. }
  rewrite (selected_sum_unit_scale__final_result w chosen Hweights Hlen).
  rewrite (weight_sum_unit_scale__final_result w Hweights).
  nia.
Qed.
Lemma fair_split_iff_half_selectable__final_result :
  forall w total,
    WeightValues w ->
    total = UnitSum w ->
    total mod 2 = 0 ->
    (FairSplit w <-> UnitSelectableSum w (total / 2)).
Proof.
  intros w total Hpre Htotal Heven.
  pose proof (Z.div_mod total 2 ltac:(lia)) as Hdiv.
  split.
  - intros [chosen [Hlen [Hbits Hgrams]]].
    exists chosen. repeat split; try assumption.
    pose proof
      (proj1
         (fair_split_unit_balance__final_result
            w chosen Hpre Hlen Hbits) Hgrams) as Hunits.
    lia.
  - intros [chosen [Hlen [Hbits Hunits]]].
    exists chosen. repeat split; try assumption.
    apply
      (proj2
         (fair_split_unit_balance__final_result
            w chosen Hpre Hlen Hbits)).
    lia.
Qed.
Lemma solver_return_bridge_of_bit__final_result :
  forall x, x = 0 \/ x = 1 -> SolverReturnBridge x x.
Proof.
  intros x [-> | ->]; unfold SolverReturnBridge; intuition (auto with *).
Qed.
