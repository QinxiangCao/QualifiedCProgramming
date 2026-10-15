Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Import ListNotations. Local Open Scope Z_scope.
Definition OneAdjacentMatchMove (before after : list Z) : Prop := exists i,
  0 <= i < Zlength before-1 /\
  ((Znth i before 0>0 /\ after = replace_Znth (i + 1) (Znth (i + 1) before 0 + 1) (replace_Znth i (Znth i before 0 - 1) before)) \/
   (Znth (i + 1) before 0 > 0 /\ after = replace_Znth i (Znth i before 0 + 1) (replace_Znth (i + 1) (Znth (i + 1) before 0 - 1) before))).
Definition BalanceTrace (a : list Z) (moves : Z) : Prop := exists states,
  Zlength states = moves + 1 /\ Znth 0 states nil = a /\
  (forall i, 0 <= i < moves -> OneAdjacentMatchMove (Znth i states nil) (Znth (i+1) states nil)) /\
  exists target, Forall (fun x => x = target) (Znth moves states nil).
Definition Pre (a : list Z) : Prop := 1 <= Zlength a <= 50000 /\ Forall (fun x => 0 <= x <= 1000000000) a /\ (Zlength a | fold_right Z.add 0 a).
Definition Spec (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (BalanceTrace a) (fun moves => moves) out.

Definition PrefixImbalance (a : list Z) (upto : Z) : Z :=
  ListLib.sum (sublist 0 upto a) -
  upto * (ListLib.sum a / Zlength a).

Definition PrefixTransportCost (a : list Z) (edges : Z) : Z :=
  sum (fun k : Z => 0 <= k < edges)
      (fun k => Z.abs (PrefixImbalance a (k + 1))).

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Lemma sum_sublist_succ__prefix_accounting :
  forall (xs : list Z) i,
    0 <= i < Zlength xs ->
    ListLib.sum (sublist 0 (i + 1) xs) =
      ListLib.sum (sublist 0 i xs) + Znth i xs 0.
Proof.
  intros xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single 0 i xs) by lia.
  rewrite ListLib.sum_app.
  simpl.
  lia.
Qed.
Lemma sum_sublist_full__prefix_accounting :
  forall (xs : list Z),
    sublist 0 (Zlength xs) xs = xs /\
    ListLib.sum (sublist 0 (Zlength xs) xs) = ListLib.sum xs.
Proof.
  intros xs.
  split; rewrite sublist_self by reflexivity; reflexivity.
Qed.
Lemma prefix_initial_values__prefix_accounting :
  forall (xs : list Z),
    PrefixImbalance xs 0 = 0 /\ PrefixTransportCost xs 0 = 0.
Proof.
  intros xs.
  split.
  - unfold PrefixImbalance.
    reflexivity.
  - unfold PrefixTransportCost.
    apply sum_Z_range_empty.
    lia.
Qed.
Lemma prefix_imbalance_succ__transport_step : forall (xs : list Z) i,
  0 <= i < Zlength xs ->
  PrefixImbalance xs (i + 1) =
  PrefixImbalance xs i + Znth i xs 0 -
    (ListLib.sum xs / Zlength xs).
Proof.
  intros xs i Hi.
  unfold PrefixImbalance.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (@sublist_single Z 0 i xs) by lia.
  rewrite ListLib.sum_app.
  simpl.
  ring.
Qed.
Lemma prefix_transport_cost_succ__transport_step : forall (xs : list Z) i,
  0 <= i ->
  PrefixTransportCost xs (i + 1) =
  PrefixTransportCost xs i + Z.abs (PrefixImbalance xs (i + 1)).
Proof.
  intros xs i Hi.
  unfold PrefixTransportCost.
  rewrite (SumLib.ZRange.sum_Z_range_extend_right 0 i) by lia.
  reflexivity.
Qed.
Lemma prefix_step_magnitude_bound__transport_step :
  forall balance x target i,
    -1000000000 * i <= balance <= 1000000000 * i ->
    0 <= x <= 1000000000 ->
    0 <= target <= 1000000000 ->
    -1000000000 * (i + 1) <= balance + (x - target) /\
    balance + (x - target) <= 1000000000 * (i + 1).
Proof.
  intros balance x target i Hbalance Hx Htarget.
  lia.
Qed.
Lemma Zlength_replace_Znth__final_optimality : forall {A : Type}
    (xs : list A) i (v : A),
  Zlength (replace_Znth i v xs) = Zlength xs.
Proof.
  intros A xs i v. revert i.
  induction xs as [|x xs IH]; simpl; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat i) as [|n].
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IH (Z.of_nat n)).
    replace (Z.to_nat (Z.of_nat n)) with n in IH by lia.
    rewrite IH. lia.
Qed.
Lemma pre_balanced_state__final_optimality : forall a,
  Pre a ->
  1 <= Zlength a /\
  Forall (fun x => 0 <= x) a /\
  (Zlength a | ListLib.sum a).
Proof.
  intros a [Hlen [Hnonneg Hdiv]].
  split; [lia|]. split.
  - rewrite Forall_forall in *. intros x Hin.
    specialize (Hnonneg x Hin). lia.
  - exact Hdiv.
Qed.
Lemma sum_replace_Znth__final_optimality : forall xs i v,
  0 <= i < Zlength xs ->
  ListLib.sum (replace_Znth i v xs) =
  ListLib.sum xs - Znth i xs 0 + v.
Proof.
  induction xs as [|x xs IH]; intros i v Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + unfold replace_Znth, Znth, ListLib.sum. simpl. ring.
    + assert (0 < i) by lia.
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons by lia.
      unfold ListLib.sum in *. simpl.
      rewrite IH by lia.
      ring.
Qed.
Lemma sum_prefix_replace_outside__final_optimality : forall xs i v upto,
  0 <= upto <= Zlength xs ->
  0 <= i < Zlength xs ->
  upto <= i ->
  ListLib.sum (sublist 0 upto (replace_Znth i v xs)) =
  ListLib.sum (sublist 0 upto xs).
Proof.
  intros xs i v upto Hup Hi Hout.
  assert (Hlen : Zlength (replace_Znth i v xs) = Zlength xs)
    by apply Zlength_replace_Znth__final_optimality.
  rewrite !list_sum_sublist_as_Z_range_sum by
      lia.
  apply sum_Z_range_ext. intros k Hk.
  rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth__final_optimality; lia).
  reflexivity.
Qed.
Lemma sum_prefix_replace_inside__final_optimality : forall xs i v upto,
  0 <= i < upto /\ upto <= Zlength xs ->
  ListLib.sum (sublist 0 upto (replace_Znth i v xs)) =
  ListLib.sum (sublist 0 upto xs) - Znth i xs 0 + v.
Proof.
  intros xs i v upto [Hi Hup].
  assert (Hlen : Zlength (replace_Znth i v xs) = Zlength xs)
    by apply Zlength_replace_Znth__final_optimality.
  rewrite !list_sum_sublist_as_Z_range_sum by
      lia.
  rewrite (sum_Z_range_split 0 i upto
    (fun k => Znth k (replace_Znth i v xs) 0)) by lia.
  rewrite (sum_Z_range_split 0 i upto
    (fun k => Znth k xs 0)) by lia.
  rewrite (sum_Z_range_cons i upto
    (fun k => Znth k (replace_Znth i v xs) 0)) by lia.
  rewrite (sum_Z_range_cons i upto (fun k => Znth k xs 0)) by lia.
  rewrite Znth_replace_Znth_Same by lia.
  assert (Hleft :
    SumLib.Sum.sum (fun x : Z => 0 <= x < i)
      (fun k => Znth k (replace_Znth i v xs) 0) =
    SumLib.Sum.sum (fun x : Z => 0 <= x < i)
      (fun k => Znth k xs 0)).
  { apply sum_Z_range_ext. intros k Hk.
    rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  assert (Hright :
    SumLib.Sum.sum (fun x : Z => i + 1 <= x < upto)
      (fun k => Znth k (replace_Znth i v xs) 0) =
    SumLib.Sum.sum (fun x : Z => i + 1 <= x < upto)
      (fun k => Znth k xs 0)).
  { apply sum_Z_range_ext. intros k Hk.
    rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  rewrite Hleft, Hright. ring.
Qed.
Lemma prefix_imbalance_succ__final_optimality : forall xs k,
  0 <= k < Zlength xs ->
  PrefixImbalance xs (k + 1) =
  PrefixImbalance xs k + Znth k xs 0 -
    (ListLib.sum xs / Zlength xs).
Proof.
  intros xs k Hk.
  unfold PrefixImbalance.
  rewrite !list_sum_sublist_as_Z_range_sum by lia.
  rewrite sum_Z_range_extend_right by lia.
  ring.
Qed.
Lemma prefix_imbalance_zero__final_optimality : forall xs,
  PrefixImbalance xs 0 = 0.
Proof.
  intros xs. unfold PrefixImbalance, sublist, ListLib.sum. simpl.
  reflexivity.
Qed.
Lemma prefix_imbalance_full__final_optimality : forall xs,
  1 <= Zlength xs ->
  (Zlength xs | ListLib.sum xs) ->
  PrefixImbalance xs (Zlength xs) = 0.
Proof.
  intros xs Hlen Hdiv.
  unfold PrefixImbalance.
  rewrite sublist_self by reflexivity.
  destruct Hdiv as [q Hq].
  assert (Hquot : q * Zlength xs / Zlength xs = q).
  { apply Z.div_mul. lia. }
  rewrite Hq, Hquot. ring.
Qed.
Lemma adjacent_move_preserves_length_sum__final_optimality : forall before after,
  OneAdjacentMatchMove before after ->
  Zlength after = Zlength before /\ ListLib.sum after = ListLib.sum before.
Proof.
  intros before after [i [Hi [[Hpos ->]|[Hpos ->]]]].
  - split.
    + repeat rewrite Zlength_replace_Znth__final_optimality. reflexivity.
    + rewrite sum_replace_Znth__final_optimality by
          (rewrite Zlength_replace_Znth__final_optimality; lia).
      rewrite Znth_replace_Znth_Diff by
          (repeat rewrite Zlength_replace_Znth__final_optimality; lia).
      rewrite sum_replace_Znth__final_optimality by lia.
      ring.
  - split.
    + repeat rewrite Zlength_replace_Znth__final_optimality. reflexivity.
    + rewrite sum_replace_Znth__final_optimality by
          (rewrite Zlength_replace_Znth__final_optimality; lia).
      rewrite Znth_replace_Znth_Diff by
          (repeat rewrite Zlength_replace_Znth__final_optimality; lia).
      rewrite sum_replace_Znth__final_optimality by lia.
      ring.
Qed.
Lemma move_right_prefix_effect__final_optimality : forall xs i upto,
  0 <= i < Zlength xs - 1 ->
  0 <= upto <= Zlength xs ->
  let ys := replace_Znth (i + 1) (Znth (i + 1) xs 0 + 1)
              (replace_Znth i (Znth i xs 0 - 1) xs) in
  PrefixImbalance ys upto = PrefixImbalance xs upto -
    (if Z.eq_dec upto (i + 1) then 1 else 0).
Proof.
  intros xs i upto Hi Hup ys. subst ys.
  set (mid := replace_Znth i (Znth i xs 0 - 1) xs).
  assert (Hmidlen : Zlength mid = Zlength xs).
  { unfold mid. apply Zlength_replace_Znth__final_optimality. }
  assert (Hlen : Zlength
      (replace_Znth (i + 1) (Znth (i + 1) xs 0 + 1) mid) =
      Zlength xs).
  { rewrite Zlength_replace_Znth__final_optimality, Hmidlen. reflexivity. }
  assert (Hmidnth : Znth (i + 1) mid 0 = Znth (i + 1) xs 0).
  { unfold mid. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  assert (Hsum : ListLib.sum
      (replace_Znth (i + 1) (Znth (i + 1) xs 0 + 1) mid) =
      ListLib.sum xs).
  { rewrite sum_replace_Znth__final_optimality by (rewrite Hmidlen; lia).
    rewrite Hmidnth.
    unfold mid. rewrite sum_replace_Znth__final_optimality by lia. ring. }
  unfold PrefixImbalance.
  rewrite Hlen, Hsum.
  destruct (Z.eq_dec upto (i + 1)) as [->|Hneq].
  - rewrite sum_prefix_replace_outside__final_optimality by
        (try rewrite Hmidlen; lia).
    unfold mid.
    rewrite sum_prefix_replace_inside__final_optimality by lia.
    ring.
  - destruct (Z_le_gt_dec upto i).
    + rewrite sum_prefix_replace_outside__final_optimality by
          (try rewrite Hmidlen; lia).
      unfold mid.
      rewrite sum_prefix_replace_outside__final_optimality by lia.
      ring.
    + assert (i + 1 < upto) by lia.
      rewrite sum_prefix_replace_inside__final_optimality by
          (rewrite Hmidlen; lia).
      rewrite Hmidnth.
      unfold mid.
      rewrite sum_prefix_replace_inside__final_optimality by lia.
      ring.
Qed.
Lemma move_left_prefix_effect__final_optimality : forall xs i upto,
  0 <= i < Zlength xs - 1 ->
  0 <= upto <= Zlength xs ->
  let ys := replace_Znth i (Znth i xs 0 + 1)
              (replace_Znth (i + 1) (Znth (i + 1) xs 0 - 1) xs) in
  PrefixImbalance ys upto = PrefixImbalance xs upto +
    (if Z.eq_dec upto (i + 1) then 1 else 0).
Proof.
  intros xs i upto Hi Hup ys. subst ys.
  set (mid := replace_Znth (i + 1) (Znth (i + 1) xs 0 - 1) xs).
  assert (Hmidlen : Zlength mid = Zlength xs).
  { unfold mid. apply Zlength_replace_Znth__final_optimality. }
  assert (Hlen : Zlength (replace_Znth i (Znth i xs 0 + 1) mid) =
      Zlength xs).
  { rewrite Zlength_replace_Znth__final_optimality, Hmidlen. reflexivity. }
  assert (Hmidnth : Znth i mid 0 = Znth i xs 0).
  { unfold mid. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  assert (Hsum : ListLib.sum (replace_Znth i (Znth i xs 0 + 1) mid) =
      ListLib.sum xs).
  { rewrite sum_replace_Znth__final_optimality by (rewrite Hmidlen; lia).
    rewrite Hmidnth.
    unfold mid. rewrite sum_replace_Znth__final_optimality by lia. ring. }
  unfold PrefixImbalance.
  rewrite Hlen, Hsum.
  destruct (Z.eq_dec upto (i + 1)) as [->|Hneq].
  - rewrite sum_prefix_replace_inside__final_optimality by
        (rewrite Hmidlen; lia).
    rewrite Hmidnth.
    unfold mid.
    rewrite sum_prefix_replace_outside__final_optimality by lia.
    ring.
  - destruct (Z_le_gt_dec upto i).
    + rewrite sum_prefix_replace_outside__final_optimality by
          (try rewrite Hmidlen; lia).
      unfold mid.
      rewrite sum_prefix_replace_outside__final_optimality by lia.
      ring.
    + assert (i + 1 < upto) by lia.
      rewrite sum_prefix_replace_inside__final_optimality by
          (rewrite Hmidlen; lia).
      rewrite Hmidnth.
      unfold mid.
      rewrite sum_prefix_replace_inside__final_optimality by lia.
      ring.
Qed.
Lemma sum_Z_range_update_one__final_optimality : forall low high i f g,
  low <= i < high ->
  (forall k, low <= k < high -> k <> i -> f k = g k) ->
  SumLib.Sum.sum (fun k : Z => low <= k < high) f =
  SumLib.Sum.sum (fun k : Z => low <= k < high) g - g i + f i.
Proof.
  intros low high i f g Hi Heq.
  rewrite (sum_Z_range_split low i high f) by lia.
  rewrite (sum_Z_range_split low i high g) by lia.
  rewrite (sum_Z_range_cons i high f) by lia.
  rewrite (sum_Z_range_cons i high g) by lia.
  assert (Hleft :
    SumLib.Sum.sum (fun k : Z => low <= k < i) f =
    SumLib.Sum.sum (fun k : Z => low <= k < i) g).
  { apply sum_Z_range_ext. intros k Hk. apply Heq; lia. }
  assert (Hright :
    SumLib.Sum.sum (fun k : Z => i + 1 <= k < high) f =
    SumLib.Sum.sum (fun k : Z => i + 1 <= k < high) g).
  { apply sum_Z_range_ext. intros k Hk. apply Heq; lia. }
  rewrite Hleft, Hright. ring.
Qed.
Lemma prefix_transport_cost_nonnegative__final_optimality : forall xs edges,
  0 <= PrefixTransportCost xs edges.
Proof.
  intros xs edges. unfold PrefixTransportCost.
  destruct (Z_le_gt_dec 0 edges).
  - pose proof (sum_Z_range_lower_bound 0 edges
      (fun k => Z.abs (PrefixImbalance xs (k + 1))) 0 l) as H.
    specialize (H ltac:(intros k Hk; apply Z.abs_nonneg)).
    simpl in H. lia.
  - rewrite sum_Z_range_empty by lia. lia.
Qed.
Lemma move_right_cost_effect__final_optimality : forall xs i,
  0 <= i < Zlength xs - 1 ->
  let ys := replace_Znth (i + 1) (Znth (i + 1) xs 0 + 1)
              (replace_Znth i (Znth i xs 0 - 1) xs) in
  PrefixTransportCost ys (Zlength xs - 1) =
  PrefixTransportCost xs (Zlength xs - 1) -
    Z.abs (PrefixImbalance xs (i + 1)) +
    Z.abs (PrefixImbalance xs (i + 1) - 1).
Proof.
  intros xs i Hi ys. subst ys.
  unfold PrefixTransportCost.
  rewrite sum_Z_range_update_one__final_optimality with
    (i := i) (g := fun k => Z.abs (PrefixImbalance xs (k + 1))).
  - rewrite move_right_prefix_effect__final_optimality by lia.
    destruct (Z.eq_dec (i + 1) (i + 1)); [ring|contradiction].
  - lia.
  - intros k Hk Hne.
    rewrite move_right_prefix_effect__final_optimality by lia.
    destruct (Z.eq_dec (k + 1) (i + 1)); [lia|].
    replace (PrefixImbalance xs (k + 1) - 0)
      with (PrefixImbalance xs (k + 1)) by ring. reflexivity.
Qed.
Lemma move_left_cost_effect__final_optimality : forall xs i,
  0 <= i < Zlength xs - 1 ->
  let ys := replace_Znth i (Znth i xs 0 + 1)
              (replace_Znth (i + 1) (Znth (i + 1) xs 0 - 1) xs) in
  PrefixTransportCost ys (Zlength xs - 1) =
  PrefixTransportCost xs (Zlength xs - 1) -
    Z.abs (PrefixImbalance xs (i + 1)) +
    Z.abs (PrefixImbalance xs (i + 1) + 1).
Proof.
  intros xs i Hi ys. subst ys.
  unfold PrefixTransportCost.
  rewrite sum_Z_range_update_one__final_optimality with
    (i := i) (g := fun k => Z.abs (PrefixImbalance xs (k + 1))).
  - rewrite move_left_prefix_effect__final_optimality by lia.
    destruct (Z.eq_dec (i + 1) (i + 1)); [ring|contradiction].
  - lia.
  - intros k Hk Hne.
    rewrite move_left_prefix_effect__final_optimality by lia.
    destruct (Z.eq_dec (k + 1) (i + 1)); [lia|].
    replace (PrefixImbalance xs (k + 1) + 0)
      with (PrefixImbalance xs (k + 1)) by ring. reflexivity.
Qed.
Lemma adjacent_move_cost_lipschitz__final_optimality : forall before after,
  OneAdjacentMatchMove before after ->
  PrefixTransportCost before (Zlength before - 1) <=
  PrefixTransportCost after (Zlength after - 1) + 1.
Proof.
  intros before after [i [Hi [[Hpos ->]|[Hpos ->]]]].
  - rewrite Zlength_replace_Znth__final_optimality.
    rewrite Zlength_replace_Znth__final_optimality.
    rewrite move_right_cost_effect__final_optimality by exact Hi.
    pose proof (Z.abs_triangle
      (PrefixImbalance before (i + 1) - 1) 1).
    replace (PrefixImbalance before (i + 1) - 1 + 1)
      with (PrefixImbalance before (i + 1)) in H by ring.
    simpl in H. lia.
  - rewrite Zlength_replace_Znth__final_optimality.
    rewrite Zlength_replace_Znth__final_optimality.
    rewrite move_left_cost_effect__final_optimality by exact Hi.
    pose proof (Z.abs_triangle
      (PrefixImbalance before (i + 1) + 1) (-1)).
    replace (PrefixImbalance before (i + 1) + 1 + -1)
      with (PrefixImbalance before (i + 1)) in H by ring.
    simpl in H. lia.
Qed.
Lemma Forall_Znth_intro__final_optimality : forall (A : Type)
    (P : A -> Prop) (xs : list A) (dflt : A),
  (forall k, 0 <= k < Zlength xs -> P (Znth k xs dflt)) ->
  Forall P xs.
Proof.
  intros A P xs dflt Hnth. apply Forall_forall.
  intros x Hin.
  apply In_nth with (d := dflt) in Hin as [n [Hn Hx]].
  specialize (Hnth (Z.of_nat n)).
  assert (0 <= Z.of_nat n < Zlength xs).
  { rewrite Zlength_correct. lia. }
  specialize (Hnth H). unfold Znth in Hnth.
  rewrite Nat2Z.id in Hnth. now rewrite Hx in Hnth.
Qed.
Lemma replace_Znth_preserves_nonnegative__final_optimality : forall xs i v,
  Forall (fun x => 0 <= x) xs ->
  0 <= i < Zlength xs -> 0 <= v ->
  Forall (fun x => 0 <= x) (replace_Znth i v xs).
Proof.
  intros xs i v Hxs Hi Hv.
  apply Forall_Znth_intro__final_optimality with (dflt := 0).
  intros k Hk.
  rewrite Zlength_replace_Znth__final_optimality in Hk.
  destruct (Z.eq_dec k i) as [->|Hne].
  - rewrite Znth_replace_Znth_Same by lia. exact Hv.
  - rewrite Znth_replace_Znth_Diff by lia.
    eapply Forall_Znth_Zlength; eauto.
Qed.
Lemma adjacent_move_preserves_balanced_state__final_optimality :
  forall before after,
  1 <= Zlength before ->
  Forall (fun x => 0 <= x) before ->
  (Zlength before | ListLib.sum before) ->
  OneAdjacentMatchMove before after ->
  1 <= Zlength after /\
  Forall (fun x => 0 <= x) after /\
  (Zlength after | ListLib.sum after).
Proof.
  intros before after Hlen Hnonneg Hdiv
    Hmove.
  pose proof (adjacent_move_preserves_length_sum__final_optimality
    before after Hmove) as [Halen Hasum].
  destruct Hmove as [i [Hi [[Hpos ->]|[Hpos ->]]]].
  - split.
    + repeat rewrite Zlength_replace_Znth__final_optimality. exact Hlen.
    + split.
      * apply replace_Znth_preserves_nonnegative__final_optimality.
        -- apply replace_Znth_preserves_nonnegative__final_optimality;
             try assumption; lia.
        -- rewrite Zlength_replace_Znth__final_optimality. lia.
        -- pose proof (Forall_Znth_Zlength
             (fun x : Z => 0 <= x) before 0 (i + 1) Hnonneg ltac:(lia))
             as Hnext. apply Z.add_nonneg_nonneg; [exact Hnext|lia].
      * rewrite !Zlength_replace_Znth__final_optimality.
        rewrite Hasum. exact Hdiv.
  - split.
    + repeat rewrite Zlength_replace_Znth__final_optimality. exact Hlen.
    + split.
      * apply replace_Znth_preserves_nonnegative__final_optimality.
        -- apply replace_Znth_preserves_nonnegative__final_optimality;
             try assumption; lia.
        -- rewrite Zlength_replace_Znth__final_optimality. lia.
        -- pose proof (Forall_Znth_Zlength
             (fun x : Z => 0 <= x) before 0 i Hnonneg ltac:(lia))
             as Hcur. apply Z.add_nonneg_nonneg; [exact Hcur|lia].
      * rewrite !Zlength_replace_Znth__final_optimality.
        rewrite Hasum. exact Hdiv.
Qed.
Lemma sum_Z_range_term_le__final_optimality : forall low high i f,
  low <= i < high ->
  (forall k, low <= k < high -> 0 <= f k) ->
  f i <= SumLib.Sum.sum (fun k : Z => low <= k < high) f.
Proof.
  intros low high i f Hi Hnonneg.
  rewrite (sum_Z_range_split low i high f) by lia.
  rewrite (sum_Z_range_cons i high f) by lia.
  assert (Hleft : 0 <= SumLib.Sum.sum (fun k : Z => low <= k < i) f).
  { pose proof (sum_Z_range_lower_bound low i f 0 ltac:(lia)) as H.
    specialize (H ltac:(intros k Hk; apply Hnonneg; lia)).
    simpl in H. lia. }
  assert (Hright : 0 <= SumLib.Sum.sum (fun k : Z => i + 1 <= k < high) f).
  { pose proof (sum_Z_range_lower_bound (i + 1) high f 0 ltac:(lia)) as H.
    specialize (H ltac:(intros k Hk; apply Hnonneg; lia)).
    simpl in H. lia. }
  lia.
Qed.
Lemma cost_zero_prefixes_zero__final_optimality : forall xs,
  PrefixTransportCost xs (Zlength xs - 1) = 0 ->
  forall k, 0 <= k < Zlength xs - 1 ->
    PrefixImbalance xs (k + 1) = 0.
Proof.
  intros xs Hcost k Hk.
  unfold PrefixTransportCost in Hcost.
  pose proof (sum_Z_range_term_le__final_optimality 0
    (Zlength xs - 1) k
    (fun j => Z.abs (PrefixImbalance xs (j + 1))) Hk
    ltac:(intros j Hj; apply Z.abs_nonneg)) as Hterm.
  rewrite Hcost in Hterm.
  pose proof (Z.abs_nonneg (PrefixImbalance xs (k + 1))) as Habsnonneg.
  assert (Habseq : Z.abs (PrefixImbalance xs (k + 1)) = 0) by lia.
  destruct (Z_le_gt_dec 0 (PrefixImbalance xs (k + 1))).
  - rewrite Z.abs_eq in Habseq by lia. exact Habseq.
  - rewrite Z.abs_neq in Habseq by lia. lia.
Qed.
Lemma zero_cost_uniform__final_optimality : forall xs,
  1 <= Zlength xs ->
  (Zlength xs | ListLib.sum xs) ->
  PrefixTransportCost xs (Zlength xs - 1) = 0 ->
  exists target, Forall (fun x => x = target) xs.
Proof.
  intros xs Hlen Hdiv Hcost.
  exists (ListLib.sum xs / Zlength xs).
  apply Forall_Znth_intro__final_optimality with (dflt := 0).
  intros k Hk.
  pose proof (prefix_imbalance_succ__final_optimality xs k Hk) as Hrec.
  assert (Hbefore : PrefixImbalance xs k = 0).
  { destruct (Z.eq_dec k 0) as [->|Hne].
    - apply prefix_imbalance_zero__final_optimality.
    - replace k with ((k - 1) + 1) by ring.
      apply cost_zero_prefixes_zero__final_optimality; try assumption; lia. }
  assert (Hafter : PrefixImbalance xs (k + 1) = 0).
  { destruct (Z.eq_dec k (Zlength xs - 1)) as [->|Hne].
    - replace (Zlength xs - 1 + 1) with (Zlength xs) by ring.
      apply prefix_imbalance_full__final_optimality; assumption.
    - apply cost_zero_prefixes_zero__final_optimality; try assumption; lia. }
  lia.
Qed.
Lemma bounded_leftmost__final_optimality : forall (P : Z -> Prop) n,
  0 <= n ->
  (exists k, 0 <= k < n /\ P k) ->
  exists k, 0 <= k < n /\ P k /\
    forall j, 0 <= j < k -> ~ P j.
Proof.
  intros P n Hn Hex.
  remember (Z.to_nat n) as m eqn:Hm.
  assert (Hnm : n = Z.of_nat m) by lia. subst n. clear Hn Hm.
  revert P Hex. induction m as [|m IH]; intros P Hex.
  - simpl in Hex. destruct Hex as [k [Hk _]]. lia.
  - destruct (classic (P 0)) as [HP0|HnP0].
    + exists 0. split; [lia|]. split; [exact HP0|].
      intros j Hj. lia.
    + assert (Hex' : exists k, 0 <= k < Z.of_nat m /\ P (k + 1)).
      { destruct Hex as [k [Hk HP]].
        assert (k <> 0) by (intro; subst; contradiction).
        exists (k - 1). split; [lia|].
        replace (k - 1 + 1) with k by ring. exact HP. }
      specialize (IH (fun k => P (k + 1)) Hex')
        as [k [Hk [HP Hmin]]].
      exists (k + 1). split; [lia|]. split; [exact HP|].
      intros j Hj HPj.
      destruct (Z.eq_dec j 0) as [->|Hj0]; [contradiction|].
      specialize (Hmin (j - 1) ltac:(lia)).
      apply Hmin. replace (j - 1 + 1) with j by ring. exact HPj.
Qed.
Lemma bounded_rightmost__final_optimality : forall (P : Z -> Prop) n,
  0 <= n ->
  (exists k, 0 <= k < n /\ P k) ->
  exists k, 0 <= k < n /\ P k /\
    forall j, k < j < n -> ~ P j.
Proof.
  intros P n Hn Hex.
  remember (Z.to_nat n) as m eqn:Hm.
  assert (Hnm : n = Z.of_nat m) by lia. subst n. clear Hn Hm.
  revert P Hex. induction m as [|m IH]; intros P Hex.
  - simpl in Hex. destruct Hex as [k [Hk _]]. lia.
  - destruct (classic (P (Z.of_nat m))) as [HPlast|HnPlast].
    + exists (Z.of_nat m). split; [lia|]. split; [exact HPlast|].
      intros j Hj. lia.
    + assert (Hex' : exists k, 0 <= k < Z.of_nat m /\ P k).
      { destruct Hex as [k [Hk HP]].
        assert (k <> Z.of_nat m) by (intro; subst; contradiction).
        exists k. split; [lia|exact HP]. }
      specialize (IH P Hex') as [k [Hk [HP Hmax]]].
      exists k. split; [lia|]. split; [exact HP|].
      intros j Hj HPj.
      destruct (Z.eq_dec j (Z.of_nat m)) as [->|Hjne]; [contradiction|].
      apply (Hmax j ltac:(lia) HPj).
Qed.
Lemma nonnegative_list_sum__final_optimality : forall xs,
  Forall (fun x => 0 <= x) xs -> 0 <= ListLib.sum xs.
Proof.
  intros xs Hxs.
  rewrite list_sum_as_Z_range_sum.
  pose proof (sum_Z_range_lower_bound 0 (Zlength xs)
    (fun k => Znth k xs 0) 0 (Zlength_nonneg xs)) as H.
  specialize (H ltac:(intros k Hk;
    eapply Forall_Znth_Zlength; eauto)).
  simpl in H. lia.
Qed.
Lemma positive_cost_has_nonzero_prefix__final_optimality : forall xs,
  0 < PrefixTransportCost xs (Zlength xs - 1) ->
  exists k, 0 <= k < Zlength xs - 1 /\
    PrefixImbalance xs (k + 1) <> 0.
Proof.
  intros xs Hcost.
  destruct (classic (exists k, 0 <= k < Zlength xs - 1 /\
      PrefixImbalance xs (k + 1) <> 0)) as [Hex|Hnone]; auto.
  exfalso.
  unfold PrefixTransportCost in Hcost.
  assert (Hzero : SumLib.Sum.sum
      (fun k : Z => 0 <= k < Zlength xs - 1)
      (fun k => Z.abs (PrefixImbalance xs (k + 1))) = 0).
  { apply sum_Z_range_eq_zero. intros k Hk.
    assert (PrefixImbalance xs (k + 1) = 0).
    { destruct (Z.eq_dec (PrefixImbalance xs (k + 1)) 0); auto.
      exfalso. apply Hnone. exists k. auto. }
    rewrite H. reflexivity. }
  lia.
Qed.
Lemma one_step_descent__final_optimality : forall xs,
  1 <= Zlength xs ->
  Forall (fun x => 0 <= x) xs ->
  (Zlength xs | ListLib.sum xs) ->
  0 < PrefixTransportCost xs (Zlength xs - 1) ->
  exists ys,
    OneAdjacentMatchMove xs ys /\
    (1 <= Zlength ys /\ Forall (fun x => 0 <= x) ys /\
      (Zlength ys | ListLib.sum ys)) /\
    PrefixTransportCost ys (Zlength ys - 1) =
      PrefixTransportCost xs (Zlength xs - 1) - 1.
Proof.
  intros xs Hlen Hnonneg Hdiv Hcost.
  pose proof (positive_cost_has_nonzero_prefix__final_optimality xs Hcost)
    as [some [Hsome Hsome0]].
  pose proof (nonnegative_list_sum__final_optimality xs Hnonneg) as Hsum.
  assert (Htarget : 0 <= ListLib.sum xs / Zlength xs).
  { apply Z_div_nonneg_nonneg; lia. }
  destruct (classic (exists k, 0 <= k < Zlength xs - 1 /\
      0 < PrefixImbalance xs (k + 1))) as [Hpositive|Hnopos].
  - destruct (bounded_leftmost__final_optimality
      (fun k => 0 < PrefixImbalance xs (k + 1))
      (Zlength xs - 1) ltac:(lia) Hpositive)
      as [i [Hi [Hbi Hminimal]]].
    assert (Hprev : PrefixImbalance xs i <= 0).
    { destruct (Z.eq_dec i 0) as [->|Hine].
      - rewrite prefix_imbalance_zero__final_optimality. lia.
      - destruct (Z_le_gt_dec (PrefixImbalance xs i) 0); auto.
        exfalso. apply (Hminimal (i - 1) ltac:(lia)).
        replace (i - 1 + 1) with i by ring. lia. }
    pose proof (prefix_imbalance_succ__final_optimality xs i ltac:(lia))
      as Hrec.
    assert (Hsource : 0 < Znth i xs 0) by lia.
    set (ys := replace_Znth (i + 1) (Znth (i + 1) xs 0 + 1)
      (replace_Znth i (Znth i xs 0 - 1) xs)).
    exists ys.
    assert (Hmove : OneAdjacentMatchMove xs ys).
    { exists i. split; [exact Hi|]. left. split; [lia|reflexivity]. }
    split; [exact Hmove|]. split.
    + eapply adjacent_move_preserves_balanced_state__final_optimality; eauto.
    + unfold ys.
      rewrite !Zlength_replace_Znth__final_optimality.
      rewrite move_right_cost_effect__final_optimality by exact Hi.
      rewrite Z.abs_eq by lia.
      rewrite Z.abs_eq by lia. ring.
  - assert (Hnegative : exists k, 0 <= k < Zlength xs - 1 /\
        PrefixImbalance xs (k + 1) < 0).
    { exists some. split; [exact Hsome|].
      destruct (Z_lt_ge_dec (PrefixImbalance xs (some + 1)) 0); auto.
      exfalso. apply Hnopos. exists some. split; auto. lia. }
    destruct (bounded_rightmost__final_optimality
      (fun k => PrefixImbalance xs (k + 1) < 0)
      (Zlength xs - 1) ltac:(lia) Hnegative)
      as [i [Hi [Hbi Hmaximal]]].
    assert (Hnext : 0 <= PrefixImbalance xs (i + 2)).
    { destruct (Z.eq_dec i (Zlength xs - 2)) as [->|Hine].
      - replace (Zlength xs - 2 + 2) with (Zlength xs) by ring.
        rewrite prefix_imbalance_full__final_optimality by assumption. lia.
      - destruct (Z_le_gt_dec 0 (PrefixImbalance xs (i + 2))); auto.
        exfalso. apply (Hmaximal (i + 1) ltac:(lia)).
        replace (i + 1 + 1) with (i + 2) by ring. lia. }
    pose proof (prefix_imbalance_succ__final_optimality xs (i + 1)
      ltac:(lia)) as Hrec.
    replace (i + 1 + 1) with (i + 2) in Hrec by ring.
    assert (Hsource : 0 < Znth (i + 1) xs 0) by lia.
    set (ys := replace_Znth i (Znth i xs 0 + 1)
      (replace_Znth (i + 1) (Znth (i + 1) xs 0 - 1) xs)).
    exists ys.
    assert (Hmove : OneAdjacentMatchMove xs ys).
    { exists i. split; [exact Hi|]. right. split; [lia|reflexivity]. }
    split; [exact Hmove|]. split.
    + eapply adjacent_move_preserves_balanced_state__final_optimality; eauto.
    + unfold ys.
      rewrite !Zlength_replace_Znth__final_optimality.
      rewrite move_left_cost_effect__final_optimality by exact Hi.
      rewrite Z.abs_neq by lia.
      rewrite Z.abs_neq by lia. ring.
Qed.
Lemma balance_trace_moves_nonnegative__final_optimality : forall xs moves,
  1 <= Zlength xs -> BalanceTrace xs moves -> 0 <= moves.
Proof.
  intros xs moves Hxs [states [Hstates [Hstart _]]].
  destruct states as [|s states].
  - simpl in Hstart. subst xs. rewrite Zlength_nil in Hxs. lia.
  - rewrite Zlength_cons in Hstates. pose proof (Zlength_nonneg states). lia.
Qed.
Lemma balance_trace_cons__final_optimality : forall xs ys moves,
  1 <= Zlength ys ->
  OneAdjacentMatchMove xs ys ->
  BalanceTrace ys moves ->
  BalanceTrace xs (moves + 1).
Proof.
  intros xs ys moves Hys Hmove
    [states [Hstates [Hstart [Hsteps [target Htarget]]]]].
  assert (Hmoves : 0 <= moves).
  { eapply balance_trace_moves_nonnegative__final_optimality; [exact Hys|].
    exists states. split; [exact Hstates|]. split; [exact Hstart|].
    split; [exact Hsteps|]. exists target. exact Htarget. }
  exists (xs :: states). split.
  - rewrite Zlength_cons, Hstates. ring.
  - split; [reflexivity|]. split.
    + intros j Hj. destruct (Z.eq_dec j 0) as [->|Hj0].
      * change (OneAdjacentMatchMove xs (Znth 0 states nil)).
        rewrite Hstart. exact Hmove.
      * rewrite Znth_cons by lia. rewrite Znth_cons by lia.
        replace (j + 1 - 1) with j by ring.
        pose proof (Hsteps (j - 1) ltac:(lia)) as Hstep.
        replace (j - 1 + 1) with j in Hstep by ring. exact Hstep.
    + exists target.
      rewrite Znth_cons by lia.
      replace (moves + 1 - 1) with moves by ring. exact Htarget.
Qed.
Lemma uniform_balance_trace_zero__final_optimality : forall xs target,
  Forall (fun x => x = target) xs -> BalanceTrace xs 0.
Proof.
  intros xs target Huniform.
  exists [xs]. split; [reflexivity|]. split; [reflexivity|]. split.
  - intros i Hi. lia.
  - exists target. exact Huniform.
Qed.
Lemma balance_trace_realization_nat__final_optimality : forall n xs,
  1 <= Zlength xs ->
  Forall (fun x => 0 <= x) xs ->
  (Zlength xs | ListLib.sum xs) ->
  PrefixTransportCost xs (Zlength xs - 1) = Z.of_nat n ->
  BalanceTrace xs (Z.of_nat n).
Proof.
  induction n as [|n IH]; intros xs Hlen Hnonneg Hdiv Hcost.
  - simpl in Hcost.
    apply zero_cost_uniform__final_optimality in Hcost; try assumption.
    destruct Hcost as [target Huniform].
    apply uniform_balance_trace_zero__final_optimality with (target := target).
    exact Huniform.
  - assert (Hpos : 0 < PrefixTransportCost xs (Zlength xs - 1)) by lia.
    destruct (one_step_descent__final_optimality xs Hlen Hnonneg Hdiv Hpos)
      as [ys [Hmove [[Hyslen [Hysnonneg Hysdiv]] Hyscost]]].
    assert (Hysnat : PrefixTransportCost ys (Zlength ys - 1) = Z.of_nat n)
      by lia.
    specialize (IH ys Hyslen Hysnonneg Hysdiv Hysnat).
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    eapply balance_trace_cons__final_optimality; eauto.
Qed.
Lemma balance_trace_realization__final_optimality : forall xs,
  Pre xs ->
  BalanceTrace xs (PrefixTransportCost xs (Zlength xs - 1)).
Proof.
  intros xs Hpre.
  pose proof (pre_balanced_state__final_optimality xs Hpre)
    as [Hlen [Hnonneg Hdiv]].
  pose proof (prefix_transport_cost_nonnegative__final_optimality
    xs (Zlength xs - 1)) as Hcostnonneg.
  replace (PrefixTransportCost xs (Zlength xs - 1)) with
    (Z.of_nat (Z.to_nat (PrefixTransportCost xs (Zlength xs - 1))))
    by lia.
  apply balance_trace_realization_nat__final_optimality
    with (n := Z.to_nat (PrefixTransportCost xs (Zlength xs - 1)));
    try assumption.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma uniform_prefix_imbalance_zero__final_optimality : forall xs target upto,
  1 <= Zlength xs ->
  Forall (fun x => x = target) xs ->
  0 <= upto <= Zlength xs ->
  PrefixImbalance xs upto = 0.
Proof.
  intros xs target upto Hlen Huniform Hup.
  assert (Hnth : forall k, 0 <= k < Zlength xs -> Znth k xs 0 = target).
  { intros k Hk. eapply Forall_Znth_Zlength; eauto. }
  assert (Hsum : ListLib.sum xs = Zlength xs * target).
  { rewrite list_sum_as_Z_range_sum.
    transitivity (SumLib.Sum.sum (fun k : Z => 0 <= k < Zlength xs)
      (fun _ => target)).
    - apply sum_Z_range_ext. exact Hnth.
    - rewrite sum_Z_range_const by lia. ring. }
  assert (Hprefix : ListLib.sum (sublist 0 upto xs) = upto * target).
  { rewrite list_sum_sublist_as_Z_range_sum by lia.
    transitivity (SumLib.Sum.sum (fun k : Z => 0 <= k < upto)
      (fun _ => target)).
    - apply sum_Z_range_ext. intros k Hk. apply Hnth. lia.
    - rewrite sum_Z_range_const by lia. ring. }
  unfold PrefixImbalance. rewrite Hsum, Hprefix.
  assert (Hquot : Zlength xs * target / Zlength xs = target).
  { rewrite Z.mul_comm. apply Z.div_mul. lia. }
  rewrite Hquot. ring.
Qed.
Lemma uniform_prefix_transport_cost_zero__final_optimality : forall xs target,
  1 <= Zlength xs ->
  Forall (fun x => x = target) xs ->
  PrefixTransportCost xs (Zlength xs - 1) = 0.
Proof.
  intros xs target Hlen Huniform.
  unfold PrefixTransportCost. apply sum_Z_range_eq_zero.
  intros k Hk.
  rewrite uniform_prefix_imbalance_zero__final_optimality
    with (target := target) by (try assumption; lia).
  reflexivity.
Qed.
Lemma balance_trace_uncons__final_optimality : forall xs moves,
  1 <= Zlength xs -> 0 < moves -> BalanceTrace xs moves ->
  exists ys, OneAdjacentMatchMove xs ys /\ BalanceTrace ys (moves - 1).
Proof.
  intros xs moves Hxs Hmoves
    [states [Hstates [Hstart [Hsteps [target Htarget]]]]].
  destruct states as [|s rest].
  - rewrite Zlength_nil in Hstates. lia.
  - change (s = xs) in Hstart. subst s.
    destruct rest as [|ys tail].
    + rewrite Zlength_cons, Zlength_nil in Hstates. lia.
    + exists ys. split.
      * pose proof (Hsteps 0 ltac:(lia)) as Hstep.
        change (OneAdjacentMatchMove xs ys) in Hstep. exact Hstep.
      * exists (ys :: tail). split.
        -- do 2 rewrite Zlength_cons in Hstates.
           rewrite Zlength_cons. lia.
        -- split; [reflexivity|]. split.
           ++ intros j Hj.
              pose proof (Hsteps (j + 1) ltac:(lia)) as Hstep.
              rewrite Znth_cons in Hstep by lia.
              rewrite (Znth_cons nil (j + 1 + 1) xs (ys :: tail))
                in Hstep by lia.
              replace (j + 1 - 1) with j in Hstep by ring.
              replace (j + 1 + 1 - 1) with (j + 1) in Hstep by ring.
              exact Hstep.
           ++ exists target.
              rewrite Znth_cons in Htarget by lia. exact Htarget.
Qed.
Lemma balance_trace_lower_bound_nat__final_optimality : forall n xs,
  1 <= Zlength xs -> BalanceTrace xs (Z.of_nat n) ->
  PrefixTransportCost xs (Zlength xs - 1) <= Z.of_nat n.
Proof.
  induction n as [|n IH]; intros xs Hlen Htrace.
  - simpl.
    destruct Htrace as [states [Hstates [Hstart [Hsteps [target Htarget]]]]].
    assert (Huniform : Forall (fun x => x = target) xs).
    { rewrite <- Hstart. exact Htarget. }
    rewrite uniform_prefix_transport_cost_zero__final_optimality
      with (target := target) by assumption. lia.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in Htrace |- * by lia.
    destruct (balance_trace_uncons__final_optimality xs (Z.of_nat n + 1)
      Hlen ltac:(lia) Htrace) as [ys [Hmove Hystrace]].
    replace (Z.of_nat n + 1 - 1) with (Z.of_nat n) in Hystrace by ring.
    pose proof (adjacent_move_preserves_length_sum__final_optimality
      xs ys Hmove) as [Hyslen _].
    specialize (IH ys ltac:(lia) Hystrace).
    pose proof (adjacent_move_cost_lipschitz__final_optimality xs ys Hmove).
    lia.
Qed.
Lemma balance_trace_lower_bound__final_optimality : forall xs moves,
  Pre xs -> BalanceTrace xs moves ->
  PrefixTransportCost xs (Zlength xs - 1) <= moves.
Proof.
  intros xs moves Hpre Htrace.
  pose proof (pre_balanced_state__final_optimality xs Hpre)
    as [Hlen _].
  pose proof (balance_trace_moves_nonnegative__final_optimality
    xs moves Hlen Htrace) as Hmoves.
  replace moves with (Z.of_nat (Z.to_nat moves)) in Htrace by lia.
  replace moves with (Z.of_nat (Z.to_nat moves)) by lia.
  apply balance_trace_lower_bound_nat__final_optimality; assumption.
Qed.
Lemma prefix_transport_cost_optimal__final_optimality : forall xs,
  Pre xs -> Spec xs (PrefixTransportCost xs (Zlength xs - 1)).
Proof.
  intros xs Hpre.
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (PrefixTransportCost xs (Zlength xs - 1)).
  split.
  - split.
    + apply balance_trace_realization__final_optimality. exact Hpre.
    + intros moves Htrace.
      eapply balance_trace_lower_bound__final_optimality; eauto.
  - reflexivity.
Qed.
