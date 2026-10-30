Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition DecimalSub (s : list Z) (l r : Z) : Z :=
  fold_left (fun v c => 10 * v + (c - 48)) (sublist l (r + 1) s) 0.

Definition QueryPair (s : list Z) (w : Z) (q : Z * Z * Z)
    (p : Z * Z) : Prop :=
  let '(l, r, k) := q in
  let '(x, y) := p in
  1 <= x /\ x + w - 1 <= Zlength s /\
  1 <= y /\ y + w - 1 <= Zlength s /\ x <> y /\
  (DecimalSub s (x - 1) (x + w - 2) * DecimalSub s (l - 1) (r - 1) +
    DecimalSub s (y - 1) (y + w - 2)) mod 9 = k.

Definition Pre (w : Z) (s : list Z) (qs : list (Z * Z * Z)) : Prop :=
  2 <= Zlength s <= 200000 /\ 1 <= w < Zlength s /\
  (* Character codes: decimal digits '0'..'9' = 48..57. *)
  Forall (fun c => 48 <= c <= 57) s.

Definition Spec (w : Z) (s : list Z) (qs : list (Z * Z * Z))
    (out : list (Z * Z)) : Prop :=
  Forall2 (fun q p =>
    (p = (-1, -1) /\
      (forall candidate, ~ QueryPair s w q candidate)) \/
    min_value_of_subset
      (fun left right : Z * Z =>
        fst left < fst right \/
        fst left = fst right /\ snd left <= snd right)
      (QueryPair s w q)
      (fun candidate => candidate) p) qs out.

Definition DigitPrefixValue (s : list Z) (i : Z) : Z :=
  sum_range 0 (i - 1) (fun j => Znth j s 48 - 48).

Definition DigitPrefixSums
    (s prefix_values : list Z) (endpoints_done : Z) : Prop :=
  forall j,
    0 <= j <= endpoints_done ->
    Znth j prefix_values 0 = DigitPrefixValue s j.

(** Canonical mixed-memory image while the local [pos] table is initialized.
    Rows before [rows_done] contain two [-1] sentinels; later rows remain
    undefined. *)
Definition pos_init_stage (rows_done : Z) : list (list (option Z)) :=
  map (fun r =>
    if Z_lt_dec r rows_done
    then Some (-1) :: Some (-1) :: nil
    else None :: None :: nil) (Zrange 0 9).

(** A one-based start [x] of a width-[w] window with residue [residue], among
    the first [starts_done] possible starts. *)
Definition WindowStart
    (s : list Z) (w starts_done residue x : Z) : Prop :=
  1 <= x <= starts_done /\
  x + w - 1 <= Zlength s /\
  DecimalSub s (x - 1) (x + w - 2) mod 9 = residue.

Definition FirstWindowStart
    (s : list Z) (w starts_done residue first : Z) : Prop :=
  (first = -1 /\
    forall x, ~ WindowStart s w starts_done residue x) \/
  (WindowStart s w starts_done residue first /\
    forall x, WindowStart s w starts_done residue x -> first <= x).

Definition SecondWindowStart
    (s : list Z) (w starts_done residue first second : Z) : Prop :=
  (second = -1 /\
    forall x,
      WindowStart s w starts_done residue x -> x = first) \/
  (WindowStart s w starts_done residue second /\
    second <> first /\
    forall x,
      WindowStart s w starts_done residue x ->
      x <> first -> second <= x).

(** Each row records the first two distinct one-based window starts for its
    residue.  Bounds and memory ownership stay in the C invariant. *)
Definition PositionsPrefix
    (s : list Z) (w starts_done : Z) (rows : list (list Z)) : Prop :=
  forall residue,
    0 <= residue < 9 ->
    let row := Znth residue rows nil in
    FirstWindowStart s w starts_done residue (Znth 0 row (-1)) /\
    SecondWindowStart s w starts_done residue
      (Znth 0 row (-1)) (Znth 1 row (-1)).

Definition PairLexLe (left right : Z * Z) : Prop :=
  fst left < fst right \/
  fst left = fst right /\ snd left <= snd right.

Definition PairFirstResidue (s : list Z) (w : Z) (p : Z * Z) : Z :=
  DecimalSub s (fst p - 1) (fst p + w - 2) mod 9.

Definition PrefixEligiblePair
    (s : list Z) (w : Z) (q : Z * Z * Z) (residues_done : Z)
    (p : Z * Z) : Prop :=
  QueryPair s w q p /\
  0 <= PairFirstResidue s w p < residues_done.

(** The best pair after considering first-window residues below
    [residues_done].  The large pair is the C implementation's private empty
    sentinel; it is not part of the public result. *)
Definition QueryBestPrefix
    (s : list Z) (w : Z) (q : Z * Z * Z)
    (residues_done best1 best2 : Z) : Prop :=
  (best1 = 1073741824 /\ best2 = 1073741824 /\
    forall candidate,
      ~ PrefixEligiblePair s w q residues_done candidate) \/
  min_value_of_subset PairLexLe
    (PrefixEligiblePair s w q residues_done)
    (fun candidate => candidate) (best1, best2).

(** The already written component arrays encode a result list satisfying the
    frozen public [Spec] for the corresponding query prefix. *)
Definition QueryOutputPrefix
    (w : Z) (s : list Z) (qs : list (Z * Z * Z)) (queries_done : Z)
    (out1 out2 : list Z) : Prop :=
  exists pairs,
    Spec w s (sublist 0 queries_done qs) pairs /\
    Zlength pairs = queries_done /\
    Zlength out1 = queries_done /\
    Zlength out2 = queries_done /\
    forall i,
      0 <= i < queries_done ->
      Znth i out1 0 = fst (Znth i pairs (0, 0)) /\
      Znth i out2 0 = snd (Znth i pairs (0, 0)).

(** Interpret the executable row-major [int pos[18]] as nine logical rows of
    two entries.  This is a representation bridge only: allocation length and
    memory ownership remain explicit in the C annotations. *)
Definition FlatPositionRows (flat : list Z) : list (list Z) :=
  map (fun residue =>
    Znth (2 * residue) flat (-1) ::
    Znth (2 * residue + 1) flat (-1) :: nil) (Zrange 0 9).

(** The first-two-starts invariant for the row-major executable table. *)
Definition FlatPositionsPrefix
    (s : list Z) (w starts_done : Z) (flat : list Z) : Prop :=
  PositionsPrefix s w starts_done (FlatPositionRows flat).

(** Transparent projections for QCP's left-associated encoding of triples. *)
Definition ztriple_1 (p : Z * Z * Z) : Z := fst (fst p).
Definition ztriple_2 (p : Z * Z * Z) : Z := snd (fst p).
Definition ztriple_3 (p : Z * Z * Z) : Z := snd p.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.ZArith.Zquot.
Lemma Znth_app_left__arithmetic_safety :
  forall (l1 l2 : list Z) (d i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma digit_prefix_repeat_zero__prefix_construction :
  forall (s : list Z) k,
    1 <= k ->
    DigitPrefixSums s (repeat 0 (Z.to_nat k)) 0.
Proof.
  intros s k Hk.
  unfold DigitPrefixSums.
  intros j Hj.
  assert (j = 0) by lia; subst j.
  rewrite Znth_repeat.
  unfold DigitPrefixValue, sum_range.
  rewrite sum_Z_range_empty by lia.
  reflexivity.
Qed.
Lemma digit_prefix_replace_step__prefix_construction :
  forall (s prefix_values : list Z) i,
    0 <= i ->
    i + 1 < Zlength prefix_values ->
    DigitPrefixSums s prefix_values i ->
    DigitPrefixSums s
      (replace_Znth (i + 1)
        ((Znth i prefix_values 0 + Znth i s 48) - 48) prefix_values)
      (i + 1).
Proof.
  intros s prefix_values i Hi Hlen Hprefix.
  unfold DigitPrefixSums in *.
  intros j Hj.
  destruct (Z.eq_dec j (i + 1)) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia.
    rewrite Hprefix by lia.
    unfold DigitPrefixValue, sum_range.
    replace (i - 1 + 1) with i by lia.
    replace (i + 1 - 1 + 1) with (i + 1) by lia.
    rewrite (sum_Z_range_extend_right 0 i
      (fun j => Znth j s 48 - 48) Hi).
    ring.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Hprefix; lia.
Qed.
Lemma digit_prefix_difference_bounds__prefix_construction :
  forall (s prefix_values : list Z) n,
    0 <= n ->
    n <= Zlength s ->
    DigitPrefixSums s prefix_values n ->
    (forall j, 0 <= j < n -> 48 <= Znth j s 0 <= 57) ->
    forall lo hi,
      0 <= lo <= hi -> hi <= n ->
      0 <= Znth hi prefix_values 0 - Znth lo prefix_values 0 <=
        9 * (hi - lo).
Proof.
  intros s prefix_values n Hn Hnlen Hprefix Hdigits lo hi Hlohi Hhin.
  rewrite (Hprefix hi) by lia.
  rewrite (Hprefix lo) by lia.
  unfold DigitPrefixValue, sum_range.
  replace (hi - 1 + 1) with hi by lia.
  replace (lo - 1 + 1) with lo by lia.
  pose proof
    (sum_Z_range_split 0 lo hi (fun j => Znth j s 48 - 48)
      ltac:(lia)) as Hsplit.
  pose proof
    (sum_Z_range_bounds lo hi (fun j => Znth j s 48 - 48) 0 9
      ltac:(lia)) as Hbounds.
  assert (Hpoint : forall j : Z,
    lo <= j < hi -> 0 <= Znth j s 48 - 48 <= 9).
  {
    intros j Hj.
    specialize (Hdigits j ltac:(lia)).
    rewrite (Znth_indep s j 48 0) by lia.
    lia.
  }
  specialize (Hbounds Hpoint).
  lia.
Qed.
Lemma flat_positions_repeat_minus_one__position_initialization :
  forall (s : list Z) (w : Z),
    FlatPositionsPrefix s w 0 (repeat (-1) 18%nat).
Proof.
  intros s w.
  unfold FlatPositionsPrefix, PositionsPrefix, FlatPositionRows.
  intros residue Hresidue.
  destruct Hresidue as [Hresidue0 Hresidue9].
  assert (Hcases :
    residue = 0 \/ residue = 1 \/ residue = 2 \/ residue = 3 \/
    residue = 4 \/ residue = 5 \/ residue = 6 \/ residue = 7 \/
    residue = 8) by lia.
  destruct Hcases as
    [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
  all: cbn [FirstWindowStart SecondWindowStart WindowStart].
  all: split.
  all: left.
  all: split.
  all: try reflexivity.
  all: intros x Hx; destruct Hx as [[Hxlo Hxhi] _]; lia.
Qed.
Lemma flat_position_row_at__position_update :
  forall flat residue,
    0 <= residue < 9 ->
    Znth residue (FlatPositionRows flat) nil =
      Znth (2 * residue) flat (-1) ::
      Znth (2 * residue + 1) flat (-1) :: nil.
Proof.
  intros flat residue Hresidue.
  unfold FlatPositionRows.
  assert (Hcases :
    residue = 0 \/ residue = 1 \/ residue = 2 \/ residue = 3 \/
    residue = 4 \/ residue = 5 \/ residue = 6 \/ residue = 7 \/
    residue = 8) by lia.
  destruct Hcases as
    [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
  all: reflexivity.
Qed.
Lemma Zlength_replace_Znth__position_update :
  forall {A : Type} (xs : list A) i (v : A),
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
Lemma digit_sublist_sum__position_update :
  forall s lo hi,
    0 <= lo <= hi ->
    hi <= Zlength s ->
    ListLib.sum (map (fun c => c - 48) (sublist lo hi s)) =
      sum_range lo (hi - 1) (fun j => Znth j s 48 - 48).
Proof.
  intros s lo hi Hlo Hhi.
  rewrite (list_sum_map_as_Z_range_sum 48
    (fun c : Z => c - 48) (sublist lo hi s)).
  rewrite Zlength_sublist by lia.
  unfold sum_range.
  replace (hi - 1 + 1) with hi by lia.
  transitivity
    (SumLib.Sum.sum (fun i : Z => 0 <= i < hi - lo)
      (fun i => Znth (i + lo) s 48 - 48)).
  - apply sum_Z_range_ext. intros k Hk.
    rewrite Znth_sublist by lia. reflexivity.
  - rewrite <- (sum_Z_range_shift 0 (hi - lo) lo
      (fun j => Znth j s 48 - 48)).
    change (0 + lo) with lo.
    replace (hi - lo + lo) with hi by lia.
    reflexivity.
Qed.
Lemma decimal_fold_mod9__position_update :
  forall digits acc,
    fold_left (fun v c => 10 * v + (c - 48)) digits acc mod 9 =
    (acc + ListLib.sum (map (fun c => c - 48) digits)) mod 9.
Proof.
  induction digits as [|c digits IH]; intros acc; simpl.
  - replace (acc + 0) with acc by lia. reflexivity.
  - rewrite IH.
    change ((10 * acc + (c - 48) + ListLib.sum
      (map (fun c0 : Z => c0 - 48) digits)) mod 9 =
      (acc + (c - 48 + ListLib.sum
        (map (fun c0 : Z => c0 - 48) digits))) mod 9).
    replace (10 * acc + (c - 48) + ListLib.sum
      (map (fun c0 : Z => c0 - 48) digits))
      with ((acc + (c - 48) + ListLib.sum
        (map (fun c0 : Z => c0 - 48) digits)) + acc * 9) by ring.
    rewrite Z_mod_plus_full.
    f_equal. ring.
Qed.
Lemma decimal_sub_mod_prefix_difference__position_update :
  forall s prefix n lo hi,
    DigitPrefixSums s prefix n ->
    0 <= lo <= hi ->
    hi <= n ->
    n <= Zlength s ->
    DecimalSub s lo (hi - 1) mod 9 =
      (Znth hi prefix 0 - Znth lo prefix 0) mod 9.
Proof.
  intros s prefix n lo hi Hprefix Hlo Hhi Hn.
  unfold DigitPrefixSums in Hprefix.
  rewrite (Hprefix hi) by lia.
  rewrite (Hprefix lo) by lia.
  unfold DigitPrefixValue, DecimalSub.
  replace (hi - 1 + 1) with hi by lia.
  rewrite decimal_fold_mod9__position_update.
  rewrite digit_sublist_sum__position_update by lia.
  change ((sum_range lo (hi - 1) (fun j => Znth j s 48 - 48)) mod 9 =
    (sum_range 0 (hi - 1) (fun j => Znth j s 48 - 48) -
     sum_range 0 (lo - 1) (fun j => Znth j s 48 - 48)) mod 9).
  assert (Hsplit :
    sum_range 0 (hi - 1) (fun j => Znth j s 48 - 48) =
    sum_range 0 (lo - 1) (fun j => Znth j s 48 - 48) +
    sum_range lo (hi - 1) (fun j => Znth j s 48 - 48)).
  {
    unfold sum_range.
    replace (hi - 1 + 1) with hi by lia.
    replace (lo - 1 + 1) with lo by lia.
    apply sum_Z_range_split. lia.
  }
  rewrite Hsplit.
  f_equal. ring.
Qed.
Lemma current_window_start__position_update :
  forall s prefix n w i,
    n = Zlength s ->
    0 <= i ->
    1 <= w ->
    i + w <= n ->
    DigitPrefixSums s prefix n ->
    WindowStart s w (i + 1)
      ((Znth (i + w) prefix 0 - Znth i prefix 0) mod 9) (i + 1).
Proof.
  intros s prefix n w i Hn Hi Hw Hbound Hprefix.
  unfold WindowStart.
  repeat split; try lia.
  replace (i + 1 - 1) with i by lia.
  replace (i + 1 + w - 2) with (i + w - 1) by lia.
  apply decimal_sub_mod_prefix_difference__position_update
    with (n := n); try lia.
  exact Hprefix.
Qed.
Lemma window_start_old_to_new__position_update :
  forall s w i residue x,
    WindowStart s w i residue x ->
    WindowStart s w (i + 1) residue x.
Proof.
  intros s w i residue x H.
  unfold WindowStart in *.
  lia.
Qed.
Lemma window_start_extend_cases__position_update :
  forall s w i residue x,
    WindowStart s w (i + 1) residue x ->
    WindowStart s w i residue x \/ x = i + 1.
Proof.
  intros s w i residue x H.
  unfold WindowStart in *.
  destruct H as [[Hxlo Hxhi] [Hbound Hresidue]].
  destruct (Z.eq_dec x (i + 1)) as [-> | Hne].
  - right. reflexivity.
  - left. repeat split; try lia; assumption.
Qed.
Lemma window_start_other_residue_old__position_update :
  forall s w i residue current x,
    residue <> current ->
    WindowStart s w (i + 1) current (i + 1) ->
    WindowStart s w (i + 1) residue x ->
    WindowStart s w i residue x.
Proof.
  intros s w i residue current x Hne Hcurrent Hx.
  destruct (window_start_extend_cases__position_update
    s w i residue x Hx) as [Hold | ->]; [exact Hold |].
  unfold WindowStart in Hcurrent, Hx.
  destruct Hcurrent as [_ [_ Hcurrent]].
  destruct Hx as [_ [_ Hx]].
  congruence.
Qed.
Lemma first_window_start_preserve__position_update :
  forall s w i residue first,
    FirstWindowStart s w i residue first ->
    (forall x, WindowStart s w (i + 1) residue x ->
      WindowStart s w i residue x) ->
    FirstWindowStart s w (i + 1) residue first.
Proof.
  intros s w i residue first Hfirst Hback.
  unfold FirstWindowStart in *.
  destruct Hfirst as [[Hsentinel Hnone] | [Hfirst Hmin]].
  - left. split; [exact Hsentinel |].
    intros x Hx. apply (Hnone x). apply Hback. exact Hx.
  - right. split.
    + apply window_start_old_to_new__position_update. exact Hfirst.
    + intros x Hx. apply Hmin. apply Hback. exact Hx.
Qed.
Lemma second_window_start_preserve__position_update :
  forall s w i residue first second,
    SecondWindowStart s w i residue first second ->
    (forall x, WindowStart s w (i + 1) residue x ->
      WindowStart s w i residue x) ->
    SecondWindowStart s w (i + 1) residue first second.
Proof.
  intros s w i residue first second Hsecond Hback.
  unfold SecondWindowStart in *.
  destruct Hsecond as [[Hsentinel Honly] | [Hsecond [Hdistinct Hmin]]].
  - left. split; [exact Hsentinel |].
    intros x Hx. apply Honly. apply Hback. exact Hx.
  - right. split.
    + apply window_start_old_to_new__position_update. exact Hsecond.
    + split.
      * exact Hdistinct.
      * intros x Hx Hneq. apply Hmin; [apply Hback; exact Hx | exact Hneq].
Qed.
Lemma flat_positions_insert_first__position_update :
  forall s w i flat residue,
    Zlength flat = 18 ->
    0 <= residue < 9 ->
    FlatPositionsPrefix s w i flat ->
    WindowStart s w (i + 1) residue (i + 1) ->
    Znth (2 * residue) flat 0 < 0 ->
    FlatPositionsPrefix s w (i + 1)
      (replace_Znth (2 * residue) (i + 1) flat).
Proof.
  intros s w i flat residue Hlen Hresidue Hprefix Hcurrent Hslot.
  unfold FlatPositionsPrefix, PositionsPrefix in *.
  intros other Hother.
  specialize (Hprefix other Hother).
  rewrite flat_position_row_at__position_update in Hprefix by exact Hother.
  rewrite flat_position_row_at__position_update by exact Hother.
  change (FirstWindowStart s w i other (Znth (2 * other) flat (-1)) /\
    SecondWindowStart s w i other (Znth (2 * other) flat (-1))
      (Znth (2 * other + 1) flat (-1))) in Hprefix.
  change (FirstWindowStart s w (i + 1) other
      (Znth (2 * other) (replace_Znth (2 * residue) (i + 1) flat) (-1)) /\
    SecondWindowStart s w (i + 1) other
      (Znth (2 * other) (replace_Znth (2 * residue) (i + 1) flat) (-1))
      (Znth (2 * other + 1)
        (replace_Znth (2 * residue) (i + 1) flat) (-1))).
  destruct Hprefix as [Hfirst Hsecond].
  destruct (Z.eq_dec other residue) as [-> | Hne].
  - assert (Hfirst_bound : 0 <= 2 * residue < Zlength flat) by lia.
    assert (Hsecond_bound : 0 <= 2 * residue + 1 < Zlength flat) by lia.
    rewrite (@Znth_replace_Znth_Same Z (-1) flat (2 * residue)
      (i + 1) Hfirst_bound).
    rewrite (@Znth_replace_Znth_Diff Z (-1) flat (2 * residue)
      (2 * residue + 1) (i + 1) Hfirst_bound Hsecond_bound) by lia.
    assert (Hslot' : Znth (2 * residue) flat (-1) < 0).
    { rewrite (Znth_indep flat (2 * residue) (-1) 0) by lia.
      exact Hslot. }
    unfold FirstWindowStart in Hfirst.
    destruct Hfirst as [[Hempty Hnone] | [Hold _]].
    2: { unfold WindowStart in Hold. lia. }
    unfold SecondWindowStart in Hsecond.
    destruct Hsecond as [[Hsecond_empty _] | [Hsecond_old _]].
    2: { apply Hnone in Hsecond_old. contradiction. }
    split.
    + right. split; [exact Hcurrent |].
      intros x Hx.
      destruct (window_start_extend_cases__position_update
        s w i residue x Hx) as [Hxold | ->].
      * apply Hnone in Hxold. contradiction.
      * lia.
    + left. split; [exact Hsecond_empty |].
      intros x Hx.
      destruct (window_start_extend_cases__position_update
        s w i residue x Hx) as [Hxold | ->].
      * apply Hnone in Hxold. contradiction.
      * reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    rewrite Znth_replace_Znth_Diff by lia.
    split.
    + apply first_window_start_preserve__position_update; [exact Hfirst |].
      intros x Hx. eapply window_start_other_residue_old__position_update;
        eauto.
    + apply second_window_start_preserve__position_update; [exact Hsecond |].
      intros x Hx. eapply window_start_other_residue_old__position_update;
        eauto.
Qed.
Lemma flat_positions_insert_second__position_update :
  forall s w i flat residue,
    Zlength flat = 18 ->
    0 <= residue < 9 ->
    FlatPositionsPrefix s w i flat ->
    WindowStart s w (i + 1) residue (i + 1) ->
    0 <= Znth (2 * residue) flat 0 ->
    Znth (2 * residue + 1) flat 0 < 0 ->
    FlatPositionsPrefix s w (i + 1)
      (replace_Znth (2 * residue + 1) (i + 1) flat).
Proof.
  intros s w i flat residue Hlen Hresidue Hprefix Hcurrent
    Hfirst_slot Hsecond_slot.
  unfold FlatPositionsPrefix, PositionsPrefix in *.
  intros other Hother.
  specialize (Hprefix other Hother).
  rewrite flat_position_row_at__position_update in Hprefix by exact Hother.
  rewrite flat_position_row_at__position_update by exact Hother.
  change (FirstWindowStart s w i other (Znth (2 * other) flat (-1)) /\
    SecondWindowStart s w i other (Znth (2 * other) flat (-1))
      (Znth (2 * other + 1) flat (-1))) in Hprefix.
  change (FirstWindowStart s w (i + 1) other
      (Znth (2 * other)
        (replace_Znth (2 * residue + 1) (i + 1) flat) (-1)) /\
    SecondWindowStart s w (i + 1) other
      (Znth (2 * other)
        (replace_Znth (2 * residue + 1) (i + 1) flat) (-1))
      (Znth (2 * other + 1)
        (replace_Znth (2 * residue + 1) (i + 1) flat) (-1))).
  destruct Hprefix as [Hfirst Hsecond].
  destruct (Z.eq_dec other residue) as [-> | Hne].
  - assert (Hfirst_bound : 0 <= 2 * residue < Zlength flat) by lia.
    assert (Hsecond_bound : 0 <= 2 * residue + 1 < Zlength flat) by lia.
    rewrite (@Znth_replace_Znth_Diff Z (-1) flat (2 * residue + 1)
      (2 * residue) (i + 1) Hsecond_bound Hfirst_bound) by lia.
    rewrite (@Znth_replace_Znth_Same Z (-1) flat (2 * residue + 1)
      (i + 1) Hsecond_bound).
    assert (Hfirst_slot' : 0 <= Znth (2 * residue) flat (-1)).
    { rewrite (Znth_indep flat (2 * residue) (-1) 0) by lia.
      exact Hfirst_slot. }
    assert (Hsecond_slot' : Znth (2 * residue + 1) flat (-1) < 0).
    { rewrite (Znth_indep flat (2 * residue + 1) (-1) 0) by lia.
      exact Hsecond_slot. }
    unfold FirstWindowStart in Hfirst.
    destruct Hfirst as [[Hempty _] | [Hfirst_start Hfirst_min]].
    { lia. }
    unfold SecondWindowStart in Hsecond.
    destruct Hsecond as [[Hsecond_empty Honly] |
      [Hsecond_start [Hdistinct Hsecond_min]]].
    2: { unfold WindowStart in Hsecond_start. lia. }
    split.
    + right. split.
      * apply window_start_old_to_new__position_update. exact Hfirst_start.
      * intros x Hx.
        destruct (window_start_extend_cases__position_update
          s w i residue x Hx) as [Hxold | ->].
        -- apply Hfirst_min. exact Hxold.
        -- unfold WindowStart in Hfirst_start. lia.
    + right. split; [exact Hcurrent |].
      split.
      * unfold WindowStart in Hfirst_start. lia.
      * intros x Hx Hneq.
        destruct (window_start_extend_cases__position_update
          s w i residue x Hx) as [Hxold | ->].
        -- specialize (Honly x Hxold). contradiction.
        -- lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    rewrite Znth_replace_Znth_Diff by lia.
    split.
    + apply first_window_start_preserve__position_update; [exact Hfirst |].
      intros x Hx. eapply window_start_other_residue_old__position_update;
        eauto.
    + apply second_window_start_preserve__position_update; [exact Hsecond |].
      intros x Hx. eapply window_start_other_residue_old__position_update;
        eauto.
Qed.
Lemma flat_positions_skip_full__position_update :
  forall s w i flat residue,
    Zlength flat = 18 ->
    0 <= residue < 9 ->
    FlatPositionsPrefix s w i flat ->
    WindowStart s w (i + 1) residue (i + 1) ->
    0 <= Znth (2 * residue) flat 0 ->
    0 <= Znth (2 * residue + 1) flat 0 ->
    FlatPositionsPrefix s w (i + 1) flat.
Proof.
  intros s w i flat residue Hlen Hresidue Hprefix Hcurrent
    Hfirst_slot Hsecond_slot.
  unfold FlatPositionsPrefix, PositionsPrefix in *.
  intros other Hother.
  specialize (Hprefix other Hother).
  rewrite flat_position_row_at__position_update in Hprefix by exact Hother.
  rewrite flat_position_row_at__position_update by exact Hother.
  change (FirstWindowStart s w i other (Znth (2 * other) flat (-1)) /\
    SecondWindowStart s w i other (Znth (2 * other) flat (-1))
      (Znth (2 * other + 1) flat (-1))) in Hprefix.
  change (FirstWindowStart s w (i + 1) other
      (Znth (2 * other) flat (-1)) /\
    SecondWindowStart s w (i + 1) other
      (Znth (2 * other) flat (-1)) (Znth (2 * other + 1) flat (-1))).
  destruct Hprefix as [Hfirst Hsecond].
  destruct (Z.eq_dec other residue) as [-> | Hne].
  - assert (Hfirst_slot' : 0 <= Znth (2 * residue) flat (-1)).
    { rewrite (Znth_indep flat (2 * residue) (-1) 0) by lia.
      exact Hfirst_slot. }
    assert (Hsecond_slot' : 0 <= Znth (2 * residue + 1) flat (-1)).
    { rewrite (Znth_indep flat (2 * residue + 1) (-1) 0) by lia.
      exact Hsecond_slot. }
    unfold FirstWindowStart in Hfirst.
    destruct Hfirst as [[Hempty _] | [Hfirst_start Hfirst_min]].
    { lia. }
    unfold SecondWindowStart in Hsecond.
    destruct Hsecond as [[Hempty _] |
      [Hsecond_start [Hdistinct Hsecond_min]]].
    { lia. }
    split.
    + right. split.
      * apply window_start_old_to_new__position_update. exact Hfirst_start.
      * intros x Hx.
        destruct (window_start_extend_cases__position_update
          s w i residue x Hx) as [Hxold | ->].
        -- apply Hfirst_min. exact Hxold.
        -- unfold WindowStart in Hfirst_start. lia.
    + right. split.
      * apply window_start_old_to_new__position_update. exact Hsecond_start.
      * split; [exact Hdistinct |].
        intros x Hx Hneq.
        destruct (window_start_extend_cases__position_update
          s w i residue x Hx) as [Hxold | ->].
        -- apply Hsecond_min; assumption.
        -- unfold WindowStart in Hsecond_start. lia.
  - split.
    + apply first_window_start_preserve__position_update; [exact Hfirst |].
      intros x Hx. eapply window_start_other_residue_old__position_update;
        eauto.
    + apply second_window_start_preserve__position_update; [exact Hsecond |].
      intros x Hx. eapply window_start_other_residue_old__position_update;
        eauto.
Qed.
Lemma query_output_prefix_nil__query_setup :
  forall w s qs,
    QueryOutputPrefix w s qs 0 nil nil.
Proof.
  intros w s qs.
  unfold QueryOutputPrefix, Spec.
  exists (@nil (Z * Z)).
  repeat split; simpl; try constructor; try lia.
Qed.
Lemma query_best_prefix_zero__query_setup :
  forall s w q,
    QueryBestPrefix s w q 0 1073741824 1073741824.
Proof.
  intros s w q.
  unfold QueryBestPrefix.
  left.
  repeat split; try reflexivity.
  intros candidate Hcandidate.
  unfold PrefixEligiblePair in Hcandidate.
  destruct Hcandidate as [_ [Hlo Hlt]].
  lia.
Qed.
Lemma decimal_fold_digit_sum_mod9__query_choose_candidate :
  forall (digits : list Z) (acc : Z),
    fold_left (fun value digit => 10 * value + (digit - 48)) digits acc mod 9 =
    (acc + ListLib.sum (map (fun digit => digit - 48) digits)) mod 9.
Proof.
  induction digits as [|digit digits IH]; intros acc.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - simpl.
    rewrite IH.
    change ((10 * acc + (digit - 48) +
      ListLib.sum (map (fun digit0 : Z => digit0 - 48) digits)) mod 9 =
      (acc + (digit - 48 +
      ListLib.sum (map (fun digit0 : Z => digit0 - 48) digits))) mod 9).
    replace (10 * acc + (digit - 48) +
      ListLib.sum (map (fun digit0 : Z => digit0 - 48) digits))
      with ((acc + (digit - 48) +
        ListLib.sum (map (fun digit0 : Z => digit0 - 48) digits)) + acc * 9)
      by ring.
    rewrite Z_mod_plus_full.
    f_equal.
    ring.
Qed.
Lemma query_pair_window_starts__query_choose_candidate :
  forall (s : list Z) w l r k v x y,
    DecimalSub s (l - 1) (r - 1) mod 9 = v ->
    QueryPair s w ((l, r), k) (x, y) ->
    WindowStart s w (Zlength s - w + 1)
      (PairFirstResidue s w (x, y)) x /\
    WindowStart s w (Zlength s - w + 1)
      ((k - PairFirstResidue s w (x, y) * v) mod 9) y.
Proof.
  intros s w l r k v x y Hquery Hpair.
  unfold QueryPair in Hpair; cbn in Hpair.
  destruct Hpair as (Hxlo & Hxhi & Hylo & Hyhi & Hxy & Hmod).
  unfold PairFirstResidue; cbn.
  split.
  - unfold WindowStart.
    repeat split; try lia.
  - unfold WindowStart.
    repeat split; try lia.
    rewrite <- Hmod.
    rewrite Zminus_mod.
    rewrite Zmod_mod.
    rewrite <- Hquery.
    rewrite <- Zmult_mod.
    rewrite <- Zminus_mod.
    ring_simplify.
    f_equal.
    ring.
Qed.
Lemma query_pair_from_window_starts__query_choose_candidate :
  forall (s : list Z) w l r k v a b x y,
    0 <= k < 9 ->
    DecimalSub s (l - 1) (r - 1) mod 9 = v ->
    b = (k - a * v) mod 9 ->
    WindowStart s w (Zlength s - w + 1) a x ->
    WindowStart s w (Zlength s - w + 1) b y ->
    x <> y ->
    QueryPair s w ((l, r), k) (x, y).
Proof.
  intros s w l r k v a b x y Hk Hquery Hb Hx Hy Hxy.
  unfold WindowStart in Hx, Hy.
  destruct Hx as (Hxlo & Hxupper & Hxres).
  destruct Hy as (Hylo & Hyupper & Hyres).
  unfold QueryPair; cbn.
  repeat split; try lia.
  rewrite Z.add_mod by lia.
  rewrite Z.mul_mod by lia.
  rewrite Hxres, Hquery, Hyres, Hb.
  rewrite <- Z.add_mod by lia.
  replace (a * v + (k - a * v)) with k by ring.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.
Lemma query_best_prefix_step_select__query_choose_candidate :
  forall (s : list Z) w l r k v a b old1 old2 x y,
    0 <= a < 9 ->
    0 <= b < 9 ->
    0 <= k < 9 ->
    DecimalSub s (l - 1) (r - 1) mod 9 = v ->
    b = (k - a * v) mod 9 ->
    QueryBestPrefix s w ((l, r), k) a old1 old2 ->
    FirstWindowStart s w (Zlength s - w + 1) a x ->
    ((a <> b /\
       FirstWindowStart s w (Zlength s - w + 1) b y) \/
     (a = b /\
       SecondWindowStart s w (Zlength s - w + 1) a x y)) ->
    0 <= x ->
    0 <= y ->
    (x < old1 \/ x = old1 /\ y < old2) ->
    QueryBestPrefix s w ((l, r), k) (a + 1) x y.
Proof.
  intros s w l r k v a b old1 old2 x y
    Ha Hbnd Hk Hquery Hb Hbest HfirstA Hchoice Hxnonneg Hynonneg Hbetter.
  destruct HfirstA as [[Hxsentinel Hxnone] | [Hxwindow Hxmin]]; [lia |].
  assert (Hselected_pair : QueryPair s w ((l, r), k) (x, y)).
  {
    destruct Hchoice as [[Hab HfirstB] | [Hab Hsecond]].
    - destruct HfirstB as [[Hysentinel Hynone] | [Hywindow Hymin]]; [lia |].
      apply (query_pair_from_window_starts__query_choose_candidate
        s w l r k v a b x y Hk Hquery Hb Hxwindow Hywindow).
      intro Heq; subst y.
      unfold WindowStart in Hxwindow, Hywindow.
      destruct Hxwindow as (_ & _ & Hxres).
      destruct Hywindow as (_ & _ & Hyres).
      lia.
    - assert (Hba : a = (k - a * v) mod 9) by (transitivity b; assumption).
      subst b.
      destruct Hsecond as [[Hysentinel Hynone] |
        [Hywindow [Hyneq Hymin]]]; [lia |].
      apply (query_pair_from_window_starts__query_choose_candidate
        s w l r k v a a x y Hk Hquery Hba Hxwindow Hywindow).
      congruence.
  }
  assert (Hselected_eligible :
    PrefixEligiblePair s w ((l, r), k) (a + 1) (x, y)).
  {
    split; [exact Hselected_pair |].
    unfold PairFirstResidue; cbn.
    unfold WindowStart in Hxwindow.
    destruct Hxwindow as (_ & _ & Hxres).
    rewrite Hxres.
    lia.
  }
  unfold QueryBestPrefix.
  right.
  unfold min_value_of_subset, min_object_of_subset.
  exists (x, y).
  split.
  - split; [exact Hselected_eligible |].
    intros [px py] Heligible.
    destruct Heligible as [Hpair [Hreslo Hreslt]].
    assert (Hrescases :
      PairFirstResidue s w (px, py) < a \/
      PairFirstResidue s w (px, py) = a) by lia.
    destruct Hrescases as [Hprior | Hcurrent].
    + assert (Hprior_eligible :
        PrefixEligiblePair s w ((l, r), k) a (px, py)).
      { split; [exact Hpair |]. lia. }
      destruct Hbest as [[_ [_ Hnone]] |
        [old [Holdobject Holdvalue]]].
      * exfalso. exact (Hnone (px, py) Hprior_eligible).
      * destruct Holdobject as [Holdeligible Holdminimal].
        unfold id in Holdvalue.
        subst old.
        specialize (Holdminimal (px, py) Hprior_eligible).
        unfold PairLexLe in *; cbn in *.
        destruct Hbetter as [Hbetter | [Hxeq Hylt]];
          destruct Holdminimal as [Holdminimal | [Holdxeq Holdy]];
          lia.
    + pose proof (query_pair_window_starts__query_choose_candidate
        s w l r k v px py Hquery Hpair) as [Hpxwindow Hpywindow].
      rewrite Hcurrent in Hpxwindow, Hpywindow.
      rewrite <- Hb in Hpywindow.
      specialize (Hxmin px Hpxwindow).
      unfold PairLexLe; cbn.
      destruct (Z_lt_ge_dec x px) as [Hxp | Hpx].
      * left; exact Hxp.
      * assert (Hxpeq : x = px) by lia.
        right; split; [exact Hxpeq |].
        destruct Hchoice as [[Hab HfirstB] | [Hab Hsecond]].
        -- destruct HfirstB as [[Hysentinel Hynone] |
             [Hywindow Hymin]]; [lia |].
           apply Hymin; exact Hpywindow.
        -- rewrite <- Hab in Hpywindow.
           destruct Hsecond as [[Hysentinel Hynone] |
             [Hywindow [Hyneq Hymin]]]; [lia |].
           apply Hymin; [exact Hpywindow |].
           unfold QueryPair in Hpair; cbn in Hpair.
           destruct Hpair as (_ & _ & _ & _ & Hpxpy & _).
           congruence.
  - reflexivity.
Qed.
Lemma flat_positions_starts__query_choose_candidate :
  forall (s flat : list Z) w starts_done residue,
    Zlength flat = 18 ->
    0 <= residue < 9 ->
    FlatPositionsPrefix s w starts_done flat ->
    FirstWindowStart s w starts_done residue (Znth (2 * residue) flat 0) /\
    SecondWindowStart s w starts_done residue
      (Znth (2 * residue) flat 0) (Znth (2 * residue + 1) flat 0).
Proof.
  intros s flat w starts_done residue Hlen Hresidue Hpositions.
  unfold FlatPositionsPrefix, PositionsPrefix in Hpositions.
  specialize (Hpositions residue Hresidue).
  unfold FlatPositionRows in Hpositions.
  assert (Hcases : residue = 0 \/ residue = 1 \/ residue = 2 \/
    residue = 3 \/ residue = 4 \/ residue = 5 \/ residue = 6 \/
    residue = 7 \/ residue = 8) by lia.
  destruct Hcases as
    [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    cbn [Zrange Zrange_aux] in Hpositions |-;
    repeat rewrite (Znth_indep flat _ 0 (-1)) by (rewrite Hlen; lia);
    exact Hpositions.
Qed.
Lemma digit_sum_sublist_as_prefix_difference__query_choose_candidate :
  forall (s : list Z) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength s ->
    ListLib.sum (map (fun digit => digit - 48) (sublist lo hi s)) =
    DigitPrefixValue s hi - DigitPrefixValue s lo.
Proof.
  intros s lo hi Hlo Hhi.
  rewrite (SumLib.ZRange.list_sum_map_as_Z_range_sum 48).
  rewrite Zlength_sublist by lia.
  transitivity
    (SumLib.Sum.sum (fun i => lo <= i < hi)
      (fun i => Znth i s 48 - 48)).
  - pose proof (SumLib.ZRange.sum_Z_range_shift 0 (hi - lo) lo
      (fun i => Znth i s 48 - 48)) as Hshift.
    replace (0 + lo) with lo in Hshift by lia.
    replace (hi - lo + lo) with hi in Hshift by lia.
    rewrite Hshift.
    apply SumLib.ZRange.sum_Z_range_ext.
    intros i Hi.
    rewrite Znth_sublist by lia.
    reflexivity.
  - unfold DigitPrefixValue, sum_range.
    replace (hi - 1 + 1) with hi by lia.
    replace (lo - 1 + 1) with lo by lia.
    rewrite (SumLib.ZRange.sum_Z_range_split 0 lo hi) by lia.
    ring.
Qed.
Lemma decimal_sub_query_mod9__query_choose_candidate :
  forall (s prefix : list Z) n l r v,
    n = Zlength s ->
    1 <= l <= r ->
    r <= n ->
    DigitPrefixSums s prefix n ->
    v = (Znth r prefix 0 - Znth (l - 1) prefix 0) mod 9 ->
    DecimalSub s (l - 1) (r - 1) mod 9 = v.
Proof.
  intros s prefix n l r v Hn Hlr Hrn Hprefix Hv.
  unfold DecimalSub.
  rewrite decimal_fold_digit_sum_mod9__query_choose_candidate.
  rewrite digit_sum_sublist_as_prefix_difference__query_choose_candidate
    by (subst n; lia).
  unfold DigitPrefixSums in Hprefix.
  replace (r - 1 + 1) with r by lia.
  rewrite <- (Hprefix r) by lia.
  rewrite <- (Hprefix (l - 1)) by lia.
  rewrite Z.add_0_l.
  symmetry.
  exact Hv.
Qed.
Lemma rem9_nonnegative_normalize__query_choose_candidate :
  forall x, 0 <= Z.rem x 9 -> Z.rem x 9 = x mod 9.
Proof.
  intros x Hrem.
  destruct (Z_le_gt_dec 0 x) as [Hx | Hx].
  - apply Z.rem_mod_nonneg; lia.
  - pose proof (Z.rem_nonpos x 9 ltac:(lia) ltac:(lia)) as Hnonpos.
    assert (Hzero : Z.rem x 9 = 0) by lia.
    rewrite Hzero.
    symmetry.
    apply (proj1 (Z.rem_mod_eq_0 x 9 ltac:(lia))).
    exact Hzero.
Qed.
Lemma rem9_negative_normalize__query_choose_candidate :
  forall x, Z.rem x 9 < 0 -> Z.rem x 9 + 9 = x mod 9.
Proof.
  intros x Hrem.
  assert (Hx : x < 0).
  { destruct (Z_le_gt_dec 0 x); [|lia].
    pose proof (Z.rem_nonneg x 9 ltac:(lia) ltac:(lia)); lia. }
  assert (Hopprem : Z.rem x 9 = - Z.rem (-x) 9).
  { rewrite <- (Z.opp_involutive x) at 1.
    rewrite Z.rem_opp_l by lia.
    reflexivity. }
  assert (Hposrem : Z.rem (-x) 9 = (-x) mod 9).
  { apply Z.rem_mod_nonneg; lia. }
  assert (Hnz : (-x) mod 9 <> 0) by (intro Hz; lia).
  pose proof (Z.mod_opp_l_nz (-x) 9 ltac:(lia) Hnz) as Hoppmod.
  replace (- - x) with x in Hoppmod by ring.
  change (x mod 9 = 9 - ((-x) mod 9)) in Hoppmod.
  lia.
Qed.
Lemma decimal_sub_query_rem9__query_choose_candidate :
  forall (s prefix : list Z) n l r v,
    n = Zlength s ->
    1 <= l <= r ->
    r <= n ->
    DigitPrefixSums s prefix n ->
    (forall lo hi,
      0 <= lo <= hi /\ hi <= n ->
      0 <= Znth hi prefix 0 - Znth lo prefix 0 <= 9 * (hi - lo)) ->
    v = Z.rem (Znth r prefix 0 - Znth (l - 1) prefix 0) 9 ->
    DecimalSub s (l - 1) (r - 1) mod 9 = v.
Proof.
  intros s prefix n l r v Hn Hlr Hrn Hprefix Hbounds Hv.
  eapply decimal_sub_query_mod9__query_choose_candidate;
    [exact Hn | exact Hlr | exact Hrn | exact Hprefix |].
  pose proof (Hbounds (l - 1) r ltac:(lia)) as Hdiff.
  rewrite <- Z.rem_mod_nonneg by lia.
  exact Hv.
Qed.
Lemma Zlength_map__query_preserve_low :
  forall {A B : Type} (f : A -> B) xs,
    Zlength (map f xs) = Zlength xs.
Proof.
  intros A B f xs.
  rewrite !Zlength_correct, length_map.
  reflexivity.
Qed.
Lemma Znth_map__query_preserve_low :
  forall {A B : Type} (f : A -> B) xs (da : A) (db : B) i,
    0 <= i < Zlength xs ->
    Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs.
  induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi.
    lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl.
      rewrite !Znth0_cons.
      reflexivity.
    + simpl.
      rewrite !Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hi.
      lia.
Qed.
Lemma Zlength_Zrange_aux__query_preserve_low :
  forall low m,
    Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m.
  revert low.
  induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH.
    lia.
Qed.
Lemma Zlength_Zrange__query_preserve_low :
  forall low high,
    low <= high ->
    Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle.
  unfold Zrange.
  rewrite Zlength_Zrange_aux__query_preserve_low.
  lia.
Qed.
Lemma Znth_Zrange_aux__query_preserve_low :
  forall m low i,
    0 <= i < Z.of_nat m ->
    Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl.
  destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons.
    lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia).
    lia.
Qed.
Lemma Znth_Zrange__query_preserve_low :
  forall low high i,
    low <= high ->
    0 <= i < high - low ->
    Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi.
  unfold Zrange.
  rewrite Znth_Zrange_aux__query_preserve_low by lia.
  lia.
Qed.
Lemma flat_position_row__query_preserve_low :
  forall flat residue,
    0 <= residue < 9 ->
    Znth residue (FlatPositionRows flat) nil =
      Znth (2 * residue) flat (-1) ::
      Znth (2 * residue + 1) flat (-1) :: nil.
Proof.
  intros flat residue Hresidue.
  unfold FlatPositionRows.
  rewrite (@Znth_map__query_preserve_low Z (list Z)
    (fun r =>
      Znth (2 * r) flat (-1) ::
      Znth (2 * r + 1) flat (-1) :: nil)
    (Zrange 0 9) 0 nil residue).
  - rewrite Znth_Zrange__query_preserve_low by lia.
    replace (0 + residue) with residue by lia.
    reflexivity.
  - rewrite Zlength_Zrange__query_preserve_low by lia.
    lia.
Qed.
Lemma flat_positions_slots__query_preserve_low :
  forall s w starts flat residue,
    FlatPositionsPrefix s w starts flat ->
    0 <= residue < 9 ->
    FirstWindowStart s w starts residue
      (Znth (2 * residue) flat (-1)) /\
    SecondWindowStart s w starts residue
      (Znth (2 * residue) flat (-1))
      (Znth (2 * residue + 1) flat (-1)).
Proof.
  intros s w starts flat residue Hpositions Hresidue.
  unfold FlatPositionsPrefix, PositionsPrefix in Hpositions.
  specialize (Hpositions residue Hresidue).
  rewrite flat_position_row__query_preserve_low in Hpositions by exact Hresidue.
  cbn in Hpositions.
  exact Hpositions.
Qed.
Lemma Znth_default_irrelevant__query_preserve_low :
  forall (xs : list Z) i d1 d2,
    0 <= i < Zlength xs ->
    Znth i xs d1 = Znth i xs d2.
Proof.
  intros xs i d1 d2 Hi.
  apply Znth_indep.
  exact Hi.
Qed.
Lemma flat_positions_first_le__query_preserve_low :
  forall s w starts flat residue x,
    Zlength flat = 18 ->
    FlatPositionsPrefix s w starts flat ->
    0 <= residue < 9 ->
    0 <= Znth (2 * residue) flat 0 ->
    WindowStart s w starts residue x ->
    Znth (2 * residue) flat 0 <= x.
Proof.
  intros s w starts flat residue x Hlen Hpositions Hresidue
    Hnonneg Hx.
  pose proof (flat_positions_slots__query_preserve_low
    s w starts flat residue Hpositions Hresidue) as [Hfirst Hsecond].
  assert (Hidx : 0 <= 2 * residue < Zlength flat) by lia.
  assert (Hdefault : Znth (2 * residue) flat (-1) =
      Znth (2 * residue) flat 0).
  { symmetry.
    apply Znth_default_irrelevant__query_preserve_low.
    exact Hidx. }
  rewrite Hdefault in Hfirst.
  unfold FirstWindowStart in Hfirst.
  destruct Hfirst as [[Hsentinel Hnone] | [Hstored Hleast]].
  - lia.
  - apply Hleast.
    exact Hx.
Qed.
Lemma flat_positions_second_le__query_preserve_low :
  forall s w starts flat residue first x,
    Zlength flat = 18 ->
    FlatPositionsPrefix s w starts flat ->
    0 <= residue < 9 ->
    first = Znth (2 * residue) flat 0 ->
    0 <= Znth (2 * residue + 1) flat 0 ->
    WindowStart s w starts residue x ->
    x <> first ->
    Znth (2 * residue + 1) flat 0 <= x.
Proof.
  intros s w starts flat residue first x Hlen Hpositions Hresidue
    Hfirst_eq Hnonneg Hx Hdistinct.
  pose proof (flat_positions_slots__query_preserve_low
    s w starts flat residue Hpositions Hresidue) as [Hfirst Hsecond].
  assert (Hidx0 : 0 <= 2 * residue < Zlength flat) by lia.
  assert (Hidx1 : 0 <= 2 * residue + 1 < Zlength flat) by lia.
  assert (Hdefault0 : Znth (2 * residue) flat (-1) =
      Znth (2 * residue) flat 0).
  { symmetry.
    apply Znth_default_irrelevant__query_preserve_low.
    exact Hidx0. }
  assert (Hdefault1 : Znth (2 * residue + 1) flat (-1) =
      Znth (2 * residue + 1) flat 0).
  { symmetry.
    apply Znth_default_irrelevant__query_preserve_low.
    exact Hidx1. }
  rewrite Hdefault0, Hdefault1 in Hsecond.
  unfold SecondWindowStart in Hsecond.
  destruct Hsecond as [[Hsentinel Hall_first] |
    [Hstored [Hstored_distinct Hleast]]].
  - lia.
  - apply Hleast; [exact Hx |].
    rewrite <- Hfirst_eq.
    exact Hdistinct.
Qed.
Lemma map_sublist__query_preserve_low :
  forall {A B : Type} (f : A -> B) xs lo hi,
    map f (sublist lo hi xs) = sublist lo hi (map f xs).
Proof.
  intros A B f xs lo hi.
  unfold sublist.
  rewrite firstn_map, skipn_map.
  reflexivity.
Qed.
Lemma decimal_fold_mod9__query_preserve_low :
  forall xs acc,
    fold_left (fun value digit => 10 * value + (digit - 48)) xs acc mod 9 =
    (acc + ListLib.sum (map (fun digit => digit - 48) xs)) mod 9.
Proof.
  induction xs as [|digit xs IH]; intros acc; simpl.
  - rewrite Z.add_0_r.
    reflexivity.
  - rewrite IH.
    remember (ListLib.sum (map (fun digit0 : Z => digit0 - 48) xs))
      as total.
    change ((10 * acc + (digit - 48) + total) mod 9 =
      (acc + ((digit - 48) + total)) mod 9).
    replace (10 * acc + (digit - 48) + total)
      with ((acc + ((digit - 48) + total)) + acc * 9) by ring.
    rewrite Z.add_mod by lia.
    rewrite Z.mod_mul by lia.
    rewrite Z.add_0_r, Z.mod_mod by lia.
    reflexivity.
Qed.
Lemma decimal_sub_mod9_prefix_value__query_preserve_low :
  forall s lo hi,
    0 <= lo <= hi + 1 ->
    hi + 1 <= Zlength s ->
    DecimalSub s lo hi mod 9 =
      (DigitPrefixValue s (hi + 1) - DigitPrefixValue s lo) mod 9.
Proof.
  intros s lo hi Hlo Hhi.
  unfold DecimalSub.
  rewrite decimal_fold_mod9__query_preserve_low.
  rewrite Z.add_0_l.
  rewrite map_sublist__query_preserve_low.
  rewrite list_sum_sublist_as_Z_range_sum.
  2: lia.
  2: { rewrite Zlength_map__query_preserve_low. lia. }
  rewrite sum_Z_range_ext with
    (g := fun i => Znth i s 48 - 48).
  2: {
    intros i Hi.
    rewrite (@Znth_map__query_preserve_low Z Z
      (fun digit => digit - 48) s 48 0 i) by lia.
    reflexivity.
  }
  unfold DigitPrefixValue.
  replace (hi + 1 - 1) with hi by lia.
  unfold sum_range.
  replace (lo - 1 + 1) with lo by lia.
  rewrite (sum_Z_range_split 0 lo (hi + 1)
    (fun i => Znth i s 48 - 48)) by lia.
  f_equal.
  ring.
Qed.
Lemma nonnegative_rem_eq_mod9__query_preserve_low :
  forall x,
    0 <= Z.rem x 9 ->
    Z.rem x 9 = x mod 9.
Proof.
  intros x Hrem.
  destruct (Z_le_gt_dec 0 x) as [Hx | Hx].
  - apply Z.rem_mod_nonneg; lia.
  - assert (Z.rem x 9 <= 0) by (apply Z.rem_nonpos; lia).
    assert (Z.rem x 9 = 0) by lia.
    assert (x mod 9 = 0).
    { apply (proj1 (Zrem_Zmod_zero x 9 ltac:(lia))).
      assumption. }
    lia.
Qed.
Lemma negative_rem_plus_eq_mod9__query_preserve_low :
  forall x,
    Z.rem x 9 < 0 ->
    Z.rem x 9 + 9 = x mod 9.
Proof.
  intros x Hnegative.
  pose proof (Z.rem_bound_abs x 9 ltac:(lia)) as Hbound.
  apply Z.abs_lt in Hbound.
  assert (Hsmall : 0 <= Z.rem x 9 + 9 < 9) by lia.
  assert (Hnormalized :
    (Z.rem x 9 + 9) mod 9 = x mod 9).
  {
    pose proof (Z.quot_rem x 9 ltac:(lia)) as Hquotrem.
    replace (Z.rem x 9 + 9)
      with (x + (1 - Z.quot x 9) * 9) by lia.
    apply Z.mod_add.
    lia.
  }
  rewrite Z.mod_small in Hnormalized by exact Hsmall.
  exact Hnormalized.
Qed.
Lemma second_residue_from_query_equation__query_preserve_low :
  forall dx dq dy k a v,
    (dx * dq + dy) mod 9 = k ->
    dx mod 9 = a ->
    dq mod 9 = v ->
    dy mod 9 = (k - a * v) mod 9.
Proof.
  intros dx dq dy k a v Heq Hdx Hdq.
  subst k a v.
  replace
    ((dx * dq + dy) mod 9 - (dx mod 9) * (dq mod 9))
    with
    ((dx * dq + dy) mod 9 + (- ((dx mod 9) * (dq mod 9))))
    by ring.
  rewrite Z.add_mod_idemp_l by lia.
  pose proof (Z.div_mod dx 9 ltac:(lia)) as Hdx_div.
  pose proof (Z.div_mod dq 9 ltac:(lia)) as Hdq_div.
  replace
    (dx * dq + dy + - ((dx mod 9) * (dq mod 9)))
    with
    (dy +
      (9 * (dx / 9) * (dq / 9) +
       (dx / 9) * (dq mod 9) +
       (dq / 9) * (dx mod 9)) * 9) by nia.
  symmetry.
  apply Z.mod_add.
  lia.
Qed.
Lemma query_pair_window_residues__query_preserve_low :
  forall s prefix n w l r k v x y a,
    n = Zlength s ->
    1 <= l ->
    l <= r ->
    r <= n ->
    DigitPrefixSums s prefix n ->
    v = (Znth r prefix 0 - Znth (l - 1) prefix 0) mod 9 ->
    0 <= a < 9 ->
    QueryPair s w (l, r, k) (x, y) ->
    PairFirstResidue s w (x, y) = a ->
    WindowStart s w (n - w + 1) a x /\
    WindowStart s w (n - w + 1) ((k - a * v) mod 9) y.
Proof.
  intros s prefix n w l r k v x y a Hn Hl Hlr Hrn Hprefix
    Hv Ha Hpair Hxresidue.
  unfold QueryPair in Hpair.
  cbn in Hpair.
  destruct Hpair as
    [Hxlo [Hxhi [Hylo [Hyhi [Hxy Hquery]]]]].
  assert (Hlminus : 0 <= l - 1 <= n) by lia.
  assert (Hr : 0 <= r <= n) by lia.
  pose proof (Hprefix (l - 1) Hlminus) as Hpref_l.
  pose proof (Hprefix r Hr) as Hpref_r.
  assert (Hdq : DecimalSub s (l - 1) (r - 1) mod 9 = v).
  {
    rewrite decimal_sub_mod9_prefix_value__query_preserve_low by lia.
    replace (r - 1 + 1) with r by lia.
    rewrite <- Hpref_r, <- Hpref_l.
    symmetry.
    exact Hv.
  }
  assert (Hxmod : DecimalSub s (x - 1) (x + w - 2) mod 9 = a).
  { exact Hxresidue. }
  split.
  - unfold WindowStart.
    repeat split; eauto; try lia.
  - unfold WindowStart.
    repeat split; try lia.
    eapply second_residue_from_query_equation__query_preserve_low;
      eauto.
Qed.
Lemma query_best_prefix_step_preserve__query_preserve_low :
  forall s w q a best1 best2,
    QueryBestPrefix s w q a best1 best2 ->
    (forall candidate,
      PrefixEligiblePair s w q (a + 1) candidate ->
      fst candidate < 1073741824) ->
    (forall candidate,
      PrefixEligiblePair s w q (a + 1) candidate ->
      ~ PrefixEligiblePair s w q a candidate ->
      PairLexLe (best1, best2) candidate) ->
    QueryBestPrefix s w q (a + 1) best1 best2.
Proof.
  intros s w q a best1 best2 Hbest Hbound Hnew.
  unfold QueryBestPrefix in Hbest |- *.
  destruct Hbest as
    [[Hbest1 [Hbest2 Hnone]] |
     [old_candidate [[Hold Hleast] Heq]]].
  - left.
    split; [exact Hbest1 |].
    split; [exact Hbest2 |].
    intros candidate Hcandidate.
    specialize (Hbound candidate Hcandidate).
    assert (Hnot_old : ~ PrefixEligiblePair s w q a candidate).
    { intro Hold.
      apply (Hnone candidate).
      exact Hold. }
    specialize (Hnew candidate Hcandidate Hnot_old).
    rewrite Hbest1, Hbest2 in Hnew.
    unfold PairLexLe in Hnew.
    simpl in Hnew.
    lia.
  - right.
    exists old_candidate.
    split.
    + split.
      * unfold PrefixEligiblePair in Hold |- *.
        destruct Hold as [Hpair Hresidue].
        split; [exact Hpair | lia].
      * intros candidate Hcandidate.
        destruct (classic (PrefixEligiblePair s w q a candidate)) as
          [Hcandidate_old | Hcandidate_new].
        -- apply Hleast.
           exact Hcandidate_old.
        -- rewrite Heq.
           apply Hnew; assumption.
    + exact Heq.
Qed.
Lemma flat_position_row__query_preserve_high :
  forall flat residue,
    0 <= residue < 9 ->
    Znth residue (FlatPositionRows flat) nil =
      Znth (2 * residue) flat (-1) ::
      Znth (2 * residue + 1) flat (-1) :: nil.
Proof.
  intros flat residue Hresidue.
  assert (Hcases :
    residue = 0 \/ residue = 1 \/ residue = 2 \/ residue = 3 \/
    residue = 4 \/ residue = 5 \/ residue = 6 \/ residue = 7 \/
    residue = 8) by lia.
  destruct Hcases as
    [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    reflexivity.
Qed.
Lemma decimal_fold_mod9__query_preserve_high :
  forall xs acc,
    Z.modulo
      (fold_left (fun value digit => 10 * value + (digit - 48)) xs acc) 9 =
    Z.modulo (acc + ListLib.sum xs - 48 * Z.of_nat (length xs)) 9.
Proof.
  induction xs as [|digit xs IH]; intros acc.
  - change (Z.modulo acc 9 = Z.modulo (acc + 0 - 0) 9).
    replace (acc + 0 - 0) with acc by lia. reflexivity.
  - cbn [fold_left ListLib.sum length].
    rewrite IH.
    change
      (Z.modulo
        (10 * acc + (digit - 48) + ListLib.sum xs -
          48 * Z.of_nat (length xs)) 9 =
       Z.modulo
        (acc + (digit + ListLib.sum xs) -
          48 * Z.of_nat (S (length xs))) 9).
    replace
      (10 * acc + (digit - 48) + ListLib.sum xs -
        48 * Z.of_nat (length xs))
      with
      (acc + (digit + ListLib.sum xs) -
        48 * Z.of_nat (S (length xs)) + acc * 9) by
      (rewrite Nat2Z.inj_succ; lia).
    apply Z.mod_add.
    lia.
Qed.
Lemma forall_firstn__query_preserve_high :
  forall {A : Type} (P : A -> Prop) n xs,
    Forall P xs -> Forall P (firstn n xs).
Proof.
  intros A P n.
  induction n as [|n IH]; intros xs Hforall; simpl; [constructor |].
  destruct xs as [|x xs]; simpl; [constructor |].
  inversion Hforall; subst.
  constructor; [assumption | apply IH; assumption].
Qed.
Lemma forall_skipn__query_preserve_high :
  forall {A : Type} (P : A -> Prop) n xs,
    Forall P xs -> Forall P (skipn n xs).
Proof.
  intros A P n.
  induction n as [|n IH]; intros xs Hforall; simpl; [assumption |].
  destruct xs as [|x xs]; simpl; [constructor |].
  inversion Hforall; subst.
  apply IH; assumption.
Qed.
Lemma forall_sublist__query_preserve_high :
  forall {A : Type} (P : A -> Prop) lo hi xs,
    Forall P xs -> Forall P (sublist lo hi xs).
Proof.
  intros A P lo hi xs Hforall.
  unfold sublist.
  apply forall_skipn__query_preserve_high.
  apply forall_firstn__query_preserve_high.
  exact Hforall.
Qed.
Lemma decimal_fold_nonnegative__query_preserve_high :
  forall xs acc,
    0 <= acc ->
    Forall (fun digit => 48 <= digit) xs ->
    0 <= fold_left (fun value digit => 10 * value + (digit - 48)) xs acc.
Proof.
  induction xs as [|digit xs IH]; intros acc Hacc Hdigits; simpl.
  - exact Hacc.
  - inversion Hdigits; subst.
    apply IH.
    + change (0 <= 10 * acc + (digit - 48)). nia.
    + assumption.
Qed.
Lemma decimal_sub_mod9_prefix__query_preserve_high :
  forall s prefix n l r,
    1 <= l -> l <= r -> r <= n -> n = Zlength s ->
    (forall j, 0 <= j < Zlength s -> 48 <= Znth j s 0) ->
    0 <= Znth r prefix 0 - Znth (l - 1) prefix 0 ->
    DigitPrefixSums s prefix n ->
    DecimalSub s (l - 1) (r - 1) mod 9 =
      (Znth r prefix 0 - Znth (l - 1) prefix 0) mod 9.
Proof.
  intros s prefix n l r Hl Hlr Hrn Hn Hdigits Hdiff Hprefix.
  assert (Hall : Forall (fun digit => 48 <= digit) s).
  {
    apply (proj2 (Forall_Znth (fun digit => 48 <= digit) 0 s)).
    exact Hdigits.
  }
  assert (Hdecimal : 0 <= DecimalSub s (l - 1) (r - 1)).
  {
    unfold DecimalSub.
    apply decimal_fold_nonnegative__query_preserve_high; [lia |].
    apply forall_sublist__query_preserve_high.
    exact Hall.
  }
  unfold DigitPrefixSums in Hprefix.
  pose proof (Hprefix r ltac:(lia)) as Hr.
  pose proof (Hprefix (l - 1) ltac:(lia)) as Hlpre.
  unfold DigitPrefixValue, sum_range in Hr, Hlpre.
  replace (r - 1 + 1) with r in Hr by lia.
  replace (l - 1 - 1 + 1) with (l - 1) in Hlpre by lia.
  pose proof
    (sum_Z_range_split 0 (l - 1) r
      (fun j => Znth j s 48 - 48) ltac:(lia)) as Hsplit.
  unfold DecimalSub.
  replace (r - 1 + 1) with r by lia.
  rewrite decimal_fold_mod9__query_preserve_high.
  rewrite (list_sum_sublist_as_Z_range_sum s (l - 1) r) by lia.
  assert (Hsublength :
    Z.of_nat (length (sublist (l - 1) r s)) = r - (l - 1)).
  {
    unfold sublist.
    rewrite length_skipn.
    rewrite firstn_length_le.
    - rewrite Nat2Z.inj_sub by lia.
      rewrite !Z2Nat.id by lia. lia.
    - rewrite Zlength_correct in Hn. lia.
  }
  rewrite Hsublength.
  assert (Hsumdigits :
    sum (fun j : Z => l - 1 <= j < r) (fun j => Znth j s 0 - 48) =
    sum (fun j : Z => l - 1 <= j < r) (fun j => Znth j s 0) -
      48 * (r - (l - 1))).
  {
    rewrite sum_sub.
    rewrite sum_Z_range_const by lia.
    nia.
  }
  replace
    (0 + sum (fun j : Z => l - 1 <= j < r) (fun j => Znth j s 0) -
      48 * (r - (l - 1)))
    with
    (sum (fun j : Z => l - 1 <= j < r) (fun j => Znth j s 0) -
      48 * (r - (l - 1))) by lia.
  rewrite <- Hsumdigits.
  assert (Hvalues :
    sum (fun j : Z => l - 1 <= j < r) (fun j => Znth j s 0 - 48) =
    sum (fun j : Z => l - 1 <= j < r) (fun j => Znth j s 48 - 48)).
  {
    apply sum_Z_range_ext.
    intros j Hj.
    rewrite (Znth_indep s j 0 48) by (rewrite <- Hn; lia).
    reflexivity.
  }
  rewrite Hvalues.
  rewrite <- Hr, <- Hlpre in Hsplit.
  rewrite Hsplit.
  f_equal.
  lia.
Qed.
Lemma nonnegative_rem_as_mod__query_preserve_high :
  forall x,
    0 <= Z.rem x 9 -> Z.rem x 9 = Z.modulo x 9.
Proof.
  intros x Hrem.
  destruct (Z_le_gt_dec 0 x) as [Hx | Hx].
  - apply Zrem_Zmod_pos; lia.
  - pose proof (Zrem_lt_neg_pos x 9 ltac:(lia) ltac:(lia)).
    assert (Hrem0 : Z.rem x 9 = 0) by lia.
    rewrite Hrem0.
    symmetry.
    apply (proj1 (Zrem_Zmod_zero x 9 ltac:(lia))).
    exact Hrem0.
Qed.
Lemma negative_rem_as_mod__query_preserve_high :
  forall x,
    Z.rem x 9 < 0 -> Z.rem x 9 + 9 = Z.modulo x 9.
Proof.
  intros x Hrem.
  pose proof (Z.rem_bound_abs x 9 ltac:(lia)) as Hbound.
  apply (Zmod_unique x 9 (Z.quot x 9 - 1) (Z.rem x 9 + 9)).
  - lia.
  - pose proof (Z.quot_rem x 9 ltac:(lia)) as Hqr.
    nia.
Qed.
Lemma query_best_prefix_step_preserve__query_preserve_high :
  forall s w q residues_done best1 best2,
    0 <= residues_done ->
    QueryBestPrefix s w q residues_done best1 best2 ->
    (forall candidate,
      PrefixEligiblePair s w q (residues_done + 1) candidate ->
      PrefixEligiblePair s w q residues_done candidate \/
      (best1 <> 1073741824 /\ PairLexLe (best1, best2) candidate)) ->
    QueryBestPrefix s w q (residues_done + 1) best1 best2.
Proof.
  intros s w q residues_done best1 best2 Hdone Hbest Hstep.
  unfold QueryBestPrefix in Hbest |- *.
  destruct Hbest as [[Hb1 [Hb2 Hnone]] | Hminimum].
  - left. repeat split; try assumption.
    intros candidate Hcandidate.
    destruct (Hstep candidate Hcandidate) as [Hold | [Hneq _]].
    + exact (Hnone candidate Hold).
    + contradiction.
  - right.
    unfold min_value_of_subset, min_object_of_subset in Hminimum |- *.
    destruct Hminimum as [chosen [[Hchosen Hleast] Hchosen_eq]].
    exists chosen.
    split; [split | exact Hchosen_eq].
    + unfold PrefixEligiblePair in Hchosen |- *.
      destruct Hchosen as [Hquery Hresidue].
      split; [exact Hquery | lia].
    + intros candidate Hcandidate.
      destruct (Hstep candidate Hcandidate) as [Hold | [_ Hnew]].
      * exact (Hleast candidate Hold).
      * rewrite Hchosen_eq. exact Hnew.
Qed.
Lemma candidate_windows__query_preserve_high :
  forall s prefix n w l r k v a p,
    n = Zlength s ->
    1 <= l -> l <= r -> r <= n ->
    0 <= k < 9 ->
    (forall j, 0 <= j < Zlength s -> 48 <= Znth j s 0) ->
    0 <= Znth r prefix 0 - Znth (l - 1) prefix 0 ->
    DigitPrefixSums s prefix n ->
    v = Z.rem (Znth r prefix 0 - Znth (l - 1) prefix 0) 9 ->
    QueryPair s w ((l, r), k) p ->
    PairFirstResidue s w p = a ->
    WindowStart s w (n - w + 1) a (fst p) /\
    WindowStart s w (n - w + 1) (Z.modulo (k - a * v) 9) (snd p).
Proof.
  intros s prefix n w l r k v a [x y]
    Hn Hl Hlr Hrn Hk Hdigits Hdiff Hprefix Hv Hpair Hresidue.
  unfold QueryPair in Hpair.
  cbn in Hpair.
  destruct Hpair as
    [Hx1 [Hxend [Hy1 [Hyend [Hxy Hmod]]]]].
  pose proof
    (decimal_sub_mod9_prefix__query_preserve_high
      s prefix n l r Hl Hlr Hrn Hn Hdigits Hdiff Hprefix) as Hqueryresidue.
  pose proof
    (Z.rem_bound_pos
      (Znth r prefix 0 - Znth (l - 1) prefix 0) 9 Hdiff ltac:(lia))
    as Hrembound.
  pose proof
    (nonnegative_rem_as_mod__query_preserve_high
      (Znth r prefix 0 - Znth (l - 1) prefix 0) (proj1 Hrembound)) as Hvmod.
  rewrite <- Hv in Hvmod.
  unfold PairFirstResidue in Hresidue.
  cbn in Hresidue.
  split.
  - unfold WindowStart.
    split.
    + split; [exact Hx1 |].
      rewrite <- Hn in Hxend.
      apply (proj2 (Z.add_le_mono_r x (n - w + 1) (w - 1))).
      replace (x + (w - 1)) with (x + w - 1) by ring.
      replace (n - w + 1 + (w - 1)) with n by ring.
      exact Hxend.
    + split; [exact Hxend | exact Hresidue].
  - unfold WindowStart.
    split.
    + split; [exact Hy1 |].
      rewrite <- Hn in Hyend.
      apply (proj2 (Z.add_le_mono_r y (n - w + 1) (w - 1))).
      replace (y + (w - 1)) with (y + w - 1) by ring.
      replace (n - w + 1 + (w - 1)) with n by ring.
      exact Hyend.
    + split; [exact Hyend |].
    rewrite Zplus_mod, Zmult_mod in Hmod.
    rewrite Hqueryresidue in Hmod.
    rewrite <- Hvmod in Hmod.
    rewrite Hresidue in Hmod.
    rewrite <- Hmod.
    set (A := Z.modulo (a * v) 9).
    set (B := Z.modulo (DecimalSub s (y - 1) (y + w - 2)) 9).
    change (B = Z.modulo (Z.modulo (A + B) 9 - a * v) 9).
    apply
      (Zmod_unique (Z.modulo (A + B) 9 - a * v) 9
        (- ((A + B) / 9) - (a * v) / 9) B).
    * subst B.
      exact
        (Z.mod_pos_bound (DecimalSub s (y - 1) (y + w - 2)) 9 ltac:(lia)).
    * pose proof (Z_div_mod_eq_full (A + B) 9) as HAB.
      pose proof (Z_div_mod_eq_full (a * v) 9) as Hav.
      subst A.
      nia.
Qed.
Lemma first_window_negative_none__query_preserve_high :
  forall s w starts_done residue first,
    FirstWindowStart s w starts_done residue first ->
    first < 0 ->
    forall x, ~ WindowStart s w starts_done residue x.
Proof.
  intros s w starts_done residue first Hfirst Hnegative.
  destruct Hfirst as [[_ Hnone] | [Hstored _]].
  - exact Hnone.
  - unfold WindowStart in Hstored. lia.
Qed.
Lemma second_window_negative_unique__query_preserve_high :
  forall s w starts_done residue first second,
    SecondWindowStart s w starts_done residue first second ->
    second < 0 ->
    forall x, WindowStart s w starts_done residue x -> x = first.
Proof.
  intros s w starts_done residue first second Hsecond Hnegative.
  destruct Hsecond as [[_ Honly] | [Hstored _]].
  - exact Honly.
  - unfold WindowStart in Hstored. lia.
Qed.
Lemma first_window_lower_bound__query_preserve_high :
  forall s w starts_done residue first,
    FirstWindowStart s w starts_done residue first ->
    0 <= first ->
    forall x, WindowStart s w starts_done residue x -> first <= x.
Proof.
  intros s w starts_done residue first Hfirst Hnonnegative.
  destruct Hfirst as [[Hsentinel _] | [_ Hleast]].
  - lia.
  - exact Hleast.
Qed.
Lemma query_best_full_no_pair__query_output :
  forall (s : list Z) (w : Z) (q : Z * Z * Z) (best2 : Z),
    1 <= w ->
    Zlength s <= 200000 ->
    QueryBestPrefix s w q 9 1073741824 best2 ->
    forall candidate, ~ QueryPair s w q candidate.
Proof.
  intros s w q best2 Hw Hlen Hbest candidate Hcandidate.
  unfold QueryBestPrefix in Hbest.
  destruct Hbest as [[_ [_ Hnone]] | Hminimum].
  - apply (Hnone candidate).
    split; [exact Hcandidate |].
    unfold PairFirstResidue.
    apply Z.mod_pos_bound.
    lia.
  - unfold min_value_of_subset, min_object_of_subset in Hminimum.
    destruct Hminimum as (chosen & [[Hchosen _] Hchosen_eq]).
    simpl in Hchosen_eq.
    subst chosen.
    unfold PrefixEligiblePair in Hchosen.
    destruct Hchosen as [Hchosen _].
    destruct q as [[ql qr] qk].
    cbn [QueryPair] in Hchosen.
    destruct Hchosen as [_ [Hbound _]].
    lia.
Qed.
Lemma query_best_full_minimum__query_output :
  forall (s : list Z) (w : Z) (q : Z * Z * Z) (best1 best2 : Z),
    best1 <> 1073741824 ->
    QueryBestPrefix s w q 9 best1 best2 ->
    min_value_of_subset PairLexLe (QueryPair s w q)
      (fun candidate => candidate) (best1, best2).
Proof.
  intros s w q best1 best2 Hnot_sentinel Hbest.
  unfold QueryBestPrefix in Hbest.
  destruct Hbest as [[Hsentinel _] | Hminimum].
  - contradiction.
  - unfold min_value_of_subset, min_object_of_subset in Hminimum |- *.
    destruct Hminimum as (chosen & [[Hchosen Hleast] Hchosen_eq]).
    exists chosen.
    split.
    + split.
      * exact (proj1 Hchosen).
      * intros candidate Hcandidate.
        apply Hleast.
        split; [exact Hcandidate |].
        unfold PairFirstResidue.
        apply Z.mod_pos_bound.
        lia.
    + exact Hchosen_eq.
Qed.
Lemma query_output_append_none__query_output :
  forall (w : Z) (s : list Z) (qs : list (Z * Z * Z))
    (z : Z) (out1 out2 : list Z) (default_query : Z * Z * Z),
    0 <= z < Zlength qs ->
    QueryOutputPrefix w s qs z out1 out2 ->
    (forall candidate,
      ~ QueryPair s w (Znth z qs default_query) candidate) ->
    QueryOutputPrefix w s qs (z + 1)
      (out1 ++ (-1 :: nil)) (out2 ++ (-1 :: nil)).
Proof.
  intros w s qs z out1 out2 default_query Hz Hprefix Hnone.
  unfold QueryOutputPrefix in Hprefix |- *.
  destruct Hprefix as
    (pairs & Hspec & Hpairs & Hout1 & Hout2 & Hcomponents).
  exists (pairs ++ ((-1, -1) :: nil)).
  repeat split.
  - unfold Spec in Hspec |- *.
    rewrite (sublist_split 0 (z + 1) z qs) by lia.
    rewrite (sublist_single default_query z qs) by lia.
    apply Forall2_app; [exact Hspec |].
    constructor; [left; split; [reflexivity | exact Hnone] | constructor].
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - destruct (Z_lt_ge_dec i z) as [Hiz | Hiz].
    + rewrite (app_Znth1 0 out1 (-1 :: nil)) by lia.
      rewrite (app_Znth1 (0, 0) pairs ((-1, -1) :: nil)) by lia.
      exact (proj1 (Hcomponents i ltac:(lia))).
    + assert (i = z) by lia.
      subst i.
      rewrite (app_Znth2 0 out1 (-1 :: nil)) by lia.
      rewrite (app_Znth2 (0, 0) pairs ((-1, -1) :: nil)) by lia.
      replace (z - Zlength out1) with 0 by lia.
      replace (z - Zlength pairs) with 0 by lia.
      reflexivity.
  - destruct (Z_lt_ge_dec i z) as [Hiz | Hiz].
    + rewrite (app_Znth1 0 out2 (-1 :: nil)) by lia.
      rewrite (app_Znth1 (0, 0) pairs ((-1, -1) :: nil)) by lia.
      exact (proj2 (Hcomponents i ltac:(lia))).
    + assert (i = z) by lia.
      subst i.
      rewrite (app_Znth2 0 out2 (-1 :: nil)) by lia.
      rewrite (app_Znth2 (0, 0) pairs ((-1, -1) :: nil)) by lia.
      replace (z - Zlength out2) with 0 by lia.
      replace (z - Zlength pairs) with 0 by lia.
      reflexivity.
Qed.
Lemma query_output_append_found__query_output :
  forall (w : Z) (s : list Z) (qs : list (Z * Z * Z))
    (z best1 best2 : Z) (out1 out2 : list Z)
    (default_query : Z * Z * Z),
    0 <= z < Zlength qs ->
    QueryOutputPrefix w s qs z out1 out2 ->
    min_value_of_subset PairLexLe
      (QueryPair s w (Znth z qs default_query))
      (fun candidate => candidate) (best1, best2) ->
    QueryOutputPrefix w s qs (z + 1)
      (out1 ++ (best1 :: nil)) (out2 ++ (best2 :: nil)).
Proof.
  intros w s qs z best1 best2 out1 out2 default_query
    Hz Hprefix Hminimum.
  unfold QueryOutputPrefix in Hprefix |- *.
  destruct Hprefix as
    (pairs & Hspec & Hpairs & Hout1 & Hout2 & Hcomponents).
  exists (pairs ++ ((best1, best2) :: nil)).
  repeat split.
  - unfold Spec in Hspec |- *.
    rewrite (sublist_split 0 (z + 1) z qs) by lia.
    rewrite (sublist_single default_query z qs) by lia.
    apply Forall2_app; [exact Hspec |].
    constructor.
    + right.
      unfold PairLexLe in Hminimum.
      exact Hminimum.
    + constructor.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - destruct (Z_lt_ge_dec i z) as [Hiz | Hiz].
    + rewrite (app_Znth1 0 out1 (best1 :: nil)) by lia.
      rewrite (app_Znth1 (0, 0) pairs ((best1, best2) :: nil)) by lia.
      exact (proj1 (Hcomponents i ltac:(lia))).
    + assert (i = z) by lia.
      subst i.
      rewrite (app_Znth2 0 out1 (best1 :: nil)) by lia.
      rewrite (app_Znth2 (0, 0) pairs ((best1, best2) :: nil)) by lia.
      replace (z - Zlength out1) with 0 by lia.
      replace (z - Zlength pairs) with 0 by lia.
      reflexivity.
  - destruct (Z_lt_ge_dec i z) as [Hiz | Hiz].
    + rewrite (app_Znth1 0 out2 (best2 :: nil)) by lia.
      rewrite (app_Znth1 (0, 0) pairs ((best1, best2) :: nil)) by lia.
      exact (proj2 (Hcomponents i ltac:(lia))).
    + assert (i = z) by lia.
      subst i.
      rewrite (app_Znth2 0 out2 (best2 :: nil)) by lia.
      rewrite (app_Znth2 (0, 0) pairs ((best1, best2) :: nil)) by lia.
      replace (z - Zlength out2) with 0 by lia.
      replace (z - Zlength pairs) with 0 by lia.
      reflexivity.
Qed.
Lemma query_output_prefix_full__final_result :
  forall (w : Z) (s : list Z) (qs : list (Z * Z * Z))
    (m : Z) (out1 out2 : list Z) (default_pair : Z * Z),
    m = Zlength qs ->
    QueryOutputPrefix w s qs m out1 out2 ->
    exists pairs,
      Spec w s qs pairs /\
      Zlength pairs = m /\
      Zlength out1 = m /\
      Zlength out2 = m /\
      forall i,
        0 <= i < m ->
        Znth i out1 0 = fst (Znth i pairs default_pair) /\
        Znth i out2 0 = snd (Znth i pairs default_pair).
Proof.
  intros w s qs m out1 out2 default_pair Hm Hprefix.
  unfold QueryOutputPrefix in Hprefix.
  destruct Hprefix as
    (pairs & Hspec & Hpairs & Hout1 & Hout2 & Hcomponents).
  rewrite Hm in Hspec.
  rewrite (sublist_self qs (Zlength qs) eq_refl) in Hspec.
  exists pairs.
  split; [exact Hspec |].
  split; [exact Hpairs |].
  split; [exact Hout1 |].
  split; [exact Hout2 |].
  intros i Hi.
  rewrite (Znth_indep pairs i default_pair (0, 0)).
  - apply Hcomponents; exact Hi.
  - rewrite Hpairs; exact Hi.
Qed.
