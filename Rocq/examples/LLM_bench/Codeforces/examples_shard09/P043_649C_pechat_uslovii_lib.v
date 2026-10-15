Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition CanPrint (pages : list Z) (x y teams : Z) : Prop :=
  exists chosen doubles singles : list Z,
    Zlength chosen = Zlength pages /\ Zlength doubles = Zlength pages /\ Zlength singles = Zlength pages /\
    Forall (fun z => z = 0 \/ z = 1) chosen /\ Forall (fun z => z >= 0) doubles /\ Forall (fun z => z >= 0) singles /\
    (fold_right Z.add 0) chosen = teams /\ (fold_right Z.add 0) doubles <= x /\ (fold_right Z.add 0) singles <= y /\
    (forall i, 0 <= i < Zlength pages ->
      (Znth i chosen 0 = 1 -> 2 * Znth i doubles 0 + Znth i singles 0 >= Znth i pages 0) /\
      (Znth i chosen 0 = 0 -> Znth i doubles 0 = 0 /\ Znth i singles 0 = 0)).
Definition Pre (pages : list Z) (x y : Z) : Prop :=
  (* Stated explicitly in the P043 solver Require, so dropped here:
       1 <= Zlength pages <= 200000 /\
       Forall (fun p => 1 <= p <= 10000) pages /\
       x >= 0 /\
       y >= 0   *)
  True.

Definition Spec (pages : list Z) (x y out : Z) : Prop := max_value_of_subset Z.le (CanPrint pages x y) (fun x => x) out.

Definition CanPrintAll (pages : list Z) (x y : Z) : Prop :=
  CanPrint pages x y (Zlength pages).

Definition PrefixResourceState
    (pages : list Z)
    (initial_doubles initial_singles processed
     remaining_doubles remaining_singles : Z) : Prop :=
  forall suffix,
    CanPrintAll (sublist 0 processed pages ++ suffix)
      initial_doubles initial_singles <->
    CanPrintAll suffix remaining_doubles remaining_singles.

Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zquot.
Lemma forall_znth__initialization {A : Type}
    (P : A -> Prop) (d : A) (l : list A) :
  Forall P l <->
  (forall i, 0 <= i < Zlength l -> P (Znth i l d)).
Proof.
  induction l as [| a l IH].
  - rewrite Zlength_nil. split.
    + intros _ i Hi. lia.
    + intros _. constructor.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg l) as Hnn. split.
    + intros HF i Hi. inversion HF as [| ? ? Ha Hl]; subst.
      destruct (Z.eq_dec i 0) as [-> | Hne].
      * rewrite Znth0_cons. exact Ha.
      * rewrite Znth_cons by lia.
        apply (proj1 IH Hl). lia.
    + intros H. constructor.
      * specialize (H 0 ltac:(lia)). rewrite Znth0_cons in H. exact H.
      * apply (proj2 IH). intros i Hi.
        specialize (H (i + 1) ltac:(lia)).
        rewrite Znth_cons in H by lia.
        replace (i + 1 - 1) with i in H by lia. exact H.
Qed.
Lemma prefix_resource_state_zero__initialization :
  forall (pages : list Z) (x y : Z),
    PrefixResourceState pages x y 0 x y.
Proof.
  unfold PrefixResourceState.
  intros pages x y suffix.
  rewrite Zsublist_nil by lia.
  simpl.
  reflexivity.
Qed.
Lemma permutation_preserves_znth_bounds__initialization :
  forall (input sorted : list Z) (n lo hi : Z),
    (forall i, 0 <= i < n ->
      lo <= Znth i input 0 <= hi) ->
    n = Zlength input ->
    Permutation input sorted ->
    forall i, 0 <= i < n ->
      lo <= Znth i sorted 0 <= hi.
Proof.
  intros input sorted n lo hi Hbounds Hn Hperm i Hi.
  assert (Hlen : Zlength sorted = n).
  { rewrite Hn. rewrite !Zlength_correct.
    rewrite (Permutation_length Hperm). reflexivity. }
  apply (proj1 (forall_znth__initialization
    (fun x => lo <= x <= hi) 0 sorted)).
  - eapply Permutation_Forall.
    + exact Hperm.
    + apply (proj2 (forall_znth__initialization
        (fun x => lo <= x <= hi) 0 input)).
      intros k Hk. apply Hbounds. rewrite Hn. exact Hk.
  - rewrite Hlen. exact Hi.
Qed.
Lemma binary_sum_le_length__resource_transitions :
  forall xs,
    Forall (fun z : Z => z = 0 \/ z = 1) xs ->
    fold_right Z.add 0 xs <= Zlength xs.
Proof.
  intros xs Hxs. induction Hxs as [|z xs Hz Hxs IH].
  - simpl. rewrite Zlength_nil. lia.
  - simpl. rewrite Zlength_cons. destruct Hz; subst; lia.
Qed.
Lemma nonnegative_fold__resource_transitions :
  forall xs,
    Forall (fun z : Z => z >= 0) xs ->
    0 <= fold_right Z.add 0 xs.
Proof.
  intros xs Hxs. induction Hxs as [|z xs Hz Hxs IH].
  - simpl. lia.
  - cbn [fold_right]. apply Z.ge_le in Hz.
    apply Z.add_nonneg_nonneg; assumption.
Qed.
Lemma print_need_nonnegative__resource_transitions :
  forall pages,
    0 <= fold_right Z.add 0 (map (fun p => Z.max 0 p) pages).
Proof.
  intros pages. induction pages as [|p pages IH]; simpl; [lia|].
  pose proof (Z.le_max_l 0 p). lia.
Qed.
Lemma print_units_nonnegative__resource_transitions :
  forall pages,
    0 <= fold_right Z.add 0
      (map (fun p => (Z.max 0 p + 1) / 2) pages).
Proof.
  intros pages. induction pages as [|p pages IH]; simpl; [lia|].
  assert (0 <= Z.max 0 p + 1) by (pose proof (Z.le_max_l 0 p); lia).
  pose proof (Z.div_pos (Z.max 0 p + 1) 2 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma print_units_le_need__resource_transitions :
  forall pages,
    fold_right Z.add 0 (map (fun p => (Z.max 0 p + 1) / 2) pages) <=
    fold_right Z.add 0 (map (fun p => Z.max 0 p) pages).
Proof.
  intros pages. induction pages as [|p pages IH]; simpl; [lia|].
  pose proof (Z.le_max_l 0 p) as Hp.
  destruct (Z.eq_dec (Z.max 0 p) 0) as [Hz|Hz].
  - rewrite Hz. simpl. lia.
  - assert (1 <= Z.max 0 p) by lia.
    pose proof (Zdiv_le_upper_bound (Z.max 0 p + 1) 2 (Z.max 0 p)
      ltac:(lia) ltac:(nia)). lia.
Qed.
Lemma print_need_le_twice_units__resource_transitions :
  forall pages,
    fold_right Z.add 0 (map (fun p => Z.max 0 p) pages) <=
    2 * fold_right Z.add 0
      (map (fun p => (Z.max 0 p + 1) / 2) pages).
Proof.
  intros pages. induction pages as [|p pages IH].
  - simpl. lia.
  - cbn [map fold_right].
  pose proof (Z.le_max_l 0 p) as Hp.
  pose proof (Z.div_mod (Z.max 0 p + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (Z.max 0 p + 1) 2 ltac:(lia)) as Hmod.
  remember ((Z.max 0 p + 1) / 2) as q in *.
  remember ((Z.max 0 p + 1) mod 2) as r in *.
  assert (Z.max 0 p <= 2 * q) by nia.
  rewrite Z.mul_add_distr_l. apply Z.add_le_mono; assumption.
Qed.
Lemma can_print_all_nonnegative_budgets__resource_transitions :
  forall pages x y,
    CanPrintAll pages x y -> 0 <= x /\ 0 <= y.
Proof.
  intros pages x y H.
  unfold CanPrintAll, CanPrint in H.
  destruct H as
    (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
     Hteams & Hdbudget & Hsbudget & Hcover).
  pose proof (nonnegative_fold__resource_transitions doubles Hdoubles) as Hd.
  pose proof (nonnegative_fold__resource_transitions singles Hsingles) as Hs.
  lia.
Qed.
Lemma binary_sum_eq_length_all_one__resource_transitions :
  forall xs,
    Forall (fun z : Z => z = 0 \/ z = 1) xs ->
    fold_right Z.add 0 xs = Zlength xs ->
    Forall (fun z : Z => z = 1) xs.
Proof.
  intros xs Hxs. induction Hxs as [|z xs Hz Hxs IH]; intros Hsum.
  - constructor.
  - simpl in Hsum. rewrite Zlength_cons in Hsum.
    pose proof (binary_sum_le_length__resource_transitions xs Hxs) as Hle.
    destruct Hz; subst; try lia.
    constructor; [reflexivity|]. apply IH. lia.
Qed.
Lemma all_one_sum_eq_length__resource_transitions :
  forall xs,
    Forall (fun z : Z => z = 1) xs ->
    fold_right Z.add 0 xs = Zlength xs.
Proof.
  intros xs Hxs. induction Hxs as [|z xs Hz Hxs IH].
  - simpl. rewrite Zlength_nil. reflexivity.
  - subst. change (1 + fold_right Z.add 0 xs = Zlength (1 :: xs)).
    rewrite IH, Zlength_cons. unfold Z.succ. apply Z.add_comm.
Qed.
Lemma can_print_all_cons_iff__resource_transitions :
  forall p pages x y,
    CanPrintAll (p :: pages) x y <->
    exists d s,
      0 <= d /\ 0 <= s /\ 2 * d + s >= p /\
      CanPrintAll pages (x - d) (y - s).
Proof.
  intros p pages x y. split.
  - intros Hprint.
    unfold CanPrintAll, CanPrint in Hprint.
    destruct Hprint as
      (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
       Hteams & Hdbudget & Hsbudget & Hcover).
    destruct chosen as [|c chosen].
    { rewrite Zlength_nil, Zlength_cons in Hlc.
      pose proof (Zlength_nonneg pages). lia. }
    destruct doubles as [|d doubles].
    { rewrite Zlength_nil, Zlength_cons in Hld.
      pose proof (Zlength_nonneg pages). lia. }
    destruct singles as [|s singles].
    { rewrite Zlength_nil, Zlength_cons in Hls.
      pose proof (Zlength_nonneg pages). lia. }
    inversion Hchosen as [|? ? Hc Hchosen']; subst.
    inversion Hdoubles as [|? ? Hd Hdoubles']; subst.
    inversion Hsingles as [|? ? Hs Hsingles']; subst.
    assert (Hallones : Forall (fun z : Z => z = 1) (c :: chosen)).
    { apply binary_sum_eq_length_all_one__resource_transitions; [constructor; assumption|].
      rewrite Hteams, Hlc. reflexivity. }
    inversion Hallones as [|? ? Hc1 Hallones']; subst.
    exists d, s. split; [lia|]. split; [lia|]. split.
    + specialize (Hcover 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg pages); lia)).
      rewrite !Znth0_cons in Hcover. destruct Hcover as [Hone _]. apply Hone. reflexivity.
    + unfold CanPrintAll, CanPrint.
      exists chosen, doubles, singles.
      repeat lazymatch goal with |- _ /\ _ => split end.
      * rewrite !Zlength_cons in Hlc. lia.
      * rewrite !Zlength_cons in Hld. lia.
      * rewrite !Zlength_cons in Hls. lia.
      * exact Hchosen'.
      * exact Hdoubles'.
      * exact Hsingles'.
      * transitivity (Zlength chosen).
        { apply all_one_sum_eq_length__resource_transitions. exact Hallones'. }
        rewrite !Zlength_cons in Hlc. unfold Z.succ in Hlc. lia.
      * simpl in Hdbudget. lia.
      * simpl in Hsbudget. lia.
      * intros j Hj.
        specialize (Hcover (j + 1) ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth_cons in Hcover by lia. replace (j + 1 - 1) with j in Hcover by lia.
        exact Hcover.
  - intros (d & s & Hd & Hs & Hcover_head & Htail).
    unfold CanPrintAll, CanPrint in Htail |- *.
    destruct Htail as
      (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
       Hteams & Hdbudget & Hsbudget & Hcover).
    exists (1 :: chosen), (d :: doubles), (s :: singles).
    repeat lazymatch goal with |- _ /\ _ => split end.
    + rewrite !Zlength_cons, Hlc. reflexivity.
    + rewrite !Zlength_cons, Hld. reflexivity.
    + rewrite !Zlength_cons, Hls. reflexivity.
    + constructor; [right; reflexivity|exact Hchosen].
    + constructor; [lia|exact Hdoubles].
    + constructor; [lia|exact Hsingles].
    + change (1 + fold_right Z.add 0 chosen = Zlength (p :: pages)).
      rewrite Hteams, Zlength_cons. unfold Z.succ. apply Z.add_comm.
    + simpl. lia.
    + simpl. lia.
    + intros j Hj. rewrite Zlength_cons in Hj.
      destruct (Z.eq_dec j 0) as [->|Hj0].
      * rewrite !Znth0_cons. split; intros; [lia|discriminate].
      * assert (0 < j) by lia.
        rewrite !Znth_cons by lia.
        specialize (Hcover (j - 1) ltac:(lia)). exact Hcover.
Qed.
Lemma can_print_all_numeric__resource_transitions :
  forall pages x y,
    0 <= x -> 0 <= y ->
    (CanPrintAll pages x y <->
      fold_right Z.add 0 (map (fun p => Z.max 0 p) pages) <= 2 * x + y /\
      fold_right Z.add 0 (map (fun p => (Z.max 0 p + 1) / 2) pages) <= x + y).
Proof.
  induction pages as [|p pages IH]; intros x y Hx Hy.
  - split.
    + intros _. cbn [map fold_right]. split; lia.
    + intros _. unfold CanPrintAll, CanPrint.
      exists nil, nil, nil. repeat lazymatch goal with |- _ /\ _ => split end.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * constructor.
      * constructor.
      * constructor.
      * reflexivity.
      * simpl. lia.
      * simpl. lia.
      * intros i Hi. rewrite Zlength_nil in Hi. lia.
  - rewrite can_print_all_cons_iff__resource_transitions. cbn [map fold_right].
    split.
    + intros (d & s & Hd & Hs & Hcover & Htail).
      pose proof (can_print_all_nonnegative_budgets__resource_transitions
        pages (x - d) (y - s) Htail) as [Hxd Hys].
      specialize (IH (x - d) (y - s) Hxd Hys).
      apply IH in Htail. destruct Htail as [Hneed Hunits].
      assert (Hmax : Z.max 0 p <= 2 * d + s).
      { pose proof (Z.le_max_l 0 p). pose proof (Z.le_max_r 0 p). lia. }
      assert (Hceil : (Z.max 0 p + 1) / 2 <= d + s).
      { apply Z.lt_succ_r.
        apply Zdiv_lt_upper_bound; [lia|]. nia. }
      split; nia.
    + intros [Hneed Hunits].
      pose proof (print_need_nonnegative__resource_transitions pages) as Hneed0.
      pose proof (print_units_nonnegative__resource_transitions pages) as Hunits0.
      destruct (Z_le_gt_dec p 0) as [Hp0|Hp].
      * exists 0, 0. split; [lia|]. split; [lia|]. split; [lia|].
        apply IH; [lia|lia|].
        rewrite Z.max_l in Hneed, Hunits by lia.
        change (fold_right Z.add 0 (map (fun p => Z.max 0 p) pages) <=
          2 * x + y) in Hneed.
        change (fold_right Z.add 0
          (map (fun p => (Z.max 0 p + 1) / 2) pages) <= x + y) in Hunits.
        split; lia.
      * assert (Hmax : Z.max 0 p = p) by (apply Z.max_r; lia).
        rewrite Hmax in Hneed, Hunits.
        pose proof (Z.div_mod p 2 ltac:(lia)) as Hdiv.
        pose proof (Z.mod_pos_bound p 2 ltac:(lia)) as Hmod.
        assert (Hr : p - 2 * (p / 2) = 0 \/ p - 2 * (p / 2) = 1) by nia.
        assert (Hceil : (p + 1) / 2 = p / 2 + (p - 2 * (p / 2))).
        { destruct Hr as [Hr0|Hr1].
          - symmetry. apply Zdiv_unique with (r := 1); nia.
          - symmetry. apply Zdiv_unique with (r := 0); nia. }
        rewrite Hceil in Hunits.
        destruct (Z_le_gt_dec (p / 2) x) as [Hqx|Hqx].
        -- destruct (Z_le_gt_dec (p - 2 * (p / 2)) y) as [Hry|Hry].
           ++ exists (p / 2), (p - 2 * (p / 2)).
              split; [apply Z.div_pos; lia|]. split; [lia|]. split; [nia|].
              apply IH; [lia|lia|]. split; nia.
           ++ assert (p - 2 * (p / 2) = 1 /\ y = 0) as [Hr1 Hy0].
              { destruct Hr; lia. }
              exists (p / 2 + 1), 0.
              split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia|lia]|].
              split; [lia|]. split; [nia|].
              assert (Hux : p / 2 + 1 <= x).
              { rewrite Hr1 in Hunits. nia. }
              apply IH; [lia|lia|]. split.
              { pose proof (print_need_le_twice_units__resource_transitions pages). nia. }
              { nia. }
        -- exists x, (p - 2 * x).
           split; [lia|]. split; [lia|]. split; [nia|].
           apply IH; [lia|lia|]. split.
           ++ nia.
           ++ pose proof (print_units_le_need__resource_transitions pages). nia.
Qed.
Lemma positive_page_div2_remainder__resource_transitions :
  forall p,
    1 <= p ->
    let q := p / 2 in
    let r := p - 2 * q in
    0 <= q /\ (r = 0 \/ r = 1) /\ p = 2 * q + r /\ (p + 1) / 2 = q + r.
Proof.
  intros p Hp. cbn zeta.
  pose proof (Z.div_mod p 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound p 2 ltac:(lia)) as Hmod.
  assert (Hq : 0 <= p / 2) by (apply Z.div_pos; lia).
  assert (Hr : p - 2 * (p / 2) = 0 \/ p - 2 * (p / 2) = 1) by nia.
  repeat split; try assumption; try nia.
  destruct Hr as [Hr0|Hr1].
  - symmetry. apply Zdiv_unique with (r := 1); nia.
  - symmetry. apply Zdiv_unique with (r := 0); nia.
Qed.
Lemma can_print_all_cons_resource_step__resource_transitions :
  forall p pages x y d s,
    0 <= p -> 0 <= x -> 0 <= y -> 0 <= d -> 0 <= s ->
    d <= x -> s <= y ->
    p = 2 * d + s ->
    (p + 1) / 2 = d + s ->
    (CanPrintAll (p :: pages) x y <->
     CanPrintAll pages (x - d) (y - s)).
Proof.
  intros p pages x y d s Hp Hx Hy Hd Hs Hdx Hsy Hcap Hunit.
  rewrite (can_print_all_numeric__resource_transitions (p :: pages) x y Hx Hy).
  rewrite (can_print_all_numeric__resource_transitions pages (x - d) (y - s)) by lia.
  cbn [map fold_right]. rewrite Z.max_r by lia.
  rewrite Hunit. split; intros [Hneed Hunits]; split; nia.
Qed.
Lemma positive_quot_eq_div__resource_transitions :
  forall p,
    0 <= p -> p ÷ 2 = p / 2.
Proof.
  intros p Hp. apply Z.quot_div_nonneg; lia.
Qed.
Lemma can_print_all_cons_scarce_doubles__resource_transitions :
  forall p pages x y,
    1 <= p -> 0 <= x -> 0 <= y ->
    p / 2 > x -> 0 <= p - 2 * x -> p - 2 * x <= y ->
    (CanPrintAll (p :: pages) x y <->
     CanPrintAll pages 0 (y - (p - 2 * x))).
Proof.
  intros p pages x y Hp Hx Hy Hscarce Hs Hsy.
  rewrite (can_print_all_numeric__resource_transitions (p :: pages) x y Hx Hy).
  rewrite (can_print_all_numeric__resource_transitions
    pages 0 (y - (p - 2 * x))) by lia.
  cbn [map fold_right]. rewrite Z.max_r by lia.
  pose proof (positive_page_div2_remainder__resource_transitions p Hp)
    as (Hq & Hr & Hdecomp & Hceil).
  pose proof (print_units_le_need__resource_transitions pages) as Hunit_need.
  split; intros [Hneed Hunits]; split; nia.
Qed.
Lemma can_print_all_cons_odd_no_singles__resource_transitions :
  forall p pages x,
    1 <= p -> 0 <= x ->
    p - 2 * (p / 2) = 1 -> p / 2 + 1 <= x ->
    (CanPrintAll (p :: pages) x 0 <->
     CanPrintAll pages (x - p / 2 - 1) 0).
Proof.
  intros p pages x Hp Hx Hodd Hspend.
  rewrite (can_print_all_numeric__resource_transitions (p :: pages) x 0 Hx) by lia.
  rewrite (can_print_all_numeric__resource_transitions
    pages (x - p / 2 - 1) 0) by lia.
  cbn [map fold_right]. rewrite Z.max_r by lia.
  pose proof (positive_page_div2_remainder__resource_transitions p Hp)
    as (Hq & Hr & Hdecomp & Hceil).
  pose proof (print_need_le_twice_units__resource_transitions pages) as Hneed_units.
  split; intros [Hneed Hunits]; split; nia.
Qed.
Lemma prefix_resource_state_advance__resource_transitions :
  forall pages initial_doubles initial_singles i x y x' y',
    0 <= i < Zlength pages ->
    PrefixResourceState pages initial_doubles initial_singles i x y ->
    (forall suffix,
      CanPrintAll (Znth i pages 0 :: suffix) x y <->
      CanPrintAll suffix x' y') ->
    PrefixResourceState pages initial_doubles initial_singles (i + 1) x' y'.
Proof.
  intros pages initial_doubles initial_singles i x y x' y'
    Hi Hprefix Hstep suffix.
  unfold PrefixResourceState in Hprefix.
  rewrite (sublist_split 0 (i + 1) i pages) by lia.
  rewrite (sublist_single 0 i pages) by lia.
  rewrite <- app_assoc.
  simpl.
  rewrite Hprefix.
  apply Hstep.
Qed.
Lemma binary_sum_bounds__early_exit :
  forall xs,
    Forall (fun z : Z => z = 0 \/ z = 1) xs ->
    0 <= fold_right Z.add 0 xs <= Zlength xs.
Proof.
  intros xs Hxs. induction Hxs as [|z xs Hz Hxs IH].
  - simpl. rewrite Zlength_nil. lia.
  - simpl. rewrite Zlength_cons. destruct Hz; subst; lia.
Qed.
Lemma nonnegative_sum__early_exit :
  forall xs,
    Forall (fun z : Z => z >= 0) xs ->
    0 <= fold_right Z.add 0 xs.
Proof.
  intros xs Hxs. induction Hxs as [|z xs Hz Hxs IH]; simpl; lia.
Qed.
Lemma can_print_nonnegative_budgets__early_exit :
  forall pages x y teams,
    CanPrint pages x y teams -> 0 <= x /\ 0 <= y.
Proof.
  intros pages x y teams H.
  unfold CanPrint in H.
  destruct H as
    (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
     Hteams & Hdbudget & Hsbudget & Hcover).
  pose proof (nonnegative_sum__early_exit doubles Hdoubles).
  pose proof (nonnegative_sum__early_exit singles Hsingles).
  lia.
Qed.
Lemma can_print_team_bounds__early_exit :
  forall pages x y teams,
    CanPrint pages x y teams -> 0 <= teams <= Zlength pages.
Proof.
  intros pages x y teams H.
  unfold CanPrint in H.
  destruct H as
    (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
     Hteams & Hdbudget & Hsbudget & Hcover).
  pose proof (binary_sum_bounds__early_exit chosen Hchosen).
  lia.
Qed.
Lemma can_print_permutation_pages__early_exit :
  forall pages pages' x y teams,
    Permutation pages pages' ->
    CanPrint pages x y teams ->
    CanPrint pages' x y teams.
Proof.
  intros pages pages' x y teams Hperm.
  revert x y teams.
  induction Hperm as [|p pages pages' Hperm IH|p q pages|pages mid pages' Hpm IHpm Hmp IHmp];
    intros x y teams Hprint.
  - exact Hprint.
  - unfold CanPrint in Hprint.
    destruct Hprint as
      (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
       Hteams & Hdbudget & Hsbudget & Hcover).
    destruct chosen as [|c chosen]; [rewrite Zlength_nil, Zlength_cons in Hlc; pose proof (Zlength_nonneg pages); lia|].
    destruct doubles as [|d doubles]; [rewrite Zlength_nil, Zlength_cons in Hld; pose proof (Zlength_nonneg pages); lia|].
    destruct singles as [|s singles]; [rewrite Zlength_nil, Zlength_cons in Hls; pose proof (Zlength_nonneg pages); lia|].
    inversion Hchosen as [|? ? Hc Hchosen'].
    inversion Hdoubles as [|? ? Hd Hdoubles'].
    inversion Hsingles as [|? ? Hs Hsingles'].
    assert (Htail : CanPrint pages (x - d) (y - s) (teams - c)).
    { unfold CanPrint.
      exists chosen, doubles, singles.
      repeat lazymatch goal with |- _ /\ _ => split end.
      - rewrite !Zlength_cons in Hlc. lia.
      - rewrite !Zlength_cons in Hld. lia.
      - rewrite !Zlength_cons in Hls. lia.
      - exact Hchosen'.
      - exact Hdoubles'.
      - exact Hsingles'.
      - simpl in Hteams. lia.
      - simpl in Hdbudget. lia.
      - simpl in Hsbudget. lia.
      - intros i Hi.
        specialize (Hcover (i + 1) ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth_cons in Hcover by lia.
        replace (i + 1 - 1) with i in Hcover by lia. exact Hcover. }
    specialize (IH (x - d) (y - s) (teams - c) Htail).
    unfold CanPrint in IH.
    destruct IH as
      (chosen' & doubles' & singles' & Hlc' & Hld' & Hls' & Hchosen'' & Hdoubles'' & Hsingles'' &
       Hteams' & Hdbudget' & Hsbudget' & Hcover').
    unfold CanPrint.
    exists (c :: chosen'), (d :: doubles'), (s :: singles').
    repeat lazymatch goal with |- _ /\ _ => split end.
    + rewrite !Zlength_cons, Hlc'. reflexivity.
    + rewrite !Zlength_cons, Hld'. reflexivity.
    + rewrite !Zlength_cons, Hls'. reflexivity.
    + constructor; assumption.
    + constructor; assumption.
    + constructor; assumption.
    + simpl. lia.
    + simpl. lia.
    + simpl. lia.
    + intros i Hi. rewrite Zlength_cons in Hi.
      destruct (Z.eq_dec i 0) as [->|Hi0].
      * rewrite !Znth0_cons. specialize (Hcover 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg pages); lia)).
        rewrite !Znth0_cons in Hcover. exact Hcover.
      * assert (0 < i) by lia. rewrite !Znth_cons by lia.
        specialize (Hcover' (i - 1) ltac:(lia)). exact Hcover'.
  - unfold CanPrint in Hprint.
    destruct Hprint as
      (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
       Hteams & Hdbudget & Hsbudget & Hcover).
    destruct chosen as [|c1 chosen]; [rewrite Zlength_nil, !Zlength_cons in Hlc; pose proof (Zlength_nonneg pages); lia|].
    destruct chosen as [|c2 chosen]; [rewrite Zlength_cons, Zlength_nil, !Zlength_cons in Hlc; pose proof (Zlength_nonneg pages); lia|].
    destruct doubles as [|d1 doubles]; [rewrite Zlength_nil, !Zlength_cons in Hld; pose proof (Zlength_nonneg pages); lia|].
    destruct doubles as [|d2 doubles]; [rewrite Zlength_cons, Zlength_nil, !Zlength_cons in Hld; pose proof (Zlength_nonneg pages); lia|].
    destruct singles as [|s1 singles]; [rewrite Zlength_nil, !Zlength_cons in Hls; pose proof (Zlength_nonneg pages); lia|].
    destruct singles as [|s2 singles]; [rewrite Zlength_cons, Zlength_nil, !Zlength_cons in Hls; pose proof (Zlength_nonneg pages); lia|].
    inversion Hchosen as [|? ? Hc1 Hchosen1].
    inversion Hchosen1 as [|? ? Hc2 Hchosen2].
    inversion Hdoubles as [|? ? Hd1 Hdoubles1].
    inversion Hdoubles1 as [|? ? Hd2 Hdoubles2].
    inversion Hsingles as [|? ? Hs1 Hsingles1].
    inversion Hsingles1 as [|? ? Hs2 Hsingles2].
    unfold CanPrint.
    exists (c2 :: c1 :: chosen), (d2 :: d1 :: doubles), (s2 :: s1 :: singles).
    repeat lazymatch goal with |- _ /\ _ => split end.
    + rewrite !Zlength_cons in *. lia.
    + rewrite !Zlength_cons in *. lia.
    + rewrite !Zlength_cons in *. lia.
    + constructor; [exact Hc2|constructor; assumption].
    + constructor; [exact Hd2|constructor; assumption].
    + constructor; [exact Hs2|constructor; assumption].
    + simpl in *. lia.
    + simpl in *. lia.
    + simpl in *. lia.
    + intros i Hi. rewrite !Zlength_cons in Hi.
      destruct (Z.eq_dec i 0) as [->|Hi0].
      * rewrite !Znth0_cons.
      specialize (Hcover 1 ltac:(rewrite !Zlength_cons; pose proof (Zlength_nonneg pages); lia)).
      rewrite !Znth_cons in Hcover by lia. replace (1 - 1) with 0 in Hcover by lia.
      rewrite !Znth0_cons in Hcover. exact Hcover.
      * destruct (Z.eq_dec i 1) as [->|Hi1].
        -- rewrite !Znth_cons by lia. replace (1 - 1) with 0 by lia. rewrite !Znth0_cons.
        specialize (Hcover 0 ltac:(rewrite !Zlength_cons; pose proof (Zlength_nonneg pages); lia)).
        rewrite !Znth0_cons in Hcover. exact Hcover.
        -- assert (1 < i) by lia. rewrite !Znth_cons by lia.
        replace (i - 1 - 1) with (i - 2) by lia.
        specialize (Hcover i ltac:(rewrite !Zlength_cons; lia)).
        rewrite !Znth_cons in Hcover by lia.
        replace (i - 1 - 1) with (i - 2) in Hcover by lia. exact Hcover.
  - apply IHmp. apply IHpm. exact Hprint.
Qed.
Lemma can_print_cons_cases__early_exit :
  forall p pages x y teams,
    CanPrint (p :: pages) x y teams ->
    (exists d s,
      0 <= d /\ 0 <= s /\ 2 * d + s >= p /\
      CanPrint pages (x - d) (y - s) (teams - 1)) \/
    CanPrint pages x y teams.
Proof.
  intros p pages x y teams Hprint.
  unfold CanPrint in Hprint.
  destruct Hprint as
    (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
     Hteams & Hdbudget & Hsbudget & Hcover).
  destruct chosen as [|c chosen]; [rewrite Zlength_nil, Zlength_cons in Hlc; pose proof (Zlength_nonneg pages); lia|].
  destruct doubles as [|d doubles]; [rewrite Zlength_nil, Zlength_cons in Hld; pose proof (Zlength_nonneg pages); lia|].
  destruct singles as [|s singles]; [rewrite Zlength_nil, Zlength_cons in Hls; pose proof (Zlength_nonneg pages); lia|].
  inversion Hchosen as [|? ? Hc Hchosen'].
  inversion Hdoubles as [|? ? Hd Hdoubles'].
  inversion Hsingles as [|? ? Hs Hsingles'].
  pose proof (Hcover 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg pages); lia)) as Hcover_head.
  rewrite !Znth0_cons in Hcover_head.
  destruct Hc as [Hc|Hc]; subst c.
  - right. destruct (proj2 Hcover_head eq_refl) as [Hd0 Hs0]. subst d s.
    unfold CanPrint. exists chosen, doubles, singles.
    repeat lazymatch goal with |- _ /\ _ => split end.
    + rewrite !Zlength_cons in Hlc. lia.
    + rewrite !Zlength_cons in Hld. lia.
    + rewrite !Zlength_cons in Hls. lia.
    + exact Hchosen'.
    + exact Hdoubles'.
    + exact Hsingles'.
    + simpl in Hteams. lia.
    + simpl in Hdbudget. lia.
    + simpl in Hsbudget. lia.
    + intros i Hi.
      specialize (Hcover (i + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite !Znth_cons in Hcover by lia.
      replace (i + 1 - 1) with i in Hcover by lia. exact Hcover.
  - left. exists d, s. split; [lia|]. split; [lia|]. split.
    + apply (proj1 Hcover_head). reflexivity.
    + unfold CanPrint. exists chosen, doubles, singles.
      repeat lazymatch goal with |- _ /\ _ => split end.
      * rewrite !Zlength_cons in Hlc. lia.
      * rewrite !Zlength_cons in Hld. lia.
      * rewrite !Zlength_cons in Hls. lia.
      * exact Hchosen'.
      * exact Hdoubles'.
      * exact Hsingles'.
      * change (fold_right Z.add 0 chosen = teams - 1).
        change (1 + fold_right Z.add 0 chosen = teams) in Hteams. lia.
      * simpl in Hdbudget. lia.
      * simpl in Hsbudget. lia.
      * intros i Hi.
        specialize (Hcover (i + 1) ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth_cons in Hcover by lia.
        replace (i + 1 - 1) with i in Hcover by lia. exact Hcover.
Qed.
Lemma can_print_all_prepend__early_exit :
  forall p pages x y d s,
    0 <= d -> 0 <= s -> 2 * d + s >= p ->
    CanPrintAll pages (x - d) (y - s) ->
    CanPrintAll (p :: pages) x y.
Proof.
  intros p pages x y d s Hd Hs Hcover_head Htail.
  unfold CanPrintAll, CanPrint in Htail |- *.
  destruct Htail as
    (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
     Hteams & Hdbudget & Hsbudget & Hcover).
  exists (1 :: chosen), (d :: doubles), (s :: singles).
  repeat lazymatch goal with |- _ /\ _ => split end.
  - rewrite !Zlength_cons, Hlc. reflexivity.
  - rewrite !Zlength_cons, Hld. reflexivity.
  - rewrite !Zlength_cons, Hls. reflexivity.
  - constructor; [right; reflexivity|exact Hchosen].
  - constructor; [lia|exact Hdoubles].
  - constructor; [lia|exact Hsingles].
  - change (1 + fold_right Z.add 0 chosen = Zlength (p :: pages)).
    rewrite Hteams, !Zlength_cons. unfold Z.succ. lia.
  - simpl. lia.
  - simpl. lia.
  - intros i Hi. rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite !Znth0_cons. split; intros; [exact Hcover_head|discriminate].
    + assert (0 < i) by lia. rewrite !Znth_cons by lia.
      specialize (Hcover (i - 1) ltac:(lia)). exact Hcover.
Qed.
Lemma can_print_all_weaken_pages__early_exit :
  forall small big x y,
    Zlength small = Zlength big ->
    (forall i, 0 <= i < Zlength small -> Znth i small 0 <= Znth i big 0) ->
    CanPrintAll big x y ->
    CanPrintAll small x y.
Proof.
  intros small big x y Hlen Hle Hprint.
  unfold CanPrintAll, CanPrint in Hprint |- *.
  destruct Hprint as
    (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
     Hteams & Hdbudget & Hsbudget & Hcover).
  exists chosen, doubles, singles.
  repeat lazymatch goal with |- _ /\ _ => split end.
  - lia.
  - lia.
  - lia.
  - exact Hchosen.
  - exact Hdoubles.
  - exact Hsingles.
  - lia.
  - exact Hdbudget.
  - exact Hsbudget.
  - intros i Hi.
    specialize (Hcover i ltac:(lia)). specialize (Hle i Hi).
    destruct Hcover as [Hone Hzero]. split.
    + intros Hc. specialize (Hone Hc). lia.
    + exact Hzero.
Qed.
Lemma sorted_prefix_is_easiest__early_exit :
  forall pages x y teams,
    mono_nondec pages ->
    0 <= teams ->
    CanPrint pages x y teams ->
    CanPrintAll (sublist 0 teams pages) x y.
Proof.
  induction pages as [|p pages IH]; intros x y teams Hmono Hteams Hprint.
  - pose proof (can_print_team_bounds__early_exit [] x y teams Hprint) as Hb.
    rewrite Zlength_nil in Hb. assert (teams = 0) by lia. subst teams.
    rewrite Zsublist_nil by lia. exact Hprint.
  - destruct (Z.eq_dec teams 0) as [->|Hteams0].
    + rewrite Zsublist_nil by lia.
      pose proof (can_print_nonnegative_budgets__early_exit (p :: pages) x y 0 Hprint) as [Hx Hy].
      unfold CanPrintAll, CanPrint.
      exists nil, nil, nil. repeat lazymatch goal with |- _ /\ _ => split end.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * constructor.
      * constructor.
      * constructor.
      * reflexivity.
      * simpl. lia.
      * simpl. lia.
      * intros i Hi. rewrite Zlength_nil in Hi. lia.
    + assert (Hteams_pos : 1 <= teams) by lia.
      pose proof (can_print_cons_cases__early_exit p pages x y teams Hprint) as Hcases.
      pose proof Hmono as Hmono_all.
      apply mono_nondec_cons in Hmono as [Hp_le Hmono_tail].
      destruct Hcases as [(d & s & Hd & Hs & Hcover_head & Htail)|Htail].
      * pose proof (IH (x - d) (y - s) (teams - 1) Hmono_tail ltac:(lia) Htail) as HIH.
        rewrite sublist_cons1 by lia.
        apply can_print_all_prepend__early_exit with (d := d) (s := s); assumption.
      * pose proof (can_print_team_bounds__early_exit pages x y teams Htail) as Hbound.
        pose proof (IH x y teams Hmono_tail ltac:(lia) Htail) as HIH.
        apply can_print_all_weaken_pages__early_exit with (big := sublist 0 teams pages).
        -- rewrite !Zlength_sublist by (rewrite ?Zlength_cons; lia). reflexivity.
        -- intros i Hi.
           rewrite Zlength_sublist in Hi by (rewrite Zlength_cons; lia).
           rewrite !Znth_sublist by lia.
           replace (i + 0) with i by lia.
           destruct (Z.eq_dec i 0) as [->|Hi0].
           ++ rewrite Znth0_cons.
              apply (proj1 (Forall_Znth (fun z : Z => p <= z) 0 pages) Hp_le).
              lia.
           ++ rewrite Znth_cons by lia.
              unfold mono_nondec in Hmono_tail.
              apply Hmono_tail; lia.
        -- exact HIH.
Qed.
Lemma prefix_resource_state_feasible_prefix__early_exit :
  forall pages x0 y0 processed x y,
    0 <= processed <= Zlength pages ->
    0 <= x -> 0 <= y ->
    PrefixResourceState pages x0 y0 processed x y ->
    CanPrintAll (sublist 0 processed pages) x0 y0.
Proof.
  intros pages x0 y0 processed x y Hprocessed Hx Hy Hstate.
  specialize (Hstate []). rewrite app_nil_r in Hstate.
  apply (proj2 Hstate).
  unfold CanPrintAll, CanPrint.
  exists nil, nil, nil. repeat lazymatch goal with |- _ /\ _ => split end.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - constructor.
  - constructor.
  - constructor.
  - reflexivity.
  - simpl. lia.
  - simpl. lia.
  - intros i Hi. rewrite Zlength_nil in Hi. lia.
Qed.
Lemma can_print_prepend_unselected__early_exit :
  forall p pages x y teams,
    CanPrint pages x y teams -> CanPrint (p :: pages) x y teams.
Proof.
  intros p pages x y teams Hprint.
  unfold CanPrint in Hprint |- *.
  destruct Hprint as
    (chosen & doubles & singles & Hlc & Hld & Hls & Hchosen & Hdoubles & Hsingles &
     Hteams & Hdbudget & Hsbudget & Hcover).
  exists (0 :: chosen), (0 :: doubles), (0 :: singles).
  repeat lazymatch goal with |- _ /\ _ => split end.
  - rewrite !Zlength_cons, Hlc. reflexivity.
  - rewrite !Zlength_cons, Hld. reflexivity.
  - rewrite !Zlength_cons, Hls. reflexivity.
  - constructor; [left; reflexivity|exact Hchosen].
  - constructor; [lia|exact Hdoubles].
  - constructor; [lia|exact Hsingles].
  - simpl. exact Hteams.
  - simpl. exact Hdbudget.
  - simpl. exact Hsbudget.
  - intros i Hi. rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite !Znth0_cons. split; [discriminate|intros; split; reflexivity].
    + assert (0 < i) by lia. rewrite !Znth_cons by lia.
      specialize (Hcover (i - 1) ltac:(lia)). exact Hcover.
Qed.
Lemma can_print_extend_unselected__early_exit :
  forall left right x y teams,
    CanPrint left x y teams -> CanPrint (left ++ right) x y teams.
Proof.
  intros left right x y teams Hprint.
  assert (Hrev : CanPrint (right ++ left) x y teams).
  { induction right as [|p right IH].
    - simpl. exact Hprint.
    - simpl. apply can_print_prepend_unselected__early_exit. exact IH. }
  eapply can_print_permutation_pages__early_exit.
  - apply Permutation_app_comm.
  - exact Hrev.
Qed.
Lemma can_print_all_head__early_exit :
  forall p pages x y,
    CanPrintAll (p :: pages) x y -> CanPrintAll [p] x y.
Proof.
  intros p pages x y Hprint.
  pose proof (can_print_cons_cases__early_exit p pages x y (Zlength (p :: pages)) Hprint) as Hcases.
  destruct Hcases as [(d & s & Hd & Hs & Hcover & Htail)|Htail].
  - pose proof (can_print_nonnegative_budgets__early_exit pages (x - d) (y - s)
      (Zlength (p :: pages) - 1) Htail) as [Hxd Hys].
    apply can_print_all_prepend__early_exit with (d := d) (s := s); try assumption.
    unfold CanPrintAll, CanPrint.
    exists nil, nil, nil. repeat lazymatch goal with |- _ /\ _ => split end.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + constructor.
    + constructor.
    + constructor.
    + reflexivity.
    + simpl. exact Hxd.
    + simpl. exact Hys.
    + intros i Hi. rewrite Zlength_nil in Hi. lia.
  - pose proof (can_print_team_bounds__early_exit pages x y (Zlength (p :: pages)) Htail).
    rewrite Zlength_cons in *. lia.
Qed.
Lemma single_page_infeasible__early_exit :
  forall p x y,
    0 <= x -> 0 <= y -> p > 2 * x + y ->
    ~ CanPrintAll [p] x y.
Proof.
  intros p x y Hx Hy Htoo_big Hprint.
  pose proof (can_print_cons_cases__early_exit p [] x y (Zlength [p]) Hprint) as Hcases.
  destruct Hcases as [(d & s & Hd & Hs & Hcover & Htail)|Htail].
  - pose proof (can_print_nonnegative_budgets__early_exit [] (x - d) (y - s)
      (Zlength [p] - 1) Htail) as [Hxd Hys]. lia.
  - pose proof (can_print_team_bounds__early_exit [] x y (Zlength [p]) Htail).
    rewrite !Zlength_cons, Zlength_nil in *. lia.
Qed.
Lemma spec_from_prefix_stop__early_exit :
  forall original sorted x0 y0 x y i,
    0 <= i < Zlength sorted ->
    0 <= x -> 0 <= y ->
    Permutation original sorted ->
    mono_nondec sorted ->
    PrefixResourceState sorted x0 y0 i x y ->
    ~ CanPrintAll [Znth i sorted 0] x y ->
    Spec original x0 y0 i.
Proof.
  intros original sorted x0 y0 x y i Hi Hx Hy Hperm Hmono Hstate Hstop.
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists i. split; [split|reflexivity].
  - pose proof (prefix_resource_state_feasible_prefix__early_exit
      sorted x0 y0 i x y ltac:(lia) Hx Hy Hstate) as Hprefix.
    unfold CanPrintAll in Hprefix.
    rewrite Zlength_sublist in Hprefix by lia.
    replace (i - 0) with i in Hprefix by lia.
    pose proof (can_print_extend_unselected__early_exit
      (sublist 0 i sorted) (sublist i (Zlength sorted) sorted)
      x0 y0 i Hprefix) as Hfull.
    rewrite <- (sublist_split 0 (Zlength sorted) i sorted) in Hfull by lia.
    rewrite (sublist_self sorted (Zlength sorted) eq_refl) in Hfull.
    eapply can_print_permutation_pages__early_exit.
    + apply Permutation_sym. exact Hperm.
    + exact Hfull.
  - intros b Hb.
    pose proof (can_print_team_bounds__early_exit original x0 y0 b Hb) as Hbbound.
    assert (Hlenperm : Zlength original = Zlength sorted).
    { rewrite !Zlength_correct. apply Permutation_length in Hperm. lia. }
    destruct (Z_le_gt_dec b i) as [Hbi|Hib]; [exact Hbi|].
    assert (Hb0 : 0 <= b) by lia.
    pose proof (can_print_permutation_pages__early_exit original sorted x0 y0 b Hperm Hb) as Hsorted.
    pose proof (sorted_prefix_is_easiest__early_exit sorted x0 y0 b Hmono Hb0 Hsorted) as Hprefix_b.
    specialize (Hstate (sublist i b sorted)).
    assert (Hsuffix : CanPrintAll (sublist i b sorted) x y).
    { apply (proj1 Hstate).
      rewrite <- (sublist_split 0 b i sorted) by lia. exact Hprefix_b. }
    assert (Hshape : sublist i b sorted =
        Znth i sorted 0 :: sublist (i + 1) b sorted).
    { change (sublist i b sorted =
          [Znth i sorted 0] ++ sublist (i + 1) b sorted).
      rewrite <- (@sublist_single Z 0 i sorted) by lia.
      apply sublist_split; lia. }
    rewrite Hshape in Hsuffix.
    exfalso. apply Hstop.
    eapply can_print_all_head__early_exit. exact Hsuffix.
Qed.
Lemma spec_from_complete_prefix__early_exit :
  forall original sorted x0 y0 x y n,
    n = Zlength sorted ->
    0 <= x -> 0 <= y ->
    Permutation original sorted ->
    PrefixResourceState sorted x0 y0 n x y ->
    Spec original x0 y0 n.
Proof.
  intros original sorted x0 y0 x y n Hn Hx Hy Hperm Hstate.
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists n. split; [split|reflexivity].
  - pose proof (prefix_resource_state_feasible_prefix__early_exit
      sorted x0 y0 n x y ltac:(rewrite Hn; pose proof (Zlength_nonneg sorted); lia)
      Hx Hy Hstate) as Hfull.
    rewrite Hn, (sublist_self sorted (Zlength sorted) eq_refl) in Hfull.
    unfold CanPrintAll in Hfull. rewrite <- Hn in Hfull.
    eapply can_print_permutation_pages__early_exit.
    + apply Permutation_sym. exact Hperm.
    + exact Hfull.
  - intros b Hb.
    pose proof (can_print_team_bounds__early_exit original x0 y0 b Hb) as Hbound.
    rewrite Hn. rewrite !Zlength_correct in *.
    pose proof (Permutation_length Hperm). lia.
Qed.
