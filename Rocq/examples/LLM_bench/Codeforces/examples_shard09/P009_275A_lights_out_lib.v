Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(presses:3x3 grid)->3x3 grid. Each output bit is the
   initial on-state toggled by its own and side-adjacent press counts. *)
Definition Grid3 (g : list (list Z)) : Prop :=
  Zlength g = 3 /\ Forall (fun row => Zlength row = 3) g.

(* Press count at (i, j), or 0 when (i, j) is off the grid. The low side must be
   guarded explicitly: [Znth] is [nth (Z.to_nat n)], and [Z.to_nat] maps every
   negative index to 0, so an unguarded [Znth (-1)] would return row/column 0
   instead of the default. The high side already yields the default. *)
Definition cell (g : list (list Z)) (i j : Z) : Z :=
  if andb (0 <=? i) (0 <=? j) then Znth j (Znth i g []) 0 else 0.

Definition toggles (g : list (list Z)) (i j : Z) : Z :=
  cell g i j + cell g (i - 1) j + cell g (i + 1) j +
  cell g i (j - 1) + cell g i (j + 1).
Definition Pre (g : list (list Z)) : Prop :=
  (* Grid3 g /\ Forall (Forall (fun x => 0 <= x <= 100)) g *)
  True.
Definition Spec (g out : list (list Z)) : Prop :=
  Grid3 out /\ forall i j, 0 <= i < 3 -> 0 <= j < 3 ->
    cell out i j = if Z.even (toggles g i j) then 1 else 0.

(* The two local direction tables, exposed so the C loop invariants can retain
   the exact initialized contents of the corresponding local arrays. *)
Definition lights_di : list Z := [0; -1; 1; 0; 0].
Definition lights_dj : list Z := [0; 0; 0; -1; 1].

(* Mathematical meaning of a row-major prefix of the output grid.  Cells at
   and after [k] remain unconstrained, which permits the initially undefined
   output storage to be represented by an arbitrary 3-by-3 logical grid. *)
Definition OutputPrefix
    (g out : list (list Z)) (k : Z) : Prop :=
  Grid3 out /\
  forall i j, 0 <= i < 3 -> 0 <= j < 3 -> 3 * i + j < k ->
    cell out i j =
      if Z.even (toggles g i j) then 1 else 0.

(* Meaning of the accumulator after visiting a prefix of the fixed five
   orthogonal-neighbour offsets. *)
Definition TogglePrefix
    (g : list (list Z)) (i j d tog : Z) : Prop :=
  (d = 0 /\ tog = 0) \/
  (d = 1 /\ tog = cell g i j) \/
  (d = 2 /\ tog = cell g i j + cell g (i - 1) j) \/
  (d = 3 /\ tog = cell g i j + cell g (i - 1) j + cell g (i + 1) j) \/
  (d = 4 /\ tog = cell g i j + cell g (i - 1) j + cell g (i + 1) j +
                        cell g i (j - 1)) \/
  (d = 5 /\ tog = toggles g i j).

(* A canonical staged view of one output row.  Positions before the row-major
   frontier [k] are initialized to their final values; every later position is
   still genuinely uninitialized and is represented by [None]. *)
Definition output_bit (g : list (list Z)) (i j : Z) : Z :=
  if Z.even (toggles g i j) then 1 else 0.

Definition staged_output_cell
    (g : list (list Z)) (i j k : Z) : option Z :=
  if (3 * i + j <? k)%Z then Some (output_bit g i j) else None.

Definition staged_output_row
    (g : list (list Z)) (i k : Z) : list (option Z) :=
  [staged_output_cell g i 0 k;
   staged_output_cell g i 1 k;
   staged_output_cell g i 2 k].

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.Bool.Bool.
Lemma toggle_prefix_add_in_bounds__toggle_transitions :
  forall g i j d tog,
    0 <= d < 5 ->
    TogglePrefix g i j d tog ->
    TogglePrefix g i j (d + 1)
      (tog + cell g (i + Znth d lights_di 0)
                    (j + Znth d lights_dj 0)).
Proof.
  intros g i j d tog Hd Hprefix.
  assert (Hdi0 : Znth 0 lights_di 0 = 0).
  { unfold lights_di. rewrite Znth0_cons. reflexivity. }
  assert (Hdi1 : Znth 1 lights_di 0 = -1).
  { unfold lights_di. rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Hdi2 : Znth 2 lights_di 0 = 1).
  { unfold lights_di. do 2 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdi3 : Znth 3 lights_di 0 = 0).
  { unfold lights_di. do 3 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdi4 : Znth 4 lights_di 0 = 0).
  { unfold lights_di. do 4 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdj0 : Znth 0 lights_dj 0 = 0).
  { unfold lights_dj. rewrite Znth0_cons. reflexivity. }
  assert (Hdj1 : Znth 1 lights_dj 0 = 0).
  { unfold lights_dj. rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Hdj2 : Znth 2 lights_dj 0 = 0).
  { unfold lights_dj. do 2 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdj3 : Znth 3 lights_dj 0 = -1).
  { unfold lights_dj. do 3 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdj4 : Znth 4 lights_dj 0 = 1).
  { unfold lights_dj. do 4 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  unfold TogglePrefix in *.
  destruct Hprefix as
      [[Hd0 Htog] |
       [[Hd1 Htog] |
        [[Hd2 Htog] |
         [[Hd3 Htog] |
          [[Hd4 Htog] | [Hd5 Htog]]]]]].
  - subst d tog. rewrite Hdi0, Hdj0. right; left. split; [lia |].
    replace (i + 0) with i by lia. replace (j + 0) with j by lia. lia.
  - subst d tog. rewrite Hdi1, Hdj1. right; right; left. split; [lia |].
    replace (i + -1) with (i - 1) by lia.
    replace (j + 0) with j by lia. reflexivity.
  - subst d tog. rewrite Hdi2, Hdj2. right; right; right; left. split; [lia |].
    replace (j + 0) with j by lia. ring.
  - subst d tog. rewrite Hdi3, Hdj3. right; right; right; right; left. split; [lia |].
    replace (i + 0) with i by lia.
    replace (j + -1) with (j - 1) by lia. ring.
  - subst d tog. rewrite Hdi4, Hdj4. right; right; right; right; right. split; [lia |].
    replace (i + 0) with i by lia. unfold toggles. ring.
  - lia.
Qed.
Lemma cell_bounds_from_grid_facts__valid_neighbor_a :
  forall g default i j,
    Zlength g = 3 ->
    (forall r, 0 <= r < 3 -> Zlength (Znth r g default) = 3) ->
    (forall r c, (0 <= r < 3 /\ 0 <= c) /\ c < 3 ->
       0 <= Znth c (Znth r g default) 0 <= 100) ->
    0 <= cell g i j <= 100.
Proof.
  intros g default i j Hg Hrows Hcells.
  unfold cell.
  destruct ((0 <=? i) && (0 <=? j))%bool eqn:Hnonneg.
  - apply andb_true_iff in Hnonneg.
    destruct Hnonneg as [Hi Hj].
    apply Z.leb_le in Hi.
    apply Z.leb_le in Hj.
    destruct (Z_lt_ge_dec i 3) as [Hi3 | Hi3].
    + destruct (Z_lt_ge_dec j 3) as [Hj3 | Hj3].
      * rewrite (Znth_indep g i (@nil Z) default) by lia.
        apply Hcells.
        lia.
      * assert (Hrow : Zlength (Znth i g (@nil Z)) = 3).
        {
          rewrite (Znth_indep g i (@nil Z) default) by lia.
          apply Hrows.
          lia.
        }
        change (0 <= nth (Z.to_nat j) (Znth i g (@nil Z)) 0 <= 100).
        rewrite nth_overflow.
        2: { rewrite Zlength_correct in Hrow. lia. }
        lia.
    + assert (Hout : Znth i g (@nil Z) = (@nil Z)).
      {
        unfold Znth.
        apply nth_overflow.
        rewrite Zlength_correct in Hg.
        lia.
      }
      rewrite Hout.
      unfold Znth.
      destruct (Z.to_nat j); simpl; lia.
  - lia.
Qed.
Lemma toggle_prefix_bounds__valid_neighbor_a :
  forall g default i j d tog,
    Zlength g = 3 ->
    (forall r, 0 <= r < 3 -> Zlength (Znth r g default) = 3) ->
    (forall r c, (0 <= r < 3 /\ 0 <= c) /\ c < 3 ->
       0 <= Znth c (Znth r g default) 0 <= 100) ->
    TogglePrefix g i j d tog ->
    0 <= tog <= 100 * d.
Proof.
  intros g default i j d tog Hg Hrows Hcells Hprefix.
  pose proof
    (cell_bounds_from_grid_facts__valid_neighbor_a
       g default i j Hg Hrows Hcells) as H0.
  pose proof
    (cell_bounds_from_grid_facts__valid_neighbor_a
       g default (i - 1) j Hg Hrows Hcells) as H1.
  pose proof
    (cell_bounds_from_grid_facts__valid_neighbor_a
       g default (i + 1) j Hg Hrows Hcells) as H2.
  pose proof
    (cell_bounds_from_grid_facts__valid_neighbor_a
       g default i (j - 1) Hg Hrows Hcells) as H3.
  pose proof
    (cell_bounds_from_grid_facts__valid_neighbor_a
       g default i (j + 1) Hg Hrows Hcells) as H4.
  unfold TogglePrefix in Hprefix.
  unfold toggles in Hprefix.
  destruct Hprefix as
      [[Hd0 Htog] |
       [[Hd1 Htog] |
        [[Hd2 Htog] |
         [[Hd3 Htog] |
          [[Hd4 Htog] | [Hd5 Htog]]]]]];
    subst d tog; lia.
Qed.
Lemma Znth_indep__output_write :
  forall (A : Type) (l : list A) n (d d' : A),
    0 <= n < Zlength l -> Znth n l d = Znth n l d'.
Proof.
  intros A l n d d' Hn.
  unfold Znth.
  apply nth_indep.
  rewrite Zlength_correct in Hn.
  lia.
Qed.
Lemma cell_bounds__valid_neighbor_b :
  forall g default i j,
    Zlength g = 3 ->
    (forall r, 0 <= r < 3 -> Zlength (Znth r g default) = 3) ->
    (forall r c, (0 <= r < 3 /\ 0 <= c) /\ c < 3 ->
      0 <= Znth c (Znth r g default) 0 <= 100) ->
    0 <= cell g i j <= 100.
Proof.
  intros g default i j Hlen Hrowlens Hcells.
  unfold cell.
  destruct (((0 <=? i)%Z && (0 <=? j)%Z)%bool) eqn:Hguard.
  - apply andb_true_iff in Hguard as [Hi Hj].
    apply Z.leb_le in Hi. apply Z.leb_le in Hj.
    destruct (Z_lt_ge_dec i 3) as [Hi3 | Hi3].
    + destruct (Z_lt_ge_dec j 3) as [Hj3 | Hj3].
      * assert (Hrow : Znth i g (@nil Z) = Znth i g default).
        { apply Znth_indep__output_write. lia. }
        rewrite Hrow.
        apply Hcells. lia.
      * assert (Hrow : Znth i g (@nil Z) = Znth i g default).
        { apply Znth_indep__output_write. lia. }
        rewrite Hrow.
        assert (Hrowlen := Hrowlens i ltac:(lia)).
        assert (Hjn : (length (Znth i g default) <= Z.to_nat j)%nat).
        { rewrite Zlength_correct in Hrowlen. lia. }
        unfold Znth.
        rewrite nth_overflow by exact Hjn.
        lia.
    + assert (Hin : (length g <= Z.to_nat i)%nat).
      { rewrite Zlength_correct in Hlen. lia. }
      assert (Hout : Znth i g (@nil Z) = (@nil Z)).
      { unfold Znth. apply nth_overflow. exact Hin. }
      rewrite Hout.
      assert (Hnil : Znth j (@nil Z) 0 = 0).
      { unfold Znth. destruct (Z.to_nat j); reflexivity. }
      rewrite Hnil.
      split; lia.
  - change (0 <= (0 : Z) <= 100).
    split; lia.
Qed.
Lemma cell_in_bounds__valid_neighbor_b :
  forall g default i j,
    Zlength g = 3 ->
    0 <= i < 3 ->
    0 <= j < 3 ->
    cell g i j = Znth j (Znth i g default) 0.
Proof.
  intros g default i j Hlen Hi Hj.
  unfold cell.
  replace ((0 <=? i)%Z) with true by
    (symmetry; apply Z.leb_le; lia).
  replace ((0 <=? j)%Z) with true by
    (symmetry; apply Z.leb_le; lia).
  simpl.
  assert (Hrow : Znth i g (@nil Z) = Znth i g default).
  { apply Znth_indep__output_write. lia. }
  rewrite Hrow.
  reflexivity.
Qed.
Lemma toggle_prefix_next_bounds__valid_neighbor_b :
  forall g default i j d tog,
    Zlength g = 3 ->
    (forall r, 0 <= r < 3 -> Zlength (Znth r g default) = 3) ->
    (forall r c, (0 <= r < 3 /\ 0 <= c) /\ c < 3 ->
      0 <= Znth c (Znth r g default) 0 <= 100) ->
    0 <= d < 5 ->
    TogglePrefix g i j d tog ->
    0 <= tog + cell g (i + Znth d lights_di 0)
                       (j + Znth d lights_dj 0) <= 500.
Proof.
  intros g default i j d tog Hlen Hrowlens Hcells Hd Hprefix.
  pose proof (cell_bounds__valid_neighbor_b
    g default i j Hlen Hrowlens Hcells) as Hc0.
  pose proof (cell_bounds__valid_neighbor_b
    g default (i - 1) j Hlen Hrowlens Hcells) as Hc1.
  pose proof (cell_bounds__valid_neighbor_b
    g default (i + 1) j Hlen Hrowlens Hcells) as Hc2.
  pose proof (cell_bounds__valid_neighbor_b
    g default i (j - 1) Hlen Hrowlens Hcells) as Hc3.
  pose proof (cell_bounds__valid_neighbor_b
    g default i (j + 1) Hlen Hrowlens Hcells) as Hc4.
  assert (Hdi0 : Znth 0 lights_di 0 = 0).
  { unfold lights_di. rewrite Znth0_cons. reflexivity. }
  assert (Hdi1 : Znth 1 lights_di 0 = -1).
  { unfold lights_di. rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Hdi2 : Znth 2 lights_di 0 = 1).
  { unfold lights_di. do 2 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdi3 : Znth 3 lights_di 0 = 0).
  { unfold lights_di. do 3 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdi4 : Znth 4 lights_di 0 = 0).
  { unfold lights_di. do 4 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdj0 : Znth 0 lights_dj 0 = 0).
  { unfold lights_dj. rewrite Znth0_cons. reflexivity. }
  assert (Hdj1 : Znth 1 lights_dj 0 = 0).
  { unfold lights_dj. rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Hdj2 : Znth 2 lights_dj 0 = 0).
  { unfold lights_dj. do 2 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdj3 : Znth 3 lights_dj 0 = -1).
  { unfold lights_dj. do 3 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  assert (Hdj4 : Znth 4 lights_dj 0 = 1).
  { unfold lights_dj. do 4 (rewrite Znth_cons by lia). rewrite Znth0_cons. reflexivity. }
  unfold TogglePrefix in Hprefix.
  destruct Hprefix as
      [[Hd0 Htog] |
       [[Hd1 Htog] |
        [[Hd2 Htog] |
         [[Hd3 Htog] |
          [[Hd4 Htog] | [Hd5 Htog]]]]]].
  - subst d tog. rewrite Hdi0, Hdj0.
    replace (i + 0) with i by lia. replace (j + 0) with j by lia.
    split; lia.
  - subst d tog. rewrite Hdi1, Hdj1.
    replace (i + -1) with (i - 1) by lia. replace (j + 0) with j by lia.
    split; lia.
  - subst d tog. rewrite Hdi2, Hdj2.
    replace (j + 0) with j by lia.
    split; lia.
  - subst d tog. rewrite Hdi3, Hdj3.
    replace (i + 0) with i by lia. replace (j + -1) with (j - 1) by lia.
    split; lia.
  - subst d tog. rewrite Hdi4, Hdj4.
    replace (i + 0) with i by lia.
    split; lia.
  - lia.
Qed.
Lemma toggle_prefix_skip_out_of_bounds__toggle_transitions :
  forall g i j d tog,
    0 <= d < 5 ->
    TogglePrefix g i j d tog ->
    cell g (i + Znth d lights_di 0)
           (j + Znth d lights_dj 0) = 0 ->
    TogglePrefix g i j (d + 1) tog.
Proof.
  intros g i j d tog Hd Hprefix Hcell.
  pose proof
    (toggle_prefix_add_in_bounds__toggle_transitions
       g i j d tog Hd Hprefix) as Hstep.
  rewrite Hcell, Z.add_0_r in Hstep.
  exact Hstep.
Qed.
Lemma even_of_nonnegative_rem_zero__row1_write :
  forall n, 0 <= n -> Z.rem n 2 = 0 -> Z.even n = true.
Proof.
  intros n Hn Hrem.
  apply Z.even_spec.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  apply (proj1 (Z.mod_divide n 2 ltac:(lia))) in Hrem.
  destruct Hrem as [k Hk].
  exists k. lia.
Qed.
Lemma odd_of_nonnegative_rem_nonzero__row1_write :
  forall n, 0 <= n -> Z.rem n 2 <> 0 -> Z.even n = false.
Proof.
  intros n Hn Hrem.
  destruct (Z.even n) eqn:Heven; [|reflexivity].
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  exfalso. apply Hrem.
  rewrite Hk, Z.mul_comm, Z.rem_mul; lia.
Qed.
Lemma staged_output_complete__final_result :
  forall g i,
    0 <= i < 3 ->
    staged_output_row g i 9 =
      map (@Some Z)
        [output_bit g i 0; output_bit g i 1; output_bit g i 2].
Proof.
  intros g i Hi.
  unfold staged_output_row, staged_output_cell.
  replace (3 * i + 0 <? 9)%Z with true by
    (symmetry; apply Z.ltb_lt; lia).
  replace (3 * i + 1 <? 9)%Z with true by
    (symmetry; apply Z.ltb_lt; lia).
  replace (3 * i + 2 <? 9)%Z with true by
    (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.
Lemma output_bit_grid_spec__final_result :
  forall g,
    Spec g
      [[output_bit g 0 0; output_bit g 0 1; output_bit g 0 2];
       [output_bit g 1 0; output_bit g 1 1; output_bit g 1 2];
       [output_bit g 2 0; output_bit g 2 1; output_bit g 2 2]].
Proof.
  intros g.
  unfold Spec, Grid3.
  split.
  - split; [reflexivity | repeat constructor].
  - intros i j Hi Hj.
    assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia;
      assert (j = 0 \/ j = 1 \/ j = 2) as [-> | [-> | ->]] by lia;
      unfold cell, output_bit; reflexivity.
Qed.

(* --- 2D staged view of [out], for invariants that keep IntArray2::mixed_full
   whole instead of naming the three rows separately. --- *)
Definition staged_output (g : list (list Z)) (k : Z) : list (list (option Z)) :=
  [staged_output_row g 0 k; staged_output_row g 1 k; staged_output_row g 2 k].

Definition out_grid (g : list (list Z)) : list (list Z) :=
  [[output_bit g 0 0; output_bit g 0 1; output_bit g 0 2];
   [output_bit g 1 0; output_bit g 1 1; output_bit g 1 2];
   [output_bit g 2 0; output_bit g 2 1; output_bit g 2 2]].

Lemma staged_output_init : forall g,
  staged_output g 0 = repeat (repeat (@None Z) (Z.to_nat 3)) (Z.to_nat 3).
Proof.
  intros g. unfold staged_output, staged_output_row, staged_output_cell.
  reflexivity.
Qed.

Lemma staged_output_final : forall g,
  staged_output g 9 = map (map (@Some Z)) (out_grid g).
Proof.
  intros g. unfold staged_output, out_grid.
  rewrite (staged_output_complete__final_result g 0) by lia.
  rewrite (staged_output_complete__final_result g 1) by lia.
  rewrite (staged_output_complete__final_result g 2) by lia.
  reflexivity.
Qed.

Lemma spec_out_grid : forall g, Spec g (out_grid g).
Proof. intros g. unfold out_grid. apply output_bit_grid_spec__final_result. Qed.

Lemma staged_output_advance : forall g i j,
  (i = 0 \/ i = 1 \/ i = 2) ->
  (j = 0 \/ j = 1 \/ j = 2) ->
  replace_Znth i
    (replace_Znth j (Some (output_bit g i j))
       (Znth i (staged_output g (3 * i + j)) nil))
    (staged_output g (3 * i + j))
  = staged_output g (3 * i + j + 1).
Proof.
  intros g i j Hi Hj.
  destruct Hi as [-> | [-> | ->]]; destruct Hj as [-> | [-> | ->]];
    unfold staged_output, staged_output_row, staged_output_cell;
    reflexivity.
Qed.

(* A neighbour that falls off the grid contributes nothing.  Covers all four
   directions: below 0 the [cell] guard is false, at or above 3 the underlying
   [Znth] overflows to its default. *)
Lemma cell_out_of_range__toggle_skip :
  forall g default r c,
    Zlength g = 3 ->
    (forall x, 0 <= x < 3 -> Zlength (Znth x g default) = 3) ->
    (r < 0 \/ 3 <= r \/ c < 0 \/ 3 <= c) ->
    cell g r c = 0.
Proof.
  intros g default r c Hlen Hrowlens Hout.
  unfold cell.
  destruct (((0 <=? r)%Z && (0 <=? c)%Z)%bool) eqn:Hguard; [| reflexivity].
  apply andb_true_iff in Hguard as [Hr Hc].
  apply Z.leb_le in Hr. apply Z.leb_le in Hc.
  destruct (Z_lt_ge_dec r 3) as [Hr3 | Hr3].
  - assert (Hc3 : 3 <= c) by lia.
    assert (Hrow : Znth r g (@nil Z) = Znth r g default)
      by (apply Znth_indep__output_write; lia).
    rewrite Hrow.
    assert (Hrowlen := Hrowlens r ltac:(lia)).
    assert (Hcn : (length (Znth r g default) <= Z.to_nat c)%nat)
      by (rewrite Zlength_correct in Hrowlen; lia).
    unfold Znth. rewrite nth_overflow by exact Hcn. reflexivity.
  - assert (Hrn : (length g <= Z.to_nat r)%nat)
      by (rewrite Zlength_correct in Hlen; lia).
    assert (Hnil : Znth r g (@nil Z) = (@nil Z))
      by (unfold Znth; apply nth_overflow; exact Hrn).
    rewrite Hnil.
    unfold Znth. destruct (Z.to_nat c); reflexivity.
Qed.
