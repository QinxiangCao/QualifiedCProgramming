Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition BinaryValue (d : list Z) : Z := fold_left (fun a b => 2 * a + b) d 0.
Definition BinaryRep (v : Z) (d : list Z) : Prop :=
  d <> [] /\ Forall (fun z => z = 0 \/ z = 1) d /\ BinaryValue d = v /\
  ((v = 0 /\ d = [0]) \/ (v > 0 /\ Znth 0 d 0 = 1)).
Definition GambitPair (a b k : Z) (q : list Z * list Z) : Prop :=
  let ' (x, y) := q in Zlength x = a + b /\ Zlength y = a + b /\
  Forall (fun z => z = 0 \/ z = 1) x /\ Forall (fun z => z = 0 \/ z = 1) y /\
  (#(fun i : Z => 0 <= i < Zlength x /\ Znth i x 0 = 0)) = a /\ (#(fun i : Z => 0 <= i < Zlength x /\ Znth i x 0 = 1)) = b /\ (#(fun i : Z => 0 <= i < Zlength y /\ Znth i y 0 = 0)) = a /\ (#(fun i : Z => 0 <= i < Zlength y /\ Znth i y 0 = 1)) = b /\
  Znth 0 x 0 = 1 /\ Znth 0 y 0 = 1 /\ BinaryValue x >= BinaryValue y /\
  exists diff, BinaryRep (BinaryValue x - BinaryValue y) diff /\ (#(fun i : Z => 0 <= i < Zlength diff /\ Znth i diff 0 = 1)) = k.
Definition Pre (a b k : Z) : Prop :=
  (* Every clause below is stated explicitly in the P062 solver Require, which
     therefore omits the Pre(...) call:
       0 <= a /\ 1 <= b /\ 0 <= k <= a + b /\ a + b <= 200000. *)
  True.
Definition Spec (a b k : Z) (out : option (list Z * list Z)) : Prop :=
  (out = None /\ ~exists q, GambitPair a b k q) \/ (exists q, out = Some q /\ GambitPair a b k q).

Definition pair {A B} (x : A) (y : B) : A * B := (x, y).

(* Transparent canonical values for the construction.  These describe the
   mathematical result, independently of the two C initialization loops. *)
Definition GambitX (a b : Z) : list Z :=
  repeat 1 (Z.to_nat b) ++ repeat 0 (Z.to_nat a).

Definition GambitSource (a b k : Z) : Z :=
  if Z.leb k a then b - 1 else a + b - 1 - k.

Definition GambitTarget (a b k : Z) : Z :=
  if Z.leb k a then b - 1 + k else a + b - 1.

Definition GambitY (a b k : Z) : list Z :=
  if Z.eqb k 0 then GambitX a b
  else replace_Znth (GambitTarget a b k) 1
         (replace_Znth (GambitSource a b k) 0 (GambitX a b)).

Definition EncodeDigits (digits : list Z) : list Z :=
  map (fun d => d + 48) digits.

Definition CanonicalGambit (a b k : Z) : Prop :=
  GambitPair a b k (GambitX a b, GambitY a b k).

Definition GambitImpossible (a b k : Z) : Prop :=
  ~ exists q, GambitPair a b k q.

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.ZArith.Zpow_facts.
Lemma repeat_Z_succ_app__initialization : forall (c z : Z),
  0 <= z -> repeat c (Z.to_nat (z + 1)) = repeat c (Z.to_nat z) ++ [c].
Proof.
  intros c z Hz.
  replace (Z.to_nat (z + 1)) with (S (Z.to_nat z)) by lia.
  remember (Z.to_nat z) as n.
  clear z Hz Heqn.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    f_equal.
    exact IH.
Qed.
Lemma set_card_Z_as_sum__canonical_construction :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma digit_card_count_occ__canonical_construction :
  forall (l : list Z) d,
    #(fun i : Z => 0 <= i < Zlength l /\ Znth i l 0 = d) =
    Z.of_nat (count_occ Z.eq_dec l d).
Proof.
  intros l d.
  rewrite set_card_Z_as_sum__canonical_construction.
  induction l as [|x xs IH].
  - rewrite Zlength_nil, sum_Z_range_empty by lia. reflexivity.
  - rewrite (sum_Z_range_Znth_cons 0 x xs
      (fun z => if prop_dec (z = d) then 1 else 0)).
    simpl count_occ.
    destruct (prop_dec (x = d)) as [Hxd | Hxd];
      destruct (Z.eq_dec x d) as [Hxd' | Hxd']; try contradiction;
      rewrite IH; try reflexivity;
      rewrite Nat2Z.inj_succ; lia.
Qed.
Lemma Zlength_replace_Znth__canonical_construction :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. revert n.
  induction l as [|x xs IH]; simpl; intros n; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n) as [|m].
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IH (Z.of_nat m)).
    replace (Z.to_nat (Z.of_nat m)) with m in IH by lia.
    rewrite IH. lia.
Qed.
Lemma Forall_replace_Znth__canonical_construction :
  forall (P : Z -> Prop) l i v,
    Forall P l -> P v -> Forall P (replace_Znth i v l).
Proof.
  intros P l i v Hl Hv.
  unfold replace_Znth.
  remember (Z.to_nat i) as n; clear i Heqn.
  revert n.
  induction Hl as [|x xs Hx Hxs IH]; intros n; simpl.
  - constructor.
  - destruct n; constructor; auto.
Qed.
Lemma count_occ_replace_Znth_add__canonical_construction :
  forall (l : list Z) i v d,
    0 <= i < Zlength l ->
    Znth i l 0 <> d -> v = d ->
    count_occ Z.eq_dec (replace_Znth i v l) d =
    S (count_occ Z.eq_dec l d).
Proof.
  induction l as [|x xs IH]; intros i v d Hi Hold Hv.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + unfold replace_Znth, Znth in *. simpl in *.
      destruct (Z.eq_dec v d); [|contradiction].
      destruct (Z.eq_dec x d); [contradiction |]. reflexivity.
    + assert (0 < i) by lia.
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons in Hold by lia.
      simpl count_occ.
      remember (Z.eq_dec x d) as q; destruct q; simpl.
      * f_equal. apply IH; [lia | exact Hold | exact Hv].
      * apply IH; [lia | exact Hold | exact Hv].
Qed.
Lemma count_occ_replace_Znth_remove__canonical_construction :
  forall (l : list Z) i v d,
    0 <= i < Zlength l ->
    Znth i l 0 = d -> v <> d ->
    S (count_occ Z.eq_dec (replace_Znth i v l) d) =
    count_occ Z.eq_dec l d.
Proof.
  induction l as [|x xs IH]; intros i v d Hi Hold Hv.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + unfold replace_Znth, Znth in *. simpl in *.
      destruct (Z.eq_dec v d); [contradiction |].
      destruct (Z.eq_dec x d); [reflexivity | contradiction].
    + assert (0 < i) by lia.
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons in Hold by lia.
      simpl count_occ.
      remember (Z.eq_dec x d) as q; destruct q; simpl.
      * f_equal. apply IH; [lia | exact Hold | exact Hv].
      * apply IH; [lia | exact Hold | exact Hv].
Qed.
Lemma binary_fold_affine__canonical_construction :
  forall (l : list Z) acc,
    fold_left (fun a b => 2 * a + b) l acc =
    acc * 2 ^ Zlength l + BinaryValue l.
Proof.
  induction l as [|x xs IH]; intros acc.
  - unfold BinaryValue. simpl. ring.
  - change (fold_left (fun a b => 2 * a + b) xs (2 * acc + x) =
      acc * 2 ^ Zlength (x :: xs) +
      fold_left (fun a b => 2 * a + b) xs x).
    rewrite (IH (2 * acc + x)), (IH x).
    rewrite Zlength_cons.
    rewrite Z.pow_succ_r by apply Zlength_nonneg.
    ring.
Qed.
Lemma binary_value_cons__canonical_construction :
  forall x l,
    BinaryValue (x :: l) = x * 2 ^ Zlength l + BinaryValue l.
Proof.
  intros x l.
  unfold BinaryValue at 1. simpl fold_left.
  rewrite binary_fold_affine__canonical_construction.
  ring.
Qed.
Lemma binary_value_app__canonical_construction :
  forall l1 l2,
    BinaryValue (l1 ++ l2) =
    BinaryValue l1 * 2 ^ Zlength l2 + BinaryValue l2.
Proof.
  intros l1 l2.
  unfold BinaryValue at 1.
  rewrite fold_left_app.
  rewrite binary_fold_affine__canonical_construction.
  reflexivity.
Qed.
Lemma binary_value_repeat_zero__canonical_construction :
  forall n, BinaryValue (repeat 0 n) = 0.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite binary_value_cons__canonical_construction, IH. ring.
Qed.
Lemma binary_value_repeat_one__canonical_construction :
  forall n, BinaryValue (repeat 1 n) = 2 ^ Z.of_nat n - 1.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl repeat.
    rewrite binary_value_cons__canonical_construction, IH.
    rewrite Zlength_correct, repeat_length.
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    ring.
Qed.
Lemma binary_value_replace_Znth__canonical_construction :
  forall (l : list Z) i v,
    0 <= i < Zlength l ->
    BinaryValue (replace_Znth i v l) =
    BinaryValue l + (v - Znth i l 0) * 2 ^ (Zlength l - 1 - i).
Proof.
  induction l as [|x xs IH]; intros i v Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + unfold replace_Znth, Znth. simpl.
      do 2 rewrite binary_value_cons__canonical_construction.
      rewrite Zlength_cons.
      replace (Z.succ (Zlength xs) - 1 - 0) with (Zlength xs) by lia.
      ring.
    + assert (0 < i) by lia.
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons by lia.
      do 2 rewrite binary_value_cons__canonical_construction.
      rewrite Zlength_replace_Znth__canonical_construction.
      rewrite IH by lia.
      rewrite Zlength_cons.
      replace (Z.succ (Zlength xs) - 1 - i)
        with (Zlength xs - 1 - (i - 1)) by lia.
      ring.
Qed.
Lemma gambit_x_length__canonical_construction :
  forall a b, 0 <= a -> 0 <= b -> Zlength (GambitX a b) = a + b.
Proof.
  intros a b Ha Hb.
  unfold GambitX.
  rewrite Zlength_app, !Zlength_correct, !repeat_length.
  rewrite !Z2Nat.id by lia. lia.
Qed.
Lemma Forall_repeat__canonical_construction :
  forall {A : Type} (P : A -> Prop) x n,
    P x -> Forall P (repeat x n).
Proof.
  intros A P x n Hx. induction n; simpl; constructor; auto.
Qed.
Lemma gambit_x_digits__canonical_construction :
  forall a b,
    Forall (fun z => z = 0 \/ z = 1) (GambitX a b).
Proof.
  intros a b. unfold GambitX.
  apply Forall_app. split;
    apply Forall_repeat__canonical_construction; tauto.
Qed.
Lemma gambit_x_Znth_one__canonical_construction :
  forall a b i,
    0 <= a -> 0 <= i < b ->
    Znth i (GambitX a b) 0 = 1.
Proof.
  intros a b i Ha Hi. unfold GambitX.
  rewrite app_Znth1.
  - apply Znth_repeat_lt. rewrite Z2Nat.id by lia. exact Hi.
  - rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. exact Hi.
Qed.
Lemma gambit_x_Znth_zero__canonical_construction :
  forall a b i,
    0 <= a -> 0 <= b -> b <= i < a + b ->
    Znth i (GambitX a b) 0 = 0.
Proof.
  intros a b i Ha Hb Hi. unfold GambitX.
  rewrite app_Znth2.
  - apply Znth_repeat.
  - rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. lia.
Qed.
Lemma gambit_x_zero_count__canonical_construction :
  forall a b, 0 <= a -> 0 <= b ->
    #(fun i : Z =>
      0 <= i < Zlength (GambitX a b) /\ Znth i (GambitX a b) 0 = 0) = a.
Proof.
  intros a b Ha Hb.
  rewrite digit_card_count_occ__canonical_construction.
  unfold GambitX. rewrite count_occ_app.
  rewrite (@count_occ_repeat_neq Z Z.eq_dec 0 1 (Z.to_nat b)) by lia.
  rewrite (@count_occ_repeat_eq Z Z.eq_dec 0 0 (Z.to_nat a)) by reflexivity.
  simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma gambit_x_one_count__canonical_construction :
  forall a b, 0 <= a -> 0 <= b ->
    #(fun i : Z =>
      0 <= i < Zlength (GambitX a b) /\ Znth i (GambitX a b) 0 = 1) = b.
Proof.
  intros a b Ha Hb.
  rewrite digit_card_count_occ__canonical_construction.
  unfold GambitX. rewrite count_occ_app.
  rewrite (@count_occ_repeat_eq Z Z.eq_dec 1 1 (Z.to_nat b)) by reflexivity.
  rewrite (@count_occ_repeat_neq Z Z.eq_dec 1 0 (Z.to_nat a)) by lia.
  rewrite Nat.add_0_r, Z2Nat.id by lia. reflexivity.
Qed.
Lemma gambit_x_value__canonical_construction :
  forall a b, 0 <= a -> 0 <= b ->
    BinaryValue (GambitX a b) = (2 ^ b - 1) * 2 ^ a.
Proof.
  intros a b Ha Hb. unfold GambitX.
  rewrite binary_value_app__canonical_construction.
  rewrite binary_value_repeat_one__canonical_construction.
  rewrite binary_value_repeat_zero__canonical_construction.
  rewrite Zlength_correct, repeat_length, !Z2Nat.id by lia. ring.
Qed.
Lemma digit_card_repeat_one__canonical_construction :
  forall k, 0 <= k ->
    #(fun i : Z =>
      0 <= i < Zlength (repeat 1 (Z.to_nat k)) /\
      Znth i (repeat 1 (Z.to_nat k)) 0 = 1) = k.
Proof.
  intros k Hk. rewrite digit_card_count_occ__canonical_construction.
  rewrite (@count_occ_repeat_eq Z Z.eq_dec 1 1 (Z.to_nat k)) by reflexivity.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma digit_card_repeat_one_zeros__canonical_construction :
  forall k r, 0 <= k -> 0 <= r ->
    #(fun i : Z =>
      0 <= i < Zlength
        (repeat 1 (Z.to_nat k) ++ repeat 0 (Z.to_nat r)) /\
      Znth i (repeat 1 (Z.to_nat k) ++ repeat 0 (Z.to_nat r)) 0 = 1) = k.
Proof.
  intros k r Hk Hr. rewrite digit_card_count_occ__canonical_construction.
  rewrite count_occ_app.
  rewrite (@count_occ_repeat_eq Z Z.eq_dec 1 1 (Z.to_nat k)) by reflexivity.
  rewrite (@count_occ_repeat_neq Z Z.eq_dec 1 0 (Z.to_nat r)) by lia.
  rewrite Nat.add_0_r, Z2Nat.id by lia. reflexivity.
Qed.
Lemma binary_value_repeat_one_zeros__canonical_construction :
  forall k r, 0 <= k -> 0 <= r ->
    BinaryValue (repeat 1 (Z.to_nat k) ++ repeat 0 (Z.to_nat r)) =
    (2 ^ k - 1) * 2 ^ r.
Proof.
  intros k r Hk Hr.
  rewrite binary_value_app__canonical_construction.
  rewrite binary_value_repeat_one__canonical_construction.
  rewrite binary_value_repeat_zero__canonical_construction.
  rewrite !Zlength_correct, !repeat_length, !Z2Nat.id by lia. ring.
Qed.
Lemma gambit_pair_zero__canonical_construction :
  forall a b, 0 <= a -> 1 <= b ->
    GambitPair a b 0 (GambitX a b, GambitX a b).
Proof.
  intros a b Ha Hb.
  unfold GambitPair; cbn.
  repeat split.
  - apply gambit_x_length__canonical_construction; lia.
  - apply gambit_x_length__canonical_construction; lia.
  - apply gambit_x_digits__canonical_construction.
  - apply gambit_x_digits__canonical_construction.
  - apply gambit_x_zero_count__canonical_construction; lia.
  - apply gambit_x_one_count__canonical_construction; lia.
  - apply gambit_x_zero_count__canonical_construction; lia.
  - apply gambit_x_one_count__canonical_construction; lia.
  - apply gambit_x_Znth_one__canonical_construction; lia.
  - apply gambit_x_Znth_one__canonical_construction; lia.
  - lia.
  - exists [0]. split.
    + unfold BinaryRep. repeat split.
      * discriminate.
      * constructor; [left; reflexivity | constructor].
      * change (0 = BinaryValue (GambitX a b) - BinaryValue (GambitX a b)).
        ring.
      * left. split.
        -- ring.
        -- reflexivity.
    + change (#(fun i : Z =>
        0 <= i < Zlength [0] /\ Znth i [0] 0 = 1) = 0).
      rewrite digit_card_count_occ__canonical_construction. reflexivity.
Qed.
Lemma gambit_pair_two_replacements__canonical_construction :
  forall a b k s t diff,
    0 <= a -> 1 <= b -> 0 < k ->
    1 <= s < t -> t < a + b ->
    Znth s (GambitX a b) 0 = 1 ->
    Znth t (GambitX a b) 0 = 0 ->
    BinaryRep
      (2 ^ (a + b - 1 - s) - 2 ^ (a + b - 1 - t)) diff ->
    #(fun i : Z => 0 <= i < Zlength diff /\ Znth i diff 0 = 1) = k ->
    GambitPair a b k
      (GambitX a b,
       replace_Znth t 1 (replace_Znth s 0 (GambitX a b))).
Proof.
  intros a b k s t diff Ha Hb Hk Hst Ht Hxs Hxt Hrep Hdiffcount.
  assert (Hlenx : Zlength (GambitX a b) = a + b)
    by (apply gambit_x_length__canonical_construction; lia).
  assert (Hsbound : 0 <= s < Zlength (GambitX a b)) by lia.
  assert (Htbound : 0 <= t < Zlength (GambitX a b)) by lia.
  assert (Hlen1 : Zlength (replace_Znth s 0 (GambitX a b)) = a + b)
    by (rewrite Zlength_replace_Znth__canonical_construction; exact Hlenx).
  assert (Htbound1 :
    0 <= t < Zlength (replace_Znth s 0 (GambitX a b))) by lia.
  assert (Hmid_t : Znth t (replace_Znth s 0 (GambitX a b)) 0 = 0).
  {
    rewrite Znth_replace_Znth_Diff with (i := s) (j := t).
    - exact Hxt.
    - exact Hsbound.
    - exact Htbound.
    - lia.
  }
  assert (Hleny :
    Zlength (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) = a + b)
    by (rewrite Zlength_replace_Znth__canonical_construction; exact Hlen1).
  assert (Hdigits_mid :
    Forall (fun z => z = 0 \/ z = 1)
      (replace_Znth s 0 (GambitX a b))).
  {
    apply Forall_replace_Znth__canonical_construction.
    - apply gambit_x_digits__canonical_construction.
    - tauto.
  }
  assert (Hdigits_y :
    Forall (fun z => z = 0 \/ z = 1)
      (replace_Znth t 1 (replace_Znth s 0 (GambitX a b)))).
  {
    apply Forall_replace_Znth__canonical_construction; [exact Hdigits_mid | tauto].
  }
  assert (Hzero_mid :
    count_occ Z.eq_dec (replace_Znth s 0 (GambitX a b)) 0 =
    S (count_occ Z.eq_dec (GambitX a b) 0)).
  {
    apply count_occ_replace_Znth_add__canonical_construction; auto; lia.
  }
  assert (Hzero_y :
    S (count_occ Z.eq_dec
      (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) 0) =
    count_occ Z.eq_dec (replace_Znth s 0 (GambitX a b)) 0).
  {
    apply count_occ_replace_Znth_remove__canonical_construction; auto; lia.
  }
  assert (Hone_mid :
    S (count_occ Z.eq_dec (replace_Znth s 0 (GambitX a b)) 1) =
    count_occ Z.eq_dec (GambitX a b) 1).
  {
    apply count_occ_replace_Znth_remove__canonical_construction; auto; lia.
  }
  assert (Hone_y :
    count_occ Z.eq_dec
      (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) 1 =
    S (count_occ Z.eq_dec (replace_Znth s 0 (GambitX a b)) 1)).
  {
    apply count_occ_replace_Znth_add__canonical_construction; auto; lia.
  }
  assert (Hzero_same :
    count_occ Z.eq_dec
      (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) 0 =
    count_occ Z.eq_dec (GambitX a b) 0).
  { apply Nat.succ_inj. rewrite Hzero_y, Hzero_mid. reflexivity. }
  assert (Hone_same :
    count_occ Z.eq_dec
      (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) 1 =
    count_occ Z.eq_dec (GambitX a b) 1).
  { rewrite Hone_y, Hone_mid. reflexivity. }
  assert (Hleadx : Znth 0 (GambitX a b) 0 = 1)
    by (apply gambit_x_Znth_one__canonical_construction; lia).
  assert (Hleadmid : Znth 0 (replace_Znth s 0 (GambitX a b)) 0 = 1).
  {
    rewrite Znth_replace_Znth_Diff with (i := s) (j := 0); auto; lia.
  }
  assert (Hleady :
    Znth 0 (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) 0 = 1).
  {
    rewrite Znth_replace_Znth_Diff with (i := t) (j := 0); auto; lia.
  }
  pose proof (binary_value_replace_Znth__canonical_construction
    (GambitX a b) s 0 Hsbound) as Hvalmid.
  pose proof (binary_value_replace_Znth__canonical_construction
    (replace_Znth s 0 (GambitX a b)) t 1 Htbound1) as Hvaly.
  rewrite Hlenx, Hxs in Hvalmid.
  rewrite Hlen1, Hmid_t in Hvaly.
  assert (Hdelta :
    BinaryValue (GambitX a b) -
      BinaryValue (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) =
    2 ^ (a + b - 1 - s) - 2 ^ (a + b - 1 - t)) by lia.
  assert (Hdeltanonneg :
    0 <= 2 ^ (a + b - 1 - s) - 2 ^ (a + b - 1 - t)).
  {
    pose proof Hrep as Hrep_copy.
    unfold BinaryRep in Hrep_copy.
    destruct Hrep_copy as [_ [_ [_ [[Hz _] | [Hpos _]]]]]; lia.
  }
  assert (Hyzero_card :
    #(fun i : Z =>
      0 <= i < Zlength
        (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) /\
      Znth i (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) 0 = 0) = a).
  {
    rewrite digit_card_count_occ__canonical_construction, Hzero_same.
    rewrite <- digit_card_count_occ__canonical_construction.
    apply gambit_x_zero_count__canonical_construction; lia.
  }
  assert (Hyone_card :
    #(fun i : Z =>
      0 <= i < Zlength
        (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) /\
      Znth i (replace_Znth t 1 (replace_Znth s 0 (GambitX a b))) 0 = 1) = b).
  {
    rewrite digit_card_count_occ__canonical_construction, Hone_same.
    rewrite <- digit_card_count_occ__canonical_construction.
    apply gambit_x_one_count__canonical_construction; lia.
  }
  unfold GambitPair; cbn.
  repeat split.
  - exact Hlenx.
  - exact Hleny.
  - apply gambit_x_digits__canonical_construction.
  - exact Hdigits_y.
  - apply gambit_x_zero_count__canonical_construction; lia.
  - apply gambit_x_one_count__canonical_construction; lia.
  - exact Hyzero_card.
  - exact Hyone_card.
  - exact Hleadx.
  - exact Hleady.
  - lia.
  - exists diff. split.
    + rewrite Hdelta. exact Hrep.
    + exact Hdiffcount.
Qed.
Lemma binary_rep_repeat_one__canonical_construction :
  forall k, 0 < k ->
    BinaryRep (2 ^ k - 1) (repeat 1 (Z.to_nat k)).
Proof.
  intros k Hk. unfold BinaryRep. repeat split.
  - intro Hnil.
    pose proof (f_equal (@length Z) Hnil) as Hlen.
    rewrite repeat_length in Hlen. simpl in Hlen.
    assert (0 < Z.to_nat k)%nat by lia. lia.
  - apply Forall_repeat__canonical_construction. tauto.
  - rewrite binary_value_repeat_one__canonical_construction.
    rewrite Z2Nat.id by lia. reflexivity.
  - right. split.
    + pose proof (proj1 (Z.pow_gt_1 2 k ltac:(lia)) Hk). lia.
    + apply Znth_repeat_lt. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma binary_rep_repeat_one_zeros__canonical_construction :
  forall k r, 0 < k -> 0 <= r ->
    BinaryRep ((2 ^ k - 1) * 2 ^ r)
      (repeat 1 (Z.to_nat k) ++ repeat 0 (Z.to_nat r)).
Proof.
  intros k r Hk Hr. unfold BinaryRep. repeat split.
  - intro Hnil.
    pose proof (f_equal (@length Z) Hnil) as Hlen.
    rewrite length_app, !repeat_length in Hlen. simpl in Hlen.
    assert (0 < Z.to_nat k)%nat by lia. lia.
  - apply Forall_app. split;
      apply Forall_repeat__canonical_construction; tauto.
  - apply binary_value_repeat_one_zeros__canonical_construction; lia.
  - right. split.
    + pose proof (proj1 (Z.pow_gt_1 2 k ltac:(lia)) Hk).
      pose proof (Z.pow_pos_nonneg 2 r ltac:(lia) Hr). nia.
    + rewrite app_Znth1.
      * apply Znth_repeat_lt. rewrite Z2Nat.id by lia. lia.
      * rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. lia.
Qed.
Lemma gambit_pair_le__canonical_construction :
  forall a b k,
    0 <= a -> 2 <= b -> 0 < k <= a ->
    CanonicalGambit a b k.
Proof.
  intros a b k Ha Hb Hk.
  unfold CanonicalGambit, GambitY, GambitSource, GambitTarget.
  assert (Hkeqb : Z.eqb k 0 = false) by (apply Z.eqb_neq; lia).
  assert (Hleb : Z.leb k a = true) by (apply Z.leb_le; lia).
  rewrite Hkeqb, Hleb.
  apply (gambit_pair_two_replacements__canonical_construction
    a b k (b - 1) (b - 1 + k)
    (repeat 1 (Z.to_nat k) ++ repeat 0 (Z.to_nat (a - k)))); try lia.
  - apply gambit_x_Znth_one__canonical_construction; lia.
  - apply gambit_x_Znth_zero__canonical_construction; lia.
  - replace
      (2 ^ (a + b - 1 - (b - 1)) -
       2 ^ (a + b - 1 - (b - 1 + k)))
      with ((2 ^ k - 1) * 2 ^ (a - k)).
    + apply binary_rep_repeat_one_zeros__canonical_construction; lia.
    + replace (a + b - 1 - (b - 1)) with a by lia.
      replace (a + b - 1 - (b - 1 + k)) with (a - k) by lia.
      assert (Hpow : 2 ^ a = 2 ^ k * 2 ^ (a - k)).
      {
        pose proof (Z.pow_add_r 2 k (a - k) ltac:(lia) ltac:(lia)) as Hp.
        replace (k + (a - k)) with a in Hp by lia. exact Hp.
      }
      rewrite Hpow. ring.
  - apply digit_card_repeat_one_zeros__canonical_construction; lia.
Qed.
Lemma gambit_pair_gt__canonical_construction :
  forall a b k,
    0 < a -> 2 <= b -> a < k <= a + b - 2 ->
    CanonicalGambit a b k.
Proof.
  intros a b k Ha Hb Hk.
  unfold CanonicalGambit, GambitY, GambitSource, GambitTarget.
  assert (Hkeqb : Z.eqb k 0 = false) by (apply Z.eqb_neq; lia).
  assert (Hleb : Z.leb k a = false) by (apply Z.leb_gt; lia).
  rewrite Hkeqb, Hleb.
  apply (gambit_pair_two_replacements__canonical_construction
    a b k (a + b - 1 - k) (a + b - 1)
    (repeat 1 (Z.to_nat k))); try lia.
  - apply gambit_x_Znth_one__canonical_construction; lia.
  - apply gambit_x_Znth_zero__canonical_construction; lia.
  - replace
      (2 ^ (a + b - 1 - (a + b - 1 - k)) -
       2 ^ (a + b - 1 - (a + b - 1)))
      with (2 ^ k - 1).
    + apply binary_rep_repeat_one__canonical_construction; lia.
    + replace (a + b - 1 - (a + b - 1 - k)) with k by lia.
      replace (a + b - 1 - (a + b - 1)) with 0 by lia.
      rewrite Z.pow_0_r. reflexivity.
  - apply digit_card_repeat_one__canonical_construction; lia.
Qed.
Lemma set_card_Z_as_sum__impossibility :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma digit_count_count_occ__impossibility :
  forall (d : list Z) (bit : Z),
    #(fun i : Z => 0 <= i < Zlength d /\ Znth i d 0 = bit) =
    Z.of_nat (count_occ Z.eq_dec d bit).
Proof.
  intros d bit.
  induction d as [|z d IH].
  - rewrite set_card_Z_as_sum__impossibility.
    cbn [Zlength SumLib.Sum.sum finite_Z_range Zrange Zrange_aux].
    reflexivity.
  - rewrite set_card_Z_as_sum__impossibility.
    rewrite (SumLib.ZRange.sum_Z_range_Znth_cons 0 z d
      (fun x => if prop_dec (x = bit) then 1 else 0)).
    destruct (Z.eq_dec z bit) as [Heq | Hneq].
    + rewrite count_occ_cons_eq by exact Heq.
      destruct (prop_dec (z = bit)) as [_ | Hbad]; [|contradiction].
      rewrite Nat2Z.inj_succ, <- IH.
      rewrite set_card_Z_as_sum__impossibility.
      lia.
    + rewrite count_occ_cons_neq by exact Hneq.
      destruct (prop_dec (z = bit)) as [Hbad | _]; [contradiction |].
      rewrite <- IH.
      rewrite set_card_Z_as_sum__impossibility.
      lia.
Qed.
Lemma binary_no_one_all_zero__impossibility :
  forall d : list Z,
    Forall (fun z => z = 0 \/ z = 1) d ->
    count_occ Z.eq_dec d 1 = 0%nat ->
    Forall (fun z => z = 0) d.
Proof.
  intros d Hd.
  induction Hd as [|z d Hz Hd IH]; intros Hcount.
  - constructor.
  - destruct Hz as [Hz | Hz].
    + constructor; [exact Hz |].
      apply IH.
      rewrite count_occ_cons_neq in Hcount by lia.
      exact Hcount.
    + subst z.
      rewrite count_occ_cons_eq in Hcount by reflexivity.
      discriminate.
Qed.
Lemma binary_no_zero_all_one__impossibility :
  forall d : list Z,
    Forall (fun z => z = 0 \/ z = 1) d ->
    count_occ Z.eq_dec d 0 = 0%nat ->
    Forall (fun z => z = 1) d.
Proof.
  intros d Hd.
  induction Hd as [|z d Hz Hd IH]; intros Hcount.
  - constructor.
  - destruct Hz as [Hz | Hz].
    + subst z.
      rewrite count_occ_cons_eq in Hcount by reflexivity.
      discriminate.
    + constructor; [exact Hz |].
      apply IH.
      rewrite count_occ_cons_neq in Hcount by lia.
      exact Hcount.
Qed.
Lemma Forall_eq_Zlength_eq__impossibility :
  forall (v : Z) (x y : list Z),
    Forall (fun z => z = v) x ->
    Forall (fun z => z = v) y ->
    Zlength x = Zlength y ->
    x = y.
Proof.
  intros v x.
  induction x as [|zx x IH]; intros y Hx Hy Hlen.
  - destruct y as [|zy y]; [reflexivity |].
    rewrite Zlength_nil, Zlength_cons in Hlen.
    pose proof (Zlength_nonneg y). lia.
  - destruct y as [|zy y].
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg x). lia.
    +
    inversion Hx as [|? ? Hzx Hx']; subst.
    inversion Hy as [|? ? Hzy Hy']; subst.
    f_equal.
    apply IH; [exact Hx' | exact Hy' |].
    rewrite !Zlength_cons in Hlen.
    lia.
Qed.
Lemma binary_single_one_equal__impossibility :
  forall x y : list Z,
    Forall (fun z => z = 0 \/ z = 1) x ->
    Forall (fun z => z = 0 \/ z = 1) y ->
    Zlength x = Zlength y ->
    Znth 0 x 0 = 1 ->
    Znth 0 y 0 = 1 ->
    count_occ Z.eq_dec x 1 = 1%nat ->
    count_occ Z.eq_dec y 1 = 1%nat ->
    x = y.
Proof.
  intros x y Hx Hy Hlen Hx0 Hy0 Hcx Hcy.
  destruct x as [|zx x]; [simpl in Hx0; discriminate |].
  destruct y as [|zy y]; [simpl in Hy0; discriminate |].
  rewrite Znth0_cons in Hx0, Hy0.
  subst zx; subst zy.
  rewrite count_occ_cons_eq in Hcx, Hcy by reflexivity.
  assert (Hcx0 : count_occ Z.eq_dec x 1 = 0%nat) by lia.
  assert (Hcy0 : count_occ Z.eq_dec y 1 = 0%nat) by lia.
  inversion Hx as [|? ? _ Hxt]; subst.
  inversion Hy as [|? ? _ Hyt]; subst.
  f_equal.
  apply (Forall_eq_Zlength_eq__impossibility 0).
  - apply binary_no_one_all_zero__impossibility; assumption.
  - apply binary_no_one_all_zero__impossibility; assumption.
  - rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma binary_all_ones_equal__impossibility :
  forall x y : list Z,
    Forall (fun z => z = 0 \/ z = 1) x ->
    Forall (fun z => z = 0 \/ z = 1) y ->
    Zlength x = Zlength y ->
    count_occ Z.eq_dec x 0 = 0%nat ->
    count_occ Z.eq_dec y 0 = 0%nat ->
    x = y.
Proof.
  intros x y Hx Hy Hlen Hcx Hcy.
  apply (Forall_eq_Zlength_eq__impossibility 1).
  - apply binary_no_zero_all_one__impossibility; assumption.
  - apply binary_no_zero_all_one__impossibility; assumption.
  - exact Hlen.
Qed.
Lemma gambit_impossible_single_one__impossibility :
  forall a b k,
    b = 1 -> 0 < k -> GambitImpossible a b k.
Proof.
  intros a b k Hb Hk [[x y] Hpair].
  subst b.
  cbn [GambitPair] in Hpair.
  destruct Hpair as [Hlx Hpair].
  destruct Hpair as [Hly Hpair].
  destruct Hpair as [Hdx Hpair].
  destruct Hpair as [Hdy Hpair].
  destruct Hpair as [Hcx0 Hpair].
  destruct Hpair as [Hcx1 Hpair].
  destruct Hpair as [Hcy0 Hpair].
  destruct Hpair as [Hcy1 Hpair].
  destruct Hpair as [Hx0 Hpair].
  destruct Hpair as [Hy0 Hpair].
  destruct Hpair as [Hge [diff [Hrep Hcdiff]]].
  rewrite digit_count_count_occ__impossibility in Hcx1, Hcy1.
  assert (Hxy : x = y).
  {
    apply binary_single_one_equal__impossibility; try assumption.
    - lia.
    - lia.
    - lia.
  }
  subst y.
  unfold BinaryRep in Hrep.
  destruct Hrep as [_ [_ [Hvalue Hpositive]]].
  replace (BinaryValue x - BinaryValue x) with 0 in Hvalue, Hpositive by lia.
  destruct Hpositive as [[_ Hdiff] | [Hbad _]].
  - subst diff.
    rewrite digit_count_count_occ__impossibility in Hcdiff.
    simpl in Hcdiff.
    lia.
  - lia.
Qed.
Lemma gambit_impossible_all_ones__impossibility :
  forall a b k,
    a = 0 -> 0 < k -> GambitImpossible a b k.
Proof.
  intros a b k Ha Hk [[x y] Hpair].
  subst a.
  cbn [GambitPair] in Hpair.
  destruct Hpair as [Hlx Hpair].
  destruct Hpair as [Hly Hpair].
  destruct Hpair as [Hdx Hpair].
  destruct Hpair as [Hdy Hpair].
  destruct Hpair as [Hcx0 Hpair].
  destruct Hpair as [Hcx1 Hpair].
  destruct Hpair as [Hcy0 Hpair].
  destruct Hpair as [Hcy1 Hpair].
  destruct Hpair as [Hx0 Hpair].
  destruct Hpair as [Hy0 Hpair].
  destruct Hpair as [Hge [diff [Hrep Hcdiff]]].
  rewrite digit_count_count_occ__impossibility in Hcx0, Hcy0.
  assert (Hxy : x = y).
  {
    apply binary_all_ones_equal__impossibility; try assumption; lia.
  }
  subst y.
  unfold BinaryRep in Hrep.
  destruct Hrep as [_ [_ [Hvalue Hpositive]]].
  replace (BinaryValue x - BinaryValue x) with 0 in Hvalue, Hpositive by lia.
  destruct Hpositive as [[_ Hdiff] | [Hbad _]].
  - subst diff.
    rewrite digit_count_count_occ__impossibility in Hcdiff.
    simpl in Hcdiff.
    lia.
  - lia.
Qed.
Lemma binary_value_acc__impossibility :
  forall (d : list Z) (acc : Z),
    fold_left (fun a b => 2 * a + b) d acc =
    2 ^ (Z.of_nat (length d)) * acc + BinaryValue d.
Proof.
  intros d.
  induction d as [|z d IH]; intros acc.
  - change (acc = 1 * acc + 0). ring.
  - unfold BinaryValue.
    change (fold_left (fun a b : Z => 2 * a + b) d (2 * acc + z) =
      2 ^ Z.of_nat (length (z :: d)) * acc +
      fold_left (fun a b : Z => 2 * a + b) d z).
    rewrite IH, (IH z).
    simpl length.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    ring.
Qed.
Lemma binary_value_cons__impossibility :
  forall (z : Z) (d : list Z),
    BinaryValue (z :: d) =
    2 ^ (Z.of_nat (length d)) * z + BinaryValue d.
Proof.
  intros z d.
  unfold BinaryValue at 1.
  simpl fold_left.
  apply binary_value_acc__impossibility.
Qed.
Lemma binary_value_bounds__impossibility :
  forall d : list Z,
    Forall (fun z => z = 0 \/ z = 1) d ->
    0 <= BinaryValue d <= 2 ^ (Z.of_nat (length d)) - 1.
Proof.
  intros d Hd.
  induction Hd as [|z d Hz Hd IH].
  - change (0 <= 0 <= 1 - 1). lia.
  - rewrite binary_value_cons__impossibility.
    destruct Hz as [Hz | Hz]; subst z;
      simpl length;
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia;
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (length d)) ltac:(lia) ltac:(lia));
      nia.
Qed.
Lemma binary_value_ones_lower__impossibility :
  forall d : list Z,
    Forall (fun z => z = 0 \/ z = 1) d ->
    2 ^ (Z.of_nat (count_occ Z.eq_dec d 1)) - 1 <= BinaryValue d.
Proof.
  intros d Hd.
  induction Hd as [|z d Hz Hd IH].
  - change (1 - 1 <= 0). lia.
  - rewrite binary_value_cons__impossibility.
    destruct Hz as [Hz | Hz].
    + subst z.
      rewrite count_occ_cons_neq by lia.
      nia.
    + subst z.
      rewrite count_occ_cons_eq by reflexivity.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      assert (Hcount : Z.of_nat (count_occ Z.eq_dec d 1) <=
          Z.of_nat (length d)).
      { apply Nat2Z.inj_le. apply count_occ_bound. }
      pose proof (Zpower_le_monotone 2
        (Z.of_nat (count_occ Z.eq_dec d 1))
        (Z.of_nat (length d)) ltac:(lia) ltac:(lia)) as Hpow.
      nia.
Qed.
Lemma gambit_impossible_span__impossibility :
  forall a b k n,
    n = a + b ->
    0 <= a ->
    2 <= b ->
    0 < k ->
    k <= n ->
    k > n - 2 ->
    GambitImpossible a b k.
Proof.
  intros a b k n Hn Ha Hb Hk Hkn Hspan [[x y] Hpair].
  cbn [GambitPair] in Hpair.
  destruct Hpair as [Hlx Hpair].
  destruct Hpair as [Hly Hpair].
  destruct Hpair as [Hdx Hpair].
  destruct Hpair as [Hdy Hpair].
  destruct Hpair as [Hcx0 Hpair].
  destruct Hpair as [Hcx1 Hpair].
  destruct Hpair as [Hcy0 Hpair].
  destruct Hpair as [Hcy1 Hpair].
  destruct Hpair as [Hx0 Hpair].
  destruct Hpair as [Hy0 Hpair].
  destruct Hpair as [Hge [diff [Hrep Hcdiff]]].
  rewrite digit_count_count_occ__impossibility in Hcy1, Hcdiff.
  pose proof (binary_value_bounds__impossibility x Hdx) as Hxbound.
  destruct y as [|zy yt].
  - rewrite Zlength_nil in Hly. lia.
  - rewrite Znth0_cons in Hy0.
    subst zy.
    inversion Hdy as [|? ? _ Hdyt].
    rewrite count_occ_cons_eq in Hcy1 by reflexivity.
    rewrite Nat2Z.inj_succ in Hcy1.
    assert (Hcountyt : 1 <= Z.of_nat (count_occ Z.eq_dec yt 1)) by lia.
    pose proof (binary_value_ones_lower__impossibility yt Hdyt) as Hytlower.
    assert (Hpowyt : 2 <= 2 ^ Z.of_nat (count_occ Z.eq_dec yt 1)).
    {
      change (2 ^ 1 <= 2 ^ Z.of_nat (count_occ Z.eq_dec yt 1)).
      apply Zpower_le_monotone; lia.
    }
    assert (Hytvalue : 1 <= BinaryValue yt) by nia.
    rewrite binary_value_cons__impossibility in Hge, Hrep.
    rewrite Zlength_correct in Hlx.
    rewrite Zlength_cons, Zlength_correct in Hly.
    assert (Hxlen : Z.of_nat (length x) = n) by lia.
    assert (Hytlen : Z.of_nat (length yt) = n - 1) by lia.
    rewrite Hxlen in Hxbound.
    rewrite Hytlen in Hge, Hrep.
    assert (Hnpositive : 0 <= n - 1) by lia.
    assert (Hxupper : BinaryValue x <= 2 * 2 ^ (n - 1) - 1).
    {
      rewrite <- Z.pow_succ_r by exact Hnpositive.
      replace (Z.succ (n - 1)) with n by lia.
      lia.
    }
    assert (Hdiffupper : BinaryValue x -
        (2 ^ (n - 1) * 1 + BinaryValue yt) <= 2 ^ (n - 1) - 2) by nia.
    unfold BinaryRep in Hrep.
    destruct Hrep as [_ [Hddigits [Hdiffvalue Hpositive]]].
    pose proof (binary_value_ones_lower__impossibility diff Hddigits)
      as Hdifflower.
    rewrite Hcdiff in Hdifflower.
    assert (Hpowk : 2 ^ (n - 1) <= 2 ^ k).
    {
      apply Zpower_le_monotone; lia.
    }
    nia.
Qed.
Lemma Zlength_map__successful_returns : forall {A B : Type} (f : A -> B) xs,
  Zlength (map f xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__successful_returns : forall {A B : Type} (f : A -> B) xs
    (da : A) (db : B) i,
  0 <= i < Zlength xs ->
  Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma map_replace_Znth__successful_returns :
  forall (A B : Type) (f : A -> B) n x (xs : list A),
    map f (replace_Znth n x xs) =
    replace_Znth n (f x) (map f xs).
Proof.
  intros A B f n x xs.
  unfold replace_Znth.
  generalize (Z.to_nat n) as m.
  induction xs as [|a xs IH]; intros m; destruct m; simpl; auto.
  rewrite IH; reflexivity.
Qed.
Lemma Zlength_replace_Znth__successful_returns : forall {A : Type}
    (n : Z) (x : A) (xs : list A),
  Zlength (replace_Znth n x xs) = Zlength xs.
Proof.
  intros A n x xs.
  rewrite !Zlength_correct. f_equal.
  unfold replace_Znth.
  generalize (Z.to_nat n) as m.
  induction xs as [|a xs IH]; intros m; destruct m; simpl; auto.
Qed.
Lemma encode_gambit_x__successful_returns : forall a b,
  0 <= a -> 0 <= b ->
  EncodeDigits (GambitX a b) =
    repeat 49 (Z.to_nat b) ++ repeat 48 (Z.to_nat a) /\
  Zlength (EncodeDigits (GambitX a b)) = a + b /\
  forall i, 0 <= i < a + b ->
    Znth i (EncodeDigits (GambitX a b)) 0 =
    Znth i (GambitX a b) 0 + 48.
Proof.
  intros a b Ha Hb.
  assert (HE : EncodeDigits (GambitX a b) =
      repeat 49 (Z.to_nat b) ++ repeat 48 (Z.to_nat a)).
  {
    unfold EncodeDigits, GambitX.
    rewrite map_app, !map_repeat. reflexivity.
  }
  split; [exact HE|]. split.
  - rewrite HE, Zlength_app.
    rewrite !Zlength_correct, !repeat_length. lia.
  - intros i Hi. unfold EncodeDigits.
    rewrite (Znth_map__successful_returns (fun d : Z => d + 48)
      (GambitX a b) 0 0 i).
    + reflexivity.
    + unfold GambitX. rewrite Zlength_app.
      rewrite !Zlength_correct, !repeat_length. lia.
Qed.
Lemma Zlength_gambit_y__successful_returns : forall a b k,
  0 <= a -> 0 <= b -> Zlength (GambitY a b k) = a + b.
Proof.
  intros a b k Ha Hb. unfold GambitY.
  destruct (Z.eqb k 0).
  - unfold GambitX. rewrite Zlength_app.
    rewrite !Zlength_correct, !repeat_length. lia.
  - rewrite !Zlength_replace_Znth__successful_returns.
    unfold GambitX. rewrite Zlength_app.
    rewrite !Zlength_correct, !repeat_length. lia.
Qed.
Lemma encode_gambit_y_le__successful_returns : forall a b k,
  0 < k <= a -> 2 <= b ->
  EncodeDigits (GambitY a b k) ++ [0] =
  replace_Znth (b - 1 + k) 49
    (replace_Znth (b - 1) 48
      (EncodeDigits (GambitX a b) ++ [0])).
Proof.
  intros a b k Hk Hb.
  assert (HE : EncodeDigits (GambitY a b k) =
      replace_Znth (b - 1 + k) 49
        (replace_Znth (b - 1) 48 (EncodeDigits (GambitX a b)))).
  {
    unfold GambitY.
    destruct (Z.eqb_spec k 0); [lia|].
    unfold GambitTarget, GambitSource.
    destruct (Z.leb_spec k a); [|lia].
    unfold EncodeDigits.
    rewrite !map_replace_Znth__successful_returns.
    reflexivity.
  }
  rewrite HE. symmetry.
  destruct (encode_gambit_x__successful_returns a b) as [_ [HL _]]; try lia.
  rewrite replace_Znth_app_l by
    (try rewrite Zlength_replace_Znth__successful_returns; try rewrite HL; lia).
  rewrite replace_Znth_app_l by
    (try rewrite Zlength_replace_Znth__successful_returns; try rewrite HL; lia).
  reflexivity.
Qed.
Lemma encode_gambit_y_gt__successful_returns : forall a b k,
  0 < a -> 2 <= b -> a < k <= a + b - 2 ->
  EncodeDigits (GambitY a b k) ++ [0] =
  replace_Znth (a + b - 1) 49
    (replace_Znth (a + b - 1 - k) 48
      (EncodeDigits (GambitX a b) ++ [0])).
Proof.
  intros a b k Ha Hb Hk.
  assert (HE : EncodeDigits (GambitY a b k) =
      replace_Znth (a + b - 1) 49
        (replace_Znth (a + b - 1 - k) 48
          (EncodeDigits (GambitX a b)))).
  {
    unfold GambitY.
    destruct (Z.eqb_spec k 0); [lia|].
    unfold GambitTarget, GambitSource.
    destruct (Z.leb_spec k a); [lia|].
    unfold EncodeDigits.
    rewrite !map_replace_Znth__successful_returns.
    reflexivity.
  }
  rewrite HE. symmetry.
  destruct (encode_gambit_x__successful_returns a b) as [_ [HL _]]; try lia.
  rewrite replace_Znth_app_l by
    (try rewrite Zlength_replace_Znth__successful_returns; try rewrite HL; lia).
  rewrite replace_Znth_app_l by
    (try rewrite Zlength_replace_Znth__successful_returns; try rewrite HL; lia).
  reflexivity.
Qed.
Lemma spec_none_of_impossible__impossible_returns :
  forall a b k,
    GambitImpossible a b k -> Spec a b k None.
Proof.
  intros a b k Himpossible.
  unfold Spec.
  left.
  split.
  - reflexivity.
  - exact Himpossible.
Qed.
