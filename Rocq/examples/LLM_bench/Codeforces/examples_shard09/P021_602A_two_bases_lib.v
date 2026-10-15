Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Compares the two statement-given positional numerals. *)
Definition numeral (base : Z) (digits : list Z) : Z :=
  fold_left (fun acc d => acc*base + d) digits 0.
Definition Pre (bx basey : Z) (x y : list Z) : Prop :=
  (* 2 <= bx <= 40 /\ *)
  (* 2 <= basey <= 40 /\ *)
  bx <> basey /\
  (* 1 <= Zlength x <= 10 /\ 1 <= Zlength y <= 10 /\ *)
  Znth 0 x 0 <> 0 /\ Znth 0 y 0 <> 0 
  (* /\Forall (fun d => 0 <= d < bx) x /\ Forall (fun d => 0 <= d < basey) y *)
  .
Definition Spec (bx basey : Z) (x y : list Z) (out : Z) : Prop :=
  (out=60 /\ numeral bx x < numeral basey y) \/
  (out=62 /\ numeral bx x > numeral basey y) \/
  (out=61 /\ numeral bx x = numeral basey y).

Require Import Coq.micromega.Psatz.
Lemma numeral_sublist_succ__numeral_arithmetic :
  forall (b i : Z) (digits : list Z),
    0 <= i < Zlength digits ->
    numeral b (sublist 0 (i + 1) digits) =
      numeral b (sublist 0 i digits) * b + Znth i digits 0.
Proof.
  intros b i digits Hi.
  unfold numeral.
  rewrite (sublist_split 0 (i + 1) i digits) by lia.
  rewrite (sublist_single 0 i digits) by lia.
  rewrite fold_left_app.
  simpl.
  reflexivity.
Qed.
Lemma pow40_successor_bound__numeral_arithmetic :
  forall i v b d : Z,
    0 <= i ->
    0 <= v <= 40 ^ i - 1 ->
    2 <= b <= 40 ->
  0 <= d < b ->
    v * b + d <= 40 ^ (i + 1) - 1.
Proof.
  intros i v b d Hi Hv Hb Hd.
  replace (i + 1) with (Z.succ i) by lia.
  rewrite Z.pow_succ_r by lia.
  assert (0 <= 40 ^ i) by (apply Z.pow_nonneg; lia).
  nia.
Qed.
Lemma pow40_int64_bound__numeral_arithmetic :
  forall i : Z,
    0 <= i <= 9 ->
    40 ^ (i + 1) - 1 <= 9223372036854775807.
Proof.
  intros i Hi.
  assert (Hpow : 40 ^ (i + 1) <= 40 ^ 10).
  { apply Z.pow_le_mono_r; lia. }
  assert (Hcalc : 40 ^ 10 = 10485760000000000) by reflexivity.
  lia.
Qed.
Lemma numeral_sublist_full__numeral_endpoints :
  forall (b : Z) (digits : list Z),
    numeral b (sublist 0 (Zlength digits) digits) = numeral b digits.
Proof.
  intros b digits.
  rewrite (sublist_self digits (Zlength digits)) by reflexivity.
  reflexivity.
Qed.
