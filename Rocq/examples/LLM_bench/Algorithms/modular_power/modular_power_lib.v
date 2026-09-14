From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition ModularPower
    (base exponent modulus result : Z) : Prop :=
  result = (base ^ exponent) mod modulus.

Definition ModularPowerProgress
    (original_base original_exponent modulus
     current_base remaining_exponent accumulator : Z) : Prop :=
  (accumulator * current_base ^ remaining_exponent) mod modulus =
  (original_base ^ original_exponent) mod modulus.

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Lemma pow_mod_base__loop_transitions :
  forall x m n,
    m <> 0 ->
    0 <= n ->
    ((x mod m) ^ n) mod m = (x ^ n) mod m.
Proof.
  intros x m n Hm Hn.
  replace n with (Z.of_nat (Z.to_nat n)) by
      (apply Z2Nat.id; exact Hn).
  generalize (Z.to_nat n).
  intros k.
  induction k as [| k IHk].
  - reflexivity.
  - rewrite Nat2Z.inj_succ.
    rewrite !Z.pow_succ_r by lia.
    rewrite (Z.mul_mod (x mod m) ((x mod m) ^ Z.of_nat k) m Hm).
    rewrite Z.mod_mod by exact Hm.
    rewrite IHk.
    symmetry.
    apply Z.mul_mod.
    exact Hm.
Qed.
Lemma modular_power_progress_odd_step__loop_transitions :
  forall original_base original_exponent m a b r,
    0 < m ->
    0 <= b ->
    b mod 2 = 1 ->
    ModularPowerProgress
      original_base original_exponent m a b r ->
    ModularPowerProgress
      original_base original_exponent m
      ((a * a) mod m) (b / 2) ((r * a) mod m).
Proof.
  intros original_base original_exponent m a b r
    Hm Hb Hodd Hprogress.
  assert (Hm0 : m <> 0) by lia.
  set (q := b / 2).
  assert (Hq : 0 <= q) by
      (unfold q; apply Z.div_pos; lia).
  pose proof (Z.div_mod b 2 ltac:(lia)) as Hdecomp.
  fold q in Hdecomp.
  rewrite Hodd in Hdecomp.
  unfold ModularPowerProgress in *.
  fold q.
  transitivity ((r * a ^ b) mod m).
  - rewrite
      (Z.mul_mod ((r * a) mod m)
        (((a * a) mod m) ^ q) m Hm0).
    rewrite Z.mod_mod by exact Hm0.
    rewrite
      (pow_mod_base__loop_transitions
        (a * a) m q Hm0 Hq).
    rewrite <-
      (Z.mul_mod (r * a) ((a * a) ^ q) m Hm0).
    apply (f_equal (fun z => z mod m)).
    rewrite Hdecomp.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_twice_r.
    rewrite Z.pow_mul_l.
    cbn.
    ring.
  - exact Hprogress.
Qed.
Lemma modular_power_progress_even_step__loop_transitions :
  forall original_base original_exponent m a b r,
    0 < m ->
    0 <= b ->
    b mod 2 = 0 ->
    ModularPowerProgress
      original_base original_exponent m a b r ->
    ModularPowerProgress
      original_base original_exponent m
      ((a * a) mod m) (b / 2) r.
Proof.
  intros original_base original_exponent m a b r
    Hm Hb Heven Hprogress.
  assert (Hm0 : m <> 0) by lia.
  set (q := b / 2).
  assert (Hq : 0 <= q) by
      (unfold q; apply Z.div_pos; lia).
  pose proof (Z.div_mod b 2 ltac:(lia)) as Hdecomp.
  fold q in Hdecomp.
  rewrite Heven in Hdecomp.
  unfold ModularPowerProgress in *.
  fold q.
  transitivity ((r * a ^ b) mod m).
  - rewrite
      (Z.mul_mod r (((a * a) mod m) ^ q) m Hm0).
    rewrite
      (pow_mod_base__loop_transitions
        (a * a) m q Hm0 Hq).
    rewrite <-
      (Z.mul_mod r ((a * a) ^ q) m Hm0).
    apply (f_equal (fun z => z mod m)).
    rewrite Hdecomp.
    replace (2 * q + 0) with (2 * q) by ring.
    rewrite Z.pow_twice_r.
    rewrite Z.pow_mul_l.
    reflexivity.
  - exact Hprogress.
Qed.
