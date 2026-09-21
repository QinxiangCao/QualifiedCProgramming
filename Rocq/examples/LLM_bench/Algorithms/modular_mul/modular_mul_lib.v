From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition ModularMul
    (multiplicand multiplier modulus result : Z) : Prop :=
  (* A bounded residue of the mathematical product.  This interval defines
     the answer, independently of C integer bounds or execution safety. *)
  -modulus < result < modulus /\
  (modulus | multiplicand * multiplier - result).

Definition ModularMulProgress
    (original_multiplicand original_multiplier modulus
     current_multiplicand remaining_multiplier accumulator sign : Z) : Prop :=
  exists quotient,
    original_multiplicand * original_multiplier =
      sign * (accumulator + current_multiplicand * remaining_multiplier) +
      modulus * quotient.

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
From Coq Require Import Lia.
Lemma modular_mul_progress_odd_step__odd_transition :
  forall original_multiplicand original_multiplier modulus
         current_multiplicand remaining_multiplier accumulator sign,
    remaining_multiplier mod 2 = 1 ->
    modulus <> 0 ->
    ModularMulProgress
      original_multiplicand original_multiplier modulus
      current_multiplicand remaining_multiplier accumulator sign ->
    ModularMulProgress
      original_multiplicand original_multiplier modulus
      (Z.rem (current_multiplicand + current_multiplicand) modulus)
      (remaining_multiplier / 2)
      (Z.rem (accumulator + current_multiplicand) modulus)
      sign.
Proof.
  intros original_multiplicand original_multiplier modulus
    current_multiplicand remaining_multiplier accumulator sign
    Hodd Hmodulus Hprogress.
  set (half := remaining_multiplier / 2).
  unfold ModularMulProgress in *.
  destruct Hprogress as [quotient Hprogress].
  exists
    (quotient +
      sign *
        (Z.quot (accumulator + current_multiplicand) modulus +
         Z.quot (current_multiplicand + current_multiplicand) modulus *
           half)).
  pose proof
    (Z.div_mod remaining_multiplier 2 ltac:(lia)) as Hremaining.
  fold half in Hremaining.
  rewrite Hodd in Hremaining.
  pose proof
    (Z.quot_rem (accumulator + current_multiplicand)
      modulus Hmodulus) as Haccumulator.
  pose proof
    (Z.quot_rem (current_multiplicand + current_multiplicand)
      modulus Hmodulus) as Hmultiplicand.
  rewrite Hprogress.
  rewrite Hremaining at 1.
  replace
    (accumulator +
      current_multiplicand * (2 * half + 1))
    with
      ((accumulator + current_multiplicand) +
       (current_multiplicand + current_multiplicand) *
         half) by ring.
  rewrite Haccumulator at 1.
  rewrite Hmultiplicand at 1.
  ring.
Qed.
Lemma modular_mul_progress_even_step__even_transition :
  forall original_multiplicand original_multiplier modulus
         current_multiplicand remaining_multiplier accumulator sign,
    Z.rem remaining_multiplier 2 = 0 ->
    modulus <> 0 ->
    ModularMulProgress
      original_multiplicand original_multiplier modulus
      current_multiplicand remaining_multiplier accumulator sign ->
    ModularMulProgress
      original_multiplicand original_multiplier modulus
      (Z.rem (current_multiplicand + current_multiplicand) modulus)
      (Z.quot remaining_multiplier 2) accumulator sign.
Proof.
  intros original_multiplicand original_multiplier modulus
         current_multiplicand remaining_multiplier accumulator sign
         Hrem Hmod [quotient Hprogress].
  exists
    (quotient +
     sign *
       ((Z.quot (current_multiplicand + current_multiplicand) modulus) *
        (Z.quot remaining_multiplier 2))).
  pose proof (Z.quot_rem remaining_multiplier 2 ltac:(lia)) as Hremaining.
  pose proof
    (Z.quot_rem (current_multiplicand + current_multiplicand) modulus Hmod)
    as Hcurrent.
  nia.
Qed.
Lemma z_rem_strict_bounds__even_transition :
  forall value modulus,
    0 < modulus ->
    -modulus < Z.rem value modulus < modulus.
Proof.
  intros value modulus Hmodulus.
  destruct (Z_le_gt_dec 0 value) as [Hvalue | Hvalue].
  - pose proof
      (Z.rem_bound_pos value modulus Hvalue Hmodulus) as Hremainder.
    lia.
  - pose proof
      (Z.rem_bound_pos (-value) modulus ltac:(lia) Hmodulus) as Hremainder.
    rewrite Z.rem_opp_l in Hremainder by lia.
    lia.
Qed.
Lemma modular_mul_progress_finish__final_result :
  forall original_multiplicand original_multiplier modulus
         current_multiplicand remaining_multiplier accumulator sign,
    remaining_multiplier = 0 ->
    (sign = 1 \/ sign = -1) ->
    -modulus < accumulator < modulus ->
    ModularMulProgress
      original_multiplicand original_multiplier modulus
      current_multiplicand remaining_multiplier accumulator sign ->
    ModularMul
      original_multiplicand original_multiplier modulus (accumulator * sign).
Proof.
  intros original_multiplicand original_multiplier modulus
         current_multiplicand remaining_multiplier accumulator sign
         Hremaining Hsign Hbounds Hprogress.
  unfold ModularMulProgress in Hprogress.
  destruct Hprogress as [quotient Hprogress].
  destruct Hsign as [Hsign | Hsign]; subst remaining_multiplier; subst sign;
    unfold ModularMul; split.
  - lia.
  - exists quotient. nia.
  - lia.
  - exists quotient. nia.
Qed.
