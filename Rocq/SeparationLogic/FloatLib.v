Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
From Coq Require Import SpecFloat.

From compcert.lib Require Import Integers.
From Flocq.Core Require Import Core.
From Flocq.IEEE754 Require Import BinarySingleNaN Binary Bits.

Local Open Scope Z_scope.
Local Open Scope R_scope.

Definition fp32 : Type := binary32.
Definition fp64 : Type := binary64.
Definition fp128 : Type := Binary.binary_float 113 16384.

Definition fp32_nan_payload : positive := 1%positive.
Lemma fp32_nan_payload_valid : Binary.nan_pl 24 fp32_nan_payload = true.
Proof. reflexivity. Qed.

Definition fp64_nan_payload : positive := 1%positive.
Lemma fp64_nan_payload_valid : Binary.nan_pl 53 fp64_nan_payload = true.
Proof. reflexivity. Qed.

Definition fp128_nan_payload : positive := 1%positive.
Lemma fp128_nan_payload_valid : Binary.nan_pl 113 fp128_nan_payload = true.
Proof. reflexivity. Qed.

Definition fp32_nan : fp32 :=
  @Binary.B754_nan 24 128 false fp32_nan_payload fp32_nan_payload_valid.

Definition fp64_nan : fp64 :=
  @Binary.B754_nan 53 1024 false fp64_nan_payload fp64_nan_payload_valid.

Definition fp128_nan : fp128 :=
  @Binary.B754_nan 113 16384 false fp128_nan_payload fp128_nan_payload_valid.

Definition fp32_unary_nan (_ : fp32)
  : { x : fp32 | Binary.is_nan 24 128 x = true } :=
  exist _ fp32_nan (eq_refl : Binary.is_nan 24 128 fp32_nan = true).

Definition fp64_unary_nan (_ : fp64)
  : { x : fp64 | Binary.is_nan 53 1024 x = true } :=
  exist _ fp64_nan (eq_refl : Binary.is_nan 53 1024 fp64_nan = true).

Definition fp128_unary_nan (_ : fp128)
  : { x : fp128 | Binary.is_nan 113 16384 x = true } :=
  exist _ fp128_nan (eq_refl : Binary.is_nan 113 16384 fp128_nan = true).

Definition fp32_binary_nan (_ _ : fp32)
  : { x : fp32 | Binary.is_nan 24 128 x = true } :=
  exist _ fp32_nan (eq_refl : Binary.is_nan 24 128 fp32_nan = true).

Definition fp64_binary_nan (_ _ : fp64)
  : { x : fp64 | Binary.is_nan 53 1024 x = true } :=
  exist _ fp64_nan (eq_refl : Binary.is_nan 53 1024 fp64_nan = true).

Definition fp128_binary_nan (_ _ : fp128)
  : { x : fp128 | Binary.is_nan 113 16384 x = true } :=
  exist _ fp128_nan (eq_refl : Binary.is_nan 113 16384 fp128_nan = true).

Definition fp32_add : fp32 -> fp32 -> fp32 :=
  Bplus 24 128 eq_refl eq_refl fp32_binary_nan mode_NE.
Definition fp32_sub : fp32 -> fp32 -> fp32 :=
  Bminus 24 128 eq_refl eq_refl fp32_binary_nan mode_NE.
Definition fp32_mul : fp32 -> fp32 -> fp32 :=
  Bmult 24 128 eq_refl eq_refl fp32_binary_nan mode_NE.
Definition fp32_div : fp32 -> fp32 -> fp32 :=
  Bdiv 24 128 eq_refl eq_refl fp32_binary_nan mode_NE.
Definition fp32_neg : fp32 -> fp32 :=
  Bopp 24 128 fp32_unary_nan.

Definition fp64_add : fp64 -> fp64 -> fp64 :=
  Bplus 53 1024 eq_refl eq_refl fp64_binary_nan mode_NE.
Definition fp64_sub : fp64 -> fp64 -> fp64 :=
  Bminus 53 1024 eq_refl eq_refl fp64_binary_nan mode_NE.
Definition fp64_mul : fp64 -> fp64 -> fp64 :=
  Bmult 53 1024 eq_refl eq_refl fp64_binary_nan mode_NE.
Definition fp64_div : fp64 -> fp64 -> fp64 :=
  Bdiv 53 1024 eq_refl eq_refl fp64_binary_nan mode_NE.
Definition fp64_neg : fp64 -> fp64 :=
  Bopp 53 1024 fp64_unary_nan.

Definition fp128_add : fp128 -> fp128 -> fp128 :=
  Bplus 113 16384 eq_refl eq_refl fp128_binary_nan mode_NE.
Definition fp128_sub : fp128 -> fp128 -> fp128 :=
  Bminus 113 16384 eq_refl eq_refl fp128_binary_nan mode_NE.
Definition fp128_mul : fp128 -> fp128 -> fp128 :=
  Bmult 113 16384 eq_refl eq_refl fp128_binary_nan mode_NE.
Definition fp128_div : fp128 -> fp128 -> fp128 :=
  Bdiv 113 16384 eq_refl eq_refl fp128_binary_nan mode_NE.
Definition fp128_neg : fp128 -> fp128 :=
  Bopp 113 16384 fp128_unary_nan.

Definition fp32_isFinite (x : fp32) : Prop :=
  Binary.is_finite 24 128 x = true.
Definition fp64_isFinite (x : fp64) : Prop :=
  Binary.is_finite 53 1024 x = true.
Definition fp128_isFinite (x : fp128) : Prop :=
  Binary.is_finite 113 16384 x = true.

Definition fp32_isNaN (x : fp32) : Prop :=
  Binary.is_nan 24 128 x = true.
Definition fp64_isNaN (x : fp64) : Prop :=
  Binary.is_nan 53 1024 x = true.
Definition fp128_isNaN (x : fp128) : Prop :=
  Binary.is_nan 113 16384 x = true.

Definition fp32_isInf (x : fp32) : Prop :=
  match x with
  | Binary.B754_infinity _ _ _ => True
  | _ => False
  end.
Definition fp64_isInf (x : fp64) : Prop :=
  match x with
  | Binary.B754_infinity _ _ _ => True
  | _ => False
  end.
Definition fp128_isInf (x : fp128) : Prop :=
  match x with
  | Binary.B754_infinity _ _ _ => True
  | _ => False
  end.

Definition fp32_compare : fp32 -> fp32 -> option Datatypes.comparison :=
  Bcompare 24 128.
Definition fp64_compare : fp64 -> fp64 -> option Datatypes.comparison :=
  Bcompare 53 1024.
Definition fp128_compare : fp128 -> fp128 -> option Datatypes.comparison :=
  Bcompare 113 16384.

Definition fp32_eq (x y : fp32) : Prop := fp32_compare x y = Some Datatypes.Eq.
Definition fp32_ne (x y : fp32) : Prop := fp32_compare x y <> Some Datatypes.Eq.
Definition fp32_lt (x y : fp32) : Prop := fp32_compare x y = Some Datatypes.Lt.
Definition fp32_le (x y : fp32) : Prop :=
  match fp32_compare x y with Some Datatypes.Lt | Some Datatypes.Eq => True | _ => False end.
Definition fp32_gt (x y : fp32) : Prop := fp32_compare x y = Some Datatypes.Gt.
Definition fp32_ge (x y : fp32) : Prop :=
  match fp32_compare x y with Some Datatypes.Gt | Some Datatypes.Eq => True | _ => False end.

Definition fp64_eq (x y : fp64) : Prop := fp64_compare x y = Some Datatypes.Eq.
Definition fp64_ne (x y : fp64) : Prop := fp64_compare x y <> Some Datatypes.Eq.
Definition fp64_lt (x y : fp64) : Prop := fp64_compare x y = Some Datatypes.Lt.
Definition fp64_le (x y : fp64) : Prop :=
  match fp64_compare x y with Some Datatypes.Lt | Some Datatypes.Eq => True | _ => False end.
Definition fp64_gt (x y : fp64) : Prop := fp64_compare x y = Some Datatypes.Gt.
Definition fp64_ge (x y : fp64) : Prop :=
  match fp64_compare x y with Some Datatypes.Gt | Some Datatypes.Eq => True | _ => False end.

Definition fp128_eq (x y : fp128) : Prop := fp128_compare x y = Some Datatypes.Eq.
Definition fp128_ne (x y : fp128) : Prop := fp128_compare x y <> Some Datatypes.Eq.
Definition fp128_lt (x y : fp128) : Prop := fp128_compare x y = Some Datatypes.Lt.
Definition fp128_le (x y : fp128) : Prop :=
  match fp128_compare x y with Some Datatypes.Lt | Some Datatypes.Eq => True | _ => False end.
Definition fp128_gt (x y : fp128) : Prop := fp128_compare x y = Some Datatypes.Gt.
Definition fp128_ge (x y : fp128) : Prop :=
  match fp128_compare x y with Some Datatypes.Gt | Some Datatypes.Eq => True | _ => False end.

Definition fp32_of_bits (z : Z) : fp32 := b32_of_bits z.
Definition fp64_of_bits (z : Z) : fp64 := b64_of_bits z.
Definition fp128_of_bits (z : Z) : fp128 :=
  binary_float_of_bits 112 15 (refl_equal _) (refl_equal _) (refl_equal _) z.
Definition bits_of_fp32 (x : fp32) : Z := bits_of_b32 x.
Definition bits_of_fp64 (x : fp64) : Z := bits_of_b64 x.
Definition bits_of_fp128 (x : fp128) : Z := bits_of_binary_float 112 15 x.

Definition bits_of_float_value (x : fp32) : option Z := Some (bits_of_fp32 x).
Definition bits_of_double_value (x : fp64) : option Z := Some (bits_of_fp64 x).
Definition bits_of_long_double_value (x : fp128) : option Z := Some (bits_of_fp128 x).
Definition max_unsigned_128 : Z := 2 ^ 128 - 1.

Lemma bits_of_float_value_range :
  forall v z,
    bits_of_float_value v = Some z ->
    (0 <= z <= Int.max_unsigned)%Z.
Proof.
  intros v z H. unfold bits_of_float_value in H. inversion H; subst z; clear H.
  pose proof (bits_of_binary_float_range 23 8 ltac:(lia) ltac:(lia) v) as Hrange.
  unfold bits_of_fp32, bits_of_b32.
  simpl in Hrange.
  replace (Z.pow_pos 2 32) with 4294967296%Z in Hrange by reflexivity.
  replace Int.max_unsigned with 4294967295%Z by reflexivity.
  lia.
Qed.

Lemma bits_of_double_value_range :
  forall v z,
    bits_of_double_value v = Some z ->
    (0 <= z <= Int64.max_unsigned)%Z.
Proof.
  intros v z H. unfold bits_of_double_value in H. inversion H; subst z; clear H.
  pose proof (bits_of_binary_float_range 52 11 ltac:(lia) ltac:(lia) v) as Hrange.
  unfold bits_of_fp64, bits_of_b64.
  simpl in Hrange.
  replace (Z.pow_pos 2 64) with 18446744073709551616%Z in Hrange by reflexivity.
  replace Int64.max_unsigned with 18446744073709551615%Z by reflexivity.
  lia.
Qed.

Lemma bits_of_long_double_value_range :
  forall v z,
    bits_of_long_double_value v = Some z ->
    (0 <= z <= max_unsigned_128)%Z.
Proof.
  intros v z H. unfold bits_of_long_double_value in H. inversion H; subst z; clear H.
  pose proof (bits_of_binary_float_range 112 15 ltac:(lia) ltac:(lia) v) as Hrange.
  unfold bits_of_fp128.
  unfold max_unsigned_128.
  change (112 + 15 + 1)%Z with 128%Z in Hrange.
  lia.
Qed.

Definition fexp32 := FLT_exp (-149) 24.
Definition fexp64 := FLT_exp (-1074) 53.
Definition fexp128 := FLT_exp (-16494) 113.

Definition rounded32 (m : mode) (r : R) : R :=
  round radix2 fexp32 (round_mode m) r.

Definition rounded64 (m : mode) (r : R) : R :=
  round radix2 fexp64 (round_mode m) r.
Definition rounded128 (m : mode) (r : R) : R :=
  round radix2 fexp128 (round_mode m) r.

Definition in_float32_range (m : mode) (r : R) : Prop :=
  Rabs (rounded32 m r) < bpow radix2 128.

Definition in_float64_range (m : mode) (r : R) : Prop :=
  Rabs (rounded64 m r) < bpow radix2 1024.
Definition in_float128_range (m : mode) (r : R) : Prop :=
  Rabs (rounded128 m r) < bpow radix2 16384.

Lemma rounded32_generic :
  forall m r,
    generic_format radix2 fexp32 (rounded32 m r).
Proof.
  intros.
  unfold rounded32, fexp32.
  apply generic_format_round.
  - apply FLT_exp_valid. reflexivity.
  - apply valid_rnd_round_mode.
Qed.

Lemma rounded64_generic :
  forall m r,
    generic_format radix2 fexp64 (rounded64 m r).
Proof.
  intros.
  unfold rounded64, fexp64.
  apply generic_format_round.
  - apply FLT_exp_valid. reflexivity.
  - apply valid_rnd_round_mode.
Qed.

Lemma rounded128_generic :
  forall m r,
    generic_format radix2 fexp128 (rounded128 m r).
Proof.
  intros.
  unfold rounded128, fexp128.
  apply generic_format_round.
  - apply FLT_exp_valid. reflexivity.
  - apply valid_rnd_round_mode.
Qed.

Definition fp32_of_real (r : R) : fp32 :=
  let rr := rounded32 mode_NE r in
  Binary.binary_normalize 24 128
    (eq_refl : Prec_gt_0 24)
    (eq_refl : Prec_lt_emax 24 128)
    mode_NE
    (Ztrunc (scaled_mantissa radix2 fexp32 rr))
    (cexp radix2 fexp32 rr)
    (Rlt_bool r 0).
Definition fp64_of_real (r : R) : fp64 :=
  let rr := rounded64 mode_NE r in
  Binary.binary_normalize 53 1024
    (eq_refl : Prec_gt_0 53)
    (eq_refl : Prec_lt_emax 53 1024)
    mode_NE
    (Ztrunc (scaled_mantissa radix2 fexp64 rr))
    (cexp radix2 fexp64 rr)
    (Rlt_bool r 0).
Definition fp128_of_real (r : R) : fp128 :=
  let rr := rounded128 mode_NE r in
  Binary.binary_normalize 113 16384
    (eq_refl : Prec_gt_0 113)
    (eq_refl : Prec_lt_emax 113 16384)
    mode_NE
    (Ztrunc (scaled_mantissa radix2 fexp128 rr))
    (cexp radix2 fexp128 rr)
    (Rlt_bool r 0).
Definition fp32_of_Z (z : Z) : fp32 := fp32_of_real (IZR z).
Definition fp64_of_Z (z : Z) : fp64 := fp64_of_real (IZR z).
Definition fp128_of_Z (z : Z) : fp128 := fp128_of_real (IZR z).
Definition Z_to_fp32 := fp32_of_Z.
Definition Z_to_fp64 := fp64_of_Z.
Definition Z_to_fp128 := fp128_of_Z.

Definition fp32_to_R (x : fp32) : option R :=
  if Binary.is_finite 24 128 x then Some (Binary.B2R 24 128 x) else None.
Definition fp64_to_R (x : fp64) : option R :=
  if Binary.is_finite 53 1024 x then Some (Binary.B2R 53 1024 x) else None.
Definition fp128_to_R (x : fp128) : option R :=
  if Binary.is_finite 113 16384 x then Some (Binary.B2R 113 16384 x) else None.
Definition fp32_to_R_total (x : fp32) : R := Binary.B2R 24 128 x.
Definition fp64_to_R_total (x : fp64) : R := Binary.B2R 53 1024 x.
Definition fp128_to_R_total (x : fp128) : R := Binary.B2R 113 16384 x.

Definition fp32_zero : fp32 := fp32_of_bits 0.
Definition fp32_neg_zero : fp32 := fp32_of_bits 2147483648.
Definition fp64_zero : fp64 := fp64_of_bits 0.
Definition fp64_neg_zero : fp64 := fp64_of_bits 9223372036854775808.
Definition fp128_zero : fp128 := fp128_of_bits 0.
Definition fp128_neg_zero : fp128 := fp128_of_bits (2 ^ 127).

Definition fp32_pos_infinity : fp32 := @Binary.B754_infinity 24 128 false.
Definition fp32_neg_infinity : fp32 := @Binary.B754_infinity 24 128 true.
Definition fp64_pos_infinity : fp64 := @Binary.B754_infinity 53 1024 false.
Definition fp64_neg_infinity : fp64 := @Binary.B754_infinity 53 1024 true.
Definition fp128_pos_infinity : fp128 := @Binary.B754_infinity 113 16384 false.
Definition fp128_neg_infinity : fp128 := @Binary.B754_infinity 113 16384 true.

Definition FLT_MAX : fp32 := fp32_of_bits 2139095039.
Definition FLT_MIN : fp32 := fp32_of_bits 8388608.
Definition DBL_MAX : fp64 := fp64_of_bits 9218868437227405311.
Definition DBL_MIN : fp64 := fp64_of_bits 4503599627370496.
Definition LDBL_MAX : fp128 := fp128_of_bits (2 ^ 127 - 2 ^ 112).
Definition LDBL_MIN : fp128 := fp128_of_bits (2 ^ 112).
