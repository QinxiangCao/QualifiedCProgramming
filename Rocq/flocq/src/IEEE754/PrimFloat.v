(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: https://flocq.gitlabpages.inria.fr/

Copyright (C) 2018-2019 Guillaume Bertholon
#<br />#
Copyright (C) 2018-2019 Érik Martin-Dorel
#<br />#
Copyright (C) 2018-2019 Pierre Roux

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Interface Flocq with Coq (>= 8.11) primitive floating-point numbers. *)

From Coq Require Import Uint63.
From Coq Require Import ZArith Reals Floats SpecFloat.
Require Import Zaux BinarySingleNaN.

(** Conversions from/to Flocq binary_float *)

Definition Prim2B (x : float) : binary_float prec emax :=
  SF2B (Prim2SF x) (Prim2SF_valid x).

Definition B2Prim (x : binary_float prec emax) : float :=
  SF2Prim (B2SF x).

Lemma B2Prim_Prim2B : forall x, B2Prim (Prim2B x) = x.
Proof.
intros x.
unfold Prim2B, B2Prim.
now rewrite B2SF_SF2B, SF2Prim_Prim2SF.
Qed.

Lemma Prim2B_B2Prim : forall x, Prim2B (B2Prim x) = x.
Proof.
intro x.
unfold Prim2B, B2Prim.
apply B2SF_inj.
rewrite B2SF_SF2B.
apply Prim2SF_SF2Prim.
apply valid_binary_B2SF.
Qed.

Lemma Prim2B_inj : forall x y, Prim2B x = Prim2B y -> x = y.
Proof.
intros x y Heq.
generalize (f_equal B2Prim Heq).
now rewrite 2!B2Prim_Prim2B.
Qed.

Lemma B2Prim_inj : forall x y, B2Prim x = B2Prim y -> x = y.
Proof.
intros x y Heq.
generalize (f_equal Prim2B Heq).
now rewrite 2!Prim2B_B2Prim.
Qed.

Lemma B2SF_Prim2B : forall x, B2SF (Prim2B x) = Prim2SF x.
Proof.
intros x.
apply SF2Prim_inj.
- rewrite SF2Prim_Prim2SF.
  apply B2Prim_Prim2B.
- apply valid_binary_B2SF.
- apply Prim2SF_valid.
Qed.

Lemma Prim2SF_B2Prim : forall x, Prim2SF (B2Prim x) = B2SF x.
Proof.
intro x; unfold B2Prim.
now rewrite Prim2SF_SF2Prim; [ | apply valid_binary_B2SF].
Qed.

(** Basic properties of the Binary64 format *)

Local Instance Hprec : FLX.Prec_gt_0 prec := eq_refl _.

Local Instance Hmax : Prec_lt_emax prec emax := eq_refl _.

(** Equivalence between prim_float and Flocq binary_float operations *)

Theorem opp_equiv : forall x, Prim2B (- x) = Bopp (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite opp_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B as [sx|sx| |sx mx ex Bx].
Qed.

Theorem abs_equiv : forall x, Prim2B (abs x) = Babs (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite abs_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B as [sx|sx| |sx mx ex Bx].
Qed.

Theorem compare_equiv :
  forall x y,
  (x ?= y)%float = flatten_cmp_opt (Bcompare (Prim2B x) (Prim2B y)).
Proof.
intros x y.
rewrite compare_spec.
rewrite <-!B2SF_Prim2B.
now case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By].
Qed.

Lemma round_nearest_even_equiv s m l :
  round_nearest_even m l = choice_mode mode_NE s m l.
Proof.
case l; [reflexivity|intro c].
case c; [ | reflexivity..].
now simpl; unfold Round.cond_incr; case Z.even.
Qed.

Lemma binary_round_aux_equiv sx mx ex lx :
  SpecFloat.binary_round_aux prec emax sx mx ex lx
  = binary_round_aux prec emax mode_NE sx mx ex lx.
Proof.
unfold SpecFloat.binary_round_aux, binary_round_aux.
set (mrse' := shr_fexp _ _ _).
case mrse'; intros mrs' e'; simpl.
now rewrite (round_nearest_even_equiv sx).
Qed.

Theorem mul_equiv :
  forall x y,
  Prim2B (x * y) = Bmult mode_NE (Prim2B x) (Prim2B y).
Proof.
intros x y.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite mul_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By]; [now trivial.. | ].
simpl.
rewrite B2SF_SF2B.
apply binary_round_aux_equiv.
Qed.

Lemma binary_round_equiv s m e :
  SpecFloat.binary_round prec emax s m e =
  binary_round prec emax mode_NE s m e.
Proof.
unfold SpecFloat.binary_round, binary_round, shl_align_fexp.
set (mez := shl_align _ _ _); case mez as [mz ez].
apply binary_round_aux_equiv.
Qed.


Lemma binary_normalize_equiv m e szero :
  SpecFloat.binary_normalize prec emax m e szero
  = B2SF (binary_normalize prec emax Hprec Hmax mode_NE m e szero).
Proof.
case m as [ | p | p].
- now simpl.
- simpl; rewrite B2SF_SF2B; apply binary_round_equiv.
- simpl; rewrite B2SF_SF2B; apply binary_round_equiv.
Qed.

Theorem add_equiv :
  forall x y,
  Prim2B (x + y) = Bplus mode_NE (Prim2B x) (Prim2B y).
Proof.
intros x y.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite add_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By];
  [now (trivial || simpl; now case sx, sy).. | ].
apply binary_normalize_equiv.
Qed.

Theorem sub_equiv :
  forall x y,
  Prim2B (x - y) = Bminus mode_NE (Prim2B x) (Prim2B y).
Proof.
intros x y.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite sub_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By];
  [now (trivial || simpl; now case sx, sy).. | ].
simpl.
unfold Zminus.
rewrite <- cond_Zopp_negb.
apply binary_normalize_equiv.
Qed.

Theorem div_equiv :
  forall x y,
  Prim2B (x / y) = Bdiv mode_NE (Prim2B x) (Prim2B y).
Proof.
intros x y.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite div_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By];
  [now (trivial || simpl; case Bool.eqb).. | ].
simpl.
rewrite B2SF_SF2B.
set (melz := SFdiv_core_binary _ _ _ _ _ _).
case melz as [[mz ez] lz].
apply binary_round_aux_equiv.
Qed.

Theorem sqrt_equiv :
  forall x, Prim2B (sqrt x) = Bsqrt mode_NE (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite sqrt_spec.
rewrite <-B2SF_Prim2B.
case Prim2B as [sx|sx| |sx mx ex Bx]; [now (trivial || case sx).. | ].
case sx; [reflexivity | ].
simpl.
rewrite B2SF_SF2B.
set (melz := SFsqrt_core_binary _ _ _ _).
case melz as [[mz ez] lz].
apply binary_round_aux_equiv.
Qed.

Theorem normfr_mantissa_equiv :
  forall x,
  to_Z (normfr_mantissa x) = Z.of_N (Bnormfr_mantissa (Prim2B x)).
Proof.
intro x.
rewrite normfr_mantissa_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B.
Qed.

Theorem ldexp_equiv :
  forall x e,
  Prim2B (Z.ldexp x e) = Bldexp mode_NE (Prim2B x) e.
Proof.
intros x e.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite Z_ldexp_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx]; [now trivial.. | ].
simpl.
rewrite B2SF_SF2B.
apply binary_round_equiv.
Qed.

Theorem ldshiftexp_equiv :
  forall x e,
  Prim2B (ldshiftexp x e) = Bldexp mode_NE (Prim2B x) (to_Z e - shift).
Proof.
intros x e.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite ldshiftexp_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx]; [now trivial.. | ].
simpl.
rewrite B2SF_SF2B.
apply binary_round_equiv.
Qed.

Theorem frexp_equiv :
  forall x : float,
  let (m, e) := Z.frexp x in
  (Prim2B m, e) = Bfrexp (Prim2B x).
Proof.
intro x.
generalize (Z_frexp_spec x).
destruct Z.frexp as [f e].
rewrite <-(B2SF_Prim2B x).
replace (SFfrexp _ _ _)
  with (let (f, e) := Bfrexp (Prim2B x) in
        (B2SF f, e)).
- case Bfrexp; intros f' e' [= H ->]; f_equal.
  now apply B2SF_inj; rewrite B2SF_Prim2B.
- case (Prim2B x) as [s|s| |s m e' Hme] ; try easy.
  simpl.
  rewrite B2SF_SF2B.
  unfold Ffrexp_core_binary, prec.
  change (digits2_pos m) with (Digits.digits2_pos m).
  rewrite <-?Pos2Z.inj_leb.
  now destruct Pos.leb.
Qed.

Theorem frshiftexp_equiv :
  forall x : float,
  let (m, e) := frshiftexp x in
  (Prim2B m, (to_Z e - shift)%Z) = Bfrexp (Prim2B x).
Proof.
intro x.
generalize (frexp_equiv x).
unfold Z.frexp.
now case frshiftexp.
Qed.

Theorem infinity_equiv : infinity = B2Prim (B754_infinity false).
Proof. now compute. Qed.

Theorem neg_infinity_equiv : neg_infinity = B2Prim (B754_infinity true).
Proof. now compute. Qed.

Theorem nan_equiv : nan = B2Prim B754_nan.
Proof. now compute. Qed.

Theorem zero_equiv : zero = B2Prim (B754_zero false).
Proof. now compute. Qed.

Theorem neg_zero_equiv : neg_zero = B2Prim (B754_zero true).
Proof. now compute. Qed.

Theorem one_equiv : one = B2Prim Bone.
Proof. now compute. Qed.

Theorem two_equiv : two = B2Prim (Bplus mode_NE Bone Bone).
Proof. now compute. Qed.

Theorem ulp_equiv :
  forall x, Prim2B (ulp x) = Bulp' (Prim2B x).
Proof.
intro x.
unfold ulp, Bulp'.
rewrite one_equiv, ldexp_equiv, Prim2B_B2Prim.
generalize (frexp_equiv x).
case Z.frexp; intros f e.
destruct Bfrexp as [f' e'].
now intros [= _ <-].
Qed.

Theorem next_up_equiv :
  forall x, Prim2B (next_up x) = Bsucc (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite next_up_spec.
rewrite <-B2SF_Prim2B.
assert (Hsndfrexp : forall x : binary_float prec emax, snd (SFfrexp prec emax (B2SF x)) = snd (Bfrexp x)).
{ intro x'.
  generalize (Z_frexp_spec (B2Prim x')).
  generalize (frexp_equiv (B2Prim x')).
  case Z.frexp; intros f' e'.
  rewrite Prim2B_B2Prim, Prim2SF_B2Prim.
  intros H H'; generalize (f_equal snd H'); generalize (f_equal snd H); simpl.
  now intros ->. }
assert (Hldexp : forall x e, SFldexp prec emax (B2SF x) e = B2SF (Bldexp mode_NE x e)).
{ intros x' e'.
  rewrite <-(Prim2B_B2Prim x'), B2SF_Prim2B, <-Z_ldexp_spec.
  now rewrite <-B2SF_Prim2B, ldexp_equiv. }
assert (Hulp : forall x, SFulp prec emax (B2SF x) = B2SF (Bulp' x)).
{ intro x'.
  unfold SFulp, Bulp'.
  now rewrite Hsndfrexp, <-Hldexp. }
assert (Hpred_pos : forall x, (0 < B2R x)%R -> SFpred_pos prec emax (B2SF x) = B2SF (Bpred_pos' x)).
{ intros x' Fx'.
  unfold SFpred_pos, Bpred_pos'.
  rewrite Hsndfrexp.
  set (fe := fexp _ _ _).
  change (SFone _ _) with (B2SF Bone).
  rewrite Hldexp, Hulp.
  case x' as [sx|sx| |sx mx ex Bx]; try easy.
  unfold B2SF at 1.
  set (y := Bldexp _ _ _).
  set (z := Bulp' _).
  fold (shift_pos (Z.to_pos prec) 1).
  case Pos.eqb.
  - rewrite <-(Prim2B_B2Prim (B754_finite _ _ _ _)).
    rewrite <-(Prim2B_B2Prim y).
    now rewrite <-sub_equiv, !B2SF_Prim2B, sub_spec.
  - rewrite <-(Prim2B_B2Prim (B754_finite _ _ _ _)).
    rewrite <-(Prim2B_B2Prim z).
    now rewrite <-sub_equiv, !B2SF_Prim2B, sub_spec. }
case Prim2B as [sx|sx| |sx mx ex Bx]; [reflexivity|now case sx|reflexivity| ].
rewrite <- Bsucc'_correct by easy.
unfold SF64succ, SFsucc, B2SF at 1, Bsucc'.
case sx.
- unfold B2SF at 1, SFopp at 2.
  rewrite <-(Prim2B_B2Prim (Bpred_pos' _)).
  rewrite <- opp_equiv, B2SF_Prim2B, opp_spec, Prim2SF_B2Prim.
  rewrite <- Hpred_pos.
  easy.
  now apply Float_prop.F2R_gt_0.
- rewrite Hulp.
  rewrite Bulp'_correct by easy.
  rewrite <-(Prim2B_B2Prim (B754_finite _ _ _ _)).
  rewrite <-(Prim2B_B2Prim (Bulp _)).
  rewrite <-add_equiv, !B2SF_Prim2B, add_spec, !Prim2SF_B2Prim.
  now unfold SF64add.
Qed.

Theorem next_down_equiv :
  forall x, Prim2B (next_down x) = Bpred (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite next_down_spec.
rewrite <-B2SF_Prim2B.
unfold Bpred.
rewrite <-(Prim2B_B2Prim (Bopp (Prim2B x))).
rewrite <-next_up_equiv, <-opp_equiv, !B2SF_Prim2B, opp_spec, next_up_spec.
unfold SF64pred, SFpred, SF64succ.
do 2 f_equal.
now rewrite <-opp_equiv, B2Prim_Prim2B, opp_spec.
Qed.

Theorem is_nan_equiv :
  forall x, PrimFloat.is_nan x = is_nan (Prim2B x).
Proof.
intro x.
unfold PrimFloat.is_nan.
rewrite eqb_spec.
rewrite <-B2SF_Prim2B.
case Prim2B as [sx|sx| |sx mx ex Bx]; [reflexivity|now case sx|reflexivity| ].
simpl.
rewrite Bool.negb_false_iff.
unfold SFeqb, SFcompare.
rewrite Z.compare_refl, Pos.compare_refl.
now case sx.
Qed.

Theorem is_zero_equiv :
  forall x,
  is_zero x = match Prim2B x with B754_zero _ => true | _ => false end.
Proof.
intro x.
unfold is_zero.
rewrite eqb_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B as [sx|sx| |sx mx ex Bx]; try reflexivity; case sx.
Qed.

Theorem is_infinity_equiv :
  forall x,
  is_infinity x = match Prim2B x with B754_infinity _ => true | _ => false end.
Proof.
intro x.
unfold is_infinity.
rewrite eqb_spec.
rewrite <-B2SF_Prim2B.
rewrite B2SF_Prim2B, abs_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B.
Qed.

Theorem get_sign_equiv : forall x, get_sign x = Bsign (Prim2B x).
Proof.
intro x.
unfold get_sign.
rewrite is_zero_equiv.
rewrite ltb_spec.
rewrite <-(B2Prim_Prim2B x).
case (Prim2B x) as [sx|sx| |sx mx ex Bx]; rewrite Prim2B_B2Prim.
- now rewrite div_spec; case sx.
- now case sx.
- now simpl.
- now rewrite Prim2SF_B2Prim; case sx.
Qed.

Theorem is_finite_equiv :
  forall x, PrimFloat.is_finite x = is_finite (Prim2B x).
Proof.
intro x.
unfold PrimFloat.is_finite.
rewrite is_nan_equiv, is_infinity_equiv.
now case (Prim2B x) as [sx|sx| |sx mx ex Bx].
Qed.

Theorem of_int63_equiv :
  forall i,
  Prim2B (of_uint63 i)
  = binary_normalize prec emax Hprec Hmax mode_NE (to_Z i) 0 false.
Proof.
intro i.
apply B2SF_inj.
rewrite B2SF_Prim2B.
rewrite of_uint63_spec.
apply binary_normalize_equiv.
Qed.

Theorem eqb_equiv :
  forall x y,
  eqb x y = Beqb (Prim2B x) (Prim2B y).
Proof.
intros x y.
rewrite eqb_spec.
unfold Beqb.
now rewrite !B2SF_Prim2B.
Qed.

Theorem ltb_equiv :
  forall x y,
  ltb x y = Bltb (Prim2B x) (Prim2B y).
Proof.
intros x y.
rewrite ltb_spec.
unfold Bltb.
now rewrite !B2SF_Prim2B.
Qed.

Theorem leb_equiv :
  forall x y,
  leb x y = Bleb (Prim2B x) (Prim2B y).
Proof.
intros x y.
rewrite leb_spec.
unfold Bleb.
now rewrite !B2SF_Prim2B.
Qed.
