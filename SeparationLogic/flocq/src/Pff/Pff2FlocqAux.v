(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: https://flocq.gitlabpages.inria.fr/

Copyright (C) 2013-2018 Sylvie Boldo
#<br />#
Copyright (C) 2013-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** Translation from Flocq to Pff *)

From Coq Require Import Lia.
Require Import Pff Core.

Section RND_Closest_c.
(* extension of pff for rounding function with arbitrary tie *)
Variable b : Fbound.
Variable beta : radix.
Variable p : nat.

Coercion FtoRradix := FtoR beta.
Hypothesis pGreaterThanOne : 1 < p.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat beta p.

Variable choice: Z -> bool.


Definition RND_Closest (r : R) :=
   let ru := RND_Max b beta p r in
   let rd := RND_Min b beta p r in
  match Rle_dec (Rabs (ru - r)) (Rabs (rd - r)) with
  | left H =>
      match
        Rle_lt_or_eq_dec (Rabs (ru - r)) (Rabs (rd - r)) H
      with
      | left _ => ru
      | right _ =>
          match choice (Zfloor (scaled_mantissa beta (FLT_exp (- dExp b) p) r)) with
          | true => ru
          | false => rd
          end
      end
  | right _ => rd
  end.


Theorem RND_Closest_canonic :
 forall r : R, Fcanonic beta b (RND_Closest r).
Proof.
intros r; unfold RND_Closest in |- *.
case (Rle_dec _ _ ); intros H1.
case (Rle_lt_or_eq_dec _ _ H1); intros H2.
apply RND_Max_canonic; try easy; apply radix_gt_1.
case (choice _).
now apply RND_Max_canonic; try easy; apply radix_gt_1.
now apply RND_Min_canonic; try easy; apply radix_gt_1.
now apply RND_Min_canonic; try easy; apply radix_gt_1.
Qed.

Theorem RND_Closest_correct :
 forall r : R, Closest b beta r (RND_Closest r).
Proof.
intros r.
generalize (radix_gt_1 beta); intros M.
split.
apply FcanonicBound with beta; apply RND_Closest_canonic.
intros f H3; fold FtoRradix.
(* *)
cut (RND_Min b beta p r <= r)%R; [ intros V1 | idtac ].
2: apply (RND_Min_correct b beta p) with (r:=r); easy.
cut (r <= RND_Max b beta p r)%R; [ intros V2 | idtac ].
2: apply (RND_Max_correct b beta p) with (r:=r); easy.
cut (forall v w : R, (v <= w)%R -> (0 <= w - v)%R); [ intros V3 | idtac ].
2: intros v w H; apply Rplus_le_reg_l with v; ring_simplify; auto with real.
cut (forall v w : R, (v <= w)%R -> (v - w <= 0)%R); [ intros V4 | idtac ].
2: intros v w H; apply Rplus_le_reg_l with w; ring_simplify; auto with real.
(* *)
unfold RND_Closest; case (Rle_dec _ _); intros H1.
case (Rle_lt_or_eq_dec _ _ H1); intros H2.
(* . *)
rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Rabs_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
case (Rle_or_lt f r); intros H4.
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
apply Rle_trans with (1 := H1); apply Ropp_le_contravar;
 unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Min_correct b beta p) with (r:=r); easy.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Max_correct b beta p) with (r:=r); try easy.
now apply Rlt_le.
(* . *)
case (choice _).
rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Rabs_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
case (Rle_or_lt f r); intros H5.
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
apply Rle_trans with (1 := H1); apply Ropp_le_contravar;
 unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Min_correct b beta p) with (r:=r); easy.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Max_correct b beta p) with (r:=r); try easy.
now apply Rlt_le.
(* . *)
rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Rabs_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite <- H2.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
case (Rle_or_lt f r); intros H5.
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
apply Rle_trans with (1 := H1); apply Ropp_le_contravar;
 unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Min_correct b beta p) with (r:=r); easy.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Max_correct b beta p) with (r:=r); try easy.
now apply Rlt_le.
(* . *)
apply Rnot_le_lt in H1.
rewrite Rabs_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
case (Rle_or_lt f r); intros H4.
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
apply Ropp_le_contravar, Rplus_le_compat_r.
apply (RND_Min_correct b beta p) with (r:=r); easy.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
left; apply Rlt_le_trans with (1:=H1).
apply Rplus_le_compat_r.
apply (RND_Max_correct b beta p) with (r:=r); try easy.
now left.
Qed.

End RND_Closest_c.


Section Bounds.

Variable beta : radix.
Variable p E:Z.
Hypothesis precisionNotZero : (1 < p)%Z.

Definition make_bound := Bound
      (Z.to_pos (Zpower beta p))
      (Z.abs_N E).

Lemma make_bound_Emin: (E <= 0)%Z ->
        ((Z_of_N (dExp (make_bound)))=-E)%Z.
Proof.
simpl.
rewrite Zabs2N.id_abs.
now apply Z.abs_neq.
Qed.

Lemma make_bound_p:
        Zpos (vNum (make_bound))=(Zpower_nat beta (Z.abs_nat p)).
Proof.
unfold make_bound, vNum; simpl.
rewrite Z2Pos.id.
apply Zpower_nat_Zpower.
lia.
generalize (Zpower_gt_0 beta); simpl.
intros T; apply T.
lia.
Qed.


Lemma FtoR_F2R: forall (f:Pff.float) (g: float beta), Pff.Fnum f = Fnum g -> Pff.Fexp f = Fexp g ->
  FtoR beta f = F2R g.
Proof.
intros f g H1 H2; unfold FtoR, F2R.
rewrite H1, H2.
now rewrite bpow_powerRZ.
Qed.


End Bounds.
Section b_Bounds.

Definition bsingle := make_bound radix2 24 (-149)%Z.

Lemma psGivesBound: Zpos (vNum bsingle) = Zpower_nat 2 24.
Proof.
unfold bsingle; apply make_bound_p.
lia.
Qed.

Definition bdouble := make_bound radix2 53 1074.

Lemma pdGivesBound: Zpos (vNum bdouble) = Zpower_nat 2 53.
Proof.
unfold bdouble; apply make_bound_p.
lia.
Qed.

End b_Bounds.
Section Equiv.

Variable beta: radix.
Variable b : Fbound.
Variable p : Z.

Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat beta (Z.abs_nat p).
Hypothesis precisionNotZero : (1 < p)%Z.


Lemma pff_format_is_format: forall f, Fbounded b f ->
  (generic_format beta (FLT_exp (-dExp b) p) (FtoR beta f)).
Proof.
intros f Hf.
apply generic_format_FLT; auto with zarith.
exists (Float beta (Pff.Fnum f) (Pff.Fexp f)).
unfold F2R, FtoR; simpl.
rewrite bpow_powerRZ.
reflexivity.
destruct Hf.
apply Z.lt_le_trans with (1:=H).
rewrite pGivesBound.
rewrite Zpower_Zpower_nat; auto with zarith.
now destruct Hf.
Qed.


Lemma format_is_pff_format': forall r,
   (generic_format beta (FLT_exp (-dExp b) p) r) ->
    Fbounded b (Pff.Float (Ztrunc (scaled_mantissa beta (FLT_exp (-dExp b) p) r))
                            (cexp beta (FLT_exp (-dExp b) p) r)).
Proof.
intros x; unfold generic_format.
set (ex := cexp beta (FLT_exp (-dExp b) p) x).
set (mx := Ztrunc (scaled_mantissa beta (FLT_exp (-dExp b) p) x)).
intros Hx; repeat split ; simpl.
apply lt_IZR.
rewrite pGivesBound, IZR_Zpower_nat.
apply Rmult_lt_reg_r with (bpow beta ex).
apply bpow_gt_0.
rewrite <- bpow_plus.
rewrite inj_abs; try lia.
change (F2R (Float beta (Z.abs mx) ex) < bpow beta (p + ex))%R.
rewrite F2R_Zabs.
rewrite <- Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
unfold cexp in ex.
destruct (mag beta x) as (ex', He).
simpl in ex.
specialize (He Hx0).
apply Rlt_le_trans with (1 := proj2 He).
apply bpow_le.
cut (ex' - p <= ex)%Z. lia.
unfold ex, FLT_exp.
apply Z.le_max_l.
apply Z.le_max_r.
Qed.


Lemma format_is_pff_format: forall r,
  (generic_format beta (FLT_exp (-dExp b) p) r)
  -> exists f, FtoR beta f = r /\ Fbounded b f.
Proof.
intros r Hr.
eexists; split.
2: apply (format_is_pff_format' _ Hr).
rewrite Hr at 3; unfold FtoR, F2R; simpl.
now rewrite bpow_powerRZ.
Qed.


Lemma format_is_pff_format_can: forall r,
  (generic_format beta (FLT_exp (-dExp b) p) r)
  -> exists f, FtoR beta f = r /\ Fcanonic beta b f.
Proof.
intros r Hr.
destruct (format_is_pff_format r Hr) as (f,(Hf1,Hf2)).
exists (Fnormalize beta b (Z.abs_nat p) f); split.
rewrite <- Hf1; apply FnormalizeCorrect.
apply radix_gt_1.
apply FnormalizeCanonic; try assumption.
apply radix_gt_1.
lia.
Qed.


Lemma equiv_RNDs_aux: forall z, Z.even z = true -> Even z.
Proof.
intros z; unfold Z.even, Even.
case z.
intros; exists 0%Z; auto with zarith.
intros p0; case p0.
intros p1 H; contradict H; auto.
intros p1 _.
exists (Zpos p1); auto with zarith.
intros H; contradict H; auto.
intros p0; case p0.
intros p1 H; contradict H; auto.
intros p1 _.
exists (Zneg p1); auto with zarith.
intros H; contradict H; auto.
Qed.

Lemma pff_canonic_is_canonic: forall f, Fcanonic beta b f -> FtoR beta f <> 0 ->
  canonical beta (FLT_exp (- dExp b) p)
    (Float beta (Pff.Fnum f) (Pff.Fexp f)).
Proof.
intros f Hf1 Hf2; unfold canonical; simpl.
assert (K:(F2R (Float beta (Pff.Fnum f) (Pff.Fexp f)) = FtoR beta f)).
  unfold FtoR, F2R; simpl.
  now rewrite bpow_powerRZ.
unfold cexp, FLT_exp.
rewrite K.
destruct (mag beta (FtoR beta f)) as (e, He).
simpl; destruct Hf1.
(* . *)
destruct H as (H1,H2).
cut (Pff.Fexp f = e-p)%Z.
intros V; rewrite V.
apply sym_eq; apply Zmax_left.
rewrite <- V; destruct H1; auto with zarith.
cut (e = Pff.Fexp f + p)%Z. lia.
apply trans_eq with (mag beta (FtoR beta f)).
apply sym_eq; apply mag_unique.
apply He; assumption.
apply mag_unique.
rewrite <- K; unfold F2R; simpl.
rewrite Rabs_mult.
rewrite (Rabs_right (bpow beta (Pff.Fexp f))).
2: apply Rle_ge; apply bpow_ge_0.
split.
replace (Pff.Fexp f + p - 1)%Z with ((p-1)+Pff.Fexp f)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
(* .. *)
apply Rmult_le_reg_l with (IZR beta).
apply IZR_lt.
apply radix_gt_0.
rewrite <- bpow_plus_1.
replace (p-1+1)%Z with (Z_of_nat (Z.abs_nat p)).
rewrite <- IZR_Zpower_nat.
simpl; rewrite <- pGivesBound.
rewrite Rabs_Zabs.
rewrite <- mult_IZR.
apply IZR_le.
rewrite <- (Z.abs_eq (beta)).
rewrite <- Zabs.Zabs_Zmult.
assumption.
apply Zlt_le_weak; apply radix_gt_0.
rewrite inj_abs; try ring.
lia.
(* .. *)
rewrite Zplus_comm, bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- (inj_abs p) by lia.
rewrite <- IZR_Zpower_nat.
simpl; rewrite <- pGivesBound.
rewrite Rabs_Zabs.
apply IZR_lt.
destruct H1; assumption.
(* . *)
destruct H as (H1,(H2,H3)).
rewrite H2.
apply sym_eq; apply Zmax_right.
cut ((e-1) < p-dExp b)%Z. lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (Rabs (FtoR beta f)).
apply He; auto.
apply Rlt_le_trans with (FtoR beta (firstNormalPos beta b (Z.abs_nat p))).
rewrite <- Fabs_correct.
2: apply radix_gt_0.
apply FsubnormalLtFirstNormalPos with (3 := pGivesBound).
apply radix_gt_1.
lia.
apply FsubnormFabs; auto with zarith.
apply radix_gt_1.
split; [idtac|split]; assumption.
rewrite Fabs_correct; auto with real zarith.
apply Rabs_pos.
apply radix_gt_0.
unfold firstNormalPos, FtoR, nNormMin.
simpl.
replace (IZR (Zpower_nat beta (Peano.pred (Z.abs_nat p)))) with (bpow beta (p-1)).
rewrite <- (bpow_powerRZ _).
rewrite <- bpow_plus.
apply bpow_le.
lia.
replace (p-1)%Z with (Z_of_nat (Peano.pred (Z.abs_nat p))).
rewrite <- IZR_Zpower_nat.
reflexivity.
rewrite inj_pred; lia.
Qed.


Lemma pff_round_NE_is_round: forall (r:R),
   (FtoR beta (RND_EvenClosest b beta (Z.abs_nat p) r)
     =  round beta (FLT_exp (-dExp b) p) rndNE r).
Proof.
intros.
assert (Rnd_NE_pt beta (FLT_exp (-dExp b) p) r
         (round beta (FLT_exp (-dExp b) p) rndNE r)).
apply round_NE_pt; auto with zarith.
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
apply exists_NE_FLT.
now right.
unfold Rnd_NE_pt, Rnd_NG_pt, Rnd_N_pt, NE_prop in H.
destruct H as ((H1,H2),H3).
destruct (format_is_pff_format _ H1) as (f,(Hf1,Hf2)).
rewrite <- Hf1.
apply sym_eq.
eapply (EvenClosestUniqueP b beta (Z.abs_nat p)).
apply radix_gt_1.
lia.
exact pGivesBound.
split.
(* *)
split; auto; intros g Hg.
rewrite Hf1.
apply H2.
apply pff_format_is_format; auto.
(* *)
case (Req_dec (FtoR beta (Fnormalize beta b (Z.abs_nat p) f))  0%R); intros L.
left.
unfold FNeven, Feven, Even.
exists 0%Z.
rewrite Zmult_0_r.
apply eq_IZR.
apply Rmult_eq_reg_l with (powerRZ beta (Pff.Fexp (Fnormalize beta b (Z.abs_nat p) f)))%R.
rewrite Rmult_0_r.
rewrite <- L; unfold FtoR; simpl; ring.
apply powerRZ_NOR; auto with zarith real.
apply Rgt_not_eq.
apply IZR_lt; apply radix_gt_0.
destruct H3.
(* . *)
destruct H as (g,(Hg1,(Hg2,Hg3))).
left.
unfold FNeven, Feven.
apply equiv_RNDs_aux.
replace (Pff.Fnum (Fnormalize beta b (Z.abs_nat p) f)) with (Fnum g); try assumption.
replace g with (Float beta (Pff.Fnum (Fnormalize beta b (Z.abs_nat p) f)) (Pff.Fexp (Fnormalize beta b (Z.abs_nat p) f))).
easy.
apply canonical_unique with (FLT_exp (- dExp b) p).
2: assumption.
apply pff_canonic_is_canonic.
apply FnormalizeCanonic. 2-3: lia. 2: auto with real.
apply radix_gt_1.
exact L.
rewrite <- Hg1, <- Hf1.
rewrite <- FnormalizeCorrect with beta b (Z.abs_nat p) f; auto with zarith.
unfold F2R, FtoR; simpl.
rewrite bpow_powerRZ.
reflexivity.
apply radix_gt_1.
(* . *)
right; intros q (Hq1,Hq2).
rewrite Hf1.
apply H.
split.
apply pff_format_is_format; auto.
intros g Hg.
destruct (format_is_pff_format _ Hg) as (v,(Hv1,Hv2)).
rewrite <- Hv1.
apply Hq2; auto.
apply RND_EvenClosest_correct with (3 := pGivesBound).
apply radix_gt_1.
lia.
Qed.


Lemma round_NE_is_pff_round: forall (r:R),
   exists f:Pff.float, (Fcanonic beta b f /\ (EvenClosest b beta (Z.abs_nat p) r f) /\
    FtoR beta f =  round beta (FLT_exp (-dExp b) p) rndNE r).
Proof.
intros r.
exists (RND_EvenClosest b beta (Z.abs_nat p) r).
split.
apply RND_EvenClosest_canonic with (3 := pGivesBound).
apply radix_gt_1.
lia.
split.
apply RND_EvenClosest_correct with (3 := pGivesBound).
apply radix_gt_1.
lia.
apply pff_round_NE_is_round.
Qed.

Lemma pff_round_UP_is_round: forall (r:R),
  FtoR beta (RND_Max b beta (Z.abs_nat p) r)
             = round beta (FLT_exp (- dExp b) p) Zceil r.
Proof with auto with typeclass_instances.
intros r.
generalize (radix_gt_1 beta); intros M.
assert (K:Valid_exp (FLT_exp (- dExp b) p)).
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
destruct (format_is_pff_format_can (round beta (FLT_exp (- dExp b) p) Zceil r)) as (fu,(Hfu1,Hfu2)).
apply generic_format_round...
rewrite <- Hfu1.
apply MaxUniqueP with b r.
apply RND_Max_correct; try assumption.
apply Nat2Z.inj_lt; rewrite inj_abs; simpl; lia.
split.
apply FcanonicBound with (1:=Hfu2).
assert (T:Rnd_UP_pt (generic_format beta (FLT_exp (- dExp b) p)) r
             (round beta (FLT_exp (- dExp b) p) Zceil r)).
apply round_UP_pt...
destruct T as (T1,(T2,T3)).
split.
rewrite Hfu1; apply T2.
intros g Hg1 Hg2.
rewrite Hfu1; apply T3; try assumption.
now apply pff_format_is_format.
Qed.


Lemma pff_round_DN_is_round: forall (r:R),
  FtoR beta (RND_Min b beta (Z.abs_nat p) r)
             = round beta (FLT_exp (- dExp b) p) Zfloor r.
Proof with auto with typeclass_instances.
intros r.
generalize (radix_gt_1 beta); intros M.
assert (K:Valid_exp (FLT_exp (- dExp b) p)).
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
destruct (format_is_pff_format_can (round beta (FLT_exp (- dExp b) p) Zfloor r)) as (fd,(Hfd1,Hfd2)).
apply generic_format_round...
rewrite <- Hfd1.
apply MinUniqueP with b r.
apply RND_Min_correct; try assumption.
apply Nat2Z.inj_lt; rewrite inj_abs; simpl; lia.
split.
apply FcanonicBound with (1:=Hfd2).
assert (T:Rnd_DN_pt (generic_format beta (FLT_exp (- dExp b) p)) r
             (round beta (FLT_exp (- dExp b) p) Zfloor r)).
apply round_DN_pt...
destruct T as (T1,(T2,T3)).
split.
rewrite Hfd1; apply T2.
intros g Hg1 Hg2.
rewrite Hfd1; apply T3; try assumption.
now apply pff_format_is_format.
Qed.




Lemma pff_round_N_is_round: forall choice, forall (r:R),
   (FtoR beta (RND_Closest b beta (Z.abs_nat p) choice r)
     =  round beta (FLT_exp (-dExp b) p) (Znearest choice) r).
Proof with auto with typeclass_instances.
generalize (radix_gt_1 beta); intros M.
intros choice r; apply sym_eq.
assert (K:Valid_exp (FLT_exp (- dExp b) p)).
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
unfold RND_Closest, FtoRradix.
rewrite pff_round_DN_is_round.
rewrite pff_round_UP_is_round.
case (Rle_dec _ _); intros H1.
case (Rle_lt_or_eq_dec _ _ H1); intros H2.
(* *)
rewrite pff_round_UP_is_round.
apply round_N_eq_UP...
rewrite Rabs_right in H2;[idtac| apply Rle_ge, Rle_0_minus, round_UP_pt; easy].
rewrite Rabs_left1 in H2;[idtac| apply Rle_minus, round_DN_pt; easy].
apply Rmult_lt_reg_r with 2%R; try apply Rlt_0_2.
unfold Rdiv; rewrite Rmult_assoc, Rinv_l.
2: apply Rgt_not_eq, Rlt_0_2.
apply Rplus_lt_reg_l with (-round beta (FLT_exp (- dExp b) p) Zfloor r - r)%R.
apply Rle_lt_trans with (round beta (FLT_exp (- dExp b) p) Zceil r - r)%R;[right;ring|idtac].
apply Rlt_le_trans with (1:=H2).
right; ring.
(* *)
rewrite round_N_middle.
rewrite inj_abs by lia.
case (choice _).
apply sym_eq, pff_round_UP_is_round.
apply sym_eq, pff_round_DN_is_round.
rewrite Rabs_right in H2;[idtac| apply Rle_ge, Rle_0_minus, round_UP_pt; easy].
rewrite Rabs_left1 in H2;[idtac| apply Rle_minus, round_DN_pt; easy].
rewrite H2; ring.
(* *)
rewrite pff_round_DN_is_round.
apply round_N_eq_DN...
apply Rnot_le_lt in H1.
rewrite Rabs_left1 in H1;[idtac| apply Rle_minus, round_DN_pt; easy].
rewrite Rabs_right in H1;[idtac| apply Rle_ge, Rle_0_minus, round_UP_pt; easy].
apply Rmult_lt_reg_r with 2%R; try apply Rlt_0_2.
unfold Rdiv; rewrite Rmult_assoc, Rinv_l.
2: apply Rgt_not_eq, Rlt_0_2.
apply Rplus_lt_reg_l with (-round beta (FLT_exp (- dExp b) p) Zfloor r - r)%R.
apply Rle_lt_trans with (-(round beta (FLT_exp (- dExp b) p) Zfloor r - r))%R;[right;ring|idtac].
apply Rlt_le_trans with (1:=H1).
right; ring.
Qed.


Lemma round_N_is_pff_round: forall choice, forall (r:R),
   exists f:Pff.float, (Fcanonic beta b f /\ (Closest b beta r f) /\
    FtoR beta f =  round beta (FLT_exp (-dExp b) p) (Znearest choice) r).
Proof.
intros choice r.
assert (1 < Z.abs_nat p).
apply Nat2Z.inj_lt; simpl.
rewrite inj_abs; lia.
exists (RND_Closest b beta (Z.abs_nat p) choice r); split.
apply RND_Closest_canonic; easy.
split.
apply RND_Closest_correct; easy.
apply pff_round_N_is_round.
Qed.

Lemma pff_round_is_round_N: forall r f, Closest b beta r f ->
    exists (choice:Z->bool),
      FtoR beta f = round beta (FLT_exp (-dExp b) p) (Znearest choice) r.
Proof with auto with typeclass_instances.
intros r f Hf.
generalize (radix_gt_1 beta); intros M.
assert (M':1 < Z.abs_nat p).
apply Nat2Z.inj_lt; simpl.
rewrite inj_abs; lia.
pose (d := round beta (FLT_exp (-dExp b) p) Zfloor r).
pose (u := round beta (FLT_exp (-dExp b) p) Zceil r).
case (Rle_or_lt ((d+u)/2) r); intros L.
destruct L as [L|L].
(* rnd up *)
exists (fun _ => true).
rewrite <- pff_round_N_is_round.
apply trans_eq with (FtoR beta (RND_Max b beta (Z.abs_nat p) r)).
apply ClosestMaxEq with b r (RND_Min b beta (Z.abs_nat p) r); try assumption.
apply RND_Min_correct; assumption.
apply RND_Max_correct; assumption.
rewrite pff_round_DN_is_round; fold d.
rewrite pff_round_UP_is_round; fold u.
apply Rmult_lt_reg_r with (/2)%R.
apply pos_half_prf.
apply Rlt_le_trans with (1:=L).
right; simpl; field.
rewrite pff_round_N_is_round.
rewrite pff_round_UP_is_round; fold u.
apply sym_eq, round_N_eq_UP...
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
(* middle *)
case (ClosestMinOrMax b beta r f); try assumption; intros LL.
exists (fun _ => false).
rewrite round_N_middle.
rewrite <- pff_round_DN_is_round.
apply (MinUniqueP b beta r); try assumption.
apply RND_Min_correct; assumption.
fold d; fold u; rewrite <- L; field.
exists (fun _ => true).
rewrite round_N_middle.
rewrite <- pff_round_UP_is_round.
apply (MaxUniqueP b beta r); try assumption.
apply RND_Max_correct; assumption.
fold d; fold u; rewrite <- L; field.
(* rnd down *)
exists (fun _ => true).
rewrite <- pff_round_N_is_round.
apply trans_eq with (FtoR beta (RND_Min b beta (Z.abs_nat p) r)).
apply ClosestMinEq with b r (RND_Max b beta (Z.abs_nat p) r); try assumption.
apply RND_Min_correct; assumption.
apply RND_Max_correct; assumption.
rewrite pff_round_DN_is_round; fold d.
rewrite pff_round_UP_is_round; fold u.
apply Rmult_lt_reg_r with (/2)%R.
apply pos_half_prf.
apply Rle_lt_trans with (2:=L).
right; simpl; field.
rewrite pff_round_N_is_round.
rewrite pff_round_DN_is_round; fold d.
apply sym_eq, round_N_eq_DN...
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
Qed.



Lemma FloatFexp_gt:  forall e f, Fbounded b f ->
  (bpow beta (e+p) <= Rabs (FtoR beta f))%R ->
       (e < Pff.Fexp f)%Z.
Proof.
intros e f Ff H1.
apply lt_bpow with beta.
apply Rmult_lt_reg_r with (bpow beta p).
apply bpow_gt_0.
rewrite <- bpow_plus.
apply Rle_lt_trans with (1:=H1).
rewrite <- Fabs_correct.
2: apply radix_gt_0.
unfold Fabs, FtoR; simpl; rewrite Rmult_comm.
rewrite bpow_powerRZ.
apply Rmult_lt_compat_l.
apply powerRZ_lt.
apply IZR_lt, radix_gt_0.
destruct Ff as (T1,T2).
rewrite bpow_powerRZ.
replace p with (Z.of_nat (Z.abs_nat p)).
rewrite <- Zpower_nat_Z_powerRZ.
apply IZR_lt.
now rewrite <- pGivesBound.
rewrite inj_abs; lia.
Qed.

Lemma CanonicGeNormal:  forall f, Fcanonic beta b f ->
  (bpow beta (-dExp b+p-1) <= Rabs (FtoR beta f))%R ->
       (Fnormal beta b f)%Z.
Proof.
intros f Cf H1.
case Cf; trivial.
intros (H2,(H3,H4)).
contradict H1; apply Rlt_not_le.
rewrite <- Fabs_correct.
2: apply radix_gt_0.
unfold FtoR, Fabs; simpl.
rewrite H3, <- bpow_powerRZ.
apply Rlt_le_trans with (bpow beta (p-1)*bpow beta (-dExp b))%R.
2: rewrite <- bpow_plus.
2: right; f_equal; ring.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Rmult_lt_reg_l with (IZR beta).
apply IZR_lt, radix_gt_0.
rewrite <- mult_IZR.
apply Rlt_le_trans with (IZR (Z.pos (vNum b))).
apply IZR_lt.
rewrite <- (Z.abs_eq beta).
now rewrite <- Zabs_Zmult.
apply Zlt_le_weak, radix_gt_0.
rewrite pGivesBound.
rewrite IZR_Zpower_nat.
rewrite <- bpow_1.
rewrite <- bpow_plus.
apply bpow_le.
rewrite inj_abs; lia.
Qed.


Lemma Fulp_ulp_aux:  forall f, Fcanonic beta b f ->
   Fulp b beta (Z.abs_nat p) f
    = ulp beta (FLT_exp (-dExp b) p) (FtoR beta f).
Proof.
intros f H.
case (Req_dec (FtoR beta f) 0); intros Zf.
(* f = 0 *)
rewrite Zf, ulp_FLT_small.
2: unfold Prec_gt_0; lia.
2: rewrite Rabs_R0; apply bpow_gt_0.
rewrite Fulp_zero.
apply sym_eq, bpow_powerRZ.
apply is_Fzero_rep2 with beta; try assumption.
apply radix_gt_1.
(* f <> 0 *)
rewrite ulp_neq_0; try assumption.
replace (FtoR beta f) with (F2R (Float beta (Pff.Fnum f) (Pff.Fexp f))).
rewrite <- pff_canonic_is_canonic; try assumption.
simpl; rewrite CanonicFulp; try assumption.
unfold FtoR; simpl; rewrite bpow_powerRZ; ring.
apply radix_gt_1.
replace 1 with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
unfold F2R, FtoR; simpl.
rewrite bpow_powerRZ; easy.
Qed.


Lemma Fulp_ulp:  forall f, Fbounded b f ->
   Fulp b beta (Z.abs_nat p) f
    = ulp beta (FLT_exp (-dExp b) p) (FtoR beta f).
Proof.
intros f H.
assert (Y1: (1 < beta)%Z) by apply radix_gt_1.
assert (Y2:Z.abs_nat p <> 0).
apply sym_not_eq, Nat.lt_neq.
replace 0 with (Z.abs_nat 0) by easy.
apply Zabs_nat_lt; lia.
rewrite FulpComp with (q:=Fnormalize beta b (Z.abs_nat p) f); try assumption.
rewrite <- FnormalizeCorrect with beta b (Z.abs_nat p) f; try assumption.
apply Fulp_ulp_aux.
apply FnormalizeCanonic; try assumption.
replace 1 with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
apply FnormalizeBounded; try assumption.
apply sym_eq, FnormalizeCorrect; try assumption.
Qed.


End Equiv.

Section Equiv_instanc.

Lemma round_NE_is_pff_round_b32: forall (r:R),
   exists f:Pff.float, (Fcanonic 2 bsingle f /\ (EvenClosest bsingle 2 24 r f) /\
    FtoR 2 f =  round radix2 (FLT_exp (-149) 24) rndNE r).
Proof.
apply (round_NE_is_pff_round radix2 bsingle 24).
apply psGivesBound.
apply eq_refl.
Qed.


Lemma round_NE_is_pff_round_b64: forall (r:R),
   exists f:Pff.float, (Fcanonic 2 bdouble f /\ (EvenClosest bdouble 2 53 r f) /\
    FtoR 2 f =  round radix2 (FLT_exp (-1074) 53) rndNE r).
Proof.
apply (round_NE_is_pff_round radix2 bdouble 53).
apply pdGivesBound.
apply eq_refl.
Qed.

End Equiv_instanc.
