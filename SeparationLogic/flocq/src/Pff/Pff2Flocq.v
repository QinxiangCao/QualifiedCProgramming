(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: https://flocq.gitlabpages.inria.fr/

Copyright (C) 2016-2018 Sylvie Boldo
#<br />#
Copyright (C) 2016-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Psatz.

Require Import Core Plus_error Mult_error Operations Sterbenz.
Require Import Pff Pff2FlocqAux.

Open Scope R_scope.

Section FTS.
Variable emin prec : Z.
Variable choice : Z -> bool.
Hypothesis precisionNotZero : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.
Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).



Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) (Znearest choice)).
Notation bpow e := (bpow radix2 e).


Lemma round_N_opp_sym: forall x, round_flt (- x) =
       - round_flt x.
Proof.
intros x; unfold round; rewrite <- F2R_Zopp.
rewrite cexp_opp; f_equal; f_equal.
rewrite scaled_mantissa_opp.
rewrite Znearest_opp.
generalize (scaled_mantissa radix2 (FLT_exp emin prec) x).
intros z; unfold Znearest; case (Rcompare _); try easy.
now rewrite <- choice_sym.
Qed.


(** inputs *)
Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let a := round_flt (x+y).
Let b := round_flt (y+round_flt (x-a)).

(** Theorem *)
Theorem Fast2Sum_correct: Rabs y <= Rabs x -> a+b=x+y.
Proof with auto with typeclass_instances.
intros H.
(* *)
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
(* *)
pose (Iplus := fun (f g:Pff.float) => RND_Closest
        (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) choice
         (FtoR radix2 f + FtoR radix2 g)).
pose (Iminus := fun (f g:Pff.float) => RND_Closest
        (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) choice
         (FtoR radix2 f - FtoR radix2 g)).
assert (H1: forall x y, FtoR 2 (Iplus x y) = round_flt (FtoR 2 x + FtoR 2 y)).
clear -prec_gt_0_ precisionNotZero emin_neg; intros x y.
unfold Iplus.
apply trans_eq with (round radix2
  (FLT_exp (- dExp (make_bound radix2 prec emin)) prec)
  (Znearest choice) (FtoR radix2 x + FtoR radix2 y)).
apply pff_round_N_is_round; try assumption.
now apply make_bound_p.
rewrite make_bound_Emin; try assumption.
now rewrite Z.opp_involutive.
assert (H2: forall x y, FtoR 2 (Iminus x y) = round_flt (FtoR 2 x - FtoR 2 y)).
clear -prec_gt_0_ precisionNotZero emin_neg; intros x y.
unfold Iminus.
apply trans_eq with (round radix2
  (FLT_exp (- dExp (make_bound radix2 prec emin)) prec)
  (Znearest choice) (FtoR radix2 x - FtoR radix2 y)).
apply pff_round_N_is_round; try assumption.
now apply make_bound_p.
rewrite make_bound_Emin; try assumption.
now rewrite Z.opp_involutive.
(* *)
assert (K: FtoR 2 (Iminus fy (Iminus (Iplus fx fy) fx)) =
       FtoR 2 fx + FtoR 2 fy - FtoR 2 (Iplus fx fy)).
apply Pff.Dekker_FTS with (make_bound radix2 prec emin) (Z.abs_nat prec); try assumption.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
(* . *)
intros p q Fp Fq.
apply RND_Closest_correct.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq.
apply lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply FcanonicFopp.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite Fopp_correct, 2!H1, 2!Fopp_correct, <- Ropp_plus_distr.
now rewrite round_N_opp_sym.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite H1,H2.
rewrite Fopp_correct.
f_equal; ring.
(* . *)
unfold Pff.FtoRradix.
change 2%Z with (radix_val radix2).
rewrite Hfx, Hfy; assumption.
(* *)
generalize K; rewrite 2!H2, H1.
change 2%Z with (radix_val radix2).
rewrite Hfx, Hfy; fold a; unfold b; intros K'.
apply Rplus_eq_reg_r with (-a).
apply trans_eq with (round_flt (y - round_flt (a - x))).
2: rewrite K'; ring.
ring_simplify; f_equal; unfold Rminus; f_equal.
rewrite <- round_N_opp_sym.
f_equal; ring.
Qed.

End FTS.

Section TS.

Variable emin prec : Z.
Variable choice : Z -> bool.
Hypothesis precisionNotZero : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.
Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) (Znearest choice)).
Notation bpow e := (bpow radix2 e).

(** inputs *)
Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let a  := round_flt (x+y).
Let x' := round_flt (a-x).
Let dx := round_flt (x- round_flt (a-x')).
Let dy := round_flt (y - x').
Let b  := round_flt (dx + dy).

(** Theorem *)
Theorem TwoSum_correct: a+b=x+y.
Proof with auto with typeclass_instances.
(* *)
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
(* *)
pose (Iplus := fun (f g:Pff.float) => RND_Closest
        (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) choice
         (FtoR radix2 f + FtoR radix2 g)).
pose (Iminus := fun (f g:Pff.float) => RND_Closest
        (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) choice
         (FtoR radix2 f - FtoR radix2 g)).
assert (H1: forall x y, FtoR 2 (Iplus x y) = round_flt (FtoR 2 x + FtoR 2 y)).
clear -prec_gt_0_ precisionNotZero emin_neg; intros x y.
unfold Iplus.
apply trans_eq with (round radix2
  (FLT_exp (- dExp (make_bound radix2 prec emin)) prec)
  (Znearest choice) (FtoR radix2 x + FtoR radix2 y)).
apply pff_round_N_is_round; try assumption.
now apply make_bound_p.
rewrite make_bound_Emin; try assumption.
now rewrite Z.opp_involutive.
assert (H2: forall x y, FtoR 2 (Iminus x y) = round_flt (FtoR 2 x - FtoR 2 y)).
clear -prec_gt_0_ precisionNotZero emin_neg; intros x y.
unfold Iminus.
apply trans_eq with (round radix2
  (FLT_exp (- dExp (make_bound radix2 prec emin)) prec)
  (Znearest choice) (FtoR radix2 x - FtoR radix2 y)).
apply pff_round_N_is_round; try assumption.
now apply make_bound_p.
rewrite make_bound_Emin; try assumption.
now rewrite Z.opp_involutive.
(* *)
assert (K: FtoR 2 (Iplus (Iminus fx (Iminus (Iplus fx fy) (Iminus (Iplus fx fy) fx)))
            (Iminus fy (Iminus (Iplus fx fy) fx))) =
       FtoR 2 fx + FtoR 2 fy - FtoR 2 (Iplus fx fy)).
apply Knuth with (make_bound radix2 prec emin) (Z.abs_nat prec); try assumption.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
(* . *)
intros p q Fp Fq.
apply RND_Closest_correct.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
(* . *)
unfold FtoRradix.
intros p q r s Fp Fq Fr Fs M1 M2.
now rewrite 2!H1, M1, M2.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
now rewrite 2!H1, Rplus_comm.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply FcanonicFopp.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite Fopp_correct, 2!H1, 2!Fopp_correct, <- Ropp_plus_distr.
now rewrite round_N_opp_sym.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite H1, H2, Fopp_correct.
f_equal; ring.
(* *)
generalize K; rewrite 2!H1, 5!H2, H1.
change 2%Z with (radix_val radix2).
rewrite Hfx, Hfy.
fold a; fold x'; fold dx; fold dy; fold b.
intros K'; rewrite K'; ring.
Qed.


End TS.




Section Veltkamp.

Variable beta : radix.
Variable emin prec : Z.
Variable choice : Z -> bool.
Variable s:Z.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation round_flt_s :=(round beta (FLT_exp emin (prec-s)) (Znearest choice)).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).
Notation bpow e := (bpow beta e).

(** inputs *)
Hypothesis SLe: (2 <= s)%Z.
Hypothesis SGe: (s <= prec-2)%Z.
Variable x:R.
Hypothesis Fx: format x.

(** algorithm *)
Let p := round_flt (x*(bpow s+1)).
Let q:= round_flt (x-p).
Let hx:=round_flt (q+p).
Let tx:=round_flt (x-hx).


(** Theorems *)

Lemma C_format: format (bpow s +1).
Proof with auto with typeclass_instances.
apply generic_format_FLT.
exists (Defs.Float beta (Zpower beta s+1)%Z 0%Z); simpl.
unfold F2R; simpl.
rewrite plus_IZR, IZR_Zpower; try lia.
simpl; ring.
rewrite Z.abs_eq.
apply Z.le_lt_trans with (beta^s+beta^0)%Z.
simpl; lia.
apply Z.le_lt_trans with (beta^s+beta^s)%Z.
apply Zplus_le_compat_l.
apply Zpower_le; lia.
apply Z.le_lt_trans with (2*beta^s)%Z.
lia.
apply Z.le_lt_trans with (beta^1*beta^s)%Z.
apply Zmult_le_compat_r.
rewrite Z.pow_1_r.
apply Zle_bool_imp_le; apply beta.
apply Zpower_ge_0.
rewrite <- Zpower_plus; try lia.
apply Zpower_lt; lia.
apply Z.le_trans with (beta^s)%Z; try lia.
apply Zpower_ge_0.
assumption.
Qed.


Theorem Veltkamp_Even:
  (choice = fun z => negb (Z.even z)) ->
   hx = round_flt_s x.
Proof with auto with typeclass_instances.
intros Hchoice.
assert (precisionNotZero : (1 < prec)%Z) by lia.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  (x*(bpow s+1)))
  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  (x-p))
  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  (q+p))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by lia.
(* *)
destruct VeltkampEven with beta (make_bound beta prec emin) (Z.abs_nat s)
   (Z.abs_nat prec) fx fp fq fhx as (hx', (H1,H2)); try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 2%nat with (Z.abs_nat 2) by easy.
apply Zabs_nat_le; lia.
apply Nat2Z.inj_le.
rewrite inj_abs; lia.
rewrite Hfx; rewrite inj_abs; try lia.
rewrite bpow_powerRZ in Hfp'; exact Hfp'.
rewrite Hfx, Hfp'', <- Hchoice; assumption.
rewrite Hfp'', Hfq'', <- Hchoice; assumption.
(* *)
unfold hx; rewrite Hchoice, <- Hfhx'', <- H1.
apply trans_eq with (FtoR beta (RND_EvenClosest
 (make_bound beta (prec-s) emin) beta (Z.abs_nat (prec-s)) x)).
generalize (EvenClosestUniqueP (make_bound beta (prec-s) emin) beta
   (Z.abs_nat (prec-s))); unfold UniqueP; intros T.
apply T with x; clear T.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite <- Hfx.
replace (Z.abs_nat (prec-s)) with (Z.abs_nat prec - Z.abs_nat s)%nat.
replace (make_bound beta (prec - s) emin) with
  (Bound  (Pos.of_succ_nat
                 (Peano.pred
                    (Z.abs_nat
                       (Zpower_nat beta (Z.abs_nat prec - Z.abs_nat s)))))
           (dExp (make_bound beta prec emin))).
exact H2.
generalize (make_bound_Emin beta (prec-s) _ emin_neg).
generalize (make_bound_p beta (prec-s) emin).
destruct (make_bound beta (prec-s) emin) as (l1,l2).
simpl; intros H3 H4; f_equal.
apply Pos2Z.inj.
rewrite H3; try lia.
replace (Z.abs_nat (prec - s)) with (Z.abs_nat prec - Z.abs_nat s)%nat.
rewrite <- (p'GivesBound beta (make_bound beta prec emin) (Z.abs_nat s) (Z.abs_nat prec)) at 2.
simpl; easy.
apply radix_gt_1.
apply Nat2Z.inj.
rewrite inj_minus; repeat rewrite inj_abs; lia.
apply N2Z.inj.
rewrite H4.
rewrite Zabs2N.id_abs.
now apply Z.abs_neq.
apply Nat2Z.inj.
rewrite inj_abs; lia.
apply RND_EvenClosest_correct.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite pff_round_NE_is_round; try lia.
f_equal; f_equal.
rewrite make_bound_Emin; lia.
apply make_bound_p; lia.
Qed.

Theorem Veltkamp: exists choice': Z->bool ,
   hx = round beta (FLT_exp emin (prec-s)) (Znearest choice') x.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x*(bpow s+1)))
  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-p))
  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (q+p))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by lia.
(* *)
destruct Veltkamp with beta (make_bound beta prec emin) (Z.abs_nat s)
   (Z.abs_nat prec) fx fp fq fhx as (H1,(hx', (H2,(H3,H4)))); try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 2%nat with (Z.abs_nat 2) by easy.
apply Zabs_nat_le; lia.
apply Nat2Z.inj_le.
rewrite inj_abs; lia.
rewrite Hfx; rewrite inj_abs; try lia.
rewrite bpow_powerRZ in Hfp'; exact Hfp'.
rewrite Hfx, Hfp''; assumption.
rewrite Hfp'', Hfq''; assumption.
(* *)
destruct pff_round_is_round_N with beta (make_bound beta (prec-s) emin)
 (Z.abs_nat (prec-s)) (FtoR beta fx) hx' as (choice',M).
rewrite Zabs2Nat.id.
apply make_bound_p; lia.
rewrite inj_abs; simpl; lia.
unfold make_bound.
replace (Z.to_pos (beta ^ (prec - s))) with (Pos.of_succ_nat
                 (Init.Nat.pred
                    (Z.abs_nat
                       (Zpower_nat beta
                          (Z.abs_nat prec - Z.abs_nat s))))).
replace (Z.abs_N emin) with (dExp (make_bound beta prec emin)) by easy.
exact H3.
apply Zpos_eq_iff.
apply trans_eq with (Zpower_nat beta (Z.abs_nat prec - Z.abs_nat s)).
rewrite <- p''GivesBound with (b:=make_bound beta prec emin) at 2.
simpl; auto.
apply radix_gt_1.
rewrite Zpower_Zpower_nat,Z2Pos.id.
f_equal; apply sym_eq, Zabs2Nat.inj_sub; lia.
apply Zpower_nat_less.
apply radix_gt_1.
lia.
exists choice'.
unfold hx; rewrite <- Hfhx'', <- H2, M.
f_equal; try easy.
f_equal.
rewrite make_bound_Emin; lia.
rewrite inj_abs; simpl; lia.
Qed.

Theorem Veltkamp_tail:
 x = hx+tx /\  generic_format beta (FLT_exp emin s) tx.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x*(bpow s+1)))
  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-p))
  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (q+p))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-hx))
  as (ftx,(Hftx, (Hftx',Hftx''))).
rewrite make_bound_Emin in Hftx''; try assumption.
replace (--emin)%Z with emin in Hftx'' by lia.
(* *)
destruct Veltkamp_tail with beta (make_bound beta prec emin) (Z.abs_nat s)
   (Z.abs_nat prec) fx fp fq fhx ftx as (tx', (H1,(H2,(H3,H4)))); try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 2%nat with (Z.abs_nat 2) by easy.
apply Zabs_nat_le; lia.
apply Nat2Z.inj_le.
rewrite inj_abs; lia.
rewrite Hfx; rewrite inj_abs; try lia.
rewrite bpow_powerRZ in Hfp'; apply Hfp'.
rewrite Hfx, Hfp''; apply Hfq'.
rewrite Hfp'', Hfq''; apply Hfhx'.
rewrite Hfhx'', Hfx; apply Hftx'.
(* *)
split.
rewrite <- Hfx, <-H2, Hfhx'', H1, Hftx''; easy.
unfold tx; rewrite <- Hftx'', <- H1.
replace emin with (-dExp (Bound
       (Pos.of_succ_nat
                 (Peano.pred (Z.abs_nat (Zpower_nat beta (Z.abs_nat s)))))
       (dExp (make_bound beta prec emin))))%Z.
apply pff_format_is_format; try assumption; try lia.
simpl.
rewrite Zpos_P_of_succ_nat, inj_pred.
rewrite <- Zsucc_pred.
apply inj_abs.
apply Zpower_NR0.
apply Zlt_le_weak; apply radix_gt_0.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs.
apply Zpower_nat_less.
apply radix_gt_1.
apply Zpower_NR0.
apply Zlt_le_weak; apply radix_gt_0.
simpl.
rewrite Zabs2N.id_abs.
rewrite Z.abs_neq; lia.
Qed.

End Veltkamp.

Section Underf_mult_aux.

Variable beta : radix.
Variable b: Fbound.
Variable prec: Z.

Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat beta (Z.abs_nat prec).
Hypothesis precisionGt1 : (1 < prec)%Z.


Lemma underf_mult_aux:
 forall e x y,
  Fbounded b x ->
  Fbounded b y ->
   (bpow beta (e + 2 * prec - 1)%Z <= Rabs (FtoR beta x * FtoR beta y)) ->
     (e <= Pff.Fexp x + Pff.Fexp y)%Z.
Proof.
intros e x y Fx Fy H.
assert (HH: forall z, Fbounded b z
   -> Rabs (FtoR beta z) < bpow beta (Pff.Fexp z + prec)).
clear -precisionGt1 pGivesBound; intros z Hz.
unfold FtoR; rewrite <- bpow_powerRZ.
rewrite Rabs_mult, Rmult_comm.
rewrite Rabs_right.
2: apply Rle_ge, bpow_ge_0.
rewrite bpow_plus; apply Rmult_lt_compat_l.
apply bpow_gt_0.
destruct Hz as (T1,T2).
rewrite pGivesBound in T1.
rewrite <- abs_IZR, <- IZR_Zpower;[idtac|lia].
apply IZR_lt.
apply Z.lt_le_trans with (1:=T1).
rewrite Zpower_Zpower_nat; lia.
assert (e+2*prec-1 < (Pff.Fexp x+prec) +(Pff.Fexp y +prec))%Z; try lia.
(* *)
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=H).
rewrite Rabs_mult, bpow_plus.
apply Rmult_lt_compat.
apply Rabs_pos.
apply Rabs_pos.
now apply HH.
now apply HH.
Qed.

Lemma underf_mult_aux':
 forall x y,
  Fbounded b x ->
  Fbounded b y ->
   (bpow beta (-dExp b + 2 * prec - 1)%Z <= Rabs (FtoR beta x * FtoR beta y)) ->
     (-dExp b <= Pff.Fexp x + Pff.Fexp y)%Z.
Proof.
intros.
now apply underf_mult_aux.
Qed.



End Underf_mult_aux.


Section Dekker.

Variable beta : radix.
Variable emin prec: Z.
Variable choice : Z -> bool.
Let s:= (prec- Z.div2 prec)%Z.

Hypothesis precisionGe4 : (4 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin < 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation round_flt_s :=(round beta (FLT_exp emin (prec-s)) (Znearest choice)).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).
Notation bpow e := (bpow beta e).

(** inputs *)
Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(*** algorithm *)
(** first Veltkamp *)
Let px := round_flt (x*(bpow s+1)).
Let qx:= round_flt (x-px).
Let hx:=round_flt (qx+px).
Let tx:=round_flt (x-hx).

(** second Veltkamp *)
Let py := round_flt (y*(bpow s+1)).
Let qy:= round_flt (y-py).
Let hy:=round_flt (qy+py).
Let ty:=round_flt (y-hy).

(** all products *)
Let x1y1:=round_flt (hx*hy).
Let x1y2:=round_flt (hx*ty).
Let x2y1:=round_flt (tx*hy).
Let x2y2:=round_flt (tx*ty).

(** final summation *)
Let r :=round_flt(x*y).
Let t1 :=round_flt (-r+x1y1).
Let t2 :=round_flt (t1+x1y2).
Let t3 :=round_flt (t2+x2y1).
Let t4 :=round_flt (t3+x2y2).

Theorem Dekker: (radix_val beta=2)%Z \/ (Z.Even prec) ->
  (x*y=0 \/ bpow (emin + 2 * prec - 1) <= Rabs (x * y) ->  (x*y=r+t4)%R) /\
    (Rabs (x*y-(r+t4)) <= (7/2)*bpow emin)%R.
Proof with auto with typeclass_instances.
intros HH.
(* x=0 *)
case (Req_dec x 0); intros Kx.
assert (Kr: r=0).
unfold r; rewrite Kx, Rmult_0_l, round_0...
assert (Khx: hx=0).
unfold hx, qx, px; rewrite Kx, Rmult_0_l, round_0...
rewrite Rplus_0_r, Rminus_0_l, Ropp_0, round_0...
apply round_0...
assert (Kt4: t4=0).
unfold t4, t3, t2, t1, x1y1, x1y2, x2y1, x2y2, tx; rewrite Kr, Kx, Khx.
rewrite 2!Rmult_0_l, round_0...
rewrite Rminus_0_r, Rplus_0_r, round_0...
rewrite 2!Rmult_0_l, round_0...
rewrite 3!Rplus_0_r, Ropp_0; repeat rewrite round_0...
rewrite Kx, Kr, Kt4.
split;[intros; ring|idtac].
rewrite Rmult_0_l, Rplus_0_l, Rminus_0_l, Ropp_0, Rabs_R0.
apply Rmult_le_pos; try apply bpow_ge_0.
apply Rmult_le_pos.
apply Fourier_util.Rle_zero_pos_plus1; apply Rmult_le_pos.
left; apply Rlt_0_2.
apply Fourier_util.Rle_zero_pos_plus1; left; apply Rlt_0_2.
left; apply pos_half_prf.
(* y = 0 *)
case (Req_dec y 0); intros Ky.
assert (Kr: r=0).
unfold r; rewrite Ky, Rmult_0_r, round_0...
assert (Khy: hy=0).
unfold hy, qy, py; rewrite Ky, Rmult_0_l, round_0...
rewrite Rplus_0_r, Rminus_0_l, Ropp_0, round_0...
apply round_0...
assert (Kt4: t4=0).
unfold t4, t3, t2, t1, x1y1, x1y2, x2y1, x2y2, ty; rewrite Kr, Ky, Khy.
rewrite 2!Rmult_0_r, round_0...
rewrite Rminus_0_r, Rplus_0_r, round_0...
rewrite 2!Rmult_0_r, round_0...
rewrite 3!Rplus_0_r, Ropp_0; repeat rewrite round_0...
rewrite Ky, Kr, Kt4.
split;[intros; ring|idtac].
rewrite Rmult_0_r, Rplus_0_l, Rminus_0_l, Ropp_0, Rabs_R0.
apply Rmult_le_pos; try apply bpow_ge_0.
apply Rmult_le_pos.
apply Fourier_util.Rle_zero_pos_plus1; apply Rmult_le_pos.
left; apply Rlt_0_2.
apply Fourier_util.Rle_zero_pos_plus1; left; apply Rlt_0_2.
left; apply pos_half_prf.
(* Veltkamp x *)
assert (precisionNotZero : (1 < prec)%Z) by lia.
assert (emin_neg': (emin <= 0)%Z) by lia.
destruct (format_is_pff_format_can beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x*(bpow s+1)))
  as (fpx,(Hfpx, (Hfpx',Hfpx''))).
rewrite make_bound_Emin in Hfpx''; try assumption.
replace (--emin)%Z with emin in Hfpx'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-px))
  as (fqx,(Hfqx, (Hfqx',Hfqx''))).
rewrite make_bound_Emin in Hfqx''; try assumption.
replace (--emin)%Z with emin in Hfqx'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (qx+px))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-hx))
  as (ftx,(Hftx, (Hftx',Hftx''))).
rewrite make_bound_Emin in Hftx''; try assumption.
replace (--emin)%Z with emin in Hftx'' by lia.
(* Veltkamp y*)
destruct (format_is_pff_format_can beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (y*(bpow s+1)))
  as (fpy,(Hfpy, (Hfpy',Hfpy''))).
rewrite make_bound_Emin in Hfpy''; try assumption.
replace (--emin)%Z with emin in Hfpy'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (y-py))
  as (fqy,(Hfqy, (Hfqy',Hfqy''))).
rewrite make_bound_Emin in Hfqy''; try assumption.
replace (--emin)%Z with emin in Hfqy'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (qy+py))
  as (fhy,(Hfhy, (Hfhy',Hfhy''))).
rewrite make_bound_Emin in Hfhy''; try assumption.
replace (--emin)%Z with emin in Hfhy'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (y-hy))
  as (fty,(Hfty, (Hfty',Hfty''))).
rewrite make_bound_Emin in Hfty''; try assumption.
replace (--emin)%Z with emin in Hfty'' by lia.
(* products *)
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (hx*hy))
  as (fx1y1,(Hfx1y1, (Hfx1y1',Hfx1y1''))).
rewrite make_bound_Emin in Hfx1y1''; try assumption.
replace (--emin)%Z with emin in Hfx1y1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (hx*ty))
  as (fx1y2,(Hfx1y2, (Hfx1y2',Hfx1y2''))).
rewrite make_bound_Emin in Hfx1y2''; try assumption.
replace (--emin)%Z with emin in Hfx1y2'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (tx*hy))
  as (fx2y1,(Hfx2y1, (Hfx2y1',Hfx2y1''))).
rewrite make_bound_Emin in Hfx2y1''; try assumption.
replace (--emin)%Z with emin in Hfx2y1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (tx*ty))
  as (fx2y2,(Hfx2y2, (Hfx2y2',Hfx2y2''))).
rewrite make_bound_Emin in Hfx2y2''; try assumption.
replace (--emin)%Z with emin in Hfx2y2'' by lia.
(* t_is *)
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x*y))
  as (fr,(Hfr, (Hfr',Hfr''))).
rewrite make_bound_Emin in Hfr''; try assumption.
replace (--emin)%Z with emin in Hfr'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (-r+x1y1))
  as (ft1,(Hft1, (Hft1',Hft1''))).
rewrite make_bound_Emin in Hft1''; try assumption.
replace (--emin)%Z with emin in Hft1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (t1+x1y2))
  as (ft2,(Hft2, (Hft2',Hft2''))).
rewrite make_bound_Emin in Hft2''; try assumption.
replace (--emin)%Z with emin in Hft2'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (t2+x2y1))
  as (ft3,(Hft3, (Hft3',Hft3''))).
rewrite make_bound_Emin in Hft3''; try assumption.
replace (--emin)%Z with emin in Hft3'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (t3+x2y2))
  as (ft4,(Hft4, (Hft4',Hft4''))).
rewrite make_bound_Emin in Hft4''; try assumption.
replace (--emin)%Z with emin in Hft4'' by lia.
(* *)
assert (Hs:(s =(Z.abs_nat prec - Nat.div2 (Z.abs_nat prec))%nat)).
unfold s; rewrite inj_minus.
assert (TT: (Z.div2 prec = Nat.div2 (Z.abs_nat prec))%Z).
rewrite Nat.div2_div, Z.div2_div, Nat2Z.inj_div; simpl.
rewrite inj_abs; lia.
rewrite <- TT.
rewrite inj_abs; try lia.
rewrite Z.max_r; try lia.
assert (Z.div2 prec <= prec)%Z; try lia.
rewrite Z.div2_div; apply Zlt_le_weak.
apply Z_div_lt; lia.
(* *)
assert (D:(((- dExp (make_bound beta prec emin) <= Pff.Fexp fx + Pff.Fexp fy)%Z ->
        (FtoR beta fx * FtoR beta fy = FtoR beta fr + FtoR beta ft4)) /\
   Rabs (FtoR beta fx * FtoR beta fy - (FtoR beta fr + FtoR beta ft4)) <=
       7 / 2 * powerRZ beta (- dExp (make_bound beta prec emin)))).
apply Dekker with (Z.abs_nat prec) fpx fqx fhx ftx fpy fqy fhy fty
   fx1y1 fx1y2 fx2y1 fx2y2 ft1 ft2 ft3; try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 4%nat with (Z.abs_nat 4) by easy.
apply Zabs_nat_le; lia.
(* . *)
rewrite Hfx, <- Hs, <- bpow_powerRZ; apply Hfpx'.
rewrite Hfx, Hfpx''; apply Hfqx'.
rewrite Hfpx'', Hfqx''; apply Hfhx'.
rewrite Hfx, Hfhx''; apply Hftx'.
rewrite Hfy, <- Hs, <- bpow_powerRZ; apply Hfpy'.
rewrite Hfy, Hfpy''; apply Hfqy'.
rewrite Hfpy'', Hfqy''; apply Hfhy'.
rewrite Hfy, Hfhy''; apply Hfty'.
rewrite Hfhx'', Hfhy''; apply Hfx1y1'.
rewrite Hfhx'', Hfty''; apply Hfx1y2'.
rewrite Hftx'', Hfhy''; apply Hfx2y1'.
rewrite Hftx'', Hfty''; apply Hfx2y2'.
rewrite Hfx, Hfy; apply Hfr'.
rewrite Hfr'', Hfx1y1''; apply Hft1'.
rewrite Hft1'', Hfx1y2''; apply Hft2'.
rewrite Hft2'', Hfx2y1''; apply Hft3'.
rewrite Hft3'', Hfx2y2''; apply Hft4'.
rewrite make_bound_Emin; lia.
case HH; intros K;[now left|right].
destruct K as (l,Hl).
exists (Z.abs_nat l).
apply Nat2Z.inj.
rewrite inj_mult.
rewrite 2!inj_abs; lia.
(* *)
rewrite <- Hfx, <- Hfy.
unfold r; rewrite <- Hfr''.
unfold t4; rewrite <- Hft4''.
destruct D as (D1,D2); split.
intros L.
apply D1.
apply underf_mult_aux' with beta prec; try assumption.
apply make_bound_p; assumption.
now apply FcanonicBound with beta.
now apply FcanonicBound with beta.
case L; intros L'.
contradict L'.
apply Rmult_integral_contrapositive_currified.
rewrite Hfx; easy.
rewrite Hfy; easy.
apply Rle_trans with (2:=L').
right; repeat f_equal.
rewrite make_bound_Emin, Z.opp_involutive; lia.
apply Rle_trans with (1:=D2).
rewrite make_bound_Emin, Z.opp_involutive.
2: lia.
rewrite bpow_powerRZ.
now right.
Qed.


End Dekker.

Section ErrFMA_V1.

Variable beta : radix.
Variable emin prec : Z.
Hypothesis Even_radix: Even beta.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Variable choice : Z -> bool.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).

(** inputs *)
Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let alpha1 := round_flt (y+u2).
Let alpha2 := (y+u2)-alpha1.
Let beta1 := round_flt (u1+alpha1).
Let beta2 := (u1+alpha1) - beta1.
Let gamma := round_flt (round_flt (beta1-r1)+beta2).
Let r2 := round_flt (gamma+alpha2).
Let r3 := (gamma+alpha2) -r2.

(** Non-underflow hypotheses *)
Hypothesis V1_Und1: a * x = 0 \/ bpow beta (emin + 2 * prec - 1) <= Rabs (a * x).
Hypothesis V1_Und2: alpha1 = 0 \/ bpow beta (emin + prec) <= Rabs alpha1.
Hypothesis V1_Und4: beta1 = 0 \/ bpow beta (emin + prec+1) <= Rabs beta1.
Hypothesis V1_Und5: r1 = 0 \/ bpow beta (emin + prec-1) <= Rabs r1.

(** Deduced from non-underflow hypotheses *)
Lemma V1_Und3': u1 = 0 \/ bpow beta (emin + 2*prec-1) <= Rabs u1.
Proof with auto with typeclass_instances.
case V1_Und1; intros K.
left; unfold u1.
rewrite K; apply round_0...
right; unfold u1.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
Qed.

Lemma V1_Und3: u1 = 0 \/ bpow beta (emin + prec) <= Rabs u1.
Proof.
case V1_Und3';[now left|right].
apply Rle_trans with (2:=H).
apply bpow_le; lia.
Qed.


(** Theorems *)
Lemma ErrFMA_bounded: format r1 /\ format r2 /\ format r3.
Proof with auto with typeclass_instances.
split.
apply generic_format_round...
split.
apply generic_format_round...
replace (r3) with (-(r2-(gamma+alpha2))) by (unfold r3; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
replace (alpha2) with (-(alpha1-(y+u2))) by (unfold alpha2; ring).
apply generic_format_opp.
apply plus_error...
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case V1_Und1; easy.
Qed.


Lemma ErrFMA_correct:
   a*x+y = r1+r2+r3.
Proof with auto with typeclass_instances.
(* *)
destruct V1_Und1 as [HZ|Und1'].
assert (HZ1: u1 = 0).
unfold u1; rewrite HZ; apply round_0...
rewrite HZ; unfold r3; ring_simplify.
unfold gamma, alpha2, beta2, beta1, alpha1.
rewrite HZ1; replace u2 with 0.
rewrite Rplus_0_r, Rplus_0_l; rewrite 2!round_generic with (x:=y)...
replace r1 with y.
replace (y-y) with 0 by ring.
rewrite Rplus_0_r, round_0...
rewrite Rplus_0_r, round_0...
ring.
unfold r1; rewrite HZ.
rewrite Rplus_0_l, round_generic...
unfold u2; rewrite HZ, HZ1; ring.
(* *)
assert (precisionNotZero : (1 < prec)%Z) by lia.
replace (r1+r2+r3) with (r1+gamma+alpha2).
2: unfold r3; ring.
assert (J1: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
assert (J2: format alpha2).
replace (alpha2) with (-(alpha1-(y+u2))) by (unfold alpha2; ring).
apply generic_format_opp.
apply plus_error...
assert (J3: format beta2).
replace (beta2) with (-(beta1-(u1+alpha1))) by (unfold beta2; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
apply generic_format_round...
(* values *)
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero u2)
  as (fu2,(Hfu2,Hfu2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero alpha2)
  as (fal2,(Hfal2,Hfal2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero beta2)
  as (fbe2,(Hfbe2,Hfbe2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
rewrite <- Hfa, <- Hfx, <- Hfy, <- Hfal2.
(* roundings *)
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (a*x+y))
  as (fr1,(Hfr1, (Hfr1',Hfr1''))).
rewrite make_bound_Emin in Hfr1''; try assumption.
replace (--emin)%Z with emin in Hfr1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (a*x))
  as (fu1,(Hfu1, (Hfu1',Hfu1''))).
rewrite make_bound_Emin in Hfu1''; try assumption.
replace (--emin)%Z with emin in Hfu1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (y+u2))
  as (fal1,(Hfal1, (Hfal1',Hfal1''))).
rewrite make_bound_Emin in Hfal1''; try assumption.
replace (--emin)%Z with emin in Hfal1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (u1+alpha1))
  as (fbe1,(Hfbe1, (Hfbe1',Hfbe1''))).
rewrite make_bound_Emin in Hfbe1''; try assumption.
replace (--emin)%Z with emin in Hfbe1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (beta1-r1))
  as (ff,(Hff, (Hff',Hff''))).
rewrite make_bound_Emin in Hff''; try assumption.
replace (--emin)%Z with emin in Hff'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (FtoR beta ff+beta2))
  as (fga,(Hfga, (Hfga',Hfga''))).
rewrite make_bound_Emin in Hfga''; try assumption.
replace (--emin)%Z with emin in Hfga'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (gamma+alpha2))
  as (fr2,(Hfr2, (Hfr2',Hfr2''))).
rewrite make_bound_Emin in Hfr2''; try assumption.
replace (--emin)%Z with emin in Hfr2'' by lia.
unfold r1; rewrite <- Hfr1''.
unfold gamma; rewrite <- Hff'', <- Hfga''.
(* *)
apply FmaErr with (make_bound beta prec emin) (Z.abs_nat prec)
  (fun r f => f = RND_Closest (make_bound beta prec emin) beta (Z.abs_nat prec) choice r)
   fu1 fu2 fal1 fbe1 fbe2 ff;
  try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 3%nat with (Z.abs_nat 3).
apply Zabs_nat_le; lia.
now unfold Z.abs_nat, Pos.to_nat.
intros r f H.
rewrite H.
apply RND_Closest_correct.
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
apply make_bound_p; lia.
intros x1 x2 g1 g2 K1 K2 K3.
rewrite K1, K2, K3; easy.
(* . underflow *)
rewrite Hfal1''; fold alpha1.
case V1_Und2; intros V;[now right|left].
apply FloatFexp_gt with beta (make_bound beta prec emin) prec.
apply make_bound_p; lia.
lia.
apply FcanonicBound with (1:=Hfal1).
rewrite Hfal1''; fold alpha1.
now rewrite make_bound_Emin, Z.opp_involutive.
rewrite Hfu1''; fold u1.
case V1_Und3; intros V;[now right|left].
apply FloatFexp_gt with beta (make_bound beta prec emin) prec.
apply make_bound_p; lia.
lia.
apply FcanonicBound with (1:=Hfu1).
rewrite Hfu1''; fold u1.
now rewrite make_bound_Emin, Z.opp_involutive.
rewrite Hfbe1''; fold beta1.
case V1_Und4; intros V;[now right|left].
apply FloatFexp_gt with beta (make_bound beta prec emin) prec.
apply make_bound_p; lia.
lia.
apply FcanonicBound with (1:=Hfbe1).
rewrite Hfbe1''; fold beta1.
rewrite make_bound_Emin, Z.opp_involutive; try assumption.
apply Rle_trans with (2:=V); right.
f_equal; ring.
rewrite Hfr1''; fold r1.
case V1_Und5; intros V;[now right|left].
apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite Hfr1''; fold r1.
rewrite make_bound_Emin, Z.opp_involutive; try assumption.
apply underf_mult_aux' with beta prec; try assumption.
apply make_bound_p; lia.
rewrite Hfa, Hfx.
apply Rle_trans with (2:=Und1').
rewrite make_bound_Emin, Z.opp_involutive.
now right.
lia.
(* . end of underflow *)
rewrite Hfa, Hfx; apply Hfu1'.
now rewrite Hfu2, Hfa, Hfx, Hfu1''.
rewrite Hfy, Hfu2; apply Hfal1'.
now rewrite Hfal2, Hfy, Hfu2, Hfal1''.
now rewrite Hfbe2, Hfu1'', Hfal1'', Hfbe1''.
rewrite Hfbe1'', Hfr1''; apply Hff'.
rewrite Hfbe2; apply Hfga'.
apply FcanonicUnique with (4:=Hfr1) (precision:=Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq.
apply absolu_lt_nz; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
apply make_bound_p; lia.
rewrite Hfr1''.
rewrite Hfa, Hfx, Hfy.
rewrite pff_round_N_is_round; try assumption.
f_equal; f_equal.
rewrite make_bound_Emin; try easy; ring.
apply make_bound_p; lia.
rewrite Hfu1'', Hfal1''; fold u1; fold alpha1.
apply FcanonicUnique with (4:=Hfbe1) (precision:=Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq.
apply absolu_lt_nz; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
apply make_bound_p; lia.
rewrite pff_round_N_is_round; try assumption.
rewrite Hfbe1''.
f_equal; f_equal.
rewrite make_bound_Emin; try easy; ring.
apply make_bound_p; lia.
Qed.

End ErrFMA_V1.

Section ErrFMA_V2.

Variable beta : radix.
Variable emin prec : Z.
Hypothesis Even_radix: Even beta.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).




Lemma mult_error_FLT_ge_bpow': forall a b e, format a -> format b ->
   a*b = 0 \/ bpow beta e <= Rabs (a*b) ->
   a*b-round_flt (a*b) = 0 \/
     bpow beta (e+1-2*prec) <= Rabs (a*b-round_flt (a*b)).
Proof with auto with typeclass_instances.
intros a b e Fa Fb H.
case (Req_dec (a * b - round_flt (a * b)) 0); intros Z1;[now left|right].
rewrite <- Rabs_Ropp.
replace (- (a * b - round_flt (a * b))) with (round_flt (a * b) - a*b) by ring.
case H; intros H'.
contradict Z1.
rewrite H', round_0...
ring.
apply mult_error_FLT_ge_bpow...
apply Rle_trans with (2:=H'); apply bpow_le; lia.
replace (round_flt (a * b) - a*b) with (- (a * b - round_flt (a * b))) by ring.
now apply Ropp_neq_0_compat.
Qed.


(** inputs *)
Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let alpha1 := round_flt (y+u2).
Let alpha2 := (y+u2)-alpha1.
Let beta1 := round_flt (u1+alpha1).
Let beta2 := (u1+alpha1) - beta1.
Let gamma := round_flt (round_flt (beta1-r1)+beta2).
Let r2 := round_flt (gamma+alpha2).
Let r3 := (gamma+alpha2) -r2.

(** Non-underflow hypotheses *)
Hypothesis U1: a * x = 0 \/ bpow beta (emin + 4*prec - 3) <= Rabs (a * x).
Hypothesis U2: y = 0 \/ bpow beta (emin + 2*prec) <= Rabs y.

Lemma ErrFMA_bounded_simpl: format r1 /\ format r2 /\ format r3.
Proof with auto with typeclass_instances.
apply ErrFMA_bounded; try assumption.
case U1; intros H; [now left|right].
apply Rle_trans with (2:=H); apply bpow_le.
lia.
Qed.


Lemma V2_Und4: a*x <> 0 -> beta1 = 0 \/ bpow beta (emin + prec+1) <= Rabs beta1.
Proof with auto with typeclass_instances.
intros Zax.
unfold beta1; case U1; intros H.
now contradict H.
case (Req_dec (round_flt (u1 + alpha1)) 0%R); intros L;[now left|right].
apply round_FLT_plus_ge; try assumption...
apply generic_format_round...
apply generic_format_round...
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=H).
apply bpow_le; lia.
Qed.

Lemma V2_Und2:  y <> 0 ->  alpha1 = 0 \/ bpow beta (emin + prec) <= Rabs alpha1.
Proof with auto with typeclass_instances.
intros Zy.
unfold alpha1.
assert (Fu2: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case U1; intros H; try easy.
apply Rle_trans with (2:=H); apply bpow_le.
lia.
case (Req_dec (round_flt (y + u2)) 0%R); intros L;[now left|right].
apply round_FLT_plus_ge...
case U2; try easy; intros M.
apply Rle_trans with (2:=M); apply bpow_le; lia.
Qed.

Lemma V2_Und5: a*x <> 0 -> r1 = 0 \/ bpow beta (emin + prec-1) <= Rabs r1.
Proof with auto with typeclass_instances.
intros Zax.
case (Req_dec r1 0); intros Zr1.
now left.
case U1; intros H.
now contradict H.
right.
case U2; intros Hy.
unfold r1; rewrite Hy, Rplus_0_r.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=H).
apply bpow_le; lia.
unfold r1; replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
case (Req_dec u2 0); intros Zu2.
rewrite Zu2, Rplus_0_r.
case (Req_dec (round_flt (u1 + y)) 0%R); intros L.
contradict Zr1.
unfold r1; replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
now rewrite Zu2, Rplus_0_r.
rewrite Rplus_comm; apply round_FLT_plus_ge...
apply generic_format_round...
apply Rle_trans with (2:=Hy).
apply bpow_le; lia.
now rewrite Rplus_comm.
(* *)
assert (T:round_flt (u1 + y) <> 0 -> (bpow beta (emin + 3 * prec - 2 - prec) <=
 Rabs (round_flt (u1 + y)))).
intros K; apply round_FLT_plus_ge...
apply generic_format_round...
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=H).
apply bpow_le; lia.
case (Req_dec (u1+y) 0); intros H1.
replace (u1+u2+y) with (u1+y+u2) by ring.
rewrite H1, Rplus_0_l.
case (mult_error_FLT_ge_bpow' a x (emin + 4 * prec - 3)); try assumption.
intros H2; contradict Zr1.
unfold r1; replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
replace (u1+u2+y) with (u1+y+u2) by ring.
rewrite H1, Rplus_0_l.
unfold u2, u1; rewrite H2, round_0...
fold u1 u2; intros H2.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=H2).
apply bpow_le; lia.
generalize Zr1; unfold r1.
replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
replace (u1+u2+y) with ((u1+y)+u2) by ring.
assert (Fu2: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case U1; intros J; try easy.
apply Rle_trans with (2:=J); apply bpow_le.
lia.
intros K; apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
assert (K':u1 + y + u2 <> 0).
intros L; apply K; rewrite L.
apply round_0...
generalize K'.
unfold u1; unfold round.
rewrite Fy, Fu2.
rewrite <- F2R_plus, <- F2R_plus.
intros L.
apply Rle_trans with (2:=F2R_ge _ _ L).
rewrite 2!Fexp_Fplus.
apply bpow_le.
apply Z.min_glb.
apply Z.min_glb.
simpl.
apply Z.le_trans with (FLT_exp emin prec (emin +3*prec-1)).
unfold FLT_exp.
rewrite Z.max_l; lia.
apply cexp_ge_bpow...
apply Rle_trans with (2:=H).
apply bpow_le; lia.
simpl.
apply Z.le_trans with (FLT_exp emin prec (emin +2*prec+1)).
unfold FLT_exp.
rewrite Z.max_l; lia.
apply cexp_ge_bpow...
apply Rle_trans with (2:=Hy).
apply bpow_le; lia.
simpl.
apply Z.le_trans with (FLT_exp emin prec (emin +2*prec-1)).
unfold FLT_exp.
rewrite Z.max_l; lia.
apply cexp_ge_bpow...
case (mult_error_FLT_ge_bpow' a x (emin+4*prec-3)); try assumption.
intros Z; contradict Zu2.
unfold u2, u1; easy.
intros H2.
apply Rle_trans with (2:=H2).
apply bpow_le.
lia.
Qed.


Lemma ErrFMA_correct_simpl:
   a*x+y = r1+r2+r3.
Proof with auto with typeclass_instances.
(* *)
case (Req_dec (a*x) 0); intros Zax.
unfold r3, r2, gamma, alpha2, beta2, beta1, r1, u1, alpha1, alpha2,u2,u1.
rewrite Zax, round_0...
unfold Rminus; repeat rewrite Rplus_0_l.
rewrite Ropp_0, Rplus_0_r.
repeat rewrite (round_generic _ _ _ y)...
replace (y+-y) with 0 by ring.
rewrite round_0, Rplus_0_l...
rewrite round_0, Rplus_0_l...
rewrite round_0, Rplus_0_l...
ring.
(* *)
case (Req_dec u2 0); intros Zu2.
unfold r3, r2, gamma, alpha2, beta2, beta1, r1, u1, alpha1, alpha2.
rewrite Zu2, Rplus_0_r.
repeat rewrite (round_generic _ _ _ y)...
ring_simplify.
assert (G:round_flt (a * x) = a*x).
apply trans_eq with (u1+u2).
now rewrite Zu2, Rplus_0_r.
unfold u2, u1; ring.
rewrite G.
replace (round_flt (a * x + y) - round_flt (a * x + y)) with 0 by ring.
rewrite round_0, Rplus_0_l...
rewrite (round_generic _ _ _ (a * x + y - round_flt (a * x + y))).
ring.
replace (a * x + y - round_flt (a * x + y)) with
 (- (round_flt (a * x + y) -(a*x+y))) by ring.
apply generic_format_opp.
rewrite <- G.
apply plus_error...
apply generic_format_round...
(* *)
case (Req_dec y 0); intros Zy.
assert (Fu2: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case U1; intros H; try easy.
apply Rle_trans with (2:=H); apply bpow_le.
lia.
unfold r3, r2, gamma, alpha2, beta2, beta1, r1, alpha1, alpha2.
rewrite Zy, Rplus_0_r, Rplus_0_l; fold u1.
rewrite (round_generic _ _ _ u2)...
replace (u1+u2) with (a*x).
2: unfold u2, u1; ring.
fold u1; ring_simplify (u1-u1).
rewrite round_0...
rewrite Rplus_0_l.
fold u2; rewrite (round_generic _ _ _ u2)...
ring_simplify (u2+(u2-u2)).
rewrite (round_generic _ _ _ u2)...
unfold u2,u1; ring.
(* *)
apply ErrFMA_correct; try assumption.
case U1; intros H; [now left|right].
apply Rle_trans with (2:=H); apply bpow_le.
lia.
fold u1 u2 alpha1.
now apply V2_Und2.
fold u1 u2 alpha1 alpha2.
now apply V2_Und4.
now apply V2_Und5.
Qed.

End ErrFMA_V2.

Section ErrFmaApprox.

Variable beta : radix.
Variable emin prec : Z.
Hypothesis precisionGe3 : (4 <= prec)%Z.
Variable choice : Z -> bool.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).

(** inputs *)
Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let v1 := round_flt (y+u1).
Let v2 := (y+u1)-v1.
Let t1 := round_flt (v1-r1).
Let t2 := round_flt (u2+v2).
Let r2 := round_flt (t1+t2).

(** Non-underflow hypotheses *)
Hypothesis Und1: a * x = 0 \/ bpow beta (emin + 2 * prec - 1) <= Rabs (a * x).
Hypothesis Und2: v1 = 0 \/ bpow beta (emin + prec - 1) <= Rabs v1.
Hypothesis Und3: r1 = 0 \/ bpow beta (emin + prec - 1) <= Rabs r1.
Hypothesis Und4: r2 = 0 \/ bpow beta (emin + prec - 1) <= Rabs r2.
Hypothesis Und5: t2 = 0 \/ bpow beta (emin + prec - 1) <= Rabs t2.

(*Hypothesis Und2: alpha1 = 0 \/ bpow beta (emin + prec) <= Rabs alpha1.
Hypothesis Und4: beta1 = 0 \/ bpow beta (emin + prec+1) <= Rabs beta1.
Hypothesis Und5: r1 = 0 \/ bpow beta (emin + prec-1) <= Rabs r1.*)


Lemma ErrFmaAppr_correct:
   Rabs (r1+r2 -(a*x+y)) <= (3*beta/2+/2) * bpow beta (2-2*prec)%Z * Rabs (r1).
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.
assert (J1: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case Und1; easy.
assert (J2: format v2).
replace (v2) with (-(v1-(y+u1))) by (unfold v2; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
assert (G: forall f, Fcanonic beta (make_bound beta prec emin) f -> (FtoR beta f = 0 \/
   bpow beta (emin+prec-1)%Z <= Rabs (FtoR beta f)) ->
    Fnormal beta (make_bound beta prec emin) f \/
      FtoR beta f = 0%nat).
intros f Hf K; case K; [right|left].
now rewrite H.
apply CanonicGeNormal with prec; try easy.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
apply Rle_trans with (2:=H).
apply bpow_le; lia.
(* ax = 0 *)
case Und1; intros Und1'.
unfold r2, t1, t2, v2, v1, r1, u2, u1; rewrite Und1'.
rewrite round_0...
rewrite Rplus_0_l, Rplus_0_r.
rewrite (round_generic _ _ _ y)...
replace (y-y) with 0 by ring.
rewrite Rplus_0_r, Rminus_0_l, Ropp_0, round_0...
rewrite Rplus_0_l, round_0...
replace (y+0-y) with 0 by ring; rewrite Rabs_R0.
apply Rmult_le_pos.
2: apply Rabs_pos.
apply Rmult_le_pos; try apply bpow_ge_0.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos.
apply Rmult_le_pos.
auto with real.
left; apply IZR_lt; apply radix_gt_0.
left; apply pos_half_prf.
left; apply pos_half_prf.
(* values *)
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero u2)
  as (fu2,(Hfu2,Hfu2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero v2)
  as (fv2,(Hfv2,Hfv2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
(* roundings *)
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (a*x+y))
  as (fr1,(Hfr1, (Hfr1',Hfr1''))).
rewrite make_bound_Emin in Hfr1''; try assumption.
replace (--emin)%Z with emin in Hfr1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (a*x))
  as (fu1,(Hfu1, (Hfu1',Hfu1''))).
rewrite make_bound_Emin in Hfu1''; try assumption.
replace (--emin)%Z with emin in Hfu1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (y+u1))
  as (fv1,(Hfv1, (Hfv1',Hfv1''))).
rewrite make_bound_Emin in Hfv1''; try assumption.
replace (--emin)%Z with emin in Hfv1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (v1-r1))
  as (ft1,(Hft1, (Hft1',Hft1''))).
rewrite make_bound_Emin in Hft1''; try assumption.
replace (--emin)%Z with emin in Hft1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (u2+v2))
  as (ft2,(Hft2, (Hft2',Hft2''))).
rewrite make_bound_Emin in Hft2''; try assumption.
replace (--emin)%Z with emin in Hft2'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (t1+t2))
  as (fr2,(Hfr2, (Hfr2',Hfr2''))).
rewrite make_bound_Emin in Hfr2''; try assumption.
replace (--emin)%Z with emin in Hfr2'' by lia.
(* *)
unfold r1; rewrite <- Hfr1''.
unfold r2; rewrite <- Hfr2''.
rewrite <- Hfa, <- Hfx, <- Hfy.
rewrite bpow_powerRZ.
replace prec with (Z.of_nat (Z.abs_nat prec)).
2: rewrite inj_abs; lia.
apply ErrFmaApprox with (make_bound beta prec emin) fu1 fu2 fv1 fv2 ft1 ft2; try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 4%nat with (Z.abs_nat 4).
apply Zabs_nat_le; lia.
now unfold Z.abs_nat, Pos.to_nat.
(* underflow *)
apply G; try assumption.
case Und1; intros K1;[left|right].
rewrite Hfu1'', K1, round_0...
rewrite Hfu1''.
apply abs_round_ge_generic...
apply generic_format_bpow.
unfold FLT_exp; rewrite Z.max_l; lia.
apply Rle_trans with (2:=K1).
apply bpow_le; lia.
apply G; try assumption.
rewrite Hfv1''; apply Und2.
apply G; try assumption.
rewrite Hfr1''; apply Und3.
apply G; try assumption.
rewrite Hfr2''; apply Und4.
apply G; try assumption.
rewrite Hft2''; apply Und5.
apply underf_mult_aux' with beta prec; try assumption.
apply make_bound_p; assumption.
rewrite Hfa, Hfx.
apply Rle_trans with (2:=Und1').
apply bpow_le.
rewrite make_bound_Emin, Z.opp_involutive; lia.
(* *)
rewrite Hfa, Hfx, Hfy; apply Hfr1'.
rewrite Hfa, Hfx; apply Hfu1'.
now rewrite Hfu2, Hfa, Hfx, Hfu1''.
rewrite Hfu1'', Hfy, Rplus_comm; apply Hfv1'.
rewrite Hfv2, Hfu1'', Hfy, Hfv1''.
unfold v2; unfold v1; unfold u1; ring.
rewrite Hfv1'', Hfr1''; apply Hft1'.
rewrite Hfu2, Hfv2; apply Hft2'.
rewrite Hft1'', Hft2''; apply Hfr2'.
Qed.

End ErrFmaApprox.

Section Axpy.
Variable emin prec : Z.
Variable choice : Z -> bool.
Hypothesis precisionGt : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) (Znearest choice)).
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation bpow e := (bpow radix2 e).

(** inputs *)
Variable a x y:R.
Variable ta tx ty:R.
Hypothesis Fta: format ta.
Hypothesis Ftx: format tx.
Hypothesis Fty: format ty.

(** algorithm *)
Let tv := round_flt (ty+ round_flt (ta*tx)).

(** Hypotheses *)
Hypothesis H1 : (5+4*bpow (-prec))/(1-bpow (-prec))*
   (Rabs (ta*tx)+ bpow (emin-1)) <= Rabs ty.

Hypothesis H2 : Rabs (y-ty) + Rabs (a*x-ta*tx) <=
    bpow (-prec-2)*(1-bpow (1-prec))*Rabs ty -
    bpow (-prec-2)*Rabs (ta*tx) - bpow (emin-2).

Theorem Axpy :
  tv = round radix2 (FLT_exp emin prec) Zfloor (y+a*x) \/
     tv = round radix2 (FLT_exp emin prec) Zceil (y+a*x).
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.
(* values *)
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero ta)
  as (fta,(Hfta,Hfta')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero tx)
  as (ftx,(Hftx,Hftx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero ty)
  as (fty,(Hfty,Hfty')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
(* algo *)
destruct (round_N_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero choice (ta*tx))
  as (fg,(Hfg, (Hfg',Hfg''))).
rewrite make_bound_Emin in Hfg''; try assumption.
replace (--emin)%Z with emin in Hfg'' by lia.
destruct (round_N_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero choice (ty+FtoR radix2 fg))
  as (ftv,(Hftv, (Hftv',Hftv''))).
rewrite make_bound_Emin in Hftv''; try assumption.
replace (--emin)%Z with emin in Hftv'' by lia.
(* call to Axpy_opt *)
assert (MinOrMax radix2 (make_bound radix2 prec emin) (a*x+y) ftv).
unfold radix2 in Hfty, Hftx, Hfta; simpl in Hfty, Hftx, Hfta.
apply Axpy_opt with (Z.abs_nat prec) fta ftx fty fg; try assumption.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
now apply FcanonicBound with radix2.
now apply FcanonicBound with radix2.
now rewrite Hfta, Hftx.
now rewrite Rplus_comm, Hfty.
rewrite Hfty, Hftx, Hfta.
rewrite inj_abs; try lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
clear -H1.
apply Rle_trans with (2:=H1); right.
f_equal.
rewrite bpow_powerRZ.
unfold Rdiv; simpl; f_equal; ring.
f_equal; rewrite bpow_powerRZ.
simpl; f_equal; easy.
rewrite Hfty, Hfta,Hftx.
rewrite inj_abs; try lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
clear -H2.
apply Rle_trans with (1:=H2); right.
rewrite 3!bpow_powerRZ; unfold Z.pred, Z.succ.
unfold Rminus; f_equal; f_equal; f_equal.
f_equal; f_equal;[ring| f_equal; f_equal; ring].
f_equal; f_equal; ring.
ring.
(* *)
unfold tv; rewrite <- Hfg'', <- Hftv''.
case H; intros H'; [left|right].
apply trans_eq with (FtoR radix2 (RND_Min
   (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (a*x+y))).
apply MinUniqueP with  (make_bound radix2 prec emin) (a*x+y)%R; try easy.
apply RND_Min_correct; try easy.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite pff_round_DN_is_round.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Rplus_comm; easy.
apply make_bound_p; lia.
lia.
apply trans_eq with (FtoR radix2 (RND_Max
   (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (a*x+y))).
apply MaxUniqueP with  (make_bound radix2 prec emin) (a*x+y)%R; try easy.
apply RND_Max_correct; try easy.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite pff_round_UP_is_round.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Rplus_comm; easy.
apply make_bound_p; lia.
lia.
Qed.

End Axpy.

Section Discri1.
Variable emin prec : Z.
Hypothesis precisionGt : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation bpow e := (bpow radix2 e).

(** inputs *)
Variable a b c:R.
Hypothesis Fa: format a.
Hypothesis Fb: format b.
Hypothesis Fc: format c.

(** algorithm *)
Let p:=round_flt (b*b).
Let q:=round_flt (a*c).
Let dp:= b*b-p.
Let dq:= a*c-q.
Let d:= if (Rle_bool (p+q) (3*Rabs (p-q)))
            then round_flt (p-q)
            else round_flt (round_flt (p-q) + round_flt(dp-dq)).

(** No-underflow hypotheses *)
Hypothesis U1 : b * b <> 0 ->
    bpow (emin + 3 * prec) <= Rabs (b * b).
Hypothesis U2 : a * c <> 0 ->
    bpow (emin + 3 * prec) <= Rabs (a * c).
Hypothesis Zd : d <> 0.


Lemma U3_discri1 : b * b <> 0 -> a * c <> 0 -> p - q <> 0 ->
   bpow (emin + 2*prec) <= Rabs (round_flt (p-q)).
Proof with auto with typeclass_instances.
intros Z1 Z2 Z3.
unfold Rminus; apply round_FLT_plus_ge...
apply generic_format_round...
apply generic_format_opp, generic_format_round...
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=U1 Z1); apply bpow_le; lia.
apply round_plus_neq_0...
apply generic_format_round...
apply generic_format_opp, generic_format_round...
Qed.

Lemma U4_discri1 : b * b <> 0 -> a * c <> 0 -> p - q <> 0 ->
    bpow (emin + prec) <= Rabs d.
Proof with auto with typeclass_instances.
intros Z1 Z2 Z3; generalize Zd; unfold d.
case (Rle_bool_spec _ _); intros H Z4.
apply Rle_trans with (2:=U3_discri1 Z1 Z2 Z3).
apply bpow_le; lia.
apply round_FLT_plus_ge...
apply generic_format_round...
apply generic_format_round...
replace (emin + prec + prec)%Z with (emin+2*prec)%Z by ring.
apply U3_discri1; easy.
Qed.

Lemma format_dp : format dp.
Proof with auto with typeclass_instances.
replace (dp) with (-(p-(b*b))) by (unfold dp; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros Zbb; apply Rle_trans with (2:=U1 Zbb).
apply bpow_le; lia.
Qed.

Lemma format_dq : format dq.
Proof with auto with typeclass_instances.
replace (dq) with (-(q-(a*c))) by (unfold dq; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros Zac; apply Rle_trans with (2:=U2 Zac).
apply bpow_le; lia.
Qed.

Lemma format_d_discri1 : format d.
Proof with auto with typeclass_instances.
unfold d; case (Rle_bool _ _).
apply generic_format_round...
apply generic_format_round...
Qed.

Lemma U5_discri1_aux : forall x y e, format x -> format y
   -> (emin <= e)%Z -> bpow e <= Rabs x -> bpow e <= Rabs y
   -> round_flt (x+y) <> x+y
   -> bpow e <= Rabs (round_flt (x+y)).
Proof with auto with typeclass_instances.
intros x y e Fx Fy He Hex Hey H.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
case (Rle_or_lt (bpow e) (Rabs (x+y))); intros H1; try easy.
absurd (round_flt (x + y) = x + y); try assumption.
apply round_generic...
apply generic_format_plus...
apply Rlt_le; apply Rlt_le_trans with (1:=H1).
destruct (mag radix2 x) as (ex,Y1).
destruct (mag radix2 y) as (ey,Y2); simpl.
apply bpow_le.
apply Z.min_glb.
apply le_bpow with radix2.
apply Rle_trans with (1:=Hex).
apply Rlt_le, Y1.
intros Zx; contradict H.
rewrite Zx, Rplus_0_l, round_generic...
apply le_bpow with radix2.
apply Rle_trans with (1:=Hey).
apply Rlt_le, Y2.
intros Zy; contradict H.
rewrite Zy, Rplus_0_r, round_generic...
Qed.


Lemma U5_discri1 : b * b <> 0 -> a*c <> 0 ->
  round_flt (dp - dq) <> dp - dq ->
  bpow (emin + prec - 1) <= Rabs (round_flt (dp - dq)).
Proof with auto with typeclass_instances.
intros Z1 Z2 Z3.
apply U5_discri1_aux.
apply format_dp...
apply generic_format_opp, format_dq...
lia.
unfold dp; replace (b * b - p) with (-(p-b*b)) by ring.
rewrite Rabs_Ropp; unfold p.
apply mult_error_FLT_ge_bpow...
apply Rle_trans with (2:=U1 Z1).
apply bpow_le; lia.
replace (round_flt (b * b) - b * b) with (-dp).
apply Ropp_neq_0_compat.
intros Z4; contradict Z3.
rewrite Z4, Rminus_0_l, round_generic...
apply generic_format_opp, format_dq...
unfold dp, p; ring.
unfold dq; replace (-(a * c - q)) with (q-a*c) by ring.
unfold q; apply mult_error_FLT_ge_bpow...
apply Rle_trans with (2:=U2 Z2).
apply bpow_le; lia.
replace (round_flt (a * c) - a * c) with (-dq).
apply Ropp_neq_0_compat.
intros Z4; contradict Z3.
rewrite Z4, Rminus_0_r, round_generic...
apply format_dp...
unfold dq, q; ring.
easy.
Qed.

(** Correctness of d *)
Theorem discri_correct_test :
 Rabs (d-(b*b-a*c)) <= 2* ulp_flt d.
Proof with auto with typeclass_instances.
(* b*b=0 or a*c=0 *)
case (Req_dec (b*b) 0); intros Zbb.
unfold d, p; rewrite Zbb, round_0...
rewrite Rplus_0_l, Rminus_0_l, Rabs_Ropp.
rewrite Rle_bool_true.
rewrite round_NE_opp.
rewrite ulp_opp.
rewrite round_generic...
2: apply generic_format_round...
apply Rle_trans with (Rabs (-(q-a*c))).
right; f_equal; ring.
rewrite Rabs_Ropp.
apply Rle_trans with (1:=error_le_half_ulp_round _ _ _ _).
fold q; apply Rmult_le_compat_r.
apply ulp_ge_0.
lra.
apply Rle_trans with (1:=RRle_abs _).
rewrite <- (Rmult_1_l (Rabs _)) at 1.
apply Rmult_le_compat_r.
apply Rabs_pos.
lra.
case (Req_dec (a*c) 0); intros Zac.
unfold d, q; rewrite Zac, round_0...
rewrite Rplus_0_r, 2!Rminus_0_r.
rewrite Rle_bool_true.
rewrite round_generic...
2: apply generic_format_round...
apply Rle_trans with (1:=error_le_half_ulp_round _ _ _ _).
fold p; apply Rmult_le_compat_r.
apply ulp_ge_0.
lra.
apply Rle_trans with (1:=RRle_abs _).
rewrite <- (Rmult_1_l (Rabs _)) at 1.
apply Rmult_le_compat_r.
apply Rabs_pos.
lra.
(* p-q = 0 *)
case (Req_dec (p-q) 0); intros Zpq.
assert (H:d = round_flt (dp - dq)).
unfold d; case (Rle_bool_spec _ _); intros H.
contradict Zd.
unfold d; rewrite Rle_bool_true; try assumption.
rewrite Zpq, round_0...
rewrite Zpq, round_0...
rewrite Rplus_0_l, round_generic...
apply generic_format_round...
replace d with (round_flt (b * b - a * c)).
apply Rle_trans with (1:=error_le_half_ulp_round _ _ _ _).
apply Rmult_le_compat_r.
apply ulp_ge_0.
lra.
rewrite H; f_equal.
unfold dp, dq; apply trans_eq with (b * b - a * c - (p-q)).
rewrite Zpq; ring.
ring.
(* round_flt (dp - dq) <> dp - dq when Sterbenz *)
assert (G: (3 * Rabs (p - q) < p + q /\ round_flt (dp - dq) = dp-dq) \/
    ((3 * Rabs (p - q) < p + q) -> round_flt (dp - dq) <> dp-dq)).
case (Req_dec (round_flt (dp - dq)) (dp-dq)); intros G1;
  case (Rlt_or_le (3 * Rabs (p - q)) (p+q)); intros G2.
left; now split.
right; intros G3; contradict G2; apply Rlt_not_le; easy.
now right.
now right.
destruct G as [(G1,G2)|G].
unfold d; rewrite Rle_bool_false...
rewrite G2.
replace (round_flt (p - q)) with (p-q).
replace ((p - q + (dp - dq))) with (b * b - a * c).
2: unfold dp, p, dq, q; ring.
apply Rle_trans with (1:=error_le_half_ulp_round _ _ _ _).
apply Rmult_le_compat_r.
apply ulp_ge_0.
lra.
apply sym_eq, round_generic...
apply sterbenz...
apply generic_format_round...
apply generic_format_round...
split.
apply Rmult_le_reg_l with 4%R.
lra.
apply Rplus_le_reg_l with (q-3*p).
apply Rle_trans with (p+q);[idtac|right; ring].
apply Rlt_le, Rle_lt_trans with (2:=G1).
rewrite <- Rabs_Ropp.
apply Rle_trans with (3*(-(p-q))).
right; field.
apply Rmult_le_compat_l; [lra|apply RRle_abs].
apply Rmult_le_reg_l with 2%R.
lra.
apply Rplus_le_reg_l with (p-3*q).
apply Rle_trans with (p+q);[idtac|right; ring].
apply Rlt_le, Rle_lt_trans with (2:=G1).
apply Rle_trans with (3*(p-q)).
right; field.
apply Rmult_le_compat_l; [lra|apply RRle_abs].
assert (precisionNotZero : (1 < prec)%Z) by lia.
(* variables *)
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero b)
  as (fb,(Hfb,Hfb')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero c)
  as (fc,(Hfc,Hfc')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
(* algo *)
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (b*b))  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (a*c))  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero dp)
  as (fdp,(Hfdp,Hfdp')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
apply format_dp.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero dq)
  as (fdq,(Hfdq,Hfdq')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
apply format_dq.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (p-q))  as (ft,(Hft, (Hft',Hft''))).
rewrite make_bound_Emin in Hft''; try assumption.
replace (--emin)%Z with emin in Hft'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (dp-dq))  as (fs,(Hfs, (Hfs',Hfs''))).
rewrite make_bound_Emin in Hfs''; try assumption.
replace (--emin)%Z with emin in Hfs'' by lia.
destruct (format_is_pff_format_can radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero d)
  as (fd,(Hfd,Hfd')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
apply format_d_discri1.
assert (K: (1 < Z.abs_nat prec)%nat).
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
(* application of theo *)
rewrite <- Hfd, <- Hfb, <- Hfa, <- Hfc.
apply Rle_trans with (2 * Fulp (make_bound radix2 prec emin) 2 (Z.abs_nat prec) fd)%R.
apply discri with fp fq ft fdp fdq fs; try assumption.
apply make_bound_p; lia.
apply FcanonicBound with radix2; try assumption.
apply FcanonicBound with radix2; try assumption.
apply FcanonicBound with radix2; try assumption.
apply FcanonicBound with radix2; try assumption.
(* underflow *)
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
assert (emin < Pff.Fexp fd)%Z; try lia.
apply FloatFexp_gt with radix2 (make_bound radix2 prec emin) prec; try assumption.
apply make_bound_p; lia.
apply FcanonicBound with radix2; try assumption.
rewrite Hfd.
apply U4_discri1; assumption.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
assert (emin < Pff.Fexp ft)%Z; try lia.
apply FloatFexp_gt with radix2 (make_bound radix2 prec emin) prec; try assumption.
apply make_bound_p; lia.
now apply FcanonicBound with radix2.
rewrite Hft''.
apply Rle_trans with (2:=U3_discri1 Zbb Zac Zpq).
apply bpow_le; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite inj_abs;[idtac|lia].
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfb.
apply Rle_trans with (2:=U1 Zbb).
rewrite <- bpow_powerRZ.
apply bpow_le; simpl (radix_val radix2); lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite inj_abs;[idtac|lia].
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfa, Hfc.
apply Rle_trans with (2:=U2 Zac).
rewrite <- bpow_powerRZ.
apply bpow_le; simpl (radix_val radix2); lia.
replace 2%Z with (radix_val radix2) by easy.
right; apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Hfp''.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=U1 Zbb).
apply bpow_le; lia.
replace 2%Z with (radix_val radix2) by easy.
right; apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Hfq''.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=U2 Zac).
apply bpow_le; lia.
intros C; right.
replace 2%Z with (radix_val radix2) by easy.
apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Hfs''.
apply U5_discri1; try assumption.
apply G.
unfold p, q; rewrite <- Hfp'', <- Hfq''; easy.
replace 2%Z with (radix_val radix2) by easy.
apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Hfd.
apply Rle_trans with (2:=U4_discri1 Zbb Zac Zpq).
apply bpow_le; lia.
(* *)
rewrite <- Hfb in Hfp'; assumption.
rewrite <- Hfa, <- Hfc in Hfq'; assumption.
intros Y.
assert (Y' : d = round_flt (p - q)).
unfold d; rewrite Rle_bool_true; try easy.
unfold p; rewrite <- Hfp''; unfold q; rewrite <- Hfq''.
easy.
apply EvenClosestCompatible with (p-q)
   (RND_EvenClosest (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (p-q)); try easy.
apply make_bound_p; lia.
apply RND_EvenClosest_correct; try easy.
apply make_bound_p; lia.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfd, Y'.
rewrite pff_round_NE_is_round; try easy.
2: apply make_bound_p; lia.
2: apply FcanonicBound with radix2; try assumption.
rewrite make_bound_Emin; try assumption.
now replace (--emin)%Z with emin by lia.
intros _; generalize Hft'.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
intros _; replace 2%Z with (radix_val radix2) by easy.
rewrite Hfdp; unfold dp; now rewrite <- Hfb, Hfp''.
intros _; replace 2%Z with (radix_val radix2) by easy.
rewrite Hfdq; unfold dq; now rewrite <- Hfa, <- Hfc, Hfq''.
intros _; generalize Hfs'.
now rewrite <- Hfdp, <- Hfdq.
intros Y.
assert (Y' : d = round_flt (round_flt (p - q) + round_flt (dp - dq))).
unfold d; rewrite Rle_bool_false; try easy.
unfold p; rewrite <- Hfp''; unfold q; rewrite <- Hfq''.
easy.
apply EvenClosestCompatible with (FtoR radix2 ft+FtoR radix2 fs)
   (RND_EvenClosest (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (FtoR radix2 ft+FtoR radix2 fs)); try easy.
apply make_bound_p; lia.
apply RND_EvenClosest_correct; try easy.
apply make_bound_p; lia.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfd, Y'.
rewrite pff_round_NE_is_round; try easy.
2: apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
now rewrite Hfs'', Hft''.
apply FcanonicBound with radix2; try assumption.
right; f_equal.
replace 2%Z with (radix_val radix2) by easy.
rewrite Fulp_ulp; try easy.
2: apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
now replace (--emin)%Z with emin by lia.
apply FcanonicBound with radix2; try assumption.
Qed.


End Discri1.

Section Discri2.
Variable emin prec : Z.
Hypothesis precisionGt : (4 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation bpow e := (bpow radix2 e).

(** inputs *)
Variable a b c:R.
Hypothesis Fa: format a.
Hypothesis Fb: format b.
Hypothesis Fc: format c.

(** algorithm *)
Let p:=round_flt (b*b).
Let q:=round_flt (a*c).
Let dp:= b*b-p.
Let dq:= a*c-q.
Let d:= if (Rle_bool (round_flt (p+q)) (round_flt (3*Rabs (round_flt (p-q)))))
            then round_flt (p-q)
            else round_flt (round_flt (p-q) + round_flt(dp-dq)).

(** No-underflow hypotheses *)
Hypothesis U1 : b * b <> 0 ->
    bpow (emin + 3 * prec) <= Rabs (b * b).
Hypothesis U2 : a * c <> 0 ->
    bpow (emin + 3 * prec) <= Rabs (a * c).
Hypothesis Zd : d <> 0.


Lemma format_d_discri2 : format d.
Proof with auto with typeclass_instances.
unfold d; case (Rle_bool _ _).
apply generic_format_round...
apply generic_format_round...
Qed.


(** Correctness of d *)
Theorem discri_fp_test :
 Rabs (d-(b*b-a*c)) <= 2* ulp_flt d.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.
(* variables *)
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero b)
  as (fb,(Hfb,Hfb')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero c)
  as (fc,(Hfc,Hfc')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
(* algo *)
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (b*b))  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (a*c))  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (format_is_pff_format_can radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero dp)
  as (fdp,(Hfdp,Hfdp')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
now apply format_dp.
destruct (format_is_pff_format_can radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero dq)
  as (fdq,(Hfdq,Hfdq')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
now apply format_dq.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (p-q))  as (ft,(Hft, (Hft',Hft''))).
rewrite make_bound_Emin in Hft''; try assumption.
replace (--emin)%Z with emin in Hft'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (dp-dq))  as (fs,(Hfs, (Hfs',Hfs''))).
rewrite make_bound_Emin in Hfs''; try assumption.
replace (--emin)%Z with emin in Hfs'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (p+q))  as (fv,(Hfv, (Hfv',Hfv''))).
rewrite make_bound_Emin in Hfv''; try assumption.
replace (--emin)%Z with emin in Hfv'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (3*Rabs (FtoR radix2 ft)))  as (fu,(Hfu, (Hfu',Hfu''))).
rewrite make_bound_Emin in Hfu''; try assumption.
replace (--emin)%Z with emin in Hfu'' by lia.
destruct (format_is_pff_format_can radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero d)
  as (fd,(Hfd,Hfd')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
apply format_d_discri2.
assert (K: (1 < Z.abs_nat prec)%nat).
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
(* application of theo *)
rewrite <- Hfd, <- Hfb, <- Hfa, <- Hfc.
apply Rle_trans with (2 * Fulp (make_bound radix2 prec emin) 2 (Z.abs_nat prec) fd)%R.
cut ((FtoR radix2 fd = 0 \/ (Rabs  (FtoR radix2 fd -
   (FtoR radix2 fb * FtoR radix2 fb -
    FtoR radix2 fa * FtoR radix2 fc)) <=
    2 * Fulp (make_bound radix2 prec emin) 2 (Z.abs_nat prec) fd))).
intros M; case M; try easy.
intros KK; contradict Zd; rewrite <- Hfd; easy.
apply discri16 with fp fq ft fdp fdq fs fu fv; try assumption.
apply make_bound_p; lia.
change 4%nat with (Z.abs_nat 4).
apply Zabs_nat_le; lia.
intros _; apply FcanonicBound with radix2; try assumption.
intros _; apply FcanonicBound with radix2; try assumption.
(* underflow *)
unfold radix2 in Hfb; simpl in Hfb; rewrite Hfb.
case (Req_dec b 0); intros Zb.
now left.
right; apply Rle_trans with (bpow (emin + 3 * prec-1)).
rewrite bpow_powerRZ; right; f_equal.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite inj_abs; lia.
apply Rle_trans with (bpow (emin + 3 * prec)).
apply bpow_le; lia.
apply U1; auto with real.
unfold radix2 in Hfa, Hfc; simpl in Hfa, Hfc; rewrite Hfa, Hfc.
case (Req_dec (a*c) 0); intros Zac.
now left.
right; apply Rle_trans with (bpow (emin + 3 * prec - 1)).
rewrite bpow_powerRZ; right; f_equal.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite inj_abs; lia.
apply Rle_trans with (2:=U2 Zac); auto with real.
apply bpow_le; lia.
(* *)
rewrite <- Hfb in Hfp'; assumption.
rewrite <- Hfa, <- Hfc in Hfq'; assumption.
generalize Hft'.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
generalize Hfv'.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
intros Y.
assert (Y' : d = round_flt (p - q)).
unfold d; rewrite Rle_bool_true; try easy.
now rewrite <- Hfv'', <- Hft'', <- Hfu''.
apply EvenClosestCompatible with (p-q)
   (RND_EvenClosest (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (p-q)); try easy.
apply make_bound_p; lia.
apply RND_EvenClosest_correct; try easy.
apply make_bound_p; lia.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfd, Y'.
rewrite pff_round_NE_is_round; try easy.
2: apply make_bound_p; lia.
2: apply FcanonicBound with radix2; try assumption.
rewrite make_bound_Emin; try assumption.
now replace (--emin)%Z with emin by lia.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfdp; unfold dp; now rewrite <- Hfb, Hfp''.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfdq; unfold dq; now rewrite <- Hfa, <- Hfc, Hfq''.
intros _; generalize Hfs'.
now rewrite <- Hfdp, <- Hfdq.
intros Y.
assert (Y' : d = round_flt (round_flt (p - q) + round_flt (dp - dq))).
unfold d; rewrite Rle_bool_false; try easy.
now rewrite <- Hfv'', <- Hft'', <- Hfu''.
apply EvenClosestCompatible with (FtoR radix2 ft+FtoR radix2 fs)
   (RND_EvenClosest (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (FtoR radix2 ft+FtoR radix2 fs)); try easy.
apply make_bound_p; lia.
apply RND_EvenClosest_correct; try easy.
apply make_bound_p; lia.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfd, Y'.
rewrite pff_round_NE_is_round; try easy.
2: apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
now rewrite Hfs'', Hft''.
apply FcanonicBound with radix2; try assumption.
right; f_equal.
replace 2%Z with (radix_val radix2) by easy.
rewrite Fulp_ulp; try easy.
2: apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
now replace (--emin)%Z with emin by lia.
apply FcanonicBound with radix2; try assumption.
Qed.


End Discri2.


