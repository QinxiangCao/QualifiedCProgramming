From compcert.lib Require Import Coqlib Integers.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

(** * Frequently used lemmas in tactics. *)

Lemma min_signed_lt0 : Int64.min_signed < 0.
Proof.
  unfold Int64.min_signed, Int64.half_modulus, Int64.modulus.
  simpl; lia.
Qed.

#[export] Hint Resolve min_signed_lt0  : int_compare_lemmas.

Lemma max_signed_gt0 : Int64.max_signed > 0.
Proof.
  unfold Int64.max_signed, Int64.half_modulus, Int64.modulus.
  simpl; lia.
Qed.

#[export] Hint Resolve min_signed_lt0  : int_compare_lemmas.

Lemma zdiv_equiv: forall x y : Z, x >= 0 -> y > 0 -> x ÷ y = x / y.
Proof.
  intros.
  rewrite Zbits.Zquot_Zdiv.
  destruct (zlt x 0).
  lia.
  trivial.
  assumption.
Qed.

Lemma zadd_rm_head: forall n p q, p = q -> n + p = n + q.
Proof.
  intros.
  rewrite H.
  trivial.
Qed.

Lemma zadd_rm_tail: forall n p q, p = q -> p + n = q + n.
Proof.
  intros.
  rewrite H.
  trivial.
Qed.

Lemma zdiv_range_le_lt : forall a b c x: Z, a <= 0 -> b > 0 -> c > 0 -> a <= x < b -> a <= x/ c < b.
Proof.
  intros.
  destruct H2.
  split.
  apply Zdiv_le_lower_bound.
  lia.
  assert(a * c <= a).
  assert(- a * c >= - a).
  rewrite <- Zmult_1_r.
  assert(c >= 1) by lia.
  apply Zmult_ge_compat_l.
  lia.
  lia.
  rewrite Zopp_mult_distr_l_reverse in H4.
  lia.
  lia.
  apply Zdiv_lt_upper_bound.
  lia.
  assert(b <= b * c).
  rewrite <- Zmult_1_r at 1.
  assert(1 <= c) by lia.
  apply Zmult_le_compat_l.
  lia.
  lia.
  lia.
Qed.

Lemma zdiv_range_le_le : forall a b c x: Z, a <= 0 -> b > 0 -> c > 0 -> a <= x <= b -> a <= x/ c <= b.
Proof.
  intros.
  destruct H2.
  split.
  apply Zdiv_le_lower_bound.
  lia.
  assert(a * c <= a).
  assert(- a * c >= - a).
  rewrite <- Zmult_1_r.
  assert(c >= 1) by lia.
  apply Zmult_ge_compat_l.
  lia.
  lia.
  rewrite Zopp_mult_distr_l_reverse in H4.
  lia.
  lia.
  apply Zdiv_le_upper_bound.
  lia.
  assert(b <= b * c).
  rewrite <- Zmult_1_r at 1.
  assert(1 <= c) by lia.
  apply Zmult_le_compat_l.
  lia.
  lia.
  lia.
Qed.

Lemma max_unsigned_gt0: Int64.max_unsigned > 0.
Proof.
  unfold Int64.max_unsigned, Int64.modulus.
  simpl; lia.
Qed.

#[export] Hint Resolve max_unsigned_gt0  : int_compare_lemmas.


Lemma max_unsigned_val: Int64.max_unsigned  = 18446744073709551615.
Proof.
  unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
  simpl. lia.
Qed.

Lemma max_signed_val : Int64.max_signed = 9223372036854775807.
Proof.
  unfold Int64.max_signed, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
  simpl. lia.
Qed.

Lemma min_signed_val : Int64.min_signed = -9223372036854775808.
Proof.
  unfold Int64.min_signed, Int64.half_modulus, Int64.modulus.
  simpl. lia.
Qed.

Lemma unsigned_mone_val : Int64.unsigned Int64.mone = 18446744073709551615.
Proof.
  rewrite Int64.unsigned_mone.
  simpl. auto.
Qed.

Lemma modulus_val : Int64.modulus = 18446744073709551616.
Proof.
  assert ( Int64.modulus - 1 = 18446744073709551615).
  unfold Int64.modulus,  Int64.wordsize, Wordsize_64.wordsize.
  simpl. lia.
  lia.
Qed.

Lemma unsigned_inj : forall a b, Int64.unsigned a = Int64.unsigned b -> a = b.
Proof.
  intros. rewrite <- (Int64.repr_unsigned a).
  rewrite <- (Int64.repr_unsigned b).
  f_equal.
  trivial.
Qed.

Lemma minus1lt: forall i:Z, i - 1 < i.
Proof.
  intro.
  lia.
Qed.

Lemma Z_land_range_lo: forall x y, 0 <= x -> 0 <= Z.land x y.
Proof.
  intros.
  rewrite Z.land_nonneg.
  left.
  assumption.
Qed. 

Lemma Z_land_range_lo_r: forall x y, 0 <= y -> 0 <= Z.land x y.
Proof.
  intros.
  rewrite Z.land_nonneg.
  right.
  assumption.
Qed.

(* Lemma Z_land_range_hi: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> Z.land x y <= Int64.max_unsigned.
Proof.
  rewrite max_unsigned_val.
  intros.
  assert(Z.land x y < 4294967296).
  apply Z.log2_lt_cancel.
  assert(Z.log2 (Z.land x y) <= Z.min (Z.log2 x) (Z.log2 y)).
  apply Z.log2_land.
  lia.
  lia.
  destruct (zlt (Z.log2 x) (Z.log2 y)).
  assert(Z.log2 x <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  lia.
  simpl in *.
  lia.
  assert(Z.log2 y <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  lia.
  simpl in *.
  lia.
  lia.
Qed.   

Lemma Z_land_range: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> 0 <= Z.land x y <= Int64.max_unsigned.
Proof.
  split.
  apply Z_land_range_lo; lia.
  apply Z_land_range_hi; lia.
Qed.

Lemma Z_lor_range_lo: forall x y, 0 <= x -> 0 <= y -> 0 <= Z.lor x y.
Proof.
  intros.
  apply Z.lor_nonneg; auto.
Qed.

Lemma Z_lor_range_hi: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> Z.lor x y <= Int64.max_unsigned.
Proof.
  rewrite max_unsigned_val; simpl.
  intros.
  assert(Z.lor x y < 4294967296).
  apply Z.log2_lt_cancel.
  assert(Z.log2 (Z.lor x y) = Z.max (Z.log2 x) (Z.log2 y)).
  apply Z.log2_lor.
  lia.
  lia.
  rewrite H1.
  destruct (zlt (Z.log2 y) (Z.log2 x)).
  assert(Z.log2 x <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  lia.
  simpl in *.
  lia.
  assert(Z.log2 y <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  lia.
  simpl in *.
  lia.
  lia.
Qed.

Lemma Z_lor_range: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> 0 <= Z.lor x y <= Int64.max_unsigned.
Proof.
  intros.
  split.
  apply Z_lor_range_lo; lia.
  apply Z_lor_range_hi; lia.
Qed.

Lemma Z_lxor_range :
  forall x y,
    0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
    0 <= Z.lxor x y <= Int64.max_unsigned.
Proof.
  rewrite max_unsigned_val; simpl.
  intros.
  split.
  rewrite Z.lxor_nonneg.
  split; lia.
  assert(Z.lxor x y < 4294967296).
  apply Z.log2_lt_cancel.
  assert(Z.log2 (Z.lxor x y) <= Z.max (Z.log2 x) (Z.log2 y)).
  apply Z.log2_lxor.
  lia.
  lia.
  apply Z.le_lt_trans with (m := Z.max (Z.log2 x) (Z.log2 y)); auto.
  destruct (zlt (Z.log2 y) (Z.log2 x)).
  assert(Z.log2 x <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  lia.
  simpl in *.
  lia.
  assert(Z.log2 y <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  lia.
  simpl in *.
  lia.
  lia.
Qed.

Lemma Z_shiftl_16_range :
  forall x,
    0 <= x < 65536 -> 0 <= Z.shiftl x 16 <= Int64.max_unsigned.
Proof.
  unfold Int64.max_unsigned. simpl (Int64.modulus - 1).
  intros.
  split.
  rewrite Z.shiftl_nonneg. lia.

  assert (Z.shiftl x 16 < 4294967296).
  case_eq (zeq x 0); intros; subst.

  (* x = 0 *)
  simpl. lia.

  (* x <> 0 *)
  apply Z.log2_lt_cancel.
  rewrite Z.log2_shiftl; try lia.

  assert (Z.log2 x <= Z.log2 65535).
  apply Z.log2_le_mono. lia.
  simpl in *. lia.

  lia.
Qed. *)

(** * Hints for autorewrite *)

Lemma unsigned_zero: Int64.unsigned Int64.zero = 0.
Proof. reflexivity. Qed.

Lemma unsigned_one: Int64.unsigned Int64.one = 1.
Proof. reflexivity. Qed.

Lemma eq_one_zero: Int64.eq Int64.one Int64.zero = false.
Proof. reflexivity. Qed.

Lemma eq_zero_zero: Int64.eq Int64.zero Int64.zero = true.
Proof. reflexivity. Qed.

Lemma negb_true: negb true = false.
Proof. reflexivity. Qed.

Lemma negb_false: negb false = true.
Proof. reflexivity. Qed.

Lemma repr_zero: Int64.repr 0 = Int64.zero.
Proof. reflexivity. Qed.

Lemma repr_one: Int64.repr 1 = Int64.one.
Proof. reflexivity. Qed.

Lemma and_zero_zero: Z.land 0 0 = 0.
Proof. reflexivity. Qed.

Lemma and_one_zero: Z.land 1 0 = 0.
Proof. reflexivity. Qed.

Lemma and_zero_one: Z.land 0 1 = 0.
Proof. reflexivity. Qed.

Lemma and_one_one: Z.land 1 1 = 1.
Proof. reflexivity. Qed.

Lemma or_zero_zero: Z.lor 0 0 = 0.
Proof. reflexivity. Qed.

Lemma or_one_zero: Z.lor 1 0 = 1.
Proof. reflexivity. Qed.

Lemma or_zero_one: Z.lor 0 1 = 1.
Proof. reflexivity. Qed.

Lemma or_one_one: Z.lor 1 1 = 1.
Proof. reflexivity. Qed.

#[export] Hint Rewrite unsigned_zero unsigned_one eq_one_zero eq_zero_zero negb_true negb_false repr_zero repr_one: arith.
#[export] Hint Rewrite and_zero_zero and_zero_one and_one_zero and_one_one or_zero_zero or_zero_one or_one_zero or_one_one : arith.


(** * Auxiliary tactics used by other main tactics below. *)
(* Check svn version before 1408 *)

Ltac simpleproof := match goal with
                      | [|- _ <= _] => contradiction|| assumption || lia || trivial || eassumption || auto with int_compare_lemmas || idtac
                      | _ => contradiction || assumption || lia || trivial || reflexivity || eassumption || auto with int_compare_lemmas  || idtac
                    end.

Ltac autorewritearith := autorewrite with arith using simpleproof.

Ltac solve_signed_range c x:= 
  assert(cge0: c > 0) by lia; 
  generalize(zdiv_range_le_le Int64.min_signed Int64.max_signed c (Int64.signed x) min_signed_lt0 max_signed_gt0 cge0 (Int64.signed_range x));
  lia; clear cge0.

Ltac solve_unsigned_range c x :=
  assert(cge0: c > 0) by lia;
  assert(zlez: 0 <= 0) by lia; 
  generalize(zdiv_range_le_le 0 Int64.max_unsigned c (Int64.unsigned x) zlez max_unsigned_gt0 cge0 (Int64.unsigned_range_2 x));
  lia; clear cge0 zlez.

Ltac solve_unsigned_range_lt c x := 
  assert(cge0: c > 0) by lia; 
  assert(zlez: 0 <= 0) by lia;
  assert(xpre: 0 <= x < Int64.max_unsigned) by lia;
  generalize(zdiv_range_le_lt 0 Int64.max_unsigned c x zlez max_unsigned_gt0 cge0 xpre);
  lia; clear cge0 zlez xpre.

Ltac computedivmul := 
  match goal with
    | [|- context [?x / ?y]] => let val := eval compute in (x / y) in change (x / y) with val
    | [|- context [?x * ?y]] => let val := eval compute in (x * y) in change (x * y) with val
  end.


(** * The tactic to prove the integers fit in signed range or unsigned range. *)

Ltac gen_signed_unsigned_range e :=
  let H := fresh in
  match e with
    | ?e1 + ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2
    | ?e1 - ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2
    | ?e1 * ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2
    | ?e1 / ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2
    | context [ Int64.signed ?i ] => 
      generalize (Int64.signed_range i);
        intros H; rewrite max_signed_val in H; rewrite min_signed_val in H
    | context [ Int64.unsigned ?i ] =>
      generalize (Int64.unsigned_range i);
        intros H ; rewrite modulus_val in H 
    | _ => idtac
  end.

Ltac solve_int_unequal :=
  match goal with
    | H: _ /\ _ |- _=> destruct H; solve_int_unequal
    | |- _ /\ _ => split; solve_int_unequal
    | |- ?e1 <= ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2; try lia
    | |- ?e1 < ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2; try lia
    | |- ?e1 >= ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2; try lia
    | |- ?e1 > ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2; try lia
    | |- Int64.min_signed <= Int64.signed ?x / ?c =>
      solve_signed_range c x
    | |- Int64.min_signed <= ?x / ?c => 
      rewrite <- Int64.signed_repr with (z:= x); solve_signed_range c (Int64.repr x)
    | |- Int64.signed ?x / ?c <= Int64.max_signed =>
      solve_signed_range c x
    | |- ?x / ?c <= Int64.max_signed => 
      rewrite <- Int64.signed_repr with (z:= x); solve_signed_range c (Int64.repr x)
    | |- 0 <= Int64.unsigned ?x / ?c => solve_unsigned_range c x
    | |- 0 <= ?x / ?c => rewrite <- Int64.unsigned_repr with (z:= x); solve_unsigned_range c (Int64.repr x)
    | |- 0 <= ?x / ?c + 1 => rewrite <- Int64.unsigned_repr with (z:= x); solve_unsigned_range c (Int64.repr x)
    | |- Int64.unsigned ?x / ?c <= Int64.max_unsigned => solve_unsigned_range c x
    | |- ?x / ?c <= Int64.max_unsigned => rewrite <- Int64.unsigned_repr with (z:= x); solve_unsigned_range c (Int64.repr x)
    | |- ?x / ?c + 1 <= Int64.max_unsigned => solve_unsigned_range_lt c x
    | |- ?x / ?y * ?c => try (computedivmul; lia)
    | _ => idtac
  end.

 
   

Ltac unsigned_range := 
  match goal with
   | [|- 0 <= ?af] =>
      match af with
        | _ => try lia
      end
    | [|- ?af <= Int64.max_unsigned] => 
      match af with
        | _ => repeat rewrite max_unsigned_val; try lia
      end
  end.

Ltac int_auto_simpl :=
  match goal with
    | H: _ /\ _ |- _ => destruct H; int_auto_simpl

    | H: context [Int64.signed Int64.zero] |- _ => change (Int64.signed Int64.zero) with 0 in H; int_auto_simpl
    | |- context [Int64.signed Int64.zero] => change (Int64.signed Int64.zero) with 0; int_auto_simpl
    | H: context [Int64.signed Int64.one] |- _ => change (Int64.signed Int64.one) with 1 in H; int_auto_simpl
    | |- context [Int64.signed Int64.one] => change (Int64.signed Int64.one) with 1; int_auto_simpl

    | H: context [Int64.unsigned Int64.zero] |- _ => change (Int64.unsigned Int64.zero) with 0 in H; int_auto_simpl
    | |- context [Int64.unsigned Int64.zero] => change (Int64.unsigned Int64.zero) with 0; int_auto_simpl
    | H: context [Int64.unsigned Int64.one] |- _ => change (Int64.unsigned Int64.one) with 1 in H; int_auto_simpl
    | |- context [Int64.unsigned Int64.one] => change (Int64.unsigned Int64.one) with 1; int_auto_simpl
    | H: context [Int64.unsigned Int64.mone] |- _ => rewrite unsigned_mone_val in H; int_auto_simpl
    | |- context [Int64.unsigned Int64.mone] => rewrite unsigned_mone_val; int_auto_simpl

    | H: context [Int64.eq ?x ?x] |- _ => rewrite Int64.eq_true in H; int_auto_simpl
    | |- context [Int64.eq ?x ?x] => rewrite Int64.eq_true; int_auto_simpl
    | H: context [Int64.eq Int64.one Int64.zero] |- _ => change (Int64.eq Int64.one Int64.zero) with false in H; int_auto_simpl
    | |- context [Int64.eq Int64.one Int64.zero] => change (Int64.eq Int64.one Int64.zero) with false; int_auto_simpl

    | H: context [Int64.and Int64.zero _] |- _ => rewrite Int64.and_zero_l in H; int_auto_simpl
    | |- context [Int64.and Int64.zero _] => rewrite Int64.and_zero_l; int_auto_simpl
    | H: context [Int64.and _ Int64.zero] |- _ => rewrite Int64.and_zero in H; int_auto_simpl
    | |- context [Int64.and _ Int64.zero] => rewrite Int64.and_zero; int_auto_simpl
                                                                 
    | H: context [negb true] |- _ => change (negb true) with false in H; int_auto_simpl
    | |- context [negb true] => change (negb true) with false; int_auto_simpl
    | H: context [negb false] |- _ => change (negb false) with true in H; int_auto_simpl
    | |- context [negb false] => change (negb false) with true; int_auto_simpl

    | H: context [Int64.repr (Int64.signed _)] |- _ => rewrite Int64.repr_signed in H; int_auto_simpl
    | |- context [Int64.repr (Int64.signed _)] => rewrite Int64.repr_signed; int_auto_simpl
    | H: context [Int64.repr (Int64.unsigned _)] |- _ => rewrite Int64.repr_unsigned in H; int_auto_simpl
    | |- context [Int64.repr (Int64.unsigned _)] => rewrite Int64.repr_unsigned; int_auto_simpl

    | H: context [Int64.signed (Int64.repr _)] |- _ => rewrite Int64.signed_repr in H; [ int_auto_simpl | rewrite min_signed_val, max_signed_val; try lia ]
    | H: context [Int64.unsigned (Int64.repr _)] |- _ => rewrite Int64.unsigned_repr in H; [ int_auto_simpl | rewrite max_unsigned_val; try lia ]
    | |- context [Int64.signed (Int64.repr _)] => rewrite Int64.signed_repr; [ int_auto_simpl | rewrite min_signed_val, max_signed_val; try lia ]
    | |- context [Int64.unsigned (Int64.repr _)] => rewrite Int64.unsigned_repr; [ int_auto_simpl | rewrite max_unsigned_val; try lia ]

    | H: context [Int64.min_signed] |- _ => rewrite min_signed_val in H; int_auto_simpl
    | |- context [Int64.min_signed] => rewrite min_signed_val; int_auto_simpl
    | H: context [Int64.max_signed] |- _ => rewrite max_signed_val in H; int_auto_simpl
    | |- context [Int64.max_signed] => rewrite max_signed_val; int_auto_simpl
    | H: context [Int64.max_unsigned] |- _ => rewrite max_unsigned_val in H; int_auto_simpl
    | |- context [Int64.max_unsigned] => rewrite max_unsigned_val; int_auto_simpl

    | H: context [Int64.cmpu] |- _ => unfold Int64.cmpu in H; int_auto_simpl
    | H: context [Int64.eq] |- _ => unfold Int64.eq in H; int_auto_simpl
    | H: context [Int64.ltu] |- _ => unfold Int64.ltu in H; int_auto_simpl
    | H: context [Int64.add] |- _ => unfold Int64.add in H; int_auto_simpl
    | H: context [Int64.sub] |- _ => unfold Int64.sub in H; int_auto_simpl
    | H: context [Int64.mul] |- _ => unfold Int64.mul in H; int_auto_simpl
    | H: context [Int64.divu] |- _ => unfold Int64.divu in H; int_auto_simpl
    | H: context [Int64.divs] |- _ => unfold Int64.divs in H; int_auto_simpl
    | H: context [Int64.and] |- _ => unfold Int64.and in H; int_auto_simpl
    | H: context [Int64.or] |- _ => unfold Int64.or in H; int_auto_simpl
    | H: context [Int64.xor] |- _ => unfold Int64.xor in H; int_auto_simpl
    | H: context [Int64.shl] |- _ => unfold Int64.shl in H; int_auto_simpl
    | H: context [Int64.shr] |- _ => unfold Int64.shr in H; int_auto_simpl
    | H: context [Int64.lt] |- _ => unfold Int64.lt in H; int_auto_simpl
    | H: context [Int64.modu] |- _ => unfold Int64.modu in H; int_auto_simpl
  
    | |- context [Int64.cmpu] => unfold Int64.cmpu; int_auto_simpl
    | |- context [Int64.eq] => unfold Int64.eq; int_auto_simpl
    | |- context [Int64.ltu] => unfold Int64.ltu; int_auto_simpl
    | |- context [Int64.add] => unfold Int64.add; int_auto_simpl
    | |- context [Int64.sub] => unfold Int64.sub; int_auto_simpl
    | |- context [Int64.mul] => unfold Int64.mul; int_auto_simpl
    | |- context [Int64.divu] => unfold Int64.divu; int_auto_simpl
    | |- context [Int64.divs] => unfold Int64.divs; int_auto_simpl
    | |- context [Int64.and] => unfold Int64.and; int_auto_simpl
    | |- context [Int64.or] => unfold Int64.or; int_auto_simpl
    | |- context [Int64.xor] => unfold Int64.xor; int_auto_simpl
    | |- context [Int64.shl] => unfold Int64.shl; int_auto_simpl
    | |- context [Int64.shr] => unfold Int64.shr; int_auto_simpl
    | |- context [Int64.lt] => unfold Int64.lt; int_auto_simpl
    | |- context [Int64.modu] => unfold Int64.modu; int_auto_simpl

    | _ => repeat progress autorewritearith
  end.

Ltac int_auto_H :=
  int_auto_simpl;
  match goal with    
    | H: context[Int64.add] |- _ => rewrite Int64.add_signed in H; int_auto_H
    | H: context[Int64.sub] |- _ => rewrite Int64.sub_signed in H; int_auto_H
    | H: context [Int64.mul] |- _ => rewrite Int64.mul_signed in H; int_auto_H
    | H: context [_ ÷ _] |- _ => rewrite zdiv_equiv in H; int_auto_H
    
   
    | H: context [zle ?z1 ?z2] |- _ => destruct (zle z1 z2); int_auto_H
    | H: context [zlt ?z1 ?z2] |- _ => destruct (zlt z1 z2); int_auto_H
    | H: context [zeq ?z1 ?z2] |- _ => destruct (zeq z1 z2); int_auto_H
    
    | _ => idtac
  end.

Ltac int_auto' :=
  match goal with
    | |- _ /\ _ => split; int_auto'
    | |- Int64.repr _ = Int64.repr _ => apply Int64.eqm_samerepr; apply Int64.eqm_refl2; int_auto'
    | |- Int64.repr _ = _ => rewrite <- Int64.repr_signed; apply Int64.eqm_samerepr; apply Int64.eqm_refl2; int_auto'
    | |- _ = Int64.repr _ => rewrite <- Int64.repr_signed; apply Int64.eqm_samerepr; apply Int64.eqm_refl2; int_auto'
 
    | |- context[Int64.add] => rewrite Int64.add_signed; int_auto'
    | |- context[Int64.sub] => rewrite Int64.sub_signed; int_auto'
    | |- context[Int64.mul] => rewrite Int64.mul_signed; int_auto'
    | |- context [_ ÷ _] => rewrite zdiv_equiv; int_auto'    
  
    | |- context [zle ?z1 ?z2] => destruct (zle z1 z2); int_auto'
    | |- context [zlt ?z1 ?z2] => destruct (zlt z1 z2); int_auto'
    | |- context [zeq ?z1 ?z2] => destruct (zeq z1 z2); int_auto'
    
    | _ => solve_int_unequal || simpleproof
  end.

Ltac int_auto :=
  intros; 
  int_auto_H;
  int_auto'.

Ltac int_auto ::= 
     intros;
     int_auto_simpl;
  [ try solve [ simpleproof ];
    match goal with
      | |- _ /\ _ => split; int_auto
      | |- Int64.repr _ = Int64.repr _ => apply Int64.eqm_samerepr; apply Int64.eqm_refl2; int_auto
      | |- Int64.repr _ = _ => try solve [ rewrite <- Int64.repr_signed; apply Int64.eqm_samerepr; apply Int64.eqm_refl2; int_auto
                                       | rewrite <- Int64.repr_unsigned; apply Int64.eqm_samerepr; apply Int64.eqm_refl2; int_auto ]
      | |- _ = Int64.repr _ => try solve [ rewrite <- Int64.repr_signed; apply Int64.eqm_samerepr; apply Int64.eqm_refl2; int_auto
                                       | rewrite <- Int64.repr_unsigned; apply Int64.eqm_samerepr; apply Int64.eqm_refl2; int_auto ]                                                                                                        
      | H: context [zle ?z1 ?z2] |- _ => destruct (zle z1 z2); int_auto
      | H: context [zlt ?z1 ?z2] |- _ => destruct (zlt z1 z2); int_auto
      | H: context [zeq ?z1 ?z2] |- _ => destruct (zeq z1 z2); int_auto
      | |- context [zle ?z1 ?z2] => destruct (zle z1 z2); int_auto
      | |- context [zlt ?z1 ?z2] => destruct (zlt z1 z2); int_auto
      | |- context [zeq ?z1 ?z2] => destruct (zeq z1 z2); int_auto
      | _ => solve_int_unequal
    end
  | idtac.. ].

Tactic Notation "int" "auto" := int_auto.



Goal
  forall z1 z2,
    0 < z1 < Int64.max_signed ->
    0 < z2 < Int64.max_signed ->
    z1 < z2 ->
    Int64.sub (Int64.add (Int64.repr z1) (Int64.sub (Int64.repr z2) (Int64.repr z1))) (Int64.sub (Int64.repr z2) (Int64.repr z1)) = Int64.repr z1.
Proof.
  int auto.
  int auto.
  int auto.
  int auto.
Qed.

Goal
  forall x y,
    Int64.signed (Int64.repr 1) < x < Int64.signed (Int64.repr 100) ->
    Int64.signed (Int64.repr 1) < y < Int64.signed (Int64.repr 100) ->
    Int64.add (Int64.repr x) (Int64.repr y) = Int64.repr (y + x).
Proof.
  int auto.
Qed.
  

Goal forall x y, 1 < x < Int64.signed (Int64.repr 100) -> 1 < y < 100 
           -> Int64.min_signed <= x + y <= Int64.max_signed.
Proof.
  int auto.
Qed.

Goal forall x y,  0 < y < x -> x <= 1073741823 -> 
                   Int64.signed (Int64.add (Int64.repr x) (Int64.repr y))  =  x + y.
 Proof.
   int auto.
   int auto.
 Qed.

Goal forall x, Int64.ltu x (Int64.repr 100) =true -> 
               Int64.ltu (Int64.add x (Int64.repr 10))(Int64.repr 120) = true.
Proof.
  int auto.
  int auto.
Qed.

Goal forall x,
       Int64.signed x < 100 ->
       Int64.min_signed <= Int64.signed x + 10 <= Int64.max_signed.
Proof.
  int auto.
Qed.

Goal
  forall i1 i2,
    Int64.ltu (Int64.repr 0) i1 = true ->
    Int64.ltu i2 (Int64.repr Int64.max_signed) = true ->
    Int64.ltu i1 i2 = true ->
    Int64.unsigned (Int64.sub i1 i2) < 1  .
Proof.
  int auto.
  int auto.
Abort.

Goal
  forall i1 i2,
    Int64.ltu Int64.zero i1 = true ->
    Int64.ltu i1 i2 = true ->
    Int64.sub (Int64.add i1 (Int64.sub i2 i1)) (Int64.sub i2 i1) = i1.
Proof.
  int auto.
  int auto.
  int auto.
  int auto.
Qed.
